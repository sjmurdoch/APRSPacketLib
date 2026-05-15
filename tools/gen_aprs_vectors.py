#!/usr/bin/env python3
"""Generate, emit, and validate APRS test vectors.

The pipeline is:

    FIXED_POINTS / COURSE_CASES_DEG / SPEED_CASES_KN
                     │
                     │  generate          (writes JSON, byte-stable)
                     ▼
            tools/aprs_vectors.json    ◄── committed
                     │
       ┌─────────────┼───────────────────┐
       │             │                   │
   header        validate-*           (consumers)
       │             │
       ▼             ▼
test/common/   spec compliance
aprs_vectors.h checks (aprslib /
(committed)    Lean / direwolf)

Subcommands
-----------

    generate           Recompute the vectors from the spec formulas in
                       this file and (over)write tools/aprs_vectors.json.
                       Output is byte-stable across runs.

    header             Read the JSON and (over)write
                       test/common/aprs_vectors.h. Output is byte-stable.

    validate-aprslib   Decode-only cross-check. Hand each JSON-recorded
                       byte to aprslib's parser and assert the recovered
                       values match the JSON's expected fields, at the
                       tightest spec-justified tolerance.

    validate-lean      Decode + encode cross-check. Hand the JSON's
                       fixed-point rows to the Lean validator
                       (tools/ValidatedTestVectors/Main.lean). Lean
                       re-runs encodeLat/encodeLon (byte-exact) and
                       decodeLat/decodeLon (within the formally-proven
                       1/factor bound). The Python wrapper invokes
                       `lake env lean --run Main.lean` -- the macOS-safe
                       invocation documented in
                       tools/ValidatedTestVectors/CLAUDE.md.

    validate-direwolf  Stub. Direwolf encode + decode validation is on
                       the roadmap; this subcommand exists so the CLI
                       surface is stable. Returns 0 with an explanatory
                       message.

Bit-stable regeneration
-----------------------

Both aprs_vectors.json and aprs_vectors.h are committed. Re-running
`generate` followed by `header` must produce byte-identical files to
those in git. If a regeneration produces a diff, fix the generator,
not the committed artifact.

Validation tolerances
---------------------

Tolerances are picked at the tightest spec-/arithmetic-justified value
and the rationale lives next to each constant. See `_LAT_TOL_DEG`,
`_LON_TOL_DEG`, `_SPEED_TOL_KMH` in `_validate_aprslib`, and the
matching constants in `Main.lean`.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import warnings
from pathlib import Path

# aprslib 0.7.2 has unescaped backslashes in its regex literals,
# tripping SyntaxWarning under Python 3.12+. Filter once at import time.
warnings.filterwarnings(
    "ignore",
    category=SyntaxWarning,
    message=r"invalid escape sequence",
)


# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

REPO_ROOT        = Path(__file__).resolve().parent.parent
DEFAULT_JSON     = REPO_ROOT / "tools" / "aprs_vectors.json"
DEFAULT_HEADER   = REPO_ROOT / "test"  / "common" / "aprs_vectors.h"
DEFAULT_LEAN_DIR = REPO_ROOT / "tools" / "ValidatedTestVectors"


# ---------------------------------------------------------------------------
# Source-of-truth lists for `generate`
# ---------------------------------------------------------------------------

# To add coverage, edit here and re-run `generate`. The rest of the
# pipeline (header, validators) consumes the resulting JSON.

COURSE_CASES_DEG = [0, 88, 100, 180, 200, 356]
SPEED_CASES_KN   = [0, 30, 36, 50, 99]

# (name, lat_deg, lon_deg, course_deg, speed_kn, altitude_m).
FIXED_POINTS = [
    ("Munich",     48.138630,   11.573410,   90,  30,  525),
    ("CapeTown",  -33.918861,   18.423300,  180,  10,   25),
    ("Auckland",  -36.848460,  174.762189,  270, 100,    0),
    ("NorthPole",  89.999000,    0.000000,    0,   0, 5000),
    ("Equator0",    0.000000,    0.000000,    0,   0,    0),
]

# T-byte ('compression type'). The library always emits 'G' for the
# course/speed slot and 'Q' for the altitude slot.
T_BYTE_CS  = "G"
T_BYTE_ALT = "Q"

# APRS12c §9 'Conversion of Latitude/Longitude'. Lat range is 180°
# spread over 91^4-1 codes; lon is 360° spread over the same range
# (factor halved).
LAT_FACTOR = 380926
LON_FACTOR = 190463


# ---------------------------------------------------------------------------
# Spec-faithful encoders / decoders
# ---------------------------------------------------------------------------

def base91_pack(value: int, width: int) -> str:
    """Pack an int into `width` base-91 ASCII chars, big-endian.
    Each digit is in [0, 90] mapped to ASCII 33..123 ('!'..'{')."""
    if value < 0:
        raise ValueError(f"base91 cannot encode negative value {value}")
    out = []
    for i in range(width - 1, -1, -1):
        digit = (value // (91 ** i)) % 91
        out.append(chr(digit + 33))
    return "".join(out)


def encode_lat_base91(lat_deg: float) -> str:
    """APRS12c §9: YYYY = base91( floor(380926 * (90 - lat)) ).

    The spec's worked example on p.38 (190463 * 107.25 = 20427156.75
    quoted as 20427156, not rounded up) is decisive about flooring.
    Matches the C++ encoder (uint32_t truncation) and the Lean oracle
    (Int.floor)."""
    return base91_pack(math.floor(LAT_FACTOR * (90.0 - lat_deg)), 4)


def encode_lon_base91(lon_deg: float) -> str:
    """APRS12c §9: XXXX = base91( floor(190463 * (180 + lon)) )."""
    return base91_pack(math.floor(LON_FACTOR * (180.0 + lon_deg)), 4)


def encode_course(course_deg: int) -> str:
    """APRS12c §9 'Course/Speed': c = chr(round(course/4) + 33)."""
    return chr(round(course_deg / 4) + 33)


def encode_speed(speed_kn: int) -> str:
    """APRS12c §9 'Course/Speed': s = chr(round(log_1.08(speed+1)) + 33)."""
    return chr(round(math.log(speed_kn + 1) / math.log(1.08)) + 33)


def encode_altitude(altitude_ft: int) -> tuple[str, str]:
    """APRS12c §9 'Altitude': alt_c·91 + alt_s = log_1.002(altitude_ft).

    The library uses int truncation when packing the two digits;
    matched here so the on-the-wire bytes line up. For altitude_ft <= 0
    the library short-circuits to ('!','!')."""
    if altitude_ft <= 0:
        return ("!", "!")
    alt = math.log(altitude_ft) / math.log(1.002)
    alt1 = int(alt // 91)
    alt2 = int(alt) % 91
    return (chr(alt1 + 33), chr(alt2 + 33))


def decode_speed_kn(s_byte: str) -> float:
    """Spec-formula decode in knots, as a float (no rounding)."""
    return 1.08 ** (ord(s_byte) - 33) - 1


def decode_speed_kmh(s_byte: str) -> int:
    """Spec-formula decode rounded the way the C++ decoder rounds.
    The library returns `int` from a `double` expression, which both C
    and Python truncate toward zero. Matching that here lets the Unity
    test assert exact equality with no tolerance."""
    return int(decode_speed_kn(s_byte) * 1.852)


# ---------------------------------------------------------------------------
# Generate mode: build records, render JSON
# ---------------------------------------------------------------------------

def _build_records():
    """Compute every byte from the spec formulas and the source-of-truth
    lists at the top of this file. Returns (course_vecs, speed_vecs,
    fixed_points) where each row is a tuple/dict ready for
    `_render_json`."""
    course_vecs = [(encode_course(c), c) for c in COURSE_CASES_DEG]
    speed_vecs = [
        (encode_speed(s), s, decode_speed_kmh(encode_speed(s)))
        for s in SPEED_CASES_KN
    ]
    fixed_points = []
    for name, lat, lon, course, speed, alt_m in FIXED_POINTS:
        # Library's `int altitude` parameter is in feet; pre-convert.
        alt_ft = int(round(alt_m * 3.2808399))
        alt_c, alt_s = encode_altitude(alt_ft)
        fixed_points.append({
            "name":         name,
            "lat_deg":      lat,
            "lon_deg":      lon,
            "course_deg":   course,
            "speed_kn":     speed,
            "altitude_m":   alt_m,
            "altitude_ft":  alt_ft,
            "base91_lat":   encode_lat_base91(lat),
            "base91_lon":   encode_lon_base91(lon),
            "base91_c":     encode_course(course),
            "base91_s":     encode_speed(speed),
            "base91_alt_c": alt_c,
            "base91_alt_s": alt_s,
        })
    return course_vecs, speed_vecs, fixed_points


def _json_string(s: str) -> str:
    """Quote a Python string as a JSON string literal. Inputs are 7-bit
    ASCII (base-91 alphabet is 33..123); only `"` and `\\` need
    escaping."""
    out = ['"']
    for ch in s:
        if   ch == '"':  out.append('\\"')
        elif ch == '\\': out.append('\\\\')
        else:            out.append(ch)
    out.append('"')
    return "".join(out)


def _fmt_coord(v: float) -> str:
    """Render a coordinate as a JSON number with exactly 6 decimal
    places (~0.1 m, well below the encoder's 1/380926-deg ULP).

    json.dumps(48.138630) yields '48.13863' (drops trailing zero) so
    cannot be used. f'{v:.6f}' is byte-stable: for any float with at
    most 6 fractional digits of intent, the output is the canonical
    representation regardless of float repr quirks."""
    return f"{v:.6f}"


def _render_json(course_vecs, speed_vecs, fixed_points) -> str:
    """Hand-format the JSON. Templated rather than json.dumps()'d so
    that float formatting and key ordering are pinned by source code,
    not by the json module's internal heuristics. Produces stable bytes
    across Python versions and platforms."""
    L: list[str] = []
    L.append("{")
    L.append('  "_generator": "tools/gen_aprs_vectors.py generate",')
    L.append('  "_spec": "APRS Protocol Reference v1.2 section 9 (Compressed Position)",')
    L.append(f'  "_lat_factor": {LAT_FACTOR},')
    L.append(f'  "_lon_factor": {LON_FACTOR},')
    L.append(f'  "_t_byte_cs": {_json_string(T_BYTE_CS)},')
    L.append(f'  "_t_byte_alt": {_json_string(T_BYTE_ALT)},')

    L.append('  "course_vectors": [')
    for i, (encoded, course_deg) in enumerate(course_vecs):
        sep = "," if i < len(course_vecs) - 1 else ""
        L.append(
            f'    {{"course_deg": {course_deg}, '
            f'"encoded": {_json_string(encoded)}}}{sep}'
        )
    L.append('  ],')

    L.append('  "speed_vectors": [')
    for i, (encoded, kn_input, kmh_decoded) in enumerate(speed_vecs):
        sep = "," if i < len(speed_vecs) - 1 else ""
        L.append(
            f'    {{"speed_kn_input": {kn_input}, '
            f'"encoded": {_json_string(encoded)}, '
            f'"speed_kmh_decoded": {kmh_decoded}}}{sep}'
        )
    L.append('  ],')

    L.append('  "fixed_points": [')
    for i, p in enumerate(fixed_points):
        sep = "," if i < len(fixed_points) - 1 else ""
        L.append(
            "    {"
            f'"name": {_json_string(p["name"])}, '
            f'"lat_deg": {_fmt_coord(p["lat_deg"])}, '
            f'"lon_deg": {_fmt_coord(p["lon_deg"])}, '
            f'"course_deg": {p["course_deg"]}, '
            f'"speed_kn": {p["speed_kn"]}, '
            f'"altitude_m": {p["altitude_m"]}, '
            f'"altitude_ft": {p["altitude_ft"]}, '
            f'"base91_lat": {_json_string(p["base91_lat"])}, '
            f'"base91_lon": {_json_string(p["base91_lon"])}, '
            f'"base91_c": {_json_string(p["base91_c"])}, '
            f'"base91_s": {_json_string(p["base91_s"])}, '
            f'"base91_alt_c": {_json_string(p["base91_alt_c"])}, '
            f'"base91_alt_s": {_json_string(p["base91_alt_s"])}'
            "}" + sep
        )
    L.append('  ]')
    L.append('}')
    return "\n".join(L) + "\n"


def cmd_generate(args: argparse.Namespace) -> int:
    course_vecs, speed_vecs, fixed_points = _build_records()
    args.json.write_text(_render_json(course_vecs, speed_vecs, fixed_points))
    print(f"wrote {args.json}", file=sys.stderr)
    return 0


# ---------------------------------------------------------------------------
# Header mode: read JSON, render C header
# ---------------------------------------------------------------------------

def _c_string(s: str) -> str:
    out = ['"']
    for ch in s:
        if   ch == '"':  out.append('\\"')
        elif ch == '\\': out.append('\\\\')
        else:            out.append(ch)
    out.append('"')
    return "".join(out)


def _c_char(c: str) -> str:
    assert len(c) == 1
    if c == "'":  return "'\\''"
    if c == "\\": return "'\\\\'"
    return f"'{c}'"


def _render_header(data: dict) -> str:
    course_vecs  = data["course_vectors"]
    speed_vecs   = data["speed_vectors"]
    fixed_points = data["fixed_points"]

    L = [
        "// Generated by tools/gen_aprs_vectors.py — DO NOT EDIT BY HAND.",
        "//",
        "// Source: APRS Protocol Reference v1.2 §9 ('Compressed Position",
        "// Report Data Formats'). Each row is computed from the spec",
        "// formulas; aprslib is consulted as a third-party cross-check.",
        "",
        "#pragma once",
        "",
        "struct CourseVector { char encoded; int course_deg; };",
        "struct SpeedVector  { char encoded; int speed_kmh; };",
        "",
        "// Full-packet vectors for the five fixed sites used by",
        "// test_base91_encode and test_base91_roundtrip. Strings are",
        "// 4 base-91 chars + null terminator.",
        "struct Base91FixedPoint {",
        "    const char* name;",
        "    float       lat_deg;",
        "    float       lon_deg;",
        "    int         course_deg;",
        "    int         speed_kn;",
        "    int         altitude_m;",
        "    int         altitude_ft;",
        "    char        base91_lat[5];",
        "    char        base91_lon[5];",
        "    char        base91_c;",
        "    char        base91_s;",
        "    char        base91_alt_c;",
        "    char        base91_alt_s;",
        "};",
        "",
        f"static const char kBase91TByteCS  = {_c_char(data['_t_byte_cs'])};",
        f"static const char kBase91TByteAlt = {_c_char(data['_t_byte_alt'])};",
        "",
        "static const CourseVector kCourseVectors[] = {",
    ]
    for v in course_vecs:
        L.append(f"    {{ {_c_char(v['encoded']):<6}, {v['course_deg']:>3} }},")
    L.append("};")
    L.append("")
    L.append("static const SpeedVector kSpeedVectors[] = {")
    for v in speed_vecs:
        L.append(f"    {{ {_c_char(v['encoded']):<6}, {v['speed_kmh_decoded']:>3} }},")
    L.append("};")
    L.append("")
    L.append("static const Base91FixedPoint kBase91FixedPoints[] = {")
    for p in fixed_points:
        L.append(
            "    {{ {name:<13}, {lat:>13}f, {lon:>13}f, {course:>3}, {speed:>3}, "
            "{alt_m:>4}, {alt_ft:>5}, {b_lat:<8}, {b_lon:<8}, "
            "{b_c:<6}, {b_s:<6}, {b_ac:<6}, {b_as:<6} }},".format(
                name=_c_string(p["name"]),
                lat=f"{p['lat_deg']:.6f}",
                lon=f"{p['lon_deg']:.6f}",
                course=p["course_deg"],
                speed=p["speed_kn"],
                alt_m=p["altitude_m"],
                alt_ft=p["altitude_ft"],
                b_lat=_c_string(p["base91_lat"]),
                b_lon=_c_string(p["base91_lon"]),
                b_c=_c_char(p["base91_c"]),
                b_s=_c_char(p["base91_s"]),
                b_ac=_c_char(p["base91_alt_c"]),
                b_as=_c_char(p["base91_alt_s"]),
            )
        )
    L.append("};")
    L.append("")
    return "\n".join(L)


def cmd_header(args: argparse.Namespace) -> int:
    data = json.loads(args.json.read_text())
    args.header.write_text(_render_header(data))
    print(f"wrote {args.header}", file=sys.stderr)
    return 0


# ---------------------------------------------------------------------------
# validate-aprslib: decode-only cross-check
# ---------------------------------------------------------------------------

def cmd_validate_aprslib(args: argparse.Namespace) -> int:
    try:
        import aprslib  # type: ignore[import-not-found]
    except ImportError:
        print(
            "ERROR: aprslib not installed. Install with:\n"
            "  uv pip install --python tools/.venv/bin/python aprslib",
            file=sys.stderr,
        )
        return 2

    data = json.loads(args.json.read_text())
    lat_factor = data["_lat_factor"]
    lon_factor = data["_lon_factor"]
    t_byte_cs  = data["_t_byte_cs"]

    # Tolerance rationale (kept here, not at module top, so it sits
    # next to the comparison it governs):
    #
    # _LAT_TOL_DEG / _LON_TOL_DEG: exactly one ULP at the encoded-int
    # level. The decode formula is `90 - N/factor` (or `N/factor - 180`
    # for lon) where N = floor(factor * (offset + x)); the residual is
    # mathematically in [0, 1/factor) over reals. aprslib uses Python
    # floats whose round-off error is ~10⁷× smaller than 1/factor, so
    # this leaves no slack for unjustified disagreement.
    #
    # _SPEED_TOL_KMH: the spec formula `(1.08^(s-33) - 1) * 1.852` is a
    # closed-form double; aprslib evaluates the same expression. Only
    # last-bit float noise should appear -- 1e-9 km/h is ~10⁵× larger
    # than that and ~10⁹× smaller than any meaningful km/h value.
    _LAT_TOL_DEG   = 1.0 / lat_factor
    _LON_TOL_DEG   = 1.0 / lon_factor
    _SPEED_TOL_KMH = 1e-9

    failures: list[str] = []

    # Course/speed slot: cartesian product so each c-byte pairs with
    # every s-byte (parallels the legacy double-loop coverage).
    for cv in data["course_vectors"]:
        for sv in data["speed_vectors"]:
            c_byte = cv["encoded"]
            s_byte = sv["encoded"]
            packet = f"TEST>APRS:=/<<<<<<<<>{c_byte}{s_byte}{t_byte_cs}"
            parsed = aprslib.parse(packet)

            # APRS v1.2 reassigned encoded course 0 to mean due north (= 360).
            expected_course = 360 if cv["course_deg"] == 0 else cv["course_deg"]
            got_course = parsed.get("course")
            if got_course != expected_course:
                failures.append(
                    f"course byte {c_byte!r}: expected {expected_course}°, "
                    f"aprslib got {got_course}°"
                )

            spec_kmh = decode_speed_kn(s_byte) * 1.852
            got_speed = parsed.get("speed")
            if got_speed is None or abs(got_speed - spec_kmh) > _SPEED_TOL_KMH:
                failures.append(
                    f"speed byte {s_byte!r}: spec {spec_kmh} km/h, "
                    f"aprslib {got_speed} km/h "
                    f"(tolerance {_SPEED_TOL_KMH:.1e})"
                )

    # Fixed points: lat/lon decoded by aprslib from the recorded base-91
    # bytes; checked against the JSON's expected decimal-degree value.
    for p in data["fixed_points"]:
        info = (
            "=/" + p["base91_lat"] + p["base91_lon"]
            + ">" + p["base91_c"] + p["base91_s"] + t_byte_cs
        )
        packet = f"TEST>APRS:{info}"
        try:
            parsed = aprslib.parse(packet)
        except Exception as exc:  # pragma: no cover - diagnostic only
            failures.append(f"{p['name']}: aprslib raised {exc!r}")
            continue

        for field, expected, tol in (
            ("latitude",  p["lat_deg"], _LAT_TOL_DEG),
            ("longitude", p["lon_deg"], _LON_TOL_DEG),
        ):
            got = parsed.get(field)
            if got is None or abs(got - expected) >= tol:
                residual = None if got is None else got - expected
                failures.append(
                    f"{p['name']}: {field} expected {expected}, "
                    f"aprslib decoded {got} (residual {residual!r}, "
                    f"tolerance {tol:.3e} deg)"
                )

    if failures:
        print("FAIL: aprslib disagrees with JSON-recorded vectors:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(
        f"OK: {len(data['course_vectors'])} course × "
        f"{len(data['speed_vectors'])} speed pairs and "
        f"{len(data['fixed_points'])} fixed points round-trip through aprslib"
    )
    return 0


# ---------------------------------------------------------------------------
# validate-lean: encode + decode against the formally-proven Lean impl
# ---------------------------------------------------------------------------

def cmd_validate_lean(args: argparse.Namespace) -> int:
    data = json.loads(args.json.read_text())
    fps = data["fixed_points"]

    # Pipe-delimited input: name | lat_deg | lon_deg | base91_lat | base91_lon
    # `|` (ASCII 124) and `\n` (ASCII 10) lie outside the base-91 alphabet
    # (33..123), so neither needs escaping for any field carried below.
    rows = []
    for p in fps:
        rows.append(
            f"{p['name']}|{p['lat_deg']:.6f}|{p['lon_deg']:.6f}|"
            f"{p['base91_lat']}|{p['base91_lon']}"
        )
    stdin = "\n".join(rows) + "\n"

    if not args.lean_cwd.exists():
        print(f"ERROR: --lean-cwd {args.lean_cwd} not found", file=sys.stderr)
        return 2

    # `lake env lean --run Main.lean` is the macOS-safe invocation
    # documented in tools/ValidatedTestVectors/CLAUDE.md (the linked
    # exe target fails to link on macOS due to argv length limits, but
    # --run uses the .olean files directly).
    cmd = ["lake", "env", "lean", "--run", "Main.lean"]
    try:
        proc = subprocess.run(
            cmd,
            cwd=args.lean_cwd,
            input=stdin,
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError:
        print(
            "ERROR: `lake` not found on PATH. Install elan and Lean's lake:\n"
            "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh",
            file=sys.stderr,
        )
        return 2

    sys.stdout.write(proc.stdout)
    if proc.stderr:
        sys.stderr.write(proc.stderr)
    return proc.returncode


# ---------------------------------------------------------------------------
# validate-direwolf: stub
# ---------------------------------------------------------------------------

def cmd_validate_direwolf(args: argparse.Namespace) -> int:
    # Roadmap: invoke `kissutil` (or `decode_aprs`) to round-trip each
    # fixed point through Direwolf's encoder and decoder, then compare.
    # Tolerance plan: byte-exact for encode, ULP-tight for decode (same
    # rationale as validate-aprslib).
    print("direwolf validation not yet implemented")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="gen_aprs_vectors.py",
        description="Generate, emit, and validate APRS test vectors. "
                    "See module docstring for the full pipeline.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = p.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("generate", help="recompute and write the canonical JSON")
    g.add_argument("--json", type=Path, default=DEFAULT_JSON)
    g.set_defaults(func=cmd_generate)

    h = sub.add_parser("header",   help="emit the C header from the JSON")
    h.add_argument("--json",   type=Path, default=DEFAULT_JSON)
    h.add_argument("--header", type=Path, default=DEFAULT_HEADER)
    h.set_defaults(func=cmd_header)

    a = sub.add_parser("validate-aprslib", help="decode the JSON's bytes through aprslib")
    a.add_argument("--json", type=Path, default=DEFAULT_JSON)
    a.set_defaults(func=cmd_validate_aprslib)

    l = sub.add_parser("validate-lean",
                       help="encode + decode the JSON's rows through the Lean validator")
    l.add_argument("--json",     type=Path, default=DEFAULT_JSON)
    l.add_argument("--lean-cwd", type=Path, default=DEFAULT_LEAN_DIR)
    l.set_defaults(func=cmd_validate_lean)

    d = sub.add_parser("validate-direwolf",
                       help="(stub) encode + decode through Direwolf")
    d.add_argument("--json", type=Path, default=DEFAULT_JSON)
    d.set_defaults(func=cmd_validate_direwolf)

    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
