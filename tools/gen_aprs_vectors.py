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

    validate-direwolf  Decode + encode cross-check through Direwolf.
                       Decode pass: each course×speed pair and each
                       fixed point (twice -- cs slot carrying
                       course/speed, then altitude) is piped through
                       `decode_aprs(1)` and the parsed lat/lon,
                       course, speed and altitude are compared to the
                       JSON values at the tightest spec-justified
                       tolerance. Encode pass: each fixed point is
                       fed to `direwolf` via PBEACON COMPRESS=1,
                       the emitted base91 lat/lon bytes are captured
                       from the monitor log and compared two ways:
                       (a) byte-exact equality against our recorded
                       bytes (expected, since both we and direwolf
                       now round to nearest), and (b) decoded back
                       via the spec formula to within half an encoder
                       ULP of the input. Requires `decode_aprs` and
                       `direwolf` on PATH and an audio device with at
                       least one input channel (`brew install
                       direwolf` on macOS, plus a virtual loopback
                       like BlackHole 2ch if no real input device is
                       present).

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
`_LON_TOL_DEG`, `_SPEED_TOL_KMH` in `cmd_validate_aprslib` /
`cmd_validate_direwolf`, the altitude `_alt_tol_m` in
`cmd_validate_direwolf`, and the matching constants in `Main.lean`.
"""

from __future__ import annotations

import argparse
import json
import logging
import math
import re
import shutil
import subprocess
import sys
import warnings
from pathlib import Path

logger = logging.getLogger("gen_aprs_vectors")

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

# APRS12c §9 'Lat/Long Encoding' (p. 38). Lat range is 180° spread
# over 91^4-1 codes; lon is 360° spread over the same range (factor
# halved).
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


def base91_unpack(s: str) -> int:
    """Inverse of `base91_pack`. Each byte must lie in '!'..'{' (ASCII
    33..123); behaviour outside that range is unspecified."""
    n = 0
    for ch in s:
        n = n * 91 + (ord(ch) - 33)
    return n


def encode_lat_base91(lat_deg: float) -> str:
    """APRS12c §9 'Lat/Long Encoding' (p. 38):
        'YYYY  is 380926 x (90 – latitude)   [base 91]'

    The spec writes a real-valued expression and does not state a
    rounding mode for the encoder. We read it as round-to-nearest:
    that matches direwolf (the most widely-deployed reference
    implementation) and the L12 patch's `lround`, and halves the
    worst-case encode error vs. truncation. The cost is disagreement
    with the only worked example in §9, which silently floors
    (190463 × 107.25 = 20427156.75 quoted as 20427156, not rounded
    up). See wip/round_to_nearest_migration_plan.md for the full
    rationale and wip/bug_report_aprs_spec_lat_lon_example.md for the
    longer spec-ambiguity discussion.

    `int(x + 0.5)` rather than Python's `round()`: Python's round is
    banker's (ties to even); we want ties-away-from-zero to match
    C's `lround` and direwolf. For non-negative x (LAT_FACTOR ×
    (90 − lat) is always ≥ 0 over the valid range), `int(x + 0.5)`
    gives round-half-up, which coincides with ties-away on the
    positive reals."""
    return base91_pack(int(LAT_FACTOR * (90.0 - lat_deg) + 0.5), 4)


def encode_lon_base91(lon_deg: float) -> str:
    """APRS12c §9 'Lat/Long Encoding' (p. 38):
        'XXXX  is 190463 x (180 + longitude) [base 91]'

    Same rounding-mode and `int(x + 0.5)` rationale as
    encode_lat_base91 — see that docstring. LON_FACTOR × (180 + lon)
    is non-negative over the valid range."""
    return base91_pack(int(LON_FACTOR * (180.0 + lon_deg) + 0.5), 4)


def encode_course(course_deg: int) -> str:
    """APRS12c §9 'Course/Speed' (p. 39) gives only the decoder direction:
        'course = c x 4'
    with c constrained to numeric 0..89 (encoded course ∈ {0,4,…,356}).
    The spec does not write an encoder formula or state a rounding mode
    for the inversion; we round-to-nearest because it matches direwolf
    and halves the worst-case encode error vs. truncation. Direwolf's
    `(course + 2) / 4` integer expression rounds ties away from zero
    (for the non-negative course range that compressed positions cover);
    C's `lroundf` does the same.

    `int(x + 0.5)` rather than Python's `round()`: Python's `round` is
    banker's (ties to even); we want ties-away-from-zero to match C's
    `lroundf` and direwolf. For course_deg ≥ 0 (the only legal input
    range), `int(x + 0.5)` gives round-half-up, which coincides with
    ties-away on the non-negative reals. The lat/lon encoder above
    uses the same pattern for the same reason."""
    return chr(int(course_deg / 4 + 0.5) + 33)


def encode_speed(speed_kn: int) -> str:
    """APRS12c §9 'Course/Speed' (p. 39) gives only the decoder direction:
        'speed = 1.08^s – 1'  (knots)
    Inverting under round-to-nearest (same rounding-mode caveat as
    encode_course) gives s = round(log_1.08(speed + 1)). Same
    `int(x + 0.5)` ties-away rationale as encode_course; direwolf's
    `s = (int)round(log(speed+1.0)/log(1.08))` in `set_comp_position`
    uses C99 `round()`, which is also ties-away."""
    return chr(int(math.log(speed_kn + 1) / math.log(1.08) + 0.5) + 33)


def encode_altitude(altitude_ft: int) -> tuple[str, str]:
    """APRS12c §9 'Altitude' (p. 40) gives only the decoder direction:
        'altitude = 1.002^cs feet'  where cs = c × 91 + s
    Inverting gives cs = log_1.002(altitude_ft), with the two base-91
    digits c = cs // 91 and s = cs % 91. The spec does not specify a
    rounding mode for the inversion; the C++ library uses int
    truncation when packing the two digits, and we match that here
    so the on-the-wire bytes line up — a behavioural match to the
    library, not a spec mandate. For altitude_ft <= 0 the library
    short-circuits to ('!','!')."""
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
    logger.info("wrote %s", args.json)
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
    logger.info("wrote %s", args.header)
    return 0


# ---------------------------------------------------------------------------
# validate-aprslib: decode-only cross-check
# ---------------------------------------------------------------------------

def cmd_validate_aprslib(args: argparse.Namespace) -> int:
    try:
        import aprslib  # type: ignore[import-not-found]
    except ImportError:
        logger.error(
            "aprslib not installed. Install with:\n"
            "  uv pip install --python tools/.venv/bin/python aprslib"
        )
        return 2

    data = json.loads(args.json.read_text())
    lat_factor = data["_lat_factor"]
    lon_factor = data["_lon_factor"]
    t_byte_cs  = data["_t_byte_cs"]

    # Tolerance rationale (kept here, not at module top, so it sits
    # next to the comparison it governs):
    #
    # _LAT_TOL_DEG / _LON_TOL_DEG: half a ULP at the encoded-int
    # level. The decode formula is `90 - N/factor` (or `N/factor - 180`
    # for lon) where N = round(factor * (offset + x)) (our encoder uses
    # `int(x + 0.5)`, i.e. round-half-up); under round-to-nearest the
    # residual is mathematically in [-0.5/factor, 0.5/factor] over
    # reals. aprslib uses Python floats whose round-off error is many
    # orders of magnitude smaller than 0.5/factor, so the 1e-12 slack
    # is plenty for last-bit float noise.
    #
    # _SPEED_TOL_KMH: the spec speed decoder formula is `1.08^(s-33) - 1`
    # knots (§9 p. 39); we convert to km/h via the standard 1.852
    # factor (a unit conversion, not a spec formula). aprslib evaluates
    # the same closed-form. Only last-bit float noise should appear --
    # 1e-9 km/h is ~10⁵× larger than that and ~10⁹× smaller than any
    # meaningful km/h value.
    _LAT_TOL_DEG   = 0.5 / lat_factor + 1e-12
    _LON_TOL_DEG   = 0.5 / lon_factor + 1e-12
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

            # §9 'Course/Speed' (p. 39) defines course = c × 4 with no
            # special-casing of 0; the compressed-format section itself
            # has no 0=unknown/360=north convention (the only "no data"
            # mechanism for the c byte is c = ˽ space, described on the
            # preceding page). But Chapter 7 'Course and Speed' (p. 27)
            # defines course as '001-360' clockwise from north for the
            # uncompressed format, and Chapter 10 'Speed and Course
            # Encoding' (p. 49, Mic-E) spells out that '0 degrees
            # represents an unknown or indefinite course, and 360
            # degrees represents due north'. aprslib applies that
            # convention when decoding compressed course bytes too
            # (c = 0 → reported course 360), so we match it here to
            # make the cross-check pass. This is observed aprslib
            # behaviour, not a §9 mandate.
            expected_course = 360 if cv["course_deg"] == 0 else cv["course_deg"]
            got_course = parsed.get("course")
            course_ok = got_course == expected_course
            logger.debug(
                "aprslib course byte %r: ours=%s°, aprslib=%s° [%s]",
                c_byte, expected_course, got_course,
                "PASS" if course_ok else "FAIL",
            )
            if not course_ok:
                failures.append(
                    f"course byte {c_byte!r}: expected {expected_course}°, "
                    f"aprslib got {got_course}°"
                )

            spec_kmh = decode_speed_kn(s_byte) * 1.852
            got_speed = parsed.get("speed")
            speed_ok = got_speed is not None and abs(got_speed - spec_kmh) <= _SPEED_TOL_KMH
            speed_residual = (
                "n/a" if got_speed is None else f"{got_speed - spec_kmh:+.3e}"
            )
            logger.debug(
                "aprslib speed byte %r: ours=%.6f km/h, aprslib=%s km/h, "
                "residual=%s, tol=%.1e [%s]",
                s_byte, spec_kmh, got_speed, speed_residual, _SPEED_TOL_KMH,
                "PASS" if speed_ok else "FAIL",
            )
            if not speed_ok:
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
            ok = got is not None and abs(got - expected) < tol
            residual = "n/a" if got is None else f"{got - expected:+.3e}"
            logger.debug(
                "aprslib %s %s: ours=%s, aprslib=%s, residual=%s, "
                "tol=%.3e [%s]",
                p["name"], field, expected, got, residual, tol,
                "PASS" if ok else "FAIL",
            )
            if not ok:
                residual_val = None if got is None else got - expected
                failures.append(
                    f"{p['name']}: {field} expected {expected}, "
                    f"aprslib decoded {got} (residual {residual_val!r}, "
                    f"tolerance {tol:.3e} deg)"
                )

    if failures:
        logger.warning("FAIL: aprslib disagrees with JSON-recorded vectors:")
        for f in failures:
            logger.warning("  - %s", f)
        return 1
    logger.info(
        "OK: %d course × %d speed pairs and %d fixed points round-trip through aprslib",
        len(data['course_vectors']),
        len(data['speed_vectors']),
        len(data['fixed_points']),
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

    logger.debug("validate-lean: sending %d rows to Lean validator", len(rows))
    for row in rows:
        logger.debug("  -> %s", row)

    if not args.lean_cwd.exists():
        logger.error("--lean-cwd %s not found", args.lean_cwd)
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
        logger.error(
            "`lake` not found on PATH. Install elan and Lean's lake:\n"
            "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
        )
        return 2

    # Lean does its own per-row comparisons and prints them; surface its
    # output verbatim so its formatting (and pass/fail reporting) is
    # preserved. We don't re-parse it -- the return code is authoritative.
    sys.stdout.write(proc.stdout)
    if proc.stderr:
        sys.stderr.write(proc.stderr)
    return proc.returncode


# ---------------------------------------------------------------------------
# validate-direwolf: decode + encode cross-checks through Direwolf
# ---------------------------------------------------------------------------

# decode_aprs colours its output with ANSI escapes; strip them so the
# regexes below see plain text.
_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")

# `N|S DD MM.mmmm, E|W DDD MM.mmmm` — the position line direwolf emits
# for every successfully parsed compressed-position frame.
_LATLON_RE = re.compile(
    r"([NS])\s+(\d+)\s+(\d+\.\d+),\s+([EW])\s+(\d+)\s+(\d+\.\d+)"
)
# `<kmh> km/h (<mph> MPH), course <deg>` — only present when the T-byte
# selects course/speed and the cs slot is not the no-data sentinel.
_CS_RE = re.compile(r"(\d+)\s+km/h\s+\(\d+\s+MPH\),\s+course\s+(\d+)")
# `alt <m> m (<ft> ft)` — only present when the T-byte selects altitude.
_ALT_RE = re.compile(r"alt\s+(-?\d+)\s+m")

# Locations decode_aprs probes for tocalls.yaml, plus the Homebrew path
# it does *not* probe but which is the canonical macOS install dir. If
# any candidate has tocalls.yaml we cd there so the relative-path lookup
# inside decode_aprs succeeds and the noisy warning disappears from
# stdout.
_DIREWOLF_DATA_CANDIDATES = (
    Path("/usr/local/share/direwolf"),
    Path("/usr/share/direwolf"),
    Path("/opt/local/share/direwolf"),
    Path("/opt/homebrew/share/direwolf"),
)


def _find_direwolf_data_dir() -> Path | None:
    for cand in _DIREWOLF_DATA_CANDIDATES:
        if (cand / "tocalls.yaml").is_file():
            return cand
    return None


def _decode_via_direwolf(packet: str, exe: str, cwd: Path | None) -> dict:
    """Run `decode_aprs` on one monitor-format packet and return the
    parsed fields. Keys (subset of): `latitude`, `longitude`, `course`,
    `speed_kmh`, `altitude_m`, plus `_raw` (ANSI-stripped stdout) for
    failure diagnostics."""
    proc = subprocess.run(
        [exe],
        input=packet + "\n",
        capture_output=True,
        text=True,
        check=False,
        cwd=str(cwd) if cwd else None,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"decode_aprs exited {proc.returncode}: {proc.stderr.strip()!r}"
        )
    clean = _ANSI_RE.sub("", proc.stdout)
    parsed: dict = {"_raw": clean}
    m = _LATLON_RE.search(clean)
    if m:
        ns, lat_d, lat_m, ew, lon_d, lon_m = m.groups()
        lat = int(lat_d) + float(lat_m) / 60.0
        if ns == "S":
            lat = -lat
        lon = int(lon_d) + float(lon_m) / 60.0
        if ew == "W":
            lon = -lon
        parsed["latitude"]  = lat
        parsed["longitude"] = lon
    m = _CS_RE.search(clean)
    if m:
        parsed["speed_kmh"] = int(m.group(1))
        parsed["course"]    = int(m.group(2))
    m = _ALT_RE.search(clean)
    if m:
        parsed["altitude_m"] = int(m.group(1))
    return parsed


# ---- encode side: drive `direwolf` to emit PBEACONs and capture the bytes ----

# Beacon monitor line: `[<chan>] <SRC>>... :!/<lat4><lon4><sym>...`.
# Direwolf prints these regardless of audio outcome -- we never decode
# the modulated audio, we just scrape the textual log.
_BEACON_LINE_RE = re.compile(
    r"^\[\s*[0-9.]+\s*\]\s+(?P<src>[A-Z0-9-]+)>[^:]+:!/(?P<lat>.{4})(?P<lon>.{4})"
)
# Audio-device dump produced by direwolf at startup; we use it to pick a
# device when the user hasn't named one and direwolf's default lookup
# fails (common on macOS). Each block looks like:
#
#     Name        = "BlackHole 2ch"
#     Host API    = Core Audio
#     Max inputs  = 2
#     Max outputs = 2
_DEVICE_BLOCK_RE = re.compile(
    r'Name\s*=\s*"(?P<name>[^"]+)"\s*\n'
    r'[^\n]*\n'
    r'\s*Max inputs\s*=\s*(?P<inputs>\d+)'
)


def _direwolf_run(conf: str, exe: str, cwd: Path | None, timeout: float) -> str:
    """Run direwolf with `conf` as the configuration file contents. We
    write a tempfile because direwolf reads its config via fopen, not
    stdin -- the `-c -` form is not supported. Returns the combined
    stdout/stderr with ANSI colour codes stripped."""
    import tempfile
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".conf", delete=False
    ) as f:
        f.write(conf)
        conf_path = f.name
    try:
        try:
            proc = subprocess.run(
                [exe, "-c", conf_path, "-t", "0", "-q", "hd"],
                capture_output=True,
                text=True,
                check=False,
                timeout=timeout,
                cwd=str(cwd) if cwd else None,
            )
            out = proc.stdout + proc.stderr
        except subprocess.TimeoutExpired as exc:
            out = (exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")) \
                + (exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or ""))
    finally:
        Path(conf_path).unlink(missing_ok=True)
    return _ANSI_RE.sub("", out)


def _direwolf_pick_audio_device(exe: str, cwd: Path | None) -> str | None:
    """Run direwolf with a stub config that has no ADEVICE; parse the
    enumerated device list it prints during startup, and pick the first
    device with at least one input channel. Returns the device name to
    pass via ADEVICE, or None if no suitable device exists."""
    stub = "ACHANNELS 1\nCHANNEL 0\nMYCALL TEST\nMODEM 1200\n"
    out = _direwolf_run(stub, exe, cwd, timeout=8.0)
    for m in _DEVICE_BLOCK_RE.finditer(out):
        if int(m.group("inputs")) > 0:
            return m.group("name")
    return None


def _encode_via_direwolf(
    points: list[dict],
    exe: str,
    audio_device: str,
    cwd: Path | None,
) -> dict[str, tuple[str, str]]:
    """Run direwolf with one staggered PBEACON per point and return
    {source_callsign: (base91_lat, base91_lon)}. Each point's beacon
    uses SENDTO=R0 (simulated reception) so direwolf never has to
    actually modulate audio -- the monitor line still prints."""
    lines = [
        f'ADEVICE "{audio_device}" "{audio_device}"',
        "ACHANNELS 1",
        "CHANNEL 0",
        "MYCALL TEST",
        "MODEM 1200",
    ]
    sources: list[str] = []
    for i, p in enumerate(points):
        src = f"TEST{i + 1}"
        sources.append(src)
        # DELAY=0:0N means N seconds; stagger so beacons don't collide.
        lines.append(
            f"PBEACON DELAY=0:0{i + 1} EVERY=10:00 SENDTO=R0 "
            f"SOURCE={src} LAT={p['lat_deg']:.6f} LONG={p['lon_deg']:.6f} "
            f"SYMBOL=/> COMPRESS=1"
        )
    conf = "\n".join(lines) + "\n"

    # Allow ~3s startup + 1s per beacon + a small safety margin.
    out = _direwolf_run(conf, exe, cwd, timeout=5.0 + len(points))

    captured: dict[str, tuple[str, str]] = {}
    for line in out.splitlines():
        m = _BEACON_LINE_RE.match(line)
        if m and m.group("src") in sources:
            captured[m.group("src")] = (m.group("lat"), m.group("lon"))
    return captured


def cmd_validate_direwolf(args: argparse.Namespace) -> int:
    exe = shutil.which("decode_aprs")
    if not exe:
        logger.error(
            "`decode_aprs` not found on PATH. Install Direwolf:\n"
            "  brew install direwolf      # macOS\n"
            "  apt-get install direwolf   # Debian/Ubuntu"
        )
        return 2

    data       = json.loads(args.json.read_text())
    lat_factor = data["_lat_factor"]
    lon_factor = data["_lon_factor"]
    t_byte_cs  = data["_t_byte_cs"]
    t_byte_alt = data["_t_byte_alt"]
    cwd        = _find_direwolf_data_dir()

    # Tolerance rationale (kept here, not at module top, so it sits
    # next to the comparison it governs):
    #
    # _LAT_TOL_DEG / _LON_TOL_DEG: the encoder rounds to nearest, so
    # encode error is at most half a ULP (≈1.3e-6 deg lat /
    # ≈2.6e-6 deg lon). decode_aprs prints `DD MM.mmmm`, so the
    # readback adds half-of-last-digit ≈ 0.5 * 1e-4 / 60 ≈ 8.3e-7
    # deg — which doesn't shrink with the encoder migration. Use the
    # half-ULP bound plus a 1e-6 slack covering the print truncation
    # plus float noise.
    #
    # _SPEED_TOL_KMH: direwolf prints km/h as a rounded integer (the
    # C library truncates; see decode_speed_kmh docstring). Comparing
    # the direwolf integer against the closed-form spec float must
    # therefore tolerate the half-LSB rounding gap. ±1 km/h is the
    # bound; anything tighter would fail on every speed whose km/h
    # value is within 0.5 of an integer (e.g. 'T' at 91.90 km/h:
    # truncates to 91, rounds to 92).
    #
    # _alt_tol_m(m): encoder is `int(log_1.002(ft))` -- one ULP in
    # log space means ft is recovered within a multiplicative factor
    # of 1.002, i.e. up to `m * 0.002` metres lost. direwolf rounds
    # the metre value when printing, adding another ±1 m. Combined
    # bound: `ceil(m * 0.002) + 1` metres. Scales naturally with
    # altitude -- the NorthPole 5000 m case sits at ±11 m, sea-level
    # cases at ±1 m.
    _LAT_TOL_DEG   = 0.5 / lat_factor + 1e-6
    _LON_TOL_DEG   = 0.5 / lon_factor + 1e-6
    _SPEED_TOL_KMH = 1
    def _alt_tol_m(m: int) -> int:
        return math.ceil(m * 0.002) + 1

    failures: list[str] = []

    # Course/speed slot: cartesian product so each c-byte pairs with
    # every s-byte (parallels validate-aprslib's coverage).
    for cv in data["course_vectors"]:
        for sv in data["speed_vectors"]:
            c_byte = cv["encoded"]
            s_byte = sv["encoded"]
            packet = f"TEST>APRS:=/<<<<<<<<>{c_byte}{s_byte}{t_byte_cs}"
            try:
                got = _decode_via_direwolf(packet, exe, cwd)
            except RuntimeError as exc:
                failures.append(f"{packet!r}: {exc}")
                continue

            # decode_aprs prints encoded-course 0 as 0 (not 360, the
            # uncompressed/Mic-E 0=unknown/360=due-north convention
            # aprslib applies — see cmd_validate_aprslib for the spec
            # citations). Compare against the raw JSON value.
            got_course = got.get("course")
            course_ok = got_course == cv["course_deg"]
            logger.debug(
                "direwolf course byte %r: ours=%s°, direwolf=%s° [%s]",
                c_byte, cv["course_deg"], got_course,
                "PASS" if course_ok else "FAIL",
            )
            if not course_ok:
                failures.append(
                    f"course byte {c_byte!r}: expected {cv['course_deg']}°, "
                    f"direwolf got {got_course}°"
                )

            # Compare against the spec float; the JSON's
            # `speed_kmh_decoded` is the *truncating* C-library value
            # and disagrees with direwolf's rounded print by ~1 km/h
            # whenever the float lies within 0.5 of an integer.
            spec_kmh = decode_speed_kn(s_byte) * 1.852
            got_kmh = got.get("speed_kmh")
            speed_ok = got_kmh is not None and abs(got_kmh - spec_kmh) <= _SPEED_TOL_KMH
            speed_residual = "n/a" if got_kmh is None else f"{got_kmh - spec_kmh:+.3f}"
            logger.debug(
                "direwolf speed byte %r: ours=%.3f km/h, direwolf=%s km/h, "
                "residual=%s, tol=±%s km/h [%s]",
                s_byte, spec_kmh, got_kmh, speed_residual, _SPEED_TOL_KMH,
                "PASS" if speed_ok else "FAIL",
            )
            if not speed_ok:
                failures.append(
                    f"speed byte {s_byte!r}: spec {spec_kmh:.3f} km/h, "
                    f"direwolf got {got_kmh} km/h "
                    f"(tolerance ±{_SPEED_TOL_KMH} km/h)"
                )

    # Fixed points: lat/lon from the recorded base-91 bytes (cs slot
    # carries course/speed for one packet, altitude for the other so
    # we exercise both T-byte branches).
    for p in data["fixed_points"]:
        packet_cs = (
            "TEST>APRS:=/"
            f"{p['base91_lat']}{p['base91_lon']}>"
            f"{p['base91_c']}{p['base91_s']}{t_byte_cs}"
        )
        try:
            got = _decode_via_direwolf(packet_cs, exe, cwd)
        except RuntimeError as exc:
            failures.append(f"{p['name']}: {exc}")
            continue

        for field, expected, tol in (
            ("latitude",  p["lat_deg"], _LAT_TOL_DEG),
            ("longitude", p["lon_deg"], _LON_TOL_DEG),
        ):
            v = got.get(field)
            ok = v is not None and abs(v - expected) <= tol
            residual = "n/a" if v is None else f"{v - expected:+.3e}"
            logger.debug(
                "direwolf %s %s: ours=%s, direwolf=%s, residual=%s, "
                "tol=%.3e [%s]",
                p["name"], field, expected, v, residual, tol,
                "PASS" if ok else "FAIL",
            )
            if not ok:
                residual_val = None if v is None else v - expected
                failures.append(
                    f"{p['name']}: {field} expected {expected}, "
                    f"direwolf got {v} (residual {residual_val!r}, "
                    f"tolerance {tol:.3e} deg)"
                )

        packet_alt = (
            "TEST>APRS:=/"
            f"{p['base91_lat']}{p['base91_lon']}>"
            f"{p['base91_alt_c']}{p['base91_alt_s']}{t_byte_alt}"
        )
        try:
            got = _decode_via_direwolf(packet_alt, exe, cwd)
        except RuntimeError as exc:
            failures.append(f"{p['name']} (alt): {exc}")
            continue

        v = got.get("altitude_m")
        alt_tol = _alt_tol_m(p["altitude_m"])
        alt_ok = v is not None and abs(v - p["altitude_m"]) <= alt_tol
        alt_residual = "n/a" if v is None else f"{v - p['altitude_m']:+d}"
        logger.debug(
            "direwolf %s altitude_m: ours=%d, direwolf=%s, residual=%s m, "
            "tol=±%d m [%s]",
            p["name"], p["altitude_m"], v, alt_residual, alt_tol,
            "PASS" if alt_ok else "FAIL",
        )
        if not alt_ok:
            failures.append(
                f"{p['name']}: altitude_m expected {p['altitude_m']}, "
                f"direwolf got {v} (tolerance ±{alt_tol} m)"
            )

    # ---- encode pass: drive direwolf's compressed-position encoder ----
    #
    # Coverage is narrower than the decode side: direwolf's PBEACON
    # command is for stationary stations, so it never emits base91
    # course/speed bytes (the cs slot is the two-space "no-data"
    # sentinel) and writes altitude as the comment-style
    # `/A=NNNNNN` block rather than packing it into cs with T='Q'.
    # That leaves lat/lon as the only base91 fields direwolf produces,
    # so this pass round-trips those alone.
    #
    # Tolerance: 0.5/factor + 1e-12 (half a ULP, since both our
    # encoder and direwolf round to nearest -- so byte-exact
    # agreement with direwolf is *expected*, not just round-trip-
    # within-ULP). The base91 byte equality is also checked below as
    # a separate failure so any future divergence (regression on our
    # side, direwolf behaviour change, or someone re-introducing
    # truncation) surfaces explicitly instead of hiding inside the
    # round-trip slack.
    encode_direwolf = shutil.which("direwolf")
    if encode_direwolf:
        audio_device = _direwolf_pick_audio_device(encode_direwolf, cwd)
        if not audio_device:
            failures.append(
                "encode: no audio-input device found via direwolf; "
                "the encode oracle requires one device with Max inputs > 0 "
                "(install BlackHole 2ch on macOS, or any ALSA capture device on Linux)"
            )
        else:
            captured = _encode_via_direwolf(
                data["fixed_points"], encode_direwolf, audio_device, cwd
            )
            _ENCODE_TOL_LAT_DEG = 0.5 / lat_factor + 1e-12
            _ENCODE_TOL_LON_DEG = 0.5 / lon_factor + 1e-12
            for i, p in enumerate(data["fixed_points"]):
                src = f"TEST{i + 1}"
                bytes_pair = captured.get(src)
                if bytes_pair is None:
                    failures.append(
                        f"encode {p['name']}: no PBEACON line captured from direwolf"
                    )
                    continue
                lat_bytes, lon_bytes = bytes_pair
                # Byte-equality check: under round-to-nearest both we
                # and direwolf should land on the same encoded bytes.
                # If they ever diverge, the round-trip-within-ULP test
                # below would still pass (the residual is half a ULP
                # in either direction), so check bytes explicitly.
                for field, expected_bytes, got_bytes in (
                    ("lat", p["base91_lat"], lat_bytes),
                    ("lon", p["base91_lon"], lon_bytes),
                ):
                    bytes_ok = got_bytes == expected_bytes
                    logger.debug(
                        "direwolf encode %s %s bytes: ours=%r, direwolf=%r [%s]",
                        p["name"], field, expected_bytes, got_bytes,
                        "PASS" if bytes_ok else "FAIL",
                    )
                    if not bytes_ok:
                        failures.append(
                            f"encode {p['name']}: {field} bytes expected "
                            f"{expected_bytes!r}, direwolf emitted "
                            f"{got_bytes!r} (byte-exact agreement is "
                            f"expected post-round-to-nearest migration)"
                        )
                dw_lat = 90.0  - base91_unpack(lat_bytes) / lat_factor
                dw_lon = base91_unpack(lon_bytes) / lon_factor - 180.0
                for field, exp, got, tol, raw_bytes in (
                    ("lat", p["lat_deg"], dw_lat, _ENCODE_TOL_LAT_DEG, lat_bytes),
                    ("lon", p["lon_deg"], dw_lon, _ENCODE_TOL_LON_DEG, lon_bytes),
                ):
                    rt_ok = abs(got - exp) <= tol
                    logger.debug(
                        "direwolf encode %s %s round-trip: ours=%s, "
                        "direwolf=%r -> %s, residual=%+.3e, tol=%.3e [%s]",
                        p["name"], field, exp, raw_bytes, got, got - exp, tol,
                        "PASS" if rt_ok else "FAIL",
                    )
                    if not rt_ok:
                        failures.append(
                            f"encode {p['name']}: {field} input {exp}, "
                            f"direwolf encoded {raw_bytes!r} "
                            f"-> {got} (residual {got - exp:.3e}, "
                            f"tolerance {tol:.3e} deg)"
                        )
    else:
        # decode_aprs is present (checked above) but the daemon binary
        # is missing -- unusual; just record and continue.
        failures.append(
            "encode: `direwolf` binary not on PATH; "
            "encode pass skipped (decode pass still ran)"
        )

    if failures:
        logger.warning("FAIL: direwolf disagrees with JSON-recorded vectors:")
        for f in failures:
            logger.warning("  - %s", f)
        return 1
    logger.info(
        "OK: %d course × %d speed pairs and %d fixed points (×2 cs/alt) decode, "
        "plus %d encode round-trips, all match direwolf within spec tolerance",
        len(data['course_vectors']),
        len(data['speed_vectors']),
        len(data['fixed_points']),
        len(data['fixed_points']),
    )
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
    p.add_argument(
        "-v", "--verbose",
        action="count",
        default=0,
        help="increase log verbosity (-v for DEBUG: per-comparison detail "
             "in validate-* subcommands)",
    )
    p.add_argument(
        "-q", "--quiet",
        action="store_true",
        help="suppress INFO-level output; only warnings and errors are shown",
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
                       help="decode + encode cross-check through Direwolf")
    d.add_argument("--json", type=Path, default=DEFAULT_JSON)
    d.set_defaults(func=cmd_validate_direwolf)

    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    if args.quiet:
        level = logging.WARNING
    elif args.verbose >= 1:
        level = logging.DEBUG
    else:
        level = logging.INFO
    # Configure the root handler at WARNING so noisy third-party
    # libraries (aprslib emits DEBUG-per-parse-step) stay quiet, and
    # bump only our own logger to the requested level. Levels are
    # filtered at the originating logger before propagation, so our
    # DEBUG/INFO records still reach the root handler.
    logging.basicConfig(
        level=logging.WARNING,
        format="%(levelname)s %(message)s",
        stream=sys.stderr,
    )
    logger.setLevel(level)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
