# tools/

Helper scripts. Set up with `uv`:

```sh
uv venv tools/.venv --python 3.13
uv pip install --python tools/.venv/bin/python aprslib
```

## gen_aprs_vectors.py

Generates `test/common/aprs_vectors.h` — committed test vectors for
the compressed-position (Base91) format, derived from APRS Protocol
Reference v1.2 §9. The header contains:

- `kCourseVectors` / `kSpeedVectors` — single-byte (encoded, expected
  decode) pairs for the c/s slot.
- `kBase91FixedPoints` — five hand-picked sites (Munich, Cape Town,
  Auckland, North Pole, Equator-0). The `base91_lat`/`base91_lon`
  bytes are imported from `Validated_Test_Vectors/proved_vectors.json`
  (see below); course/speed/altitude bytes are computed locally from
  the spec formulas.

Each row is cross-checked against aprslib's `parse()` before emission;
the script aborts loudly if aprslib disagrees with the emitted bytes.

Unity tests under `test/test_base91_*/` consume the generated header.
Re-run after editing the case lists at the top of the script:

```sh
tools/.venv/bin/python tools/gen_aprs_vectors.py
```

## Validated_Test_Vectors/

A Lean 4 / Mathlib project that formally proves the round-trip
property of the compressed lat/lon base-91 encoding (theorems
`encodeLat_decodeLat_roundtrip`, `encodeLon_decodeLon_roundtrip`).
Its `Main.lean` also acts as a generator: invoking it writes
`proved_vectors.json` containing the spec-faithful base-91
encodings for the same fixed-point list that `gen_aprs_vectors.py`
uses.

The spec example on page 38 of APRS Protocol Reference v1.2 is
unambiguous about flooring (`190463 × 107.25 = 20427156.75` is
quoted as `20427156`, not rounded up). Lean's `encodeLat`/`encodeLon`
use `Int.floor`; matches the C++ encoder, which uses `uint32_t`
truncation. The Python generator now consumes these floor-based
bytes rather than computing its own.

Regenerate the JSON after editing `Main.lean`'s `fixedPoints`:

```sh
cd tools/Validated_Test_Vectors && lake env lean --run Main.lean
```

(On macOS, `lake exe validated_test_vectors` currently fails at the
link step — `lake env lean --run` bypasses that by running the Lean
script directly. See `tools/Validated_Test_Vectors/CLAUDE.md` for
details.)

If you change `FIXED_POINTS` in `gen_aprs_vectors.py`, update the
parallel `fixedPoints` list in `Main.lean` and regenerate the JSON
before re-running the Python script — otherwise the Python side
will abort with a "fixed point missing from proved_vectors.json"
error.
