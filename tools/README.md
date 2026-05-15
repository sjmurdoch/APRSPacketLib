# tools/

Helper scripts. Set up the venv with `uv`:

```sh
uv venv tools/.venv --python 3.13
uv pip install --python tools/.venv/bin/python aprslib
```

## gen_aprs_vectors.py

A multi-mode tool that owns the lifecycle of the APRS test vectors:

```
FIXED_POINTS / COURSE_CASES_DEG / SPEED_CASES_KN  (in the .py)
                ↓ generate
tools/aprs_vectors.json                           (committed)
                ↓ header
test/common/aprs_vectors.h                        (committed)
                ↓ validate-{aprslib,lean,direwolf}
                  spec / oracle compliance reports
```

### Subcommands

| Subcommand           | Reads                | Writes                          | Cross-checks                                      |
|----------------------|----------------------|---------------------------------|---------------------------------------------------|
| `generate`           | `FIXED_POINTS` etc.  | `tools/aprs_vectors.json`       | —                                                 |
| `header`             | `aprs_vectors.json`  | `test/common/aprs_vectors.h`    | —                                                 |
| `validate-aprslib`   | `aprs_vectors.json`  | —                               | aprslib parse → recovered fields (decode only)    |
| `validate-lean`      | `aprs_vectors.json`  | —                               | Lean `encodeLat`/`decodeLat` etc. (encode+decode) |
| `validate-direwolf`  | `aprs_vectors.json`  | —                               | (stub; planned)                                   |

```sh
tools/.venv/bin/python tools/gen_aprs_vectors.py generate
tools/.venv/bin/python tools/gen_aprs_vectors.py header
tools/.venv/bin/python tools/gen_aprs_vectors.py validate-aprslib
tools/.venv/bin/python tools/gen_aprs_vectors.py validate-lean
tools/.venv/bin/python tools/gen_aprs_vectors.py validate-direwolf
```

`--json` and `--header` flags override the default paths.

### Bit-stable regeneration

Both `aprs_vectors.json` and `aprs_vectors.h` are committed. Re-running
`generate` followed by `header` must produce **byte-identical** files
to those in git. If `git diff` shows changes after re-running, fix the
generator -- do not hand-edit the artefacts.

The JSON serializer is hand-templated (not `json.dumps`) so float
formatting is pinned to `f"{v:.6f}"` and key ordering is pinned by
source-code order, not by `sort_keys`. The header emitter uses the
same fixed-width formatting it always has.

### Validation tolerances

Tolerances are picked at the tightest spec-/arithmetic-justified
value. Rationale lives next to each constant in the source so changes
are reviewable.

| Mode                | Field                  | Tolerance                                         | Source                                                  |
|---------------------|------------------------|---------------------------------------------------|---------------------------------------------------------|
| `validate-aprslib`  | `latitude`  (deg)      | `1 / 380926` (one encoder ULP)                    | `_LAT_TOL_DEG`   in `gen_aprs_vectors.py`               |
| `validate-aprslib`  | `longitude` (deg)      | `1 / 190463` (one encoder ULP)                    | `_LON_TOL_DEG`   in `gen_aprs_vectors.py`               |
| `validate-aprslib`  | `course` (deg)         | exact int (with v1.2 0↔360 normalization)         | inline check in `gen_aprs_vectors.py`                   |
| `validate-aprslib`  | `speed` (km/h)         | `1e-9` (closed-form double; only float noise)     | `_SPEED_TOL_KMH` in `gen_aprs_vectors.py`               |
| `validate-lean`     | `encodeLat`/`encodeLon`| **byte-exact** (zero)                             | `validateRow`    in `Main.lean`                         |
| `validate-lean`     | `decodeLat` (deg)      | `1 / latFactor` (proven `floor_error_lt_one`)     | `latTol`         in `Main.lean`                         |
| `validate-lean`     | `decodeLon` (deg)      | `1 / lonFactor` (proven `floor_error_lt_one`)     | `lonTol`         in `Main.lean`                         |

The Lean tolerances are tighter than `latEpsilon = 1/300000` /
`lonEpsilon = 1/150000` in `ValidatedTestVectors/Basic.lean`. Those
constants exist to give `linarith` proof slack; they are unsuitable as
runtime validation tolerances.

## ValidatedTestVectors/

A standalone Lean 4 / Mathlib project that

1. **proves** the round-trip property of the APRS Base91
   compressed-position encoding (theorems
   `encodeLat_decodeLat_roundtrip`, `encodeLon_decodeLon_roundtrip` in
   `ValidatedTestVectors/Basic.lean`), and
2. acts as the **runtime validator** for the JSON produced by
   `gen_aprs_vectors.py`. `Main.lean` reads pipe-delimited rows from
   stdin, re-runs `encodeLat`/`encodeLon`/`decodeLat`/`decodeLon` on
   each, and prints `OK <name>` or `FAIL <name>: <reason>`.

The `validate-lean` subcommand of `gen_aprs_vectors.py` invokes the
validator via `lake env lean --run Main.lean` -- the macOS-safe
invocation documented in `tools/ValidatedTestVectors/CLAUDE.md` (the
linked exe target fails to link on macOS due to argv length limits,
but `--run` uses the `.olean` artefacts directly and skips the link).

Direct invocation:

```sh
cd tools/ValidatedTestVectors
echo 'Munich|48.138630|11.573410|6/Y`|QG2.' | lake env lean --run Main.lean
```

The first build downloads Mathlib and can take 10+ minutes. Subsequent
runs are incremental.
