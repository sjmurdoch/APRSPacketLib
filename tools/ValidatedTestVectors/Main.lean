import ValidatedTestVectors
import Mathlib

/-! # Lean validator for `tools/aprs_vectors.json`

  Reads pipe-delimited rows from stdin and reports, per row, whether
  Lean's formally-proven `encodeLat`/`encodeLon`/`decodeLat`/`decodeLon`
  agree with the bytes and decimal coordinates in the JSON.

  Invocation (from this directory):

      lake env lean --run Main.lean

  Input format on stdin (one row per line):

      <name>|<lat_deg>|<lon_deg>|<base91_lat>|<base91_lon>

  `|` (ASCII 124) and `\n` (ASCII 10) lie outside the base-91 alphabet
  (33..123), so neither needs escaping for any field carried below.

  Tolerances
  ----------

  Encode side: byte equality. Lean computes `floor((90-x)*latFactor)`
  over `Rat` (exact); Python's `gen_aprs_vectors.py` computes the same
  floored integer over `Float`. For the canonical 6-decimal coordinates
  in the JSON, the float and rational answers agree, so any byte
  difference is a real bug, not a numeric artefact -- tolerance must be
  zero.

  Decode side: `latTol = 1 / latFactor`, `lonTol = 1 / lonFactor`. The
  proven `BoundedRoundTrip` bound is `< 1/factor` exactly (combine
  `floor_error_nonneg`, `floor_error_lt_one`, and `fromBase91_toBase91`
  in `Basic.lean`). The `latEpsilon = 1/300000` / `lonEpsilon = 1/150000`
  constants in `Basic.lean` are intentionally looser to give `linarith`
  proof slack; they are unsuitable as validation tolerances and are
  *not* used here.
-/

/-- Tightest decode tolerances permitted by the floor-rule encoder. -/
def latTol : Rat := 1 / latFactor
def lonTol : Rat := 1 / lonFactor

def absRat (q : Rat) : Rat := if q < 0 then -q else q

/-- Parse a signed decimal string like `-33.918861` into a `Rat`.
    Accepts the strict format the Python generator emits:
    `-?\d+\.\d{6}` (or `-?\d+` if no fractional part). -/
def parseRat (s : String) : Rat :=
  let (sign, body) : Rat × String :=
    if s.startsWith "-" then (-1, (s.drop 1).toString) else (1, s)
  match body.splitOn "." with
  | [w] =>
      sign * ((w.toNat?.getD 0 : Int) : Rat)
  | [w, f] =>
      let denom : Rat := (10 ^ f.length : Nat)
      let intPart  : Rat := ((w.toNat?.getD 0 : Int) : Rat)
      let fracPart : Rat := ((f.toNat?.getD 0 : Nat) : Rat)
      sign * (intPart + fracPart / denom)
  | _ => 0

structure RowResult where
  ok      : Bool
  message : String

def validateRow (line : String) : RowResult :=
  match line.splitOn "|" with
  | [name, latS, lonS, expLat, expLon] =>
      let lat := parseRat latS
      let lon := parseRat lonS
      let gotLatStr := encodeLat lat
      let gotLonStr := encodeLon lon
      let decLat    := decodeLat expLat
      let decLon    := decodeLon expLon
      let latDiff   := absRat (decLat - lat)
      let lonDiff   := absRat (decLon - lon)
      let errs : List String :=
        (if gotLatStr = expLat then [] else
          [s!"encodeLat: got {gotLatStr.quote} expected {expLat.quote}"]) ++
        (if gotLonStr = expLon then [] else
          [s!"encodeLon: got {gotLonStr.quote} expected {expLon.quote}"]) ++
        (if latDiff ≤ latTol then [] else
          [s!"decodeLat: |{decLat} - {lat}| = {latDiff} > latTol={latTol}"]) ++
        (if lonDiff ≤ lonTol then [] else
          [s!"decodeLon: |{decLon} - {lon}| = {lonDiff} > lonTol={lonTol}"])
      match errs with
      | [] => { ok := true,  message := s!"OK   {name}" }
      | _  => { ok := false, message := s!"FAIL {name}: " ++ String.intercalate "; " errs }
  | _ =>
      { ok := false, message := s!"FAIL malformed row: {line}" }

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let lines := input.splitOn "\n" |>.filter (fun l => ¬ l.isEmpty)
  let results := lines.map validateRow
  for r in results do IO.println r.message
  let okCount   := results.filter (·.ok)        |>.length
  let failCount := results.filter (fun r => ¬ r.ok) |>.length
  IO.println s!"-- {okCount} OK, {failCount} FAIL"
  if failCount > 0 then
    IO.Process.exit 1
