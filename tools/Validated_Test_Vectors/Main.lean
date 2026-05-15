import ValidatedTestVectors
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

/-! # Fixed-point test-vector emission

  Emits the JSON consumed by `tools/gen_aprs_vectors.py`. The
  `base91_lat` and `base91_lon` fields are produced by `encodeLat`
  and `encodeLon`, whose round-trip correctness is established by
  `encodeLat_decodeLat_roundtrip` and `encodeLon_decodeLon_roundtrip`
  in `ValidatedTestVectors.Basic`.

  The fixed-point list mirrors `FIXED_POINTS` in
  `tools/gen_aprs_vectors.py`. The Python consumer cross-checks by
  name and lat/lon string, so the two lists must stay in lock-step.
-/

structure FixedPoint where
  name   : String
  lat    : Rat
  lon    : Rat
  latStr : String
  lonStr : String

def fixedPoints : List FixedPoint := [
  { name := "Munich",    lat :=  48.138630, lon :=  11.573410,
    latStr :=  "48.138630", lonStr :=  "11.573410" },
  { name := "CapeTown",  lat := -33.918861, lon :=  18.423300,
    latStr := "-33.918861", lonStr :=  "18.423300" },
  { name := "Auckland",  lat := -36.848460, lon := 174.762189,
    latStr := "-36.848460", lonStr := "174.762189" },
  { name := "NorthPole", lat :=  89.999000, lon :=   0.000000,
    latStr :=  "89.999000", lonStr :=   "0.000000" },
  { name := "Equator0",  lat :=   0.000000, lon :=   0.000000,
    latStr :=   "0.000000", lonStr :=   "0.000000" }
]

/-- Escape a string for safe inclusion as a JSON string literal.
    `encodeLat`/`encodeLon` can emit `"` (ASCII 34) and `\` (ASCII 92);
    everything else in the base-91 range (33–123) is JSON-safe. -/
def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | c    => acc.push c) ""

def jsonQuote (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

def renderPoint (p : FixedPoint) : String :=
  let encLat := encodeLat p.lat
  let encLon := encodeLon p.lon
  "    {" ++
    "\"name\": "       ++ jsonQuote p.name ++
    ", \"lat_deg\": "  ++ p.latStr ++
    ", \"lon_deg\": "  ++ p.lonStr ++
    ", \"base91_lat\": " ++ jsonQuote encLat ++
    ", \"base91_lon\": " ++ jsonQuote encLon ++
  "}"

def renderJson : String :=
  let entries := fixedPoints.map renderPoint
  let body    := String.intercalate ",\n" entries
  "{\n" ++
  "  \"_generator\": \"tools/Validated_Test_Vectors (Lean) — encodeLat/encodeLon\",\n" ++
  "  \"_proven_fields\": [\"base91_lat\", \"base91_lon\"],\n" ++
  "  \"_theorems\": [\"encodeLat_decodeLat_roundtrip\", \"encodeLon_decodeLon_roundtrip\"],\n" ++
  "  \"_lat_factor\": 380926,\n" ++
  "  \"_lon_factor\": 190463,\n" ++
  "  \"fixed_points\": [\n" ++
  body ++ "\n" ++
  "  ]\n" ++
  "}\n"

def main : IO Unit := do
  let path := "proved_vectors.json"
  IO.FS.writeFile path renderJson
  IO.println s!"wrote {path} ({fixedPoints.length} fixed points)"
