import Mathlib
import Batteries.Data.Rat.Float

-- 1. Define your encoding and decoding signatures

/-- The Base91 character set starts at ASCII 33 ('!') and ends at 123 ('{'). -/
def base91Start : Nat := 33

/-- Converts a single character to its Base91 integer value (0-90). -/
def charToVal (c : Char) : Nat :=
  c.toNat - base91Start

/-- Converts an integer value (0-90) to its Base91 character representation. -/
def valToChar (n : Nat) : Char :=
  Char.ofNat (n + base91Start)

/--
  Converts a Natural number to a fixed-length Base91 string.
  APRS coordinates use 4 characters (base 91^4).
-/
def toBase91 (n : Nat) (len : Nat) : String :=
  let rec loop (val : Nat) (count : Nat) (acc : List Char) : List Char :=
    match count with
    | 0 => acc
    | c + 1 =>
      let digit := val % 91
      loop (val / 91) c (valToChar digit :: acc)
  String.ofList (loop n len [])

/-- Converts a Base91 string back into a Natural number. -/
def fromBase91 (s : String) : Nat :=
  s.toList.foldl (fun acc c => acc * 91 + charToVal c) 0

---

/- Constants for APRS Compressed Position format -/
def latFactor : Rat := 380926
def lonFactor : Rat := 190463

/--
  Encodes Latitude.
  Formula: P = floor(380926 * (90 - lat))
-/
def encodeLat (lat : Rat) : String :=
  let scaled := (90 - lat) * latFactor
  toBase91 scaled.floor.toNat 4

/--
  Decodes Latitude.
  Formula: lat = 90 - (P / 380926)
-/
def decodeLat (s : String) : Rat :=
  let p := fromBase91 s
  90 - (p : Rat) / latFactor

/--
  Encodes Longitude.
  Formula: X = floor(190463 * (180 + lon))
-/
def encodeLon (lon : Rat) : String :=
  let scaled := (180 + lon) * lonFactor
  toBase91 scaled.floor.toNat 4

/--
  Decodes Longitude.
  Formula: lon = (X / 190463) - 180
-/
def decodeLon (s : String) : Rat :=
  let x := fromBase91 s
  (x : Rat) / lonFactor - 180

-- 2. Define the theoretical maximum error bound (ε).
-- The compressed Base91 latitude format has a worst-case round-trip
-- error of 1 / latFactor = 1 / 380926 ≈ 2.6e-6 degrees, so we use a
-- slightly looser 1/300000 as a safe upper bound.
def aprs_epsilon : Rat := 1 / 300000

-- The compressed Base91 longitude format uses lonFactor = 190463
-- (half of latFactor), so its worst-case round-trip error is twice
-- that of latitude: ~1/190463 ≈ 5.25e-6 degrees. 1/150000 is a safe
-- upper bound chosen with the same margin philosophy as aprs_epsilon.
def lonEpsilon : Rat := 1 / 150000

-- 3. Define the Round-Trip Property
-- This Prop formally states that the difference between the
-- original coordinate and the round-tripped coordinate is within ε.
def BoundedRoundTrip (encode : Rat → String) (decode : String → Rat)
    (ε : Rat) (x : Rat) : Prop :=
  let decoded := decode (encode x)
  let diff := decoded - x
  -- -ε ≤ diff ≤ ε
  (-ε) ≤ diff ∧ diff ≤ ε

/-
-
PROOF INFRASTRUCTURE
-

charToVal is a left inverse of valToChar for values in the Base91 range.
-/
lemma charToVal_valToChar {n : Nat} (h : n < 91) : charToVal (valToChar n) = n := by
  decide +revert

/-
The loop prepends digits; this lemma relates the loop with a non-empty
    accumulator to the loop with an empty accumulator.

lemma toBase91_loop_eq_append (val count : Nat) (acc : List Char) :
    toBase91.loop val count acc = toBase91.loop val count [] ++ acc := by
  induction' count with count ih generalizing val acc;
  · rfl;
  · convert ih ( val / 91 ) ( valToChar ( val % 91 ) :: acc ) using 1;
    simp +decide [ toBase91.loop ];
    rw [ ih ];
    simp +decide [ List.append_assoc ]
-/

/-
Core round-trip property: foldl over the loop output recovers the original value
    modulo 91^count. This is the generalized induction hypothesis.
-/
lemma foldl_toBase91_loop (val count : Nat) (init : Nat) (acc : List Char) :
    List.foldl (fun a c => a * 91 + charToVal c) init
      (toBase91.loop val count acc) =
    List.foldl (fun a c => a * 91 + charToVal c)
      (init * 91 ^ count + val % 91 ^ count) acc := by
  induction' count with count ih generalizing val init acc <;> simp_all +decide [ pow_succ ];
  · unfold toBase91.loop; simp +decide [ Nat.mod_one ] ;
  · rw [ show toBase91.loop val ( count + 1 ) acc = toBase91.loop ( val / 91 ) count ( valToChar ( val % 91 ) :: acc ) by rfl ] ; simp +decide [ * ] ; ring_nf;
    rw [ show val % ( 91 ^ count * 91 ) = val / 91 % 91 ^ count * 91 + val % 91 from ?_ ];
    · rw [ show charToVal ( valToChar ( val % 91 ) ) = val % 91 from ?_ ] ; ring_nf;
      exact charToVal_valToChar ( Nat.mod_lt _ ( by decide ) );
    · rw [ ← Nat.mod_add_div val 91 ] ; ring_nf;
      norm_num [ Nat.add_mod, Nat.mul_mod_mul_right, Nat.add_div ];
      split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · omega;
      · rw [ Nat.mod_eq_of_lt ];
        · ring;
        · nlinarith [ Nat.mod_lt ( val / 91 ) ( by positivity : 0 < 91 ^ count ), pow_pos ( by decide : 0 < 91 ) count ]

/-
The base91 encoding/decoding round-trips for values in range.
-/
theorem fromBase91_toBase91 {n len : Nat} (h : n < 91 ^ len) :
    fromBase91 (toBase91 n len) = n := by
  -- By definition of `toBase91.loop`, we can rewrite the goal using the loop function.
  have h_loop : fromBase91 (String.ofList (toBase91.loop n len [])) = List.foldl (fun a c => a * 91 + charToVal c) 0 (toBase91.loop n len []) := by
    unfold fromBase91; aesop;
  have := @foldl_toBase91_loop n len 0 ( [] ) ; simp_all +decide;
  exact h_loop.trans ( Nat.mod_eq_of_lt h )

/-
Key arithmetic: for q ≥ 0, the floor error q - ⌊q⌋ is in [0, 1).
-/
lemma floor_error_nonneg (q : ℚ) (hq : 0 ≤ q) :
    0 ≤ q - ↑(⌊q⌋.toNat) := by
  linarith [ show ( ⌊q⌋.toNat : ℚ ) ≤ q by exact_mod_cast Nat.floor_le hq ]

lemma floor_error_lt_one (q : ℚ) (_hq : 0 ≤ q) :
    q - ↑(⌊q⌋.toNat) < 1 := by
  linarith [ Int.lt_floor_add_one q, show ( ⌊q⌋.toNat : ℚ ) ≥ ⌊q⌋ by exact_mod_cast Int.self_le_toNat ⌊q⌋ ]

/-
The encoded value is in the valid base91 range for valid latitudes.
-/
lemma encodeLat_in_range (x : ℚ) (hlo : -90 ≤ x) (hhi : x ≤ 90) :
    ((90 - x) * 380926).floor.toNat < 91 ^ 4 := by
  -- Since $\lfloor q \rfloor \leq q < \lfloor q \rfloor + 1$, we have $\lfloor q \rfloor < \lfloor q \rfloor + 1$.
  have h_floor_lt_succ : Int.toNat (Int.floor ((90 - x) * 380926)) < Int.floor ((90 - x) * 380926) + 1 := by
    rw [ Int.toNat_of_nonneg ( Int.floor_nonneg.mpr ( by linarith ) ) ] ; norm_num;
  exact_mod_cast ( by linarith [ show ( ⌊ ( 90 - x ) * 380926⌋ : ℤ ) ≤ 91 ^ 4 - 1 by exact Int.le_sub_one_of_lt <| Int.floor_lt.2 <| by norm_num; linarith ] : ( Int.toNat ⌊ ( 90 - x ) * 380926⌋ : ℤ ) < 91 ^ 4 )

/-
4. The main theorem: encode and decode satisfy BoundedRoundTrip for valid latitudes.
-/
theorem encodeLat_decodeLat_roundtrip (x : ℚ) (hlo : -90 ≤ x) (hhi : x ≤ 90) :
    BoundedRoundTrip encodeLat decodeLat aprs_epsilon x := by
  constructor;
  · unfold decodeLat encodeLat;
    unfold aprs_epsilon latFactor;
    rw [ fromBase91_toBase91 ];
    · have := floor_error_nonneg ( ( 90 - x ) * 380926 ) ( by linarith );
      linarith!;
    · exact encodeLat_in_range x hlo hhi
  · unfold decodeLat encodeLat;
    unfold aprs_epsilon latFactor;
    rw [ fromBase91_toBase91 ];
    · have h_floor : (Int.toNat (Int.floor ((90 - x) * 380926))) ≤ (90 - x) * 380926 ∧ (90 - x) * 380926 < (Int.toNat (Int.floor ((90 - x) * 380926))) + 1 := by
        exact ⟨ by exact_mod_cast Nat.floor_le ( by linarith ), by exact_mod_cast Nat.lt_floor_add_one _ ⟩;
      linarith!;
    · exact encodeLat_in_range x hlo hhi

-- Test vectors for encodeLat/decodeLat (Latitude)

example : BoundedRoundTrip encodeLat decodeLat aprs_epsilon (34.0) :=
  encode_decode_roundtrip 34.0 (by norm_num) (by norm_num)

example : BoundedRoundTrip encodeLat decodeLat aprs_epsilon (-42.5) :=
  encode_decode_roundtrip (-42.5) (by norm_num) (by norm_num)

example : BoundedRoundTrip encodeLat decodeLat aprs_epsilon (0.0) :=
  encode_decode_roundtrip 0.0 (by norm_num) (by norm_num)

example : BoundedRoundTrip encodeLat decodeLat aprs_epsilon (90.0) :=
  encode_decode_roundtrip 90.0 (by norm_num) (by norm_num)

example : BoundedRoundTrip encodeLat decodeLat aprs_epsilon (-90.0) :=
  encode_decode_roundtrip (-90.0) (by norm_num) (by norm_num)

-- You can evaluate the encodings directly to see the string and parsed outputs:
#eval encodeLat 34.0000004
#eval 34.0000004 |> encodeLat |> decodeLat |> Rat.toFloat

#eval encodeLon (-105.123)
#eval -105.123 |> encodeLon |> decodeLon |> Rat.toFloat

/-
The encoded value is in the valid base91 range for valid longitudes.
Mirrors `encodeLat_in_range`: at the extremes (x = -180 or x = 180),
(180 + x) * 190463 reaches 0 or 360 * 190463 = 68566680, which is
still below 91^4 = 68574961.
-/
lemma encodeLon_in_range (x : ℚ) (hlo : -180 ≤ x) (hhi : x ≤ 180) :
    ((180 + x) * 190463).floor.toNat < 91 ^ 4 := by
  have h_floor_lt_succ : Int.toNat (Int.floor ((180 + x) * 190463)) < Int.floor ((180 + x) * 190463) + 1 := by
    rw [ Int.toNat_of_nonneg ( Int.floor_nonneg.mpr ( by linarith ) ) ] ; norm_num;
  exact_mod_cast ( by linarith [ show ( ⌊ ( 180 + x ) * 190463⌋ : ℤ ) ≤ 91 ^ 4 - 1 by exact Int.le_sub_one_of_lt <| Int.floor_lt.2 <| by norm_num; linarith ] : ( Int.toNat ⌊ ( 180 + x ) * 190463⌋ : ℤ ) < 91 ^ 4 )

/-
The main theorem (longitude): encodeLon and decodeLon satisfy
BoundedRoundTrip with lonEpsilon for valid longitudes in [-180, 180].
-/
theorem encodeLon_decodeLon_roundtrip (x : ℚ) (hlo : -180 ≤ x) (hhi : x ≤ 180) :
    BoundedRoundTrip encodeLon decodeLon lonEpsilon x := by
  -- For longitude, decode(encode x) = f/190463 - 180 where f = ⌊(180+x)*190463⌋.
  -- So diff = f/190463 - (180+x) lies in (-1/190463, 0]. The branches' uses of the
  -- floor lower/upper bound are mirrored relative to the latitude proof.
  constructor;
  · unfold decodeLon encodeLon;
    unfold lonEpsilon lonFactor;
    rw [ fromBase91_toBase91 ];
    · have h_floor : (Int.toNat (Int.floor ((180 + x) * 190463))) ≤ (180 + x) * 190463 ∧ (180 + x) * 190463 < (Int.toNat (Int.floor ((180 + x) * 190463))) + 1 := by
        exact ⟨ by exact_mod_cast Nat.floor_le ( by linarith ), by exact_mod_cast Nat.lt_floor_add_one _ ⟩;
      linarith!;
    · exact encodeLon_in_range x hlo hhi
  · unfold decodeLon encodeLon;
    unfold lonEpsilon lonFactor;
    rw [ fromBase91_toBase91 ];
    · have := floor_error_nonneg ( ( 180 + x ) * 190463 ) ( by linarith );
      linarith!;
    · exact encodeLon_in_range x hlo hhi

-- Test vectors for encodeLon/decodeLon (Longitude)

example : BoundedRoundTrip encodeLon decodeLon lonEpsilon (-105.123) :=
  encodeLon_decodeLon_roundtrip (-105.123) (by norm_num) (by norm_num)

example : BoundedRoundTrip encodeLon decodeLon lonEpsilon (0.0) :=
  encodeLon_decodeLon_roundtrip 0.0 (by norm_num) (by norm_num)

example : BoundedRoundTrip encodeLon decodeLon lonEpsilon (180.0) :=
  encodeLon_decodeLon_roundtrip 180.0 (by norm_num) (by norm_num)

example : BoundedRoundTrip encodeLon decodeLon lonEpsilon (-180.0) :=
  encodeLon_decodeLon_roundtrip (-180.0) (by norm_num) (by norm_num)

example : BoundedRoundTrip encodeLon decodeLon lonEpsilon (172.3456) :=
  encodeLon_decodeLon_roundtrip 172.3456 (by norm_num) (by norm_num)

def hello := "world"
