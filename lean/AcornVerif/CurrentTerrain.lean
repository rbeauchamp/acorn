/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldState
import AcornVerif.CurrentFloor

/-!
# Refusals of the terrain generator

`Host.terrain` refuses a position exactly when the value noise of one of its two fields reaches
a lattice coordinate with no successor among the signed 64-bit coordinates. The noise of an
octave divides each coordinate of the position by the scale of the octave, takes the floor of
the quotient and casts it to a coordinate. The coordinate after it is checked, and only the last
coordinate `2 ^ 63 - 1` has none.

`PastLast` states that condition on the quotient by its exact value, with no floor and no cast:
the quotient is positive infinity, or a finite value that is not negative and is at least
`2 ^ 63 - 1`. `LatticeAdmits` states its absence for both coordinates at the four octaves of a
field, whose scales are the base scale doubled zero to three times. The two fields read one
position at the same scales, and the seed enters no refusal. `terrain_isOk` is the
characterization, and `tileKind_isOk` and `enterable_isOk` carry it to the two readers of the
world.

The statements name the binary32 quotient of a coordinate by an octave scale, which the generator
also computes: the conversion of a coordinate, the division and the doubling of the scale are
shared with it. The floor, the saturating cast and the checked successor are not: the statements
replace them with a bound on the exact value of the quotient.
-/

set_option exponentiation.threshold 2048

namespace AcornVerif.CurrentTerrain
open Acorn Acorn.Host

/-- A quotient whose floor is at least the last coordinate `2 ^ 63 - 1`: positive infinity, or a
finite word that is not negative with an exact value of at least `2 ^ 63 - 1`. The exact value of
a finite word is `Conversion.magnitudeUnits32`, in units of `2 ^ -1074`. -/
def PastLast (quotient : Binary32) : Prop :=
  quotient = ⟨0x7f800000⟩ ∨
    quotient.Finite ∧ ¬quotient.Negative ∧
      (2 ^ 63 - 1) * 2 ^ 1074 ≤ Conversion.magnitudeUnits32 quotient

/-- Whether a quotient is past the last coordinate is decided by its word. -/
instance (quotient : Binary32) : Decidable (PastLast quotient) :=
  inferInstanceAs (Decidable (quotient = ⟨0x7f800000⟩ ∨
    quotient.Finite ∧ ¬quotient.Negative ∧
      (2 ^ 63 - 1) * 2 ^ 1074 ≤ Conversion.magnitudeUnits32 quotient))

/-- The scale of an octave: the base scale doubled once for each earlier octave, in the order of
`Host.octaveLoop`. -/
def octaveScale (scale : Binary32) : Nat → Binary32
  | 0 => scale
  | octave + 1 => octaveScale (scale.mul ⟨0x40000000⟩) octave

/-- The value noise of the terrain admits a position at a base scale: at each of the four octaves,
the quotient of neither coordinate by the scale of the octave is past the last coordinate. -/
def LatticeAdmits (position : Position) (scale : Binary32) : Prop :=
  ∀ octave < 4,
    ¬PastLast ((coordinateFloat position.x).div (octaveScale scale octave)) ∧
      ¬PastLast ((coordinateFloat position.y).div (octaveScale scale octave))

/-- Whether the noise admits a position is decided by its eight quotients. -/
instance (position : Position) (scale : Binary32) : Decidable (LatticeAdmits position scale) :=
  inferInstanceAs (Decidable (∀ octave < 4,
    ¬PastLast ((coordinateFloat position.x).div (octaveScale scale octave)) ∧
      ¬PastLast ((coordinateFloat position.y).div (octaveScale scale octave))))

/-- The sign test of a binary64 word reads its high bit. -/
private theorem sign64_iff (word : UInt64) :
    (word &&& 0x8000000000000000 != 0) = true ↔ 2 ^ 63 ≤ word.toNat := by
  have bound := word.toNat_lt
  have quotient : (word.toNat &&& 2 ^ 63) / 2 ^ 63 = word.toNat / 2 ^ 63 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos 63), Nat.and_one_is_mod,
      Nat.mod_eq_of_lt (by omega)]
  have remainder : (word.toNat &&& 2 ^ 63) % 2 ^ 63 = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  simp only [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_and]
  change ¬word.toNat &&& 2 ^ 63 = 0 ↔ _
  constructor
  · intro set
    omega
  · intro high clear
    omega

/-- The cast of a word reads its widening, or the quiet binary64 NaN for a NaN. -/
private theorem cast_val (value : Binary32) : (coordinateCast value).val =
    Conversion.toI64 (if value.IsNaN then ⟨0x7ff8000000000000⟩ else Conversion.widen value) :=
  rfl

/-- The cast of the floor of a quotient is the last coordinate exactly when the quotient is past
the last coordinate. A NaN quotient casts to zero. An infinite quotient is its own floor and
saturates by its sign. A finite quotient has an integral floor less than one below it, which
reaches the last coordinate exactly when the quotient does. -/
theorem cast_floor_last (quotient : Binary32) :
    (coordinateCast (floor32 quotient)).val = 2 ^ 63 - 1 ↔ PastLast quotient := by
  by_cases finite : quotient.Finite
  · obtain ⟨floorFinite, sign, ⟨units, divisible⟩, enclosure⟩ :=
      CurrentFloor.floor_magnitude quotient finite
    have notNaN : ¬(floor32 quotient).IsNaN := by
      unfold Binary32.Finite at floorFinite
      unfold Binary32.IsNaN
      omega
    have cast : (coordinateCast (floor32 quotient)).val =
        Conversion.signedCast 63 (Conversion.widen (floor32 quotient)) := by
      rw [cast_val, ite_eq_right notNaN, Conversion.toI64_eq_signedCast]
    have highBit := Conversion.widen_sign _ floorFinite
    have widenedSign : ((Conversion.widen (floor32 quotient)).bits &&& 0x8000000000000000 != 0) =
        quotient.negative := by
      apply Bool.eq_iff_iff.mpr
      rw [sign64_iff, ← sign, Binary32.negative_iff]
      unfold Binary32.Negative
      have := (floor32 quotient).bits.toNat_lt
      have := (Conversion.widen (floor32 quotient)).bits.toNat_lt
      omega
    have notInfinite : quotient ≠ ⟨0x7f800000⟩ := by
      rintro rfl
      exact absurd finite (by decide)
    rw [cast, Conversion.signedCast_finite_value 63 _ (Conversion.widen_finite _ floorFinite),
      Conversion.widen_magnitude_exact _ floorFinite, widenedSign, divisible,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    rw [divisible] at enclosure
    unfold PastLast
    simp only [notInfinite, false_or, finite, true_and, ← Binary32.negative_iff,
      Conversion.clampInt]
    cases negative : quotient.negative
    · simp only [negative, Bool.false_eq_true, ↓reduceIte, not_false_eq_true, true_and]
        at enclosure ⊢
      omega
    · simp only [ite_true, not_true_eq_false, false_and, iff_false]
      omega
  · have bound := quotient.magnitude_lt
    have exceptional : quotient.magnitude / 2 ^ 23 = 255 := by
      unfold Binary32.Finite at finite
      omega
    rw [floor32_exceptional quotient exceptional]
    by_cases nan : quotient.IsNaN
    · have zero : (coordinateCast quotient).val = 0 := by
        rw [cast_val, ite_eq_left nan]
        decide +kernel
      rw [zero]
      constructor
      · intro last
        exact absurd last (by decide)
      · rintro (infinite | ⟨finite', _⟩)
        · subst infinite
          exact absurd nan (by decide)
        · exact absurd finite' finite
    · have infinite : quotient.magnitude = 0x7f800000 := by
        unfold Binary32.IsNaN at nan
        unfold Binary32.Finite at finite
        omega
      have low : quotient.magnitude = quotient.bits.toNat % 2 ^ 31 := by
        unfold Binary32.magnitude
        rw [UInt32.toNat_and]
        exact Nat.and_two_pow_sub_one_eq_mod _ 31
      have word := quotient.bits.toNat_lt
      have words : quotient.bits = 0x7f800000 ∨ quotient.bits = 0xff800000 := by
        rcases (by omega : quotient.bits.toNat = 0x7f800000 ∨ quotient.bits.toNat = 0xff800000)
          with high | high
        · exact .inl (UInt32.toNat_inj.mp high)
        · exact .inr (UInt32.toNat_inj.mp high)
      have eta : quotient = ⟨quotient.bits⟩ := rfl
      rcases words with bits | bits <;>
        · rw [eta, bits]
          decide +kernel

/-- The coordinate after a coordinate is checked, and only the last coordinate has none. -/
private theorem successor_isSome (coordinate : Coordinate) :
    (Coordinate.checked (coordinate.val + 1)).isSome = true ↔
      ¬coordinate.val = 2 ^ 63 - 1 := by
  have range := coordinate.property
  rw [← Option.ne_none_iff_isSome, ne_eq, Coordinate.checked_none, Classical.not_not]
  constructor
  · intro ⟨_, below⟩ last
    omega
  · intro notLast
    exact ⟨by omega, by omega⟩

/-- The value noise of an octave admits a position exactly when the quotient of neither
coordinate by the scale is past the last coordinate. -/
theorem valueNoise_isOk (position : Position) (scale : Binary32) (seed : UInt64) :
    (valueNoise position scale seed).isOk = true ↔
      ¬PastLast ((coordinateFloat position.x).div scale) ∧
        ¬PastLast ((coordinateFloat position.y).div scale) := by
  rw [← cast_floor_last, ← cast_floor_last, ← successor_isSome, ← successor_isSome]
  cases horizontal : Coordinate.checked
      ((coordinateCast (floor32 ((coordinateFloat position.x).div scale))).val + 1) <;>
    cases vertical : Coordinate.checked
      ((coordinateCast (floor32 ((coordinateFloat position.y).div scale))).val + 1) <;>
    simp [valueNoise, horizontal, vertical, Except.isOk, Except.toBool, pure, Except.pure]

/-- The octave fold admits a position exactly when the noise of each of its octaves does, whatever
the amplitude and the sum it starts from. -/
theorem octaveLoop_isOk (count : Nat) (position : Position) (seed : UInt64)
    (scale amplitude sum : Binary32) :
    (octaveLoop count position seed scale amplitude sum).isOk = true ↔
      ∀ octave < count,
        ¬PastLast ((coordinateFloat position.x).div (octaveScale scale octave)) ∧
          ¬PastLast ((coordinateFloat position.y).div (octaveScale scale octave)) := by
  induction count generalizing scale amplitude sum with
  | zero =>
    simp [octaveLoop, Except.isOk, Except.toBool]
  | succ count ih =>
    have first := valueNoise_isOk position scale seed
    simp only [octaveLoop, bind, Except.bind]
    cases noise : valueNoise position scale seed with
    | error refusal =>
      rw [noise] at first
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, false_iff] at first ⊢
      intro all
      exact first (all 0 (Nat.succ_pos _))
    | ok value =>
      rw [noise] at first
      simp only [Except.isOk, Except.toBool, true_iff] at first
      dsimp only
      rw [ih]
      constructor
      · intro rest octave below
        cases octave with
        | zero => exact first
        | succ octave => exact rest octave (by omega)
      · intro all octave below
        exact all (octave + 1) (by omega)

/-- A field of the terrain admits a position exactly when the value noise admits it at the base
scale. -/
theorem fbm_isOk (position : Position) (seed : UInt64) (scale : Binary32) :
    (fbm position seed scale).isOk = true ↔ LatticeAdmits position scale :=
  octaveLoop_isOk 4 position seed scale _ _

/-- The terrain generator admits a position exactly when the value noise admits it at the base
scale. The two fields read the same position at the same scales, and the seed enters no
refusal. -/
theorem terrain_isOk (position : Position) (seed : UInt64) (scale : Binary32) :
    (terrain position seed scale).isOk = true ↔ LatticeAdmits position scale := by
  have elevationOk := fbm_isOk position (seed ^^^ 0xe1e0e1e000000001) scale
  have moistureOk := fbm_isOk position (seed ^^^ 0xe1e0e1e000000002) scale
  unfold terrain
  cases elevation : fbm position (seed ^^^ 0xe1e0e1e000000001) scale <;>
    cases moisture : fbm position (seed ^^^ 0xe1e0e1e000000002) scale <;>
    simp_all [Except.isOk, Except.toBool, bind, Except.bind, pure, Except.pure]

/-- The effective kind of a tile is refused exactly when the value noise refuses its position at
the base scale of the world. -/
theorem tileKind_isOk {config : WorldConfig} (world : World config) (position : Position) :
    (world.tileKind position).isOk = true ↔ LatticeAdmits position config.raw.baseScale := by
  rw [← terrain_isOk position config.raw.seed]
  unfold World.tileKind
  cases terrain position config.raw.seed config.raw.baseScale with
  | error refusal => simp [bind, Except.bind, Except.isOk, Except.toBool]
  | ok base =>
    simp only [bind, Except.bind]
    repeat' split
    all_goals simp [Except.isOk, Except.toBool, pure, Except.pure]

/-- An entry into a tile is refused exactly when the value noise refuses its position at the base
scale of the world. -/
theorem enterable_isOk {config : WorldConfig} (world : World config) (position : Position) :
    (world.enterable position).isOk = true ↔ LatticeAdmits position config.raw.baseScale := by
  rw [← tileKind_isOk world position]
  unfold World.enterable
  cases world.tileKind position <;>
    simp [bind, Except.bind, Except.isOk, Except.toBool, pure, Except.pure]

end AcornVerif.CurrentTerrain
