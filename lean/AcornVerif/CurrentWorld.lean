/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldObservation
import AcornVerif.CurrentLearnerArithmetic
import AcornVerif.CurrentFloor
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Executed current-world bounds and terrain admission

These theorems concern the world used by `WorldDriver`, `Attempt` and `Runner`.
Legal state is carried by receiving types, including at arbitrary public writes;
no separate historical world model or bounded initial configuration is assumed.
The finite-container and compiler/runtime implementations remain trusted.
-/
namespace AcornVerif.CurrentWorld
open Acorn Acorn.Host

/-- Sparse harvesting has at most one timestamp for each site in the extended box. -/
theorem harvest_storage_bound {config : WorldConfig} (world : World config) :
    world.harvested.size ≤ (config.side + 2) * (config.side + 2) := by
  rw [← Std.TreeMap.length_keys]
  have h := List.Nodup.length_le_card world.harvested.nodup_keys
  simpa [HarvestKey] using h

/-- Every constructible state obeys the receiving population and body bounds. -/
theorem state_bounds {config : WorldConfig} (world : World config) :
    world.body.position.x.val < config.side ∧ world.body.position.y.val < config.side ∧
    world.body.energy.val ≤ FeatureConstants.energyMax ∧
    world.deer.entries.size ≤ config.raw.deerCap.toNat ∧
    world.food.entries.size ≤ config.raw.foodCap.toNat ∧
    world.harvested.size ≤ (config.side + 2) * (config.side + 2) :=
  ⟨world.body.position.x.isLt, world.body.position.y.isLt, by have := world.body.energy.isLt; omega,
    world.deer.bounded, world.food.bounded, harvest_storage_bound world⟩

/-- Logical variable-size records are bounded for the full raw admitted configuration.
This does not promise allocation success or bound allocator/node byte overhead. -/
theorem retained_records_bound {config : WorldConfig} (world : World config) :
    world.harvested.size + world.deer.entries.size + world.food.entries.size ≤
      (config.side + 2) * (config.side + 2) +
        config.raw.deerCap.toNat + config.raw.foodCap.toNat := by
  have := state_bounds world
  omega

/-- Every radius contributes four directed edges, each with 2r+1 visits. -/
theorem spiral_work (side : Nat) :
    (∑ radius ∈ Finset.range side, 4 * (2 * radius + 1)) = 4 * side * side := by
  induction side with
  | zero => simp
  | succ side ih => rw [Finset.sum_range_succ, ih]; ring

/-- Body-to-facing harvest admission is universal over the actual closed direction domain. -/
theorem facing_harvest_admission {config : WorldConfig} (world : World config) :
    ∃ key, harvestKey config (world.body.position.facingPosition world.body.facing) = some key :=
  world.body.position.facingKey_exists world.body.facing


/-- Every supported standard side is admitted, for every seed. Configuration
admission is separate from the terrain-dependent `World.initial` operation. -/
theorem standard_config_exists (seed : UInt64) (side : Coordinate)
    (lower : FeatureConstants.worldMinSide ≤ side.val)
    (upper : side.val ≤ FeatureConstants.worldMaxSide) :
    ∃ config, WorldConfig.standard seed side = .ok config := by
  unfold WorldConfig.standard
  split
  · omega
  · split
    · omega
    · exact ⟨_, rfl⟩

/-- Every standard-world body has representable coordinates throughout its
actual sensor neighborhood. This closes translation refusal, not terrain refusal. -/
theorem standard_body_translation (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (position : BoxPosition config) (dx dy : Int)
    (hx : -(patchShape.side / 2 : Nat) ≤ dx ∧ dx ≤ (patchShape.side / 2 : Nat))
    (hy : -(patchShape.side / 2 : Nat) ≤ dy ∧ dy ≤ (patchShape.side / 2 : Nat)) :
    ∃ next, position.position.translate dx dy = some next := by
  have fields := WorldConfig.standard_bounds seed side config standard
  have xs := position.x.isLt
  have ys := position.y.isLt
  have rawSide : config.side = side.val.toNat := by
    simp only [WorldConfig.side, fields.1]
  have xsBound : position.x.val < side.val.toNat := lt_of_lt_of_eq xs rawSide
  have ysBound : position.y.val < side.val.toNat := lt_of_lt_of_eq ys rawSide
  have maximum : side.val ≤ 3000000000 := fields.2.2
  have xbound : -(2^63 : Int) ≤ position.position.x.val + dx ∧
      position.position.x.val + dx < 2^63 := by
    dsimp only [BoxPosition.position]
    change -(5 : Int) ≤ dx ∧ dx ≤ 5 at hx
    omega
  have ybound : -(2^63 : Int) ≤ position.position.y.val + dy ∧
      position.position.y.val + dy < 2^63 := by
    dsimp only [BoxPosition.position]
    change -(5 : Int) ≤ dy ∧ dy ≤ 5 at hy
    omega
  have xok : Coordinate.checked (position.position.x.val + dx) =
      some (⟨_, xbound⟩ : Coordinate) := dif_pos xbound
  have yok : Coordinate.checked (position.position.y.val + dy) =
      some (⟨_, ybound⟩ : Coordinate) := dif_pos ybound
  exact ⟨⟨⟨_, xbound⟩, ⟨_, ybound⟩⟩, by
    simp only [Position.translate, xok, yok, Option.pure_def]
    rfl⟩

/-- The standard spawn spiral's actual pre-box signed admissions cannot overflow.
Outside-box candidates may still be skipped; terrain-dependent scoring is separate. -/
theorem standard_spiral_coordinates (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (radius offset : Nat) (hr : radius < config.side) (ho : offset < 2 * radius + 1)
    (direction : Direction) :
    let k : Int := (offset : Int) - radius
    let x := (config.side / 2 : Nat) + direction.delta.1 * radius + direction.delta.2 * k
    let y := (config.side / 2 : Nat) + direction.delta.2 * radius + direction.delta.1 * k
    ∃ cx cy, Coordinate.checked x = some cx ∧ Coordinate.checked y = some cy := by
  have fields := WorldConfig.standard_bounds seed side config standard
  have sideBound : config.side ≤ 3000000000 := by
    have h := fields.2.2
    change side.val ≤ 3000000000 at h
    simp only [WorldConfig.side, fields.1]
    omega
  have centerBound := Nat.div_le_self config.side 2
  dsimp only
  have bounds :
      (-(2^63 : Int) ≤ (config.side / 2 : Nat) + direction.delta.1 * radius +
        direction.delta.2 * ((offset : Int) - radius) ∧
      (config.side / 2 : Nat) + direction.delta.1 * radius +
        direction.delta.2 * ((offset : Int) - radius) < 2^63) ∧
      (-(2^63 : Int) ≤ (config.side / 2 : Nat) + direction.delta.2 * radius +
        direction.delta.1 * ((offset : Int) - radius) ∧
      (config.side / 2 : Nat) + direction.delta.2 * radius +
        direction.delta.1 * ((offset : Int) - radius) < 2^63) := by
    cases direction <;> simp only [Direction.delta, zero_mul, one_mul, neg_mul,
      add_zero] <;> omega
  exact ⟨⟨_, bounds.1⟩, ⟨_, bounds.2⟩, by
    simp only [Coordinate.checked, bounds.1, bounds.2, ↓reduceDIte, and_self]⟩

open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder
open AcornVerif.CurrentLearnerArithmetic AcornVerif.CurrentDivision

/-- The direct native word-to-binary32 conversion has a checked rounding envelope
on the coordinate/scale integer domain. Packing finiteness is derived separately
from the same normalized result; no binary64 conversion is substituted. -/
theorem word32_conversion (word : UInt64) (limit : Nat) (small : limit ≤ 32)
    (bounded : word.toNat ≤ 2 ^ limit) :
    (Binary32.ofUInt64 word).Finite ∧
      |numerical32 (Binary32.ofUInt64 word) - (word.toNat : ℚ)| ≤
        (2 : ℚ) ^ (max ((limit : Int) + 1 - 24) (-149)) / 2 := by
  let rounded := normalize Format.binary32 (word.toNat : Int) 0 .positive
  have magnitude : |((word.toNat : Int) : ℚ) * (2 : ℚ) ^ 0| ≤ (2 : ℚ) ^ (limit : Int) := by
    simpa using (show (word.toNat : ℚ) ≤ 2 ^ limit by exact_mod_cast bounded)
  have model := model_signed_round_value Format.binary32 (word.toNat : Int) 0
    .positive (limit : Int) magnitude
  have error : |unpackedValue rounded - (word.toNat : ℚ)| ≤
      (2 : ℚ) ^ (max ((limit : Int) + 1 - 24) (-149)) / 2 := by
    simpa only [show Format.binary32.mantissaBits = 24 from rfl,
      show Format.binary32.minExponent = -149 from rfl,
      rounded, Nat.cast_ofNat, zpow_zero, mul_one, Int.cast_natCast] using model.2
  have errorBound : (2 : ℚ) ^ (max ((limit : Int) + 1 - 24) (-149)) / 2 ≤ 256 := by
    have exponent : max ((limit : Int) + 1 - 24) (-149) ≤ 9 := by omega
    have powers := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) exponent
    norm_num at powers
    linarith
  have integerBound : (word.toNat : ℚ) ≤ 2 ^ 32 := by
    exact_mod_cast (le_trans bounded (Nat.pow_le_pow_right (by decide) small))
  have total : |unpackedValue rounded| ≤ (2 : ℚ) ^ 33 := by
    have triangle := abs_add_le (unpackedValue rounded - (word.toNat : ℚ)) (word.toNat : ℚ)
    rw [sub_add_cancel,
      abs_of_nonneg (show (0 : ℚ) ≤ word.toNat from Nat.cast_nonneg _)] at triangle
    have := le_trans error errorBound
    rw [show (2 : ℚ) ^ 32 = 4294967296 by norm_num] at integerBound
    rw [show (2 : ℚ) ^ 33 = 8589934592 by norm_num]
    linarith
  have normal : ModelNormalized Format.binary32 rounded := model.1
  have fits := model_fits_of_value_bound Format.binary32 rounded
    (model_normalized_finite _ _ normal) 33 (by decide) total
  have decoded : decoded32 (Binary32.ofUInt64 word) = rounded := by
    change unpack Format.binary32 (pack Format.binary32 rounded) = rounded
    exact model_unpack_pack_normalized _ _ normal fits
  refine ⟨?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ normal
  · change |unpackedValue (decoded32 (Binary32.ofUInt64 word)) - (word.toNat : ℚ)| ≤ _
    rw [decoded]
    exact error

/-- The standard scale's integer range remains strictly positive after the actual
word conversion. The two magnitude bands avoid assuming exact conversion of all
integers or using a large uniform rounding allowance near the lower endpoint. -/
theorem scale_word_bounds (word : UInt64)
    (lower : 8 ≤ word.toNat) (upper : word.toNat ≤ 2 ^ 28) :
    (Binary32.ofUInt64 word).Finite ∧
      4 ≤ numerical32 (Binary32.ofUInt64 word) ∧
        numerical32 (Binary32.ofUInt64 word) ≤ 2 ^ 29 := by
  have lowerQ : (8 : ℚ) ≤ word.toNat := by exact_mod_cast lower
  have upperQ : (word.toNat : ℚ) ≤ 2 ^ 28 := by exact_mod_cast upper
  rw [show (2 : ℚ) ^ 28 = 268435456 by norm_num] at upperQ
  by_cases small : word.toNat ≤ 2 ^ 20
  · have conversion := word32_conversion word 20 (by decide) small
    have error := conversion.2
    norm_num at error
    have distance := abs_le.mp error
    refine ⟨conversion.1, ?_, ?_⟩ <;> norm_num <;> linarith
  · have conversion := word32_conversion word 28 (by decide) upper
    have error := conversion.2
    norm_num at error
    have distance := abs_le.mp error
    have largeQ : (2 : ℚ) ^ 20 < word.toNat := by exact_mod_cast (Nat.lt_of_not_ge small)
    rw [show (2 : ℚ) ^ 20 = 1048576 by norm_num] at largeQ
    refine ⟨conversion.1, ?_, ?_⟩ <;> norm_num <;> linarith

/-- Every admitted standard constructor produces a finite, positive terrain
scale. Arbitrary admitted custom configurations have no corresponding premise. -/
theorem standard_scale_bounds (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config) :
    config.raw.baseScale.Finite ∧ 4 ≤ numerical32 config.raw.baseScale ∧
      numerical32 config.raw.baseScale ≤ 2 ^ 29 := by
  unfold WorldConfig.standard at standard
  split at standard
  · contradiction
  · rename_i lower
    split at standard
    · contradiction
    · rename_i upper
      cases Except.ok.inj standard
      let amount := max FeatureConstants.worldMinScale
        (side.val.toNat / FeatureConstants.worldScaleDivisor)
      have amountBounds : 8 ≤ amount ∧ amount ≤ 2 ^ 28 := by
        change ¬ side.val < 64 at lower
        change ¬ side.val > 3000000000 at upper
        dsimp [amount, FeatureConstants.worldMinScale, FeatureConstants.worldScaleDivisor]
        omega
      have word : amount.toUInt64.toNat = amount := by
        simp only [Nat.toUInt64, UInt64.toNat_ofNat']
        apply Nat.mod_eq_of_lt
        omega
      exact scale_word_bounds amount.toUInt64 (by rw [word]; exact amountBounds.1)
        (by rw [word]; exact amountBounds.2)

/-- The actual octave multiplier preserves positivity and a loose bounded growth
envelope throughout the standard four-octave range. This does not assert exact
doubling; normalization, packing and the executed multiplication are connected. -/
theorem octave_scale_double (scale : Binary32) (finite : scale.Finite)
    (lower : 4 ≤ numerical32 scale) (upper : numerical32 scale ≤ 2 ^ 38) :
    (scale.mul ⟨0x40000000⟩).Finite ∧
      numerical32 scale ≤ numerical32 (scale.mul ⟨0x40000000⟩) ∧
        numerical32 (scale.mul ⟨0x40000000⟩) ≤ 4 * numerical32 scale := by
  let two : Binary32 := ⟨0x40000000⟩
  have twoFinite : two.Finite := by decide
  have twoValue : numerical32 two = 2 := by
    dsimp only [two]
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-22 : Int) = 2
    norm_num
  have leftNormal := (model_unpack_format Format.binary32 (by decide) scale.bits.toBitVec
    ((model_decoded32_finite scale).mpr finite)).1
  have rightNormal := (model_unpack_format Format.binary32 (by decide) two.bits.toBitVec
    ((model_decoded32_finite two).mpr twoFinite)).1
  let product := UnpackedFloat.mul Format.binary32 (decoded32 scale) (decoded32 two)
  have magnitude : |numerical32 scale * numerical32 two| ≤ (2 : ℚ) ^ (39 : Int) := by
    rw [twoValue, abs_of_nonneg (by linarith : 0 ≤ numerical32 scale * 2)]
    norm_num at upper ⊢
    linarith
  have operation := model_mul_dyadic_local Format.binary32 _ _ leftNormal rightNormal
    39 magnitude
  have error : |unpackedValue product - numerical32 scale * 2| ≤ numerical32 scale := by
    by_cases small : numerical32 scale ≤ 2 ^ 20
    · have smallMagnitude : |numerical32 scale * numerical32 two| ≤
          (2 : ℚ) ^ (21 : Int) := by
        rw [twoValue, abs_of_nonneg (by linarith : 0 ≤ numerical32 scale * 2)]
        norm_num at small ⊢
        linarith
      have smallOperation := model_mul_dyadic_local Format.binary32 _ _ leftNormal
        rightNormal 21 smallMagnitude
      have bound := smallOperation.2
      change |unpackedValue product - numerical32 scale * numerical32 two| ≤ _ at bound
      rw [twoValue] at bound
      norm_num [Format.mantissaBits, Format.minExponent] at bound
      linarith
    · have bound := operation.2
      change |unpackedValue product - numerical32 scale * numerical32 two| ≤ _ at bound
      rw [twoValue] at bound
      norm_num [Format.mantissaBits, Format.minExponent] at bound
      norm_num at small
      linarith
  have distance := abs_le.mp error
  have nonnegative : 0 ≤ unpackedValue product := by linarith
  have bound : |unpackedValue product| ≤ (2 : ℚ) ^ (40 : Int) := by
    rw [abs_of_nonneg nonnegative]
    norm_num at upper ⊢
    linarith
  have fits := model_fits_of_value_bound Format.binary32 product
    (model_normalized_finite _ _ operation.1) 40 (by decide) bound
  have decoded := mul32_decoded scale two finite twoFinite operation.1 fits
  refine ⟨?_, ?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · change numerical32 scale ≤ unpackedValue (decoded32 (scale.mul two))
    rw [decoded]
    linarith
  · change unpackedValue (decoded32 (scale.mul two)) ≤ 4 * numerical32 scale
    rw [decoded]
    linarith

/-- Every prefix of the four actual octave scale multiplications stays finite
and positive. The bound also covers the final scale computed but not sampled
by the zero-count branch; it makes no claim about lattice admission. -/
theorem standard_octave_scales (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (count : Nat) (within : count ≤ 4) :
    let scale := (fun value : Binary32 => value.mul ⟨0x40000000⟩)^[count] config.raw.baseScale
    scale.Finite ∧ 4 ≤ numerical32 scale ∧ numerical32 scale ≤ 2 ^ (29 + 2 * count) := by
  induction count with
  | zero => simpa using standard_scale_bounds seed side config standard
  | succ count ih =>
    have previous := ih (by omega)
    dsimp only at previous ⊢
    rw [Function.iterate_succ_apply']
    have upper := le_trans previous.2.2
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
        (show 29 + 2 * count ≤ 38 by omega))
    have next := octave_scale_double _ previous.1 previous.2.1 upper
    refine ⟨next.1, le_trans previous.2.1 next.2.1, le_trans next.2.2 ?_⟩
    have growth : (2 : ℚ) ^ (29 + 2 * (count + 1)) =
        4 * (2 : ℚ) ^ (29 + 2 * count) := by
      rw [show 29 + 2 * (count + 1) = (29 + 2 * count) + 2 by omega, pow_add]
      ring
    rw [growth]
    exact mul_le_mul_of_nonneg_left previous.2.2 (by norm_num)

/-- Successful samples at the actual successive scales imply success of the
executed octave fold, for arbitrary accumulator/amplitude words. This is the
control-flow composition only: its lattice-sample premise remains explicit. -/
theorem octaveLoop_success_of_samples (count : Nat) (position : Position) (seed : UInt64)
    (scale amplitude sum : Binary32)
    (samples : ∀ index < count, ∃ noise,
      valueNoise position ((fun value : Binary32 => value.mul ⟨0x40000000⟩)^[index] scale)
        seed = .ok noise) :
    ∃ result, octaveLoop count position seed scale amplitude sum = .ok result := by
  induction count generalizing scale amplitude sum with
  | zero => exact ⟨sum, rfl⟩
  | succ count ih =>
    obtain ⟨noise, sample⟩ := samples 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at sample
    have remaining : ∀ index < count, ∃ noise,
        valueNoise position
          ((fun value : Binary32 => value.mul ⟨0x40000000⟩)^[index]
            (scale.mul ⟨0x40000000⟩)) seed = .ok noise := by
      intro index bound
      simpa only [Function.iterate_succ_apply] using samples (index + 1) (by omega)
    obtain ⟨result, rest⟩ := ih (scale.mul ⟨0x40000000⟩)
      (amplitude.mul ⟨0x3f000000⟩) (sum.add (amplitude.mul noise)) remaining
    exact ⟨result, by simp only [octaveLoop, sample]; exact rest⟩

/-- Both executed terrain folds succeed once every sample at a finite positive
standard-octave scale succeeds. The sample premise isolates the remaining
coordinate/division/floor/lattice obligation; it is not a terrain-totality proof. -/
theorem standard_terrain_of_samples (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (position : Position) (salt : UInt64)
    (samples : ∀ scale : Binary32, scale.Finite → 4 ≤ numerical32 scale →
      numerical32 scale ≤ 2 ^ 37 → ∀ sampleSeed, ∃ noise,
        valueNoise position scale sampleSeed = .ok noise) :
    ∃ kind, terrain position salt config.raw.baseScale = .ok kind := by
  have field : ∀ sampleSeed, ∃ result, fbm position sampleSeed config.raw.baseScale =
      .ok result := by
    intro sampleSeed
    apply octaveLoop_success_of_samples
    intro index before
    have scale := standard_octave_scales seed side config standard index (by omega)
    exact samples _ scale.1 scale.2.1 (le_trans scale.2.2
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
        (show 29 + 2 * index ≤ 37 by omega))) sampleSeed
  obtain ⟨elevation, elevationEq⟩ := field (salt ^^^ 0xe1e0e1e000000001)
  obtain ⟨moisture, moistureEq⟩ := field (salt ^^^ 0xe1e0e1e000000002)
  exact ⟨_, by simp only [terrain, elevationEq, moistureEq]; rfl⟩

/-- Direct signed coordinate conversion retains a finite magnitude bound on the
standard-world margin. The proof follows the actual sign-bit construction and
single word conversion, including zero; no intermediate binary64 is introduced. -/
theorem coordinate_float_bound (coordinate : Coordinate)
    (bounded : coordinate.val.natAbs ≤ 2 ^ 32) :
    (coordinateFloat coordinate).Finite ∧
      |numerical32 (coordinateFloat coordinate)| ≤ 2 ^ 33 := by
  have word : coordinate.val.natAbs.toUInt64.toNat = coordinate.val.natAbs := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    omega
  have conversion := word32_conversion coordinate.val.natAbs.toUInt64 32 (by decide)
    (by rw [word]; exact bounded)
  let magnitude := Binary32.ofUInt64 coordinate.val.natAbs.toUInt64
  have finite : magnitude.Finite := conversion.1
  have error := conversion.2
  rw [word] at error
  have allowance : (2 : ℚ) ^ (max (((32 : Nat) : Int) + 1 - 24) (-149)) / 2 = 256 := by
    norm_num
  rw [allowance] at error
  have integerBound : (coordinate.val.natAbs : ℚ) ≤ 4294967296 := by
    exact_mod_cast bounded
  have bound : |numerical32 magnitude| ≤ (2 : ℚ) ^ 33 := by
    have triangle := abs_add_le
      (numerical32 magnitude - (coordinate.val.natAbs : ℚ)) (coordinate.val.natAbs : ℚ)
    rw [sub_add_cancel,
      abs_of_nonneg (show (0 : ℚ) ≤ coordinate.val.natAbs from Nat.cast_nonneg _)] at triangle
    norm_num
    linarith
  rw [coordinateFloat_eq]
  split
  · have same : (⟨magnitude.bits ^^^ 0x80000000⟩ : Binary32).magnitude =
        magnitude.magnitude := by
      simp only [Binary32.magnitude, UInt32.toNat_and, UInt32.toNat_xor,
        Nat.and_xor_distrib_right]
      change (magnitude.bits.toNat &&& 2147483647) ^^^ 0 = _
      exact Nat.xor_zero _
    have signedFinite : (⟨magnitude.bits ^^^ 0x80000000⟩ : Binary32).Finite := by
      change _ < 0x7f800000
      rw [same]
      exact finite
    refine ⟨signedFinite, ?_⟩
    rw [numerical32_abs_units _ signedFinite, same, ← numerical32_abs_units _ finite]
    exact bound
  · exact ⟨finite, bound⟩

/-- The executed terrain quotient stays finite and far inside the signed-cast
range when the coordinate magnitude is bounded and the scale is at least four.
This includes signed coordinates and uses the actual binary32 division error. -/
theorem coordinate_quotient_bound (coordinate : Coordinate)
    (bounded : coordinate.val.natAbs ≤ 2 ^ 32) (scale : Binary32)
    (finite : scale.Finite) (lower : 4 ≤ numerical32 scale) :
    ((coordinateFloat coordinate).div scale).Finite ∧
      |numerical32 ((coordinateFloat coordinate).div scale)| ≤ 2 ^ 32 := by
  have source := coordinate_float_bound coordinate bounded
  have leftNormal := (model_unpack_format Format.binary32 (by decide)
    (coordinateFloat coordinate).bits.toBitVec
    ((model_decoded32_finite _).mpr source.1)).1
  have rightNormal := (model_unpack_format Format.binary32 (by decide) scale.bits.toBitVec
    ((model_decoded32_finite scale).mpr finite)).1
  have positive : 0 < numerical32 scale := by linarith
  have quotient : |numerical32 (coordinateFloat coordinate) / numerical32 scale| ≤
      (2 : ℚ) ^ (31 : Int) := by
    rw [abs_div, abs_of_pos positive]
    apply (div_le_iff₀ positive).mpr
    have bound := source.2
    norm_num at bound ⊢
    linarith
  have operation := model_div_dyadic_local Format.binary32 _ _ leftNormal rightNormal
    (ne_of_gt positive) 31 quotient
  let divided := UnpackedFloat.div Format.binary32
    (decoded32 (coordinateFloat coordinate)) (decoded32 scale)
  have error : |unpackedValue divided -
      numerical32 (coordinateFloat coordinate) / numerical32 scale| ≤ 512 := by
    have allowance : 2 * (2 : ℚ) ^
        (max ((31 : Int) + 1 - Format.binary32.mantissaBits) Format.binary32.minExponent) =
          512 := by
      norm_num [Format.mantissaBits, Format.minExponent]
    simpa only [allowance, divided, numerical32, decoded32] using operation.2
  have bound : |unpackedValue divided| ≤ (2 : ℚ) ^ (32 : Int) := by
    have triangle := abs_add_le
      (unpackedValue divided - numerical32 (coordinateFloat coordinate) / numerical32 scale)
      (numerical32 (coordinateFloat coordinate) / numerical32 scale)
    rw [sub_add_cancel] at triangle
    norm_num at quotient ⊢
    linarith
  have fits := model_fits_of_value_bound Format.binary32 divided
    (model_normalized_finite _ _ operation.1) 32 (by decide) bound
  have decoded := div32_decoded (coordinateFloat coordinate) scale source.1 finite operation.1 fits
  refine ⟨?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · change |unpackedValue (decoded32 ((coordinateFloat coordinate).div scale))| ≤ _
    rw [decoded]
    exact bound

/-- A finite quotient in the terrain envelope cannot reach the maximal signed
coordinate after floor and the executed widening/saturating cast. The proof
needs only a magnitude enclosure, not an exact floor-to-integer identity. -/
theorem floor_cast_neighbor (value : Binary32) (finite : value.Finite)
    (bounded : |numerical32 value| ≤ 2 ^ 32) :
    ∃ neighbor, Coordinate.checked ((coordinateCast (floor32 value)).val + 1) =
      some neighbor := by
  let reference : Binary32 := ⟨0x4f800000⟩
  have referenceFinite : reference.Finite := by decide
  have referenceValue : numerical32 reference = (2 : ℚ) ^ 32 := by
    dsimp only [reference]
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (9 : Int) = (2 : ℚ) ^ 32
    norm_num
  have magnitude : value.magnitude ≤ reference.magnitude := by
    apply (numerical32_magnitude_order value reference finite referenceFinite).mp
    rw [referenceValue, abs_of_nonneg (show (0 : ℚ) ≤ 2 ^ 32 by positivity)]
    exact bounded
  have units : Conversion.magnitudeUnits32 value ≤ Conversion.magnitudeUnits32 reference := by
    rw [magnitudeUnits32_fieldUnits, magnitudeUnits32_fieldUnits]
    exact Nat.mul_le_mul_right _ ((fieldUnits_order 23 _ _).mpr magnitude)
  have referenceUnits : Conversion.magnitudeUnits32 reference = 2 ^ 32 * 2 ^ 1074 := by
    have fields : fieldUnits 23 reference.magnitude = 2 ^ 23 * 2 ^ 158 := by
      dsimp only [reference]
      change (2 ^ 23 + 0) * 2 ^ (159 - 1) = 2 ^ 23 * 2 ^ 158
      rw [Nat.add_zero]
    have regroup (a b c d e : Nat) (exponents : a + b + c = d + e) :
        ((2 : Nat) ^ a * 2 ^ b) * 2 ^ c = 2 ^ d * 2 ^ e := by
      rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, exponents]
    exact (magnitudeUnits32_fieldUnits reference).trans
      ((congrArg (fun count : Nat => count * 2 ^ 925) fields).trans
        (regroup 23 158 925 32 1074 (by omega)))
  have sourceUnits : Conversion.magnitudeUnits32 value ≤ (2 : Nat) ^ 32 * 2 ^ 1074 :=
    Nat.le_trans units referenceUnits.le
  have floor := AcornVerif.CurrentFloor.floor_magnitude value finite
  have quotientBound (unit input output : Nat) (positive : 0 < unit)
      (bound : input ≤ 2 ^ 32 * unit)
      (enclosure : if value.negative then input ≤ output ∧ output < input + unit
        else output ≤ input ∧ input < output + unit) : output / unit < 2 ^ 32 + 1 := by
    have upper : output < input + unit := by
      split at enclosure
      · exact enclosure.2
      · exact lt_of_le_of_lt enclosure.1 (Nat.lt_add_of_pos_right positive)
    apply (Nat.div_lt_iff_lt_mul positive).mpr
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_of_lt_of_le upper (Nat.add_le_add_right bound unit)
  -- Bridge power instances with a symbolic exponent before instantiating the large unit.
  have positivePower (exponent : Nat) : (0 : Nat) < 2 ^ exponent := Nat.two_pow_pos exponent
  have quotient := quotientBound (2 ^ 1074) (Conversion.magnitudeUnits32 value)
    (Conversion.magnitudeUnits32 (floor32 value)) (positivePower 1074) sourceUnits floor.2.2.2
  have castBound (unit amount : Nat) (bound : amount / unit < 2 ^ 32 + 1) (negative : Bool) :
      Conversion.clampInt (if negative then -((amount / unit : Nat) : Int)
        else ((amount / unit : Nat) : Int)) (-(2 ^ 63)) (2 ^ 63 - 1) < 2 ^ 63 - 1 := by
    have quotientNonnegative : (0 : Int) ≤
        (amount : Int) / (unit : Int) :=
      Int.ediv_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    unfold Conversion.clampInt
    split <;> omega
  have endpoint : (coordinateCast (floor32 value)).val < (2 : Int) ^ 63 - 1 := by
    change Conversion.toI64 (Conversion.widen (floor32 value)) < (2 : Int) ^ 63 - 1
    rw [Conversion.toI64_eq_signedCast,
      Conversion.signedCast_finite_value _ _ (Conversion.widen_finite _ floor.1),
      Conversion.widen_magnitude_exact _ floor.1]
    -- The executed conversion uses the standard-library power instance; retain its meaning
    -- without forcing ground reduction against Mathlib's power instance at exponent 1074.
    have powerBridge (exponent : Nat) :
        @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 exponent =
          (2 : Nat) ^ exponent := by rfl
    rw [powerBridge 1074]
    exact castBound (2 ^ 1074) _ quotient _
  have admitted : -(2 ^ 63 : Int) ≤ (coordinateCast (floor32 value)).val + 1 ∧
      (coordinateCast (floor32 value)).val + 1 < 2 ^ 63 := by
    have legal := (coordinateCast (floor32 value)).property
    omega
  exact ⟨⟨_, admitted⟩, dif_pos admitted⟩

/-- The actual standard terrain operation succeeds throughout the signed margin
needed by the bounded world geometry, for every terrain salt. This establishes
arithmetic admission only, not successful world allocation or a learning prefix. -/
theorem standard_terrain_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (position : Position) (salt : UInt64)
    (xlow : -201 ≤ position.x.val) (xhigh : position.x.val ≤ (config.side : Int) + 201)
    (ylow : -201 ≤ position.y.val) (yhigh : position.y.val ≤ (config.side : Int) + 201) :
    ∃ kind, terrain position salt config.raw.baseScale = .ok kind := by
  have fields := WorldConfig.standard_bounds seed side config standard
  have size : config.side ≤ 3000000000 := by
    simp only [WorldConfig.side, fields.1]
    have upper : side.val ≤ 3000000000 := fields.2.2
    omega
  have xbound : position.x.val.natAbs ≤ 2 ^ 32 := by omega
  have ybound : position.y.val.natAbs ≤ 2 ^ 32 := by omega
  apply standard_terrain_of_samples seed side config standard position salt
  intro scale finite lower _ sampleSeed
  have xquotient := coordinate_quotient_bound position.x xbound scale finite lower
  have yquotient := coordinate_quotient_bound position.y ybound scale finite lower
  obtain ⟨xnext, xok⟩ := floor_cast_neighbor _ xquotient.1 xquotient.2
  obtain ⟨ynext, yok⟩ := floor_cast_neighbor _ yquotient.1 yquotient.2
  exact ⟨_, by simp only [valueNoise, xok, yok]; rfl⟩

/-- Harvest history can change a terrain kind but introduces no new refusal
after successful standard terrain admission. The world need not be initialized. -/
theorem standard_tileKind_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) (position : Position)
    (xlow : -201 ≤ position.x.val) (xhigh : position.x.val ≤ (config.side : Int) + 201)
    (ylow : -201 ≤ position.y.val) (yhigh : position.y.val ≤ (config.side : Int) + 201) :
    ∃ kind, world.tileKind position = .ok kind := by
  obtain ⟨kind, terrainEq⟩ := standard_terrain_success seed side config standard position
    config.raw.seed xlow xhigh ylow yhigh
  simp only [World.tileKind, terrainEq, bind, Except.bind]
  repeat' first | exact ⟨_, rfl⟩ | split

/-- Every cell of the actual standard sensor patch is admitted. Occupancy is
only queried at the resulting position; no constraint on entity coordinates is
needed to establish this observation's arithmetic success. -/
theorem standard_observeTile_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) (occupied : Occupancy) (row column : Fin patchShape.side) :
    ∃ tile, world.observeTile occupied row column = .ok tile := by
  have offset (index : Fin patchShape.side) :
      -(patchShape.side / 2 : Nat) ≤ (index.val : Int) - (patchShape.side / 2 : Nat) ∧
        (index.val : Int) - (patchShape.side / 2 : Nat) ≤ (patchShape.side / 2 : Nat) := by
    have bound : index.val < 11 := index.isLt
    change -(5 : Int) ≤ (index.val : Int) - 5 ∧ (index.val : Int) - 5 ≤ 5
    omega
  obtain ⟨position, translated⟩ := standard_body_translation seed side config standard
    world.body.position _ _ (offset column) (offset row)
  have coordinates := translated
  simp only [Position.translate, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def] at coordinates
  obtain ⟨x, xok, y, yok, result⟩ := coordinates
  have xexact := Coordinate.checked_exact _ x xok
  have yexact := Coordinate.checked_exact _ y yok
  have positionEq : (⟨x, y⟩ : Position) = position := Option.some.inj result
  have xbody := world.body.position.x.isLt
  have ybody := world.body.position.y.isLt
  have xoffset := offset column
  have yoffset := offset row
  have xmargin : -201 ≤ position.x.val ∧ position.x.val ≤ (config.side : Int) + 201 := by
    rw [← positionEq]
    dsimp only at xexact ⊢
    dsimp only [BoxPosition.position] at xexact
    change -(5 : Int) ≤ (column.val : Int) - 5 ∧ (column.val : Int) - 5 ≤ 5 at xoffset
    change x.val = (world.body.position.x.val : Int) + ((column.val : Int) - 5) at xexact
    omega
  have ymargin : -201 ≤ position.y.val ∧ position.y.val ≤ (config.side : Int) + 201 := by
    rw [← positionEq]
    dsimp only at yexact ⊢
    dsimp only [BoxPosition.position] at yexact
    change -(5 : Int) ≤ (row.val : Int) - 5 ∧ (row.val : Int) - 5 ≤ 5 at yoffset
    change y.val = (world.body.position.y.val : Int) + ((row.val : Int) - 5) at yexact
    omega
  obtain ⟨kind, kindEq⟩ := standard_tileKind_success seed side config standard world position
    xmargin.1 xmargin.2 ymargin.1 ymargin.2
  exact ⟨_, by simp only [World.observeTile, translated, kindEq]; rfl⟩

/-- Both actual row-major sensor traversals succeed for any standard-world
state. Finite occupancy construction and vector allocation remain subject to
the compiler/runtime boundary; this is the pure observation admission result. -/
theorem standard_observe_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) : ∃ observation, world.observe = .ok observation := by
  have traverse {α : Type} (size : Nat) (operation : Fin size → Except WorldError α)
      (success : ∀ index, ∃ value, operation index = .ok value) :
      ∃ values, Vector.ofFnM operation = .ok values := by
    choose values equations using success
    have functions : operation = fun index => .ok (values index) := funext equations
    rw [functions]
    exact ⟨Vector.ofFn values, Vector.ofFnM_pure⟩
  obtain ⟨tiles, tilesEq⟩ := traverse patchShape.side
    (fun row => Vector.ofFnM (world.observeTile world.occupancy row))
    (fun row => traverse patchShape.side (world.observeTile world.occupancy row)
      (fun column => standard_observeTile_success seed side config standard world
        world.occupancy row column))
  exact ⟨_, by simp only [World.observe, tilesEq]; rfl⟩

/-- Structural invariant preservation for the actual constructor traversals. -/
private theorem listTraversal_preserves {β : Type} (indices : List Nat)
    (body : Nat → β → Except WorldError (ForInStep β)) (invariant : β → Prop)
    (success : ∀ index ∈ indices, ∀ state, invariant state →
      ∃ step, body index state = .ok step ∧
        match step with | .done next => invariant next | .yield next => invariant next)
    (state : β) (initial : invariant state) :
    ∃ result, forIn indices state body = .ok result ∧ invariant result := by
  induction indices generalizing state with
  | nil => exact ⟨state, rfl, initial⟩
  | cons index rest ih =>
    obtain ⟨step, stepEq, preserved⟩ := success index (by simp) state initial
    rw [List.forIn_cons, stepEq]
    cases step with
    | done next => exact ⟨next, rfl, preserved⟩
    | yield next => exact ih (fun i hi => success i (by simp [hi])) next preserved

/-- Checked range/list correspondence retains invariants at early exits and yields. -/
private theorem rangeTraversal_preserves {β : Type} (stop : Nat)
    (body : Nat → β → Except WorldError (ForInStep β)) (invariant : β → Prop)
    (success : ∀ index, index < stop → ∀ state, invariant state →
      ∃ step, body index state = .ok step ∧
        match step with | .done next => invariant next | .yield next => invariant next)
    (state : β) (initial : invariant state) :
    ∃ result, forIn ([:stop] : Std.Legacy.Range) state body = .ok result ∧
      invariant result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply listTraversal_preserves _ _ invariant _ state initial
  intro index member
  exact success index (Std.Legacy.Range.mem_of_mem_range' member).2.1

/-- Admission alone is the constant-invariant specialization used by spawn scans. -/
private theorem rangeTraversal_success {β : Type} (stop : Nat)
    (body : Nat → β → Except WorldError (ForInStep β))
    (success : ∀ index, index < stop → ∀ state, ∃ step, body index state = .ok step)
    (state : β) :
    ∃ result, forIn ([:stop] : Std.Legacy.Range) state body = .ok result := by
  obtain ⟨result, admitted, _⟩ := rangeTraversal_preserves stop body (fun _ => True)
    (by
      intro index member current _
      obtain ⟨step, stepEq⟩ := success index member current
      exact ⟨step, stepEq, by cases step <;> trivial⟩) state trivial
  exact ⟨result, admitted⟩

/-- Successful constructor stages compose through the actual exception bind. -/
private theorem bind_success {α β : Type} (value : Except WorldError α)
    (next : α → Except WorldError β) (admitted : ∃ a, value = .ok a)
    (continues : ∀ a, ∃ b, next a = .ok b) : ∃ b, (value >>= next) = .ok b := by
  obtain ⟨a, ha⟩ := admitted
  obtain ⟨b, hb⟩ := continues a
  exact ⟨b, by rw [ha]; exact hb⟩

/-- The actual radius-four constructor scan admits every in-box center.
The structural traversal proof preserves row/column order and all count branches. -/
theorem standard_countKindNear_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) (position : BoxPosition config) (kind : TileKind) :
    ∃ count, countKindNear world position.position 4 kind = .ok count := by
  unfold countKindNear
  apply bind_success
  · apply rangeTraversal_success
    intro row rowBound count
    apply bind_success
    · apply rangeTraversal_success
      intro column columnBound count
      have offset (index : Nat) (bound : index < 9) :
          -(patchShape.side / 2 : Nat) ≤ (index : Int) - 4 ∧
            (index : Int) - 4 ≤ (patchShape.side / 2 : Nat) := by
        change -(5 : Int) ≤ (index : Int) - 4 ∧ (index : Int) - 4 ≤ 5
        omega
      obtain ⟨tile, translated⟩ := standard_body_translation seed side config standard
        position _ _ (offset column columnBound) (offset row rowBound)
      have coordinates := translated
      simp only [Position.translate, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def] at coordinates
      obtain ⟨x, xok, y, yok, result⟩ := coordinates
      have xexact := Coordinate.checked_exact _ x xok
      have yexact := Coordinate.checked_exact _ y yok
      have tileEq : (⟨x, y⟩ : Position) = tile := Option.some.inj result
      have xbody := position.x.isLt
      have ybody := position.y.isLt
      have xmargin : -201 ≤ tile.x.val ∧ tile.x.val ≤ (config.side : Int) + 201 := by
        rw [← tileEq]
        change x.val = (position.x.val : Int) + ((column : Int) - 4) at xexact
        dsimp only
        omega
      have ymargin : -201 ≤ tile.y.val ∧ tile.y.val ≤ (config.side : Int) + 201 := by
        rw [← tileEq]
        change y.val = (position.y.val : Int) + ((row : Int) - 4) at yexact
        dsimp only
        omega
      obtain ⟨tileKind, tileKindEq⟩ := standard_tileKind_success seed side config standard
        world tile xmargin.1 xmargin.2 ymargin.1 ymargin.2
      split
      · rename_i actual actualEq
        have same := Option.some.inj (actualEq.symm.trans translated)
        cases same
        simp only [tileKindEq, bind, Except.bind]
        split <;> exact ⟨_, rfl⟩
      · rename_i refused
        exact False.elim (refused tile translated)
    · intro next
      exact ⟨_, rfl⟩
  · intro next
    exact ⟨_, rfl⟩

/-- Out-of-box candidates return before terrain access; every admitted candidate
completes its actual scans and score branches without a walkability premise. -/
theorem standard_considerSpawn_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) (x y : Int) (best : Option (SpawnCandidate config)) :
    ∃ next finished, considerSpawn world x y best = .ok (next, finished) := by
  unfold considerSpawn
  split
  · rename_i position admitted
    obtain ⟨trees, treesEq⟩ := standard_countKindNear_success seed side config standard
      world position .tree
    obtain ⟨stone, stoneEq⟩ := standard_countKindNear_success seed side config standard
      world position .stone
    have hx := position.x.isLt
    have hy := position.y.isLt
    obtain ⟨kind, kindEq⟩ := standard_tileKind_success seed side config standard world
      position.position (by dsimp [BoxPosition.position]; omega)
      (by dsimp [BoxPosition.position]; omega) (by dsimp [BoxPosition.position]; omega)
      (by dsimp [BoxPosition.position]; omega)
    simp only [treesEq, stoneEq, kindEq, bind, Except.bind]
    split <;> exact ⟨_, _, rfl⟩
  · exact ⟨best, false, rfl⟩

/-- The actual standard spawn spiral always returns a legal body position.
Early exits preserve the current candidate; a complete scan may use the center
fallback. No walkable candidate, score improvement or early exit is assumed. -/
theorem standard_selectSpawn_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) : ∃ position, selectSpawn world = .ok position := by
  unfold selectSpawn
  apply bind_success
  · apply rangeTraversal_success
    intro radius radiusBound state
    apply bind_success
    · apply rangeTraversal_success
      intro directionIndex directionBound state
      dsimp only
      apply bind_success
      · apply rangeTraversal_success
        intro offset offsetBound state
        have coordinates := standard_spiral_coordinates seed side config standard
          radius offset radiusBound offsetBound
          (Direction.fromIndex ⟨directionIndex % 4, Nat.mod_lt _ (by decide)⟩)
        dsimp only at coordinates
        obtain ⟨x, y, xok, yok⟩ := coordinates
        simp only [xok, yok]
        apply bind_success
        · obtain ⟨candidate, finished, admitted⟩ := standard_considerSpawn_success
            seed side config standard world x.val y.val state.2
          exact ⟨(candidate, finished), admitted⟩
        · intro result
          rcases result with ⟨candidate, finished⟩
          dsimp only
          split <;> exact ⟨_, rfl⟩
      · intro result
        rcases result with ⟨returned, best⟩
        cases returned <;> exact ⟨_, rfl⟩
    · intro result
      rcases result with ⟨returned, best⟩
      cases returned <;> exact ⟨_, rfl⟩
  · intro result
    rcases result with ⟨returned, best⟩
    cases returned <;> exact ⟨_, rfl⟩

/-- Placement's coordinate invariant, distinct from the population capacity type.
Arbitrary world states need not satisfy this property. -/
def DeerInBox (config : WorldConfig)
    (population : Population Position config.raw.deerCap.toNat) : Prop :=
  ∀ position ∈ population.entries,
    0 ≤ position.x.val ∧ position.x.val < (config.side : Int) ∧
      0 ≤ position.y.val ∧ position.y.val < (config.side : Int)

/-- An actual two-draw placement attempt succeeds and preserves in-box entries,
including nonwalkable draws and full-capacity insertion refusal. -/
theorem standard_placeDeer_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) (population : Population Position config.raw.deerCap.toNat)
    (rng : Rng.Xoshiro256) (inside : DeerInBox config population) :
    ∃ next nextRng, placeDeer world population rng = .ok (next, nextRng) ∧
      DeerInBox config next := by
  unfold placeDeer
  split
  rename_i position nextRng drawn
  have hx := position.x.isLt
  have hy := position.y.isLt
  have positionInside : 0 ≤ position.position.x.val ∧
      position.position.x.val < (config.side : Int) ∧
      0 ≤ position.position.y.val ∧ position.position.y.val < (config.side : Int) := by
    dsimp only [BoxPosition.position]
    omega
  obtain ⟨kind, kindEq⟩ := standard_tileKind_success seed side config standard world
    position.position (by omega) (by omega) (by omega) (by omega)
  have inserted : DeerInBox config (population.push position.position) := by
    unfold Population.push
    split
    · intro entry member
      rcases Array.mem_push.mp member with old | same
      · exact inside entry old
      · subst entry
        exact positionInside
    · exact inside
  simp only [kindEq, bind, Except.bind]
  split
  · exact ⟨_, nextRng, rfl, inserted⟩
  · exact ⟨population, nextRng, rfl, inside⟩

/-- The configured placement loop preserves in-box deer using the original
world and the actual changing population/RNG accumulator. -/
theorem standard_initializeDeer_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) (inside : DeerInBox config world.deer) :
    ∃ population rng, initializeDeer world = .ok (population, rng) ∧
      DeerInBox config population := by
  suffices result : ∃ result, initializeDeer world = .ok result ∧
      DeerInBox config result.1 by
    obtain ⟨⟨population, rng⟩, admitted, preserved⟩ := result
    exact ⟨population, rng, admitted, preserved⟩
  unfold initializeDeer
  simp only [Prod.eta, bind_pure]
  apply rangeTraversal_preserves
    (β := Population Position config.raw.deerCap.toNat × Rng.Xoshiro256)
    _ _ (fun state => DeerInBox config state.1) _ _ inside
  intro index member state current
  obtain ⟨population, rng, admitted, preserved⟩ := standard_placeDeer_success
    seed side config standard world state.1 state.2 current
  exact ⟨.yield (population, rng), by simp only [admitted, bind, Except.bind]; rfl,
    preserved⟩

/-- Actual standard construction succeeds with in-box initial deer. Other
initial fields are characterized by the existing `World.initial_fields` theorem. -/
theorem standard_initial_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config) :
    ∃ world, World.initial config = .ok world ∧ DeerInBox config world.deer := by
  have emptyInside : DeerInBox config (World.empty config).deer := by
    intro entry member
    simp [World.empty, Population.empty] at member
  obtain ⟨position, spawned⟩ := standard_selectSpawn_success seed side config standard
    (World.empty config)
  obtain ⟨population, rng, initialized, inside⟩ := standard_initializeDeer_success
    seed side config standard (World.empty config) emptyInside
  simp only [World.initial, spawned, initialized, bind, Except.bind]
  exact ⟨_, rfl, inside⟩

/-- A signed-coordinate envelope after a bounded number of cardinal moves. -/
def PositionWithin (config : WorldConfig) (steps : Nat) (position : Position) : Prop :=
  -(steps : Int) ≤ position.x.val ∧ position.x.val < (config.side : Int) + steps ∧
    -(steps : Int) ≤ position.y.val ∧ position.y.val < (config.side : Int) + steps

/-- The constructor's in-box deer predicate is the zero-step envelope. -/
theorem deerInBox_iff_positionWithin (config : WorldConfig)
    (population : Population Position config.raw.deerCap.toNat) :
    DeerInBox config population ↔
      ∀ position ∈ population.entries, PositionWithin config 0 position := by
  simp [DeerInBox, PositionWithin]

/-- Actual single-deer wandering succeeds and expands the envelope by at most
one for the first 200 transitions. Both returned positions and RNGs are those
of the executed draw, direction, terrain and walkability branches. -/
theorem standard_wanderDeer_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (world : World config) (steps : Nat) (bounded : steps < 200) (position : Position)
    (rng : Rng.Xoshiro256) (inside : PositionWithin config steps position) :
    ∃ next nextRng, wanderDeer world position rng = .ok (next, nextRng) ∧
      PositionWithin config (steps + 1) next := by
  have sideBound : config.side ≤ 3000000000 := by
    have fields := WorldConfig.standard_bounds seed side config standard
    have upper := fields.2.2
    change side.val ≤ 3000000000 at upper
    simp only [WorldConfig.side, fields.1]
    omega
  have coordinates := inside
  unfold PositionWithin at coordinates
  have retained : PositionWithin config (steps + 1) position := by
    unfold PositionWithin
    push_cast
    omega
  have translated (direction : Direction) :
      ∃ candidate, position.translate direction.delta.1 direction.delta.2 = some candidate ∧
        PositionWithin config (steps + 1) candidate := by
    have dx : -1 ≤ direction.delta.1 ∧ direction.delta.1 ≤ 1 := by
      cases direction <;> decide
    have dy : -1 ≤ direction.delta.2 ∧ direction.delta.2 ≤ 1 := by
      cases direction <;> decide
    have xbound : -(2^63 : Int) ≤ position.x.val + direction.delta.1 ∧
        position.x.val + direction.delta.1 < 2^63 := by omega
    have ybound : -(2^63 : Int) ≤ position.y.val + direction.delta.2 ∧
        position.y.val + direction.delta.2 < 2^63 := by omega
    have xok : Coordinate.checked (position.x.val + direction.delta.1) =
        some (⟨_, xbound⟩ : Coordinate) := dif_pos xbound
    have yok : Coordinate.checked (position.y.val + direction.delta.2) =
        some (⟨_, ybound⟩ : Coordinate) := dif_pos ybound
    refine ⟨⟨⟨_, xbound⟩, ⟨_, ybound⟩⟩, ?_, ?_⟩
    · simp only [Position.translate, xok, yok, Option.pure_def]
      rfl
    · unfold PositionWithin
      dsimp only
      push_cast
      omega
  unfold wanderDeer
  split
  rename_i draw afterDraw drawn
  split
  · split
    rename_i directionWord afterDirection directionDraw
    obtain ⟨candidate, translation, advanced⟩ := translated
      (Direction.fromIndex ⟨directionWord.val.toNat, directionWord.property⟩)
    have margin := advanced
    unfold PositionWithin at margin
    obtain ⟨kind, kindEq⟩ := standard_tileKind_success seed side config standard world candidate
      (by push_cast at margin; omega) (by push_cast at margin; omega)
      (by push_cast at margin; omega) (by push_cast at margin; omega)
    dsimp only
    simp only [translation, kindEq, bind, Except.bind]
    split
    · exact ⟨candidate, afterDirection, rfl, advanced⟩
    · exact ⟨position, afterDirection, rfl, retained⟩
  · exact ⟨position, afterDraw, rfl, retained⟩

end AcornVerif.CurrentWorld
