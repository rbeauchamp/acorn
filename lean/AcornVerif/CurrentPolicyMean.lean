/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentBackupBounds
import AcornVerif.CurrentIntervals
import AcornVerif.FloatLibBridge

/-!
# The executed nominal policy mean

`Acorn.Features.PolicySnapshot.expected` is the value differential control compares:
the mean of the action values under the nominal ε-greedy policy, whose greedy part
averages every action within a tie window of the maximum. The tie set depends on the
values, so the mean is not convex in them and no Jensen inequality holds for it.

What holds is a sandwich. Let `C = (1 − ε) · max + ε · mean` be the convex combination
with a single greedy action. `expected_sandwich` proves that the executed word lies
between `C` less the tie window and the rounding of its threshold, and `C`, up to the
rounding of the binary64 evaluation and of the narrowing to binary32. The hypotheses
are finite action values of magnitude at most 8000 and at most eight actions; the
bounds are derived over the executed definition.

Each arithmetic fact is a rounding statement about the executed operation: binary64
additions, products and quotients at magnitude at most `2^16`, the binary32 threshold
subtraction through `AcornVerif.FloatLibBridge`, and the narrowing through
`Acorn.Conversion.narrow_finite_distance`.
-/

open Acorn Acorn.Features
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder
open AcornVerif.CurrentOperations AcornVerif.CurrentDivision AcornVerif.CurrentIntervals
open AcornVerif.CurrentBackupBounds AcornVerif.CurrentModelArithmetic AcornVerif.FloatLibBridge
open AcornVerif.CurrentLearner

namespace AcornVerif.CurrentPolicyMean

/-! ## Arithmetic at the magnitudes of the mean -/

/-- Actual binary32 subtraction is finite and follows signed nearest rounding throughout
the complete backup magnitude domain. -/
theorem binary32_rounded_sub_wide (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (bound : |numerical32 left - numerical32 right| ≤ 8589934592) :
    (left.sub right).Finite ∧
      Rounded (numerical32 left - numerical32 right) (numerical32 (left.sub right)) := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_sub_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 33 bound
  have error : |unpackedValue (UnpackedFloat.sub Format.binary32
      (decoded32 left) (decoded32 right)) - (numerical32 left - numerical32 right)| ≤ 512 := by
    apply le_trans operation.2
    norm_num [Format.mantissaBits, Format.minExponent]
  have fits : ModelFits Format.binary32
      (UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right)) := by
    apply model_fits_of_value_bound Format.binary32 _
      (model_normalized_finite _ _ operation.1) 34 (by decide)
    have triangle := abs_add_le
      (unpackedValue (UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right)) -
        (numerical32 left - numerical32 right)) (numerical32 left - numerical32 right)
    rw [sub_add_cancel] at triangle
    norm_num
    linarith
  have decoded : decoded32 (left.sub right) =
      UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right) := by
    change unpack Format.binary32 (pack Format.binary32
      (UnpackedFloat.sub Format.binary32 (Float32.Model.ofBits left.bits).unpack
        (Float32.Model.ofBits right.bits).unpack)) = _
    rw [model_ofBits32_decoded left hl, model_ofBits32_decoded right hr]
    exact model_unpack_pack_normalized _ _ operation.1 fits
  constructor
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded, model_sub_add_neg, model_neg_value, ← sub_eq_add_neg] using
      rounded_add (decoded32 left) (UnpackedFloat.neg (decoded32 right)) ln
        (model_neg_normalized _ _ rn)

/-- A finite binary32 difference of magnitude at most `2^13` is within `2^(-11)` of the
exact difference. -/
theorem binary32_sub_sum_error (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.sub right).Finite)
    (bound : |numerical32 left - numerical32 right| ≤ 8192) :
    |numerical32 (left.sub right) - (numerical32 left - numerical32 right)| ≤ 1 / 2048 := by
  have rounded := binary32_sub_roundAt left right leftFinite rightFinite finite
  have realBound : |(numerical32 left : ℝ) - (numerical32 right : ℝ)| ≤ 8192 := by
    exact_mod_cast bound
  have error := roundAt32_error_sum _ realBound
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

/-- A finite binary32 difference of magnitude at most `2^7` is within `2^(-17)` of the
exact difference. -/
theorem binary32_sub_unit_error (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.sub right).Finite)
    (bound : |numerical32 left - numerical32 right| ≤ 128) :
    |numerical32 (left.sub right) - (numerical32 left - numerical32 right)| ≤ 1 / 131072 := by
  have rounded := binary32_sub_roundAt left right leftFinite rightFinite finite
  have realBound : |(numerical32 left : ℝ) - (numerical32 right : ℝ)| ≤ 128 := by
    exact_mod_cast bound
  have error := roundAt32_error_unit _ realBound
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

set_option exponentiation.threshold 1100 in
/-- Narrowing a finite binary64 value of magnitude at most `2^13` gives a finite
binary32 word within `2^(-11)` of it: half the binary32 spacing at that magnitude. -/
theorem narrow_error (value : Binary64) (finite : value.Finite)
    (bound : |numerical64 value| ≤ 8192) :
    (Conversion.narrow value).Finite ∧
      |numerical32 (Conversion.narrow value) - numerical64 value| ≤ 1 / 2048 := by
  have resultFinite := narrow_finite_local value finite (by linarith)
  refine ⟨resultFinite, ?_⟩
  let limit : Binary64 := ⟨0x40c0000000000000⟩
  have limitFinite : limit.Finite := by decide
  have limitValue : numerical64 limit = 8192 := by
    dsimp only [limit]
    change (1 : ℚ) * 4503599627370496 * (2 : ℚ) ^ (-39 : Int) = 8192
    norm_num
  have magnitude := (numerical64_magnitude_order value limit finite limitFinite).mp
    (by rw [limitValue]; norm_num only [abs_of_pos (by norm_num : (0 : ℚ) < 8192)]; exact bound)
  have limitMagnitude : limit.magnitude = 0x40c0000000000000 := by dsimp only [limit]; rfl
  rw [limitMagnitude] at magnitude
  have fields := Conversion.fields64_decomposition value
  have exponent : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat ≤ 1036 := by omega
  have distance := Conversion.narrow_finite_distance value finite resultFinite
  have unit : Conversion.narrowUnit value ≤ 2 ^ 1064 := by
    unfold Conversion.narrowUnit
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have signs : unpackSign (spec := Format.binary32) (Conversion.narrow value).bits.toBitVec =
      unpackSign (spec := Format.binary64) value.bits.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    change ((Conversion.narrow value).bits.toNat >>> 31) % 2 = (value.bits.toNat >>> 63) % 2
    simp only [Nat.shiftRight_eq_div_pow]
    rw [Conversion.narrow_sign value finite]
  rw [numerical64_units value finite, numerical32_units _ resultFinite, signs]
  have lower : (2 * (Conversion.magnitudeUnits64 value : ℚ)) ≤
      2 * (Conversion.magnitudeUnits32 (Conversion.narrow value) : ℚ) + (2 : ℚ) ^ 1064 := by
    have cast : ((2 * Conversion.magnitudeUnits64 value : Nat) : ℚ) ≤
        ((2 * Conversion.magnitudeUnits32 (Conversion.narrow value) + 2 ^ 1064 : Nat) : ℚ) :=
      Nat.cast_le.mpr (le_trans distance.1 (Nat.add_le_add_left unit _))
    push_cast at cast
    exact cast
  have upper : (2 * (Conversion.magnitudeUnits32 (Conversion.narrow value) : ℚ)) ≤
      2 * (Conversion.magnitudeUnits64 value : ℚ) + (2 : ℚ) ^ 1064 := by
    have cast : ((2 * Conversion.magnitudeUnits32 (Conversion.narrow value) : Nat) : ℚ) ≤
        ((2 * Conversion.magnitudeUnits64 value + 2 ^ 1064 : Nat) : ℚ) :=
      Nat.cast_le.mpr (le_trans distance.2 (Nat.add_le_add_left unit _))
    push_cast at cast
    exact cast
  have scale : (2 : ℚ) ^ 1064 * (2 : ℚ) ^ (-1074 : Int) = 1 / 1024 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    norm_num
  have positive : (0 : ℚ) < (2 : ℚ) ^ (-1074 : Int) := zpow_pos (by norm_num) _
  have gap : |(Conversion.magnitudeUnits32 (Conversion.narrow value) : ℚ) -
      (Conversion.magnitudeUnits64 value : ℚ)| * (2 : ℚ) ^ (-1074 : Int) ≤ 1 / 2048 := by
    have close : |(Conversion.magnitudeUnits32 (Conversion.narrow value) : ℚ) -
        (Conversion.magnitudeUnits64 value : ℚ)| ≤ (2 : ℚ) ^ 1064 / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      _ ≤ (2 : ℚ) ^ 1064 / 2 * (2 : ℚ) ^ (-1074 : Int) :=
        mul_le_mul_of_nonneg_right close positive.le
      _ = 1 / 2048 := by rw [div_mul_eq_mul_div, scale]; norm_num
  have factor : signCoefficient (Sign.ofBitVec (unpackSign (spec := Format.binary64)
        value.bits.toBitVec)) *
        (Conversion.magnitudeUnits32 (Conversion.narrow value) : ℚ) * (2 : ℚ) ^ (-1074 : Int) -
      signCoefficient (Sign.ofBitVec (unpackSign (spec := Format.binary64)
        value.bits.toBitVec)) * (Conversion.magnitudeUnits64 value : ℚ) *
        (2 : ℚ) ^ (-1074 : Int) =
      signCoefficient (Sign.ofBitVec (unpackSign (spec := Format.binary64)
        value.bits.toBitVec)) *
        (((Conversion.magnitudeUnits32 (Conversion.narrow value) : ℚ) -
          (Conversion.magnitudeUnits64 value : ℚ)) * (2 : ℚ) ^ (-1074 : Int)) := by ring
  rw [factor, abs_mul, abs_mul, abs_of_pos positive]
  have unitSign : |signCoefficient (Sign.ofBitVec (unpackSign (spec := Format.binary64)
      value.bits.toBitVec))| = 1 := by
    cases Sign.ofBitVec (unpackSign (spec := Format.binary64) value.bits.toBitVec) <;>
      simp [signCoefficient]
  rw [unitSign, one_mul]
  exact gap

/-! ## The ordered maximum, the ordered minimum and saturation -/

/-- A fold that keeps one of its two arguments at every step returns its start or a
list element. -/
theorem fold_choice_member {α : Type} (choose : α → α → α)
    (either : ∀ kept item, choose kept item = kept ∨ choose kept item = item)
    (items : List α) (first : α) : items.foldl choose first ∈ first :: items := by
  induction items generalizing first with
  | nil => simp
  | cons head tail ih =>
    have inner := ih (choose first head)
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp inner with same | later
    · rcases either first head with kept | taken
      · rw [same, kept]
        simp
      · rw [same, taken]
        simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ later)

/-- The ordered maximum fold dominates its start and every finite list element. -/
theorem fold_best_dominates (words : List Binary32) (first : Binary32)
    (finite : ∀ word ∈ first :: words, word.Finite) :
    ∀ word ∈ first :: words, numerical32 word ≤ numerical32
      (words.foldl (fun best value => if best.less value then value else best) first) := by
  induction words generalizing first with
  | nil =>
    intro word member
    have same : word = first := by simpa using member
    subst same
    exact le_refl _
  | cons head tail ih =>
    intro word member
    have firstFinite := finite first (by simp)
    have headFinite := finite head (by simp)
    have compare := numerical32_less first head firstFinite headFinite
    have chosenFinite : (if first.less head then head else first).Finite := by
      split <;> assumption
    have rest : ∀ other ∈ (if first.less head then head else first) :: tail,
        other.Finite := by
      intro other inside
      rcases List.mem_cons.mp inside with same | later
      · rw [same]
        exact chosenFinite
      · exact finite other (by simp [later])
    have tailBound := ih (if first.less head then head else first) rest
    have chosenBound := tailBound (if first.less head then head else first) (by simp)
    have firstLe : numerical32 first ≤
        numerical32 (if first.less head then head else first) := by
      split
      · rename_i less
        rw [compare] at less
        exact le_of_lt (of_decide_eq_true less)
      · exact le_refl _
    have headLe : numerical32 head ≤
        numerical32 (if first.less head then head else first) := by
      split
      · exact le_refl _
      · rename_i notLess
        rw [compare] at notLess
        exact not_lt.mp (by simpa using notLess)
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with same | later
    · rw [same]
      exact le_trans firstLe chosenBound
    · rcases List.mem_cons.mp later with same | inTail
      · rw [same]
        exact le_trans headLe chosenBound
      · exact tailBound word (List.mem_cons_of_mem _ inTail)

variable {count : Word.Count}

/-- A snapshot's words are its first word followed by the rest. -/
theorem snapshot_words (snapshot : PolicySnapshot count) :
    snapshot.values.toList =
      snapshot.values.get (firstAction count) :: snapshot.values.toList.drop 1 := by
  have positive : 0 < snapshot.values.toList.length := by
    rw [Vector.length_toList]
    exact count.positive
  have head := List.drop_eq_getElem_cons positive
  rw [List.drop_zero] at head
  rw [head]
  simp [firstAction, vector_get]

/-- A word is one of a snapshot's words exactly when some action has it. -/
theorem snapshot_member (snapshot : PolicySnapshot count) (word : Binary32) :
    word ∈ snapshot.values.toList ↔ ∃ action, word = snapshot.values.get action := by
  constructor
  · intro inside
    obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp inside
    have small : index < count.word.toNat := by simpa using bound
    exact ⟨⟨index, small⟩, by simp [vector_get, ← same]⟩
  · rintro ⟨action, rfl⟩
    exact List.mem_iff_getElem.mpr ⟨action.val, by simp, by simp [vector_get]⟩

/-- The ordered maximum of finite action values is one of them and dominates each. -/
theorem best_spec (snapshot : PolicySnapshot count)
    (finite : ∀ action, (snapshot.values.get action).Finite) :
    (∃ action, snapshot.best = snapshot.values.get action) ∧
      ∀ action, numerical32 (snapshot.values.get action) ≤ numerical32 snapshot.best := by
  have words := snapshot_words snapshot
  have allFinite : ∀ word ∈ snapshot.values.get (firstAction count) ::
      snapshot.values.toList.drop 1, word.Finite := by
    intro word inside
    rw [← words] at inside
    obtain ⟨action, rfl⟩ := (snapshot_member snapshot word).mp inside
    exact finite action
  have member := fold_choice_member
    (fun best value : Binary32 => if best.less value then value else best)
    (fun kept item => by by_cases less : kept.less item <;> simp [less])
    (snapshot.values.toList.drop 1) (snapshot.values.get (firstAction count))
  rw [← words] at member
  refine ⟨(snapshot_member snapshot _).mp member, fun action => ?_⟩
  exact fold_best_dominates (snapshot.values.toList.drop 1)
    (snapshot.values.get (firstAction count)) allFinite (snapshot.values.get action)
    (by rw [← words]; exact (snapshot_member snapshot _).mpr ⟨action, rfl⟩)

/-- Saturation between two finite words is finite and no larger than the larger of
them, for every input word including NaNs and infinities. -/
theorem saturate_hull (value lower upper : Binary32) (lowerFinite : lower.Finite)
    (upperFinite : upper.Finite) :
    (value.saturate lower upper).Finite ∧
      |numerical32 (value.saturate lower upper)| ≤
        max |numerical32 lower| |numerical32 upper| := by
  unfold Binary32.saturate
  split
  · exact ⟨lowerFinite, le_max_left _ _⟩
  · split
    · exact ⟨upperFinite, le_max_right _ _⟩
    · rename_i notLow notHigh
      have notNaN : value.isNaN = false := by
        cases nan : value.isNaN
        · rfl
        · simp [nan] at notLow
      have keys : lower.key ≤ value.key ∧ value.key ≤ upper.key := by
        simp only [Binary32.less_eq_key, notNaN, Binary32.finite_not_nan lower lowerFinite,
          Binary32.finite_not_nan upper upperFinite, Bool.not_false, Bool.true_and,
          Bool.false_or, decide_eq_true_eq] at notLow notHigh
        omega
      have finite : value.Finite := by
        have low : lower.magnitude < 0x7f800000 := lowerFinite
        have high : upper.magnitude < 0x7f800000 := upperFinite
        have lowKey : -(lower.magnitude : Int) ≤ lower.key := by
          unfold Binary32.key
          split <;> omega
        have highKey : upper.key ≤ (upper.magnitude : Int) := by
          unfold Binary32.key
          split <;> omega
        have valueKey : value.key = (value.magnitude : Int) ∨
            value.key = -(value.magnitude : Int) := by
          unfold Binary32.key
          split
          · exact Or.inr rfl
          · exact Or.inl rfl
        change value.magnitude < 0x7f800000
        omega
      have low := (numerical32_order lower value lowerFinite finite).mpr keys.1
      have high := (numerical32_order value upper finite upperFinite).mpr keys.2
      refine ⟨finite, abs_le.mpr ⟨?_, ?_⟩⟩
      · have := neg_abs_le (numerical32 lower)
        have := le_max_left |numerical32 lower| |numerical32 upper|
        linarith
      · have := le_abs_self (numerical32 upper)
        have := le_max_right |numerical32 lower| |numerical32 upper|
        linarith

/-- The nominal policy mean of finite, bounded action values is finite and within the
same bound: the executed mean is saturated between two of the action values. -/
theorem expected_bound (snapshot : PolicySnapshot count) (radius : ℚ)
    (bounded : ∀ action, (snapshot.values.get action).Finite ∧
      |numerical32 (snapshot.values.get action)| ≤ radius) :
    snapshot.expected.Finite ∧ |numerical32 snapshot.expected| ≤ radius := by
  have lowerMember := fold_choice_member
    (fun lo v : Binary32 => if v.less lo then v else lo)
    (fun kept item => by by_cases less : item.less kept <;> simp [less])
    snapshot.values.toList (snapshot.values.get (firstAction count))
  have lowerWord : ∃ action,
      snapshot.values.toList.foldl (fun lo v : Binary32 => if v.less lo then v else lo)
        (snapshot.values.get (firstAction count)) = snapshot.values.get action := by
    rcases List.mem_cons.mp lowerMember with same | inside
    · exact ⟨firstAction count, same⟩
    · exact (snapshot_member snapshot _).mp inside
  obtain ⟨low, lowerSame⟩ := lowerWord
  obtain ⟨high, upperSame⟩ := (best_spec snapshot fun action => (bounded action).1).1
  have hull : ∀ word : Binary32,
      (word.saturate (snapshot.values.get low) (snapshot.values.get high)).Finite ∧
        |numerical32 (word.saturate (snapshot.values.get low) (snapshot.values.get high))| ≤
          radius := by
    intro word
    have inside := saturate_hull word _ _ (bounded low).1 (bounded high).1
    exact ⟨inside.1, le_trans inside.2 (max_le (bounded low).2 (bounded high).2)⟩
  unfold PolicySnapshot.expected
  simp only [lowerSame, upperSame]
  exact hull _

/-! ## The ordered minimum -/

/-- The ordered minimum fold is at most its start and every finite list element. -/
theorem fold_least_dominated (words : List Binary32) (first : Binary32)
    (finite : ∀ word ∈ first :: words, word.Finite) :
    ∀ word ∈ first :: words, numerical32
      (words.foldl (fun lo value => if value.less lo then value else lo) first) ≤
        numerical32 word := by
  induction words generalizing first with
  | nil =>
    intro word member
    have same : word = first := by simpa using member
    subst same
    exact le_refl _
  | cons head tail ih =>
    intro word member
    have firstFinite := finite first (by simp)
    have headFinite := finite head (by simp)
    have compare := numerical32_less head first headFinite firstFinite
    have chosenFinite : (if head.less first then head else first).Finite := by
      split <;> assumption
    have rest : ∀ other ∈ (if head.less first then head else first) :: tail,
        other.Finite := by
      intro other inside
      rcases List.mem_cons.mp inside with same | later
      · rw [same]
        exact chosenFinite
      · exact finite other (by simp [later])
    have tailBound := ih (if head.less first then head else first) rest
    have chosenBound := tailBound (if head.less first then head else first) (by simp)
    have firstLe : numerical32 (if head.less first then head else first) ≤
        numerical32 first := by
      split
      · rename_i less
        rw [compare] at less
        exact le_of_lt (of_decide_eq_true less)
      · exact le_refl _
    have headLe : numerical32 (if head.less first then head else first) ≤
        numerical32 head := by
      split
      · exact le_refl _
      · rename_i notLess
        rw [compare] at notLess
        exact not_lt.mp (by simpa using notLess)
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with same | later
    · rw [same]
      exact le_trans chosenBound firstLe
    · rcases List.mem_cons.mp later with same | inTail
      · rw [same]
        exact le_trans chosenBound headLe
      · exact tailBound word (List.mem_cons_of_mem _ inTail)

/-- The ordered minimum of finite action values is one of them and at most each. -/
theorem least_spec (snapshot : PolicySnapshot count)
    (finite : ∀ action, (snapshot.values.get action).Finite) :
    (∃ action, snapshot.values.toList.foldl (fun lo value : Binary32 =>
        if value.less lo then value else lo) (snapshot.values.get (firstAction count)) =
          snapshot.values.get action) ∧
      ∀ action, numerical32 (snapshot.values.toList.foldl (fun lo value : Binary32 =>
        if value.less lo then value else lo) (snapshot.values.get (firstAction count))) ≤
          numerical32 (snapshot.values.get action) := by
  have allFinite : ∀ word ∈ snapshot.values.get (firstAction count) ::
      snapshot.values.toList, word.Finite := by
    intro word inside
    rcases List.mem_cons.mp inside with same | later
    · rw [same]
      exact finite _
    · obtain ⟨action, rfl⟩ := (snapshot_member snapshot word).mp later
      exact finite action
  have member := fold_choice_member
    (fun lo value : Binary32 => if value.less lo then value else lo)
    (fun kept item => by by_cases less : item.less kept <;> simp [less])
    snapshot.values.toList (snapshot.values.get (firstAction count))
  constructor
  · rcases List.mem_cons.mp member with same | inside
    · exact ⟨firstAction count, same⟩
    · exact (snapshot_member snapshot _).mp inside
  · intro action
    exact fold_least_dominated snapshot.values.toList (snapshot.values.get (firstAction count))
      allFinite (snapshot.values.get action)
      (List.mem_cons_of_mem _ ((snapshot_member snapshot _).mpr ⟨action, rfl⟩))

/-- Saturation of a finite word between two ordered finite words is the exact
projection of its value onto their interval: it selects a word and rounds nothing. -/
theorem saturate_numeric (value lower upper : Binary32) (finite : value.Finite)
    (lowerFinite : lower.Finite) (upperFinite : upper.Finite)
    (ordered : numerical32 lower ≤ numerical32 upper) :
    numerical32 (value.saturate lower upper) =
      max (min (numerical32 value) (numerical32 upper)) (numerical32 lower) := by
  have low := numerical32_less value lower finite lowerFinite
  have high := numerical32_less upper value upperFinite finite
  unfold Binary32.saturate
  rw [Binary32.finite_not_nan value finite, low, high]
  simp only [Bool.false_or, decide_eq_true_eq]
  split
  · rename_i below
    exact (max_eq_right (le_trans (min_le_left _ _) (le_of_lt below))).symm
  · split
    · rename_i above
      rw [min_eq_right (le_of_lt above)]
      exact (max_eq_left ordered).symm
    · rename_i notBelow notAbove
      rw [min_eq_left (not_lt.mp notAbove)]
      exact (max_eq_left (not_lt.mp notBelow)).symm

/-- Projecting onto an interval that contains a point moves no value away from it. -/
theorem clamp_closer (value lower upper point : ℚ) (above : lower ≤ point)
    (below : point ≤ upper) :
    |max (min value upper) lower - point| ≤ |value - point| := by
  have positive := le_abs_self (value - point)
  have negative := neg_abs_le (value - point)
  have size := abs_nonneg (value - point)
  apply abs_le.mpr
  constructor
  · rcases le_total value upper with inside | outside
    · rw [min_eq_left inside]
      have floor := le_max_left value lower
      linarith
    · rw [min_eq_right outside]
      have floor := le_max_left upper lower
      linarith
  · rcases le_total (min value upper) lower with small | large
    · rw [max_eq_right small]
      linarith
    · rw [max_eq_left large]
      have cap := min_le_left value upper
      linarith

/-! ## The executed accumulation -/

/-- Rounding allowance of one binary64 addition, product or difference at magnitude
at most `2^16`. -/
def wideRadius : ℚ := 1 / 137438953472

/-- A product of two approximations is within the summed scaled errors of the exact
product. -/
theorem product_error (first second firstExact secondExact firstError secondError
    secondSize firstSize : ℚ) (firstClose : |first - firstExact| ≤ firstError)
    (secondClose : |second - secondExact| ≤ secondError) (secondBound : |second| ≤ secondSize)
    (firstBound : |firstExact| ≤ firstSize) :
    |first * second - firstExact * secondExact| ≤
      firstError * secondSize + firstSize * secondError := by
  have split : first * second - firstExact * secondExact =
      (first - firstExact) * second + firstExact * (second - secondExact) := by ring
  rw [split]
  have triangle := abs_add_le ((first - firstExact) * second)
    (firstExact * (second - secondExact))
  rw [abs_mul, abs_mul] at triangle
  have left : |first - firstExact| * |second| ≤ firstError * secondSize :=
    mul_le_mul firstClose secondBound (abs_nonneg _) (le_trans (abs_nonneg _) firstClose)
  have right : |firstExact| * |second - secondExact| ≤ firstSize * secondError :=
    mul_le_mul firstBound secondClose (abs_nonneg _) (le_trans (abs_nonneg _) firstBound)
  linarith

/-- A sum of values between two bounds lies between the bounds times the count. -/
theorem sum_between (words : List Binary32) (lower upper : ℚ)
    (each : ∀ word ∈ words, lower ≤ numerical32 word ∧ numerical32 word ≤ upper) :
    (words.length : ℚ) * lower ≤ (words.map numerical32).sum ∧
      (words.map numerical32).sum ≤ (words.length : ℚ) * upper := by
  induction words with
  | nil => simp
  | cons head rest ih =>
    have first := each head (by simp)
    have tail := ih fun word member => each word (List.mem_cons_of_mem _ member)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith [tail.1, tail.2]

/-- The executed accumulation of the mean over a list of finite action values of
magnitude at most 8000: started from totals within `k` rounding allowances of exact
sums of at most `k` such values, with at most eight values in all, the running total
of all values and of the values at or above the threshold stay finite and within one
allowance per value of the exact sums, and the count of tied values is exact. -/
theorem totals_spec (threshold : Binary32) (words : List Binary32)
    (bounded : ∀ word ∈ words, word.Finite ∧ |numerical32 word| ≤ 8000) :
    ∀ (all tied : Binary64) (tiedCount terms : Nat) (allExact tiedExact : ℚ),
      terms + words.length ≤ 8 → all.Finite → tied.Finite →
      |numerical64 all - allExact| ≤ (terms : ℚ) * wideRadius →
      |numerical64 tied - tiedExact| ≤ (terms : ℚ) * wideRadius →
      |allExact| ≤ 8000 * (terms : ℚ) → |tiedExact| ≤ 8000 * (terms : ℚ) →
      (words.foldl (fun (x : Binary64 × Binary64 × Nat) (v : Binary32) =>
          match x with
          | (all, tied, n) => (all.add (Conversion.widen v),
            if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
            if threshold.lessOrEqual v then n + 1 else n)) (all, tied, tiedCount)).1.Finite ∧
        (words.foldl (fun (x : Binary64 × Binary64 × Nat) (v : Binary32) =>
          match x with
          | (all, tied, n) => (all.add (Conversion.widen v),
            if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
            if threshold.lessOrEqual v then n + 1 else n)) (all, tied, tiedCount)).2.1.Finite ∧
        |numerical64 (words.foldl (fun (x : Binary64 × Binary64 × Nat) (v : Binary32) =>
          match x with
          | (all, tied, n) => (all.add (Conversion.widen v),
            if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
            if threshold.lessOrEqual v then n + 1 else n)) (all, tied, tiedCount)).1 -
          (allExact + (words.map numerical32).sum)| ≤
            ((terms + words.length : Nat) : ℚ) * wideRadius ∧
        |numerical64 (words.foldl (fun (x : Binary64 × Binary64 × Nat) (v : Binary32) =>
          match x with
          | (all, tied, n) => (all.add (Conversion.widen v),
            if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
            if threshold.lessOrEqual v then n + 1 else n)) (all, tied, tiedCount)).2.1 -
          (tiedExact + ((words.filter fun word => threshold.lessOrEqual word).map
            numerical32).sum)| ≤ ((terms + words.length : Nat) : ℚ) * wideRadius ∧
        (words.foldl (fun (x : Binary64 × Binary64 × Nat) (v : Binary32) =>
          match x with
          | (all, tied, n) => (all.add (Conversion.widen v),
            if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
            if threshold.lessOrEqual v then n + 1 else n)) (all, tied, tiedCount)).2.2 =
          tiedCount + (words.filter fun word => threshold.lessOrEqual word).length := by
  induction words with
  | nil =>
    intro all tied tiedCount terms allExact tiedExact _ allFinite tiedFinite allClose tiedClose _ _
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero, List.filter_nil,
      List.length_nil]
    exact ⟨allFinite, tiedFinite, allClose, tiedClose, trivial⟩
  | cons head rest ih =>
    intro all tied tiedCount terms allExact tiedExact few allFinite tiedFinite allClose tiedClose
      allSize tiedSize
    have headBound := bounded head (by simp)
    have wideFinite := Conversion.widen_finite head headBound.1
    have wideValue := numerical_widen_exact head headBound.1
    have count : (terms : ℚ) ≤ 7 := by
      have : terms ≤ 7 := by simp only [List.length_cons] at few; omega
      exact_mod_cast this
    have nonnegative : (0 : ℚ) ≤ (terms : ℚ) := Nat.cast_nonneg _
    have tiny : (terms : ℚ) * wideRadius ≤ 1 := by
      unfold wideRadius
      nlinarith
    have radius : (0 : ℚ) ≤ wideRadius := by unfold wideRadius; norm_num
    have size (word : Binary64) (exact : ℚ) (close : |numerical64 word - exact| ≤
        (terms : ℚ) * wideRadius) (bound : |exact| ≤ 8000 * (terms : ℚ)) :
        |numerical64 word + numerical64 (Conversion.widen head)| ≤ 65536 := by
      have triangle := abs_add_le (numerical64 word - exact) exact
      rw [sub_add_cancel] at triangle
      have outer := abs_add_le (numerical64 word) (numerical64 (Conversion.widen head))
      rw [wideValue] at outer ⊢
      linarith [headBound.2]
    have step (word : Binary64) (exact : ℚ) (finite : word.Finite)
        (close : |numerical64 word - exact| ≤ (terms : ℚ) * wideRadius)
        (bound : |exact| ≤ 8000 * (terms : ℚ)) :
        (word.add (Conversion.widen head)).Finite ∧
          |numerical64 (word.add (Conversion.widen head)) - (exact + numerical32 head)| ≤
            ((terms + 1 : Nat) : ℚ) * wideRadius ∧
          |exact + numerical32 head| ≤ 8000 * ((terms + 1 : Nat) : ℚ) := by
      have sum := binary64_add_finite_error word (Conversion.widen head) finite wideFinite
        (size word exact close bound)
      have error := sum.2
      rw [wideValue] at error
      change _ ≤ wideRadius at error
      have split : numerical64 (word.add (Conversion.widen head)) - (exact + numerical32 head) =
          (numerical64 (word.add (Conversion.widen head)) -
            (numerical64 word + numerical32 head)) + (numerical64 word - exact) := by ring
      have triangle := abs_add_le
        (numerical64 (word.add (Conversion.widen head)) - (numerical64 word + numerical32 head))
        (numerical64 word - exact)
      have outer := abs_add_le exact (numerical32 head)
      refine ⟨sum.1, ?_, ?_⟩
      · rw [split]
        push_cast
        linarith
      · push_cast
        linarith [headBound.2]
    have stay (word : Binary64) (exact : ℚ)
        (close : |numerical64 word - exact| ≤ (terms : ℚ) * wideRadius)
        (bound : |exact| ≤ 8000 * (terms : ℚ)) :
        |numerical64 word - exact| ≤ ((terms + 1 : Nat) : ℚ) * wideRadius ∧
          |exact| ≤ 8000 * ((terms + 1 : Nat) : ℚ) := by
      push_cast
      constructor <;> linarith
    have allStep := step all allExact allFinite allClose allSize
    have room : terms + 1 + rest.length ≤ 8 := by
      simp only [List.length_cons] at few
      omega
    have restBounded : ∀ word ∈ rest, word.Finite ∧ |numerical32 word| ≤ 8000 :=
      fun word member => bounded word (List.mem_cons_of_mem _ member)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons]
    by_cases tie : threshold.lessOrEqual head = true
    · have tiedStep := step tied tiedExact tiedFinite tiedClose tiedSize
      have result := ih restBounded (all.add (Conversion.widen head))
        (tied.add (Conversion.widen head)) (tiedCount + 1) (terms + 1)
        (allExact + numerical32 head) (tiedExact + numerical32 head) room allStep.1 tiedStep.1
        allStep.2.1 tiedStep.2.1 allStep.2.2 tiedStep.2.2
      simp only [tie, ↓reduceIte, List.filter_cons_of_pos, List.map_cons, List.sum_cons,
        List.length_cons]
      refine ⟨result.1, result.2.1, ?_, ?_, ?_⟩
      · have same : terms + (rest.length + 1) = terms + 1 + rest.length := by omega
        rw [same, ← add_assoc]
        exact result.2.2.1
      · have same : terms + (rest.length + 1) = terms + 1 + rest.length := by omega
        rw [same, ← add_assoc]
        exact result.2.2.2.1
      · rw [result.2.2.2.2]
        omega
    · have tiedStay := stay tied tiedExact tiedClose tiedSize
      have result := ih restBounded (all.add (Conversion.widen head)) tied tiedCount (terms + 1)
        (allExact + numerical32 head) tiedExact room allStep.1 tiedFinite allStep.2.1 tiedStay.1
        allStep.2.2 tiedStay.2
      simp only [tie, Bool.false_eq_true, ↓reduceIte, List.filter_cons_of_neg,
        not_false_eq_true]
      refine ⟨result.1, result.2.1, ?_, ?_, result.2.2.2.2⟩
      · have same : terms + (rest.length + 1) = terms + 1 + rest.length := by omega
        rw [same, ← add_assoc]
        exact result.2.2.1
      · have same : terms + (rest.length + 1) = terms + 1 + rest.length := by omega
        rw [same]
        exact result.2.2.2.1

/-! ## The closing arithmetic -/

/-- The executed closing arithmetic of the mean, as a function of its accumulated
totals: the two quotients, the convex combination in binary64, the narrowing and the
saturation between the least and the greatest action value. -/
def meanWord (lower upper : Binary32) (eps all tied : Binary64) (tiedCount : Nat)
    (actions : UInt64) : Binary32 :=
  (Conversion.narrow ((((Binary64.ofUInt64 1).sub eps).mul
    (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
      (eps.mul (all.div (Binary64.ofUInt64 actions))))).saturate lower upper

/-- Rounding allowance of the executed mean against the exact tie-window mean: half
the binary32 spacing at magnitude below `2^13`, plus the binary64 evaluation. -/
def meanRadius : ℚ := 1 / 2048 + 1 / 16777216

/-- A binary64 quotient of an accumulated total by a small positive count is finite and
within eight addition allowances plus one quotient allowance of the exact mean. -/
theorem quotient_spec (total denominator : Binary64) (count : Nat) (sum mean : ℚ)
    (totalFinite : total.Finite) (denominatorFinite : denominator.Finite)
    (denominatorValue : numerical64 denominator = (count : ℚ)) (positive : 1 ≤ count)
    (close : |numerical64 total - sum| ≤ 8 * wideRadius) (exact : mean = sum / (count : ℚ))
    (bound : |mean| ≤ 8000) :
    (total.div denominator).Finite ∧
      |numerical64 (total.div denominator) - mean| ≤ 8 * wideRadius + 1 / 34359738368 ∧
      |numerical64 (total.div denominator)| ≤ 8001 := by
  have one : (1 : ℚ) ≤ (count : ℚ) := by exact_mod_cast positive
  have countPositive : (0 : ℚ) < (count : ℚ) := by linarith
  have near : |numerical64 total / (count : ℚ) - mean| ≤ 8 * wideRadius := by
    rw [exact, ← sub_div, abs_div, abs_of_pos countPositive]
    exact le_trans (div_le_self (abs_nonneg _) one) close
  have radius : (8 : ℚ) * wideRadius ≤ 1 / 2 := by unfold wideRadius; norm_num
  have size : |numerical64 total / (count : ℚ)| ≤ 8000 + 1 / 2 := by
    have triangle := abs_add_le (numerical64 total / (count : ℚ) - mean) mean
    rw [sub_add_cancel] at triangle
    linarith
  have quotient := binary64_div_finite_error total denominator totalFinite denominatorFinite
    (by rw [denominatorValue]; exact ne_of_gt countPositive)
    (by rw [denominatorValue]; linarith)
  have error := quotient.2
  rw [denominatorValue] at error
  have split : numerical64 (total.div denominator) - mean =
      (numerical64 (total.div denominator) - numerical64 total / (count : ℚ)) +
        (numerical64 total / (count : ℚ) - mean) := by ring
  have triangle := abs_add_le
    (numerical64 (total.div denominator) - numerical64 total / (count : ℚ))
    (numerical64 total / (count : ℚ) - mean)
  refine ⟨quotient.1, ?_, ?_⟩
  · rw [split]
    linarith
  · have outer := abs_add_le (numerical64 (total.div denominator) - mean) mean
    rw [sub_add_cancel] at outer
    rw [split] at outer
    have small : (1 : ℚ) / 34359738368 ≤ 1 / 2 := by norm_num
    linarith

/-- A small machine word converts to a finite binary64 value. -/
theorem small_word_finite (word : UInt64) (small : word.toNat < 2 ^ 53) :
    (Binary64.ofUInt64 word).Finite := by
  have bound := ofUInt64_word_bound word small
  change (Binary64.ofUInt64 word).bits.toNat &&& (2 ^ 63 - 1) < 0x7ff0000000000000
  exact Nat.lt_of_le_of_lt Nat.and_le_left bound

/-- A natural number below `2^64` is its own machine word. -/
theorem word_value (count : Nat) (small : count ≤ 8) : count.toUInt64.toNat = count := by
  change count % 2 ^ 64 = count
  exact Nat.mod_eq_of_lt (by omega)

/-- The closing arithmetic of the mean, from accumulated totals within eight addition
allowances of exact sums: for a rate in `[0, 1]`, tied and overall means between the
least and the greatest action value, both of magnitude at most 8000, the executed word
is finite and within `meanRadius` of `(1 − ε) · tiedMean + ε · allMean`. -/
theorem meanWord_spec (lower upper : Binary32) (eps all tied : Binary64) (tiedCount : Nat)
    (actions : UInt64) (allSum tiedSum : ℚ) (lowerFinite : lower.Finite)
    (upperFinite : upper.Finite) (lowerSize : |numerical32 lower| ≤ 8000)
    (upperSize : |numerical32 upper| ≤ 8000) (epsFinite : eps.Finite)
    (rate : 0 ≤ numerical64 eps ∧ numerical64 eps ≤ 1) (allFinite : all.Finite)
    (tiedFinite : tied.Finite) (allClose : |numerical64 all - allSum| ≤ 8 * wideRadius)
    (tiedClose : |numerical64 tied - tiedSum| ≤ 8 * wideRadius)
    (tiedPositive : 1 ≤ tiedCount) (tiedSmall : tiedCount ≤ 8)
    (actionsPositive : 1 ≤ actions.toNat) (actionsSmall : actions.toNat ≤ 8)
    (tiedBetween : numerical32 lower ≤ tiedSum / (tiedCount : ℚ) ∧
      tiedSum / (tiedCount : ℚ) ≤ numerical32 upper)
    (allBetween : numerical32 lower ≤ allSum / (actions.toNat : ℚ) ∧
      allSum / (actions.toNat : ℚ) ≤ numerical32 upper) :
    (meanWord lower upper eps all tied tiedCount actions).Finite ∧
      |numerical32 (meanWord lower upper eps all tied tiedCount actions) -
        ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
          numerical64 eps * (allSum / (actions.toNat : ℚ)))| ≤ meanRadius := by
  have lowerBounds := abs_le.mp lowerSize
  have upperBounds := abs_le.mp upperSize
  have tiedMeanSize : |tiedSum / (tiedCount : ℚ)| ≤ 8000 :=
    abs_le.mpr ⟨by linarith [tiedBetween.1], by linarith [tiedBetween.2]⟩
  have allMeanSize : |allSum / (actions.toNat : ℚ)| ≤ 8000 :=
    abs_le.mpr ⟨by linarith [allBetween.1], by linarith [allBetween.2]⟩
  have tiedWord : numerical64 (Binary64.ofUInt64 tiedCount.toUInt64) = (tiedCount : ℚ) := by
    have value := numerical64_ofUInt64 tiedCount.toUInt64
      (by rw [word_value tiedCount tiedSmall]; omega)
    rw [word_value tiedCount tiedSmall] at value
    exact value
  have actionsWord : numerical64 (Binary64.ofUInt64 actions) = (actions.toNat : ℚ) :=
    numerical64_ofUInt64 actions (by omega)
  have tiedDenominator : (Binary64.ofUInt64 tiedCount.toUInt64).Finite :=
    small_word_finite _ (by rw [word_value tiedCount tiedSmall]; omega)
  have tiedMean := quotient_spec tied (Binary64.ofUInt64 tiedCount.toUInt64) tiedCount tiedSum
    (tiedSum / (tiedCount : ℚ)) tiedFinite tiedDenominator tiedWord tiedPositive tiedClose rfl
    tiedMeanSize
  have allMean := quotient_spec all (Binary64.ofUInt64 actions) actions.toNat allSum
    (allSum / (actions.toNat : ℚ)) allFinite (small_word_finite _ (by omega)) actionsWord
    actionsPositive allClose rfl allMeanSize
  have oneFinite : (Binary64.ofUInt64 1).Finite := by decide
  have oneValue : numerical64 (Binary64.ofUInt64 1) = 1 := by
    have value := numerical64_ofUInt64 1 (by decide)
    exact value
  have complement := binary64_sub_finite_error (Binary64.ofUInt64 1) eps oneFinite epsFinite
    (by rw [oneValue]; exact abs_le.mpr ⟨by linarith [rate.2], by linarith [rate.1]⟩)
  have complementError := complement.2
  rw [oneValue] at complementError
  change _ ≤ wideRadius at complementError
  have radius : wideRadius = 1 / 137438953472 := rfl
  have complementSize : |numerical64 ((Binary64.ofUInt64 1).sub eps)| ≤ 2 := by
    have triangle := abs_add_le
      (numerical64 ((Binary64.ofUInt64 1).sub eps) - (1 - numerical64 eps)) (1 - numerical64 eps)
    rw [sub_add_cancel] at triangle
    have inner : |1 - numerical64 eps| ≤ 1 :=
      abs_le.mpr ⟨by linarith [rate.2], by linarith [rate.1]⟩
    rw [radius] at complementError
    linarith
  have complementExact : |1 - numerical64 eps| ≤ 1 :=
    abs_le.mpr ⟨by linarith [rate.2], by linarith [rate.1]⟩
  have rateExact : |numerical64 eps| ≤ 1 := abs_le.mpr ⟨by linarith [rate.1], rate.2⟩
  have firstSize : |numerical64 ((Binary64.ofUInt64 1).sub eps) *
      numerical64 (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))| ≤ 65536 := by
    rw [abs_mul]
    have bound := mul_le_mul complementSize tiedMean.2.2 (abs_nonneg _) (by norm_num)
    linarith
  have first := binary64_mul_finite_error ((Binary64.ofUInt64 1).sub eps)
    (tied.div (Binary64.ofUInt64 tiedCount.toUInt64)) complement.1 tiedMean.1 firstSize
  have firstExact := product_error (numerical64 ((Binary64.ofUInt64 1).sub eps))
    (numerical64 (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))) (1 - numerical64 eps)
    (tiedSum / (tiedCount : ℚ)) wideRadius (8 * wideRadius + 1 / 34359738368) 8001 1
    complementError tiedMean.2.1 tiedMean.2.2 complementExact
  have secondSize : |numerical64 eps *
      numerical64 (all.div (Binary64.ofUInt64 actions))| ≤ 65536 := by
    rw [abs_mul]
    have bound := mul_le_mul rateExact allMean.2.2 (abs_nonneg _) (by norm_num)
    linarith
  have second := binary64_mul_finite_error eps (all.div (Binary64.ofUInt64 actions)) epsFinite
    allMean.1 secondSize
  have secondExact := product_error (numerical64 eps)
    (numerical64 (all.div (Binary64.ofUInt64 actions))) (numerical64 eps)
    (allSum / (actions.toNat : ℚ)) 0 (8 * wideRadius + 1 / 34359738368) 8001 1
    (by rw [sub_self, abs_zero]) allMean.2.1 allMean.2.2 rateExact
  have firstError := first.2
  have secondError := second.2
  change _ ≤ wideRadius at firstError secondError
  rw [radius] at firstError secondError firstExact secondExact complementError
  have between : numerical32 lower ≤ (1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
        numerical64 eps * (allSum / (actions.toNat : ℚ)) ∧
      (1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
        numerical64 eps * (allSum / (actions.toNat : ℚ)) ≤ numerical32 upper := by
    have complementNonnegative : 0 ≤ 1 - numerical64 eps := by linarith [rate.2]
    have low₁ := mul_le_mul_of_nonneg_left tiedBetween.1 complementNonnegative
    have low₂ := mul_le_mul_of_nonneg_left allBetween.1 rate.1
    have high₁ := mul_le_mul_of_nonneg_left tiedBetween.2 complementNonnegative
    have high₂ := mul_le_mul_of_nonneg_left allBetween.2 rate.1
    constructor <;> nlinarith
  have exactSize : |(1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
      numerical64 eps * (allSum / (actions.toNat : ℚ))| ≤ 8000 :=
    abs_le.mpr ⟨by linarith [between.1], by linarith [between.2]⟩
  have firstClose : |numerical64 (((Binary64.ofUInt64 1).sub eps).mul
      (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))) -
      (1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ))| ≤ 8014 / 137438953472 := by
    have triangle := abs_sub_le
      (numerical64 (((Binary64.ofUInt64 1).sub eps).mul
        (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))))
      (numerical64 ((Binary64.ofUInt64 1).sub eps) *
        numerical64 (tied.div (Binary64.ofUInt64 tiedCount.toUInt64)))
      ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)))
    linarith
  have secondClose : |numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions))) -
      numerical64 eps * (allSum / (actions.toNat : ℚ))| ≤ 13 / 137438953472 := by
    have triangle := abs_sub_le
      (numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions))))
      (numerical64 eps * numerical64 (all.div (Binary64.ofUInt64 actions)))
      (numerical64 eps * (allSum / (actions.toNat : ℚ)))
    linarith
  have firstWord : |numerical64 (((Binary64.ofUInt64 1).sub eps).mul
      (tied.div (Binary64.ofUInt64 tiedCount.toUInt64)))| ≤ 8001 := by
    have triangle := abs_add_le
      (numerical64 (((Binary64.ofUInt64 1).sub eps).mul
        (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))) -
        (1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)))
      ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)))
    rw [sub_add_cancel] at triangle
    have product : |(1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ))| ≤ 8000 := by
      rw [abs_mul]
      have bound := mul_le_mul complementExact tiedMeanSize (abs_nonneg _) (by norm_num)
      linarith
    linarith
  have secondWord : |numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions)))| ≤ 8001 := by
    have triangle := abs_add_le
      (numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions))) -
        numerical64 eps * (allSum / (actions.toNat : ℚ)))
      (numerical64 eps * (allSum / (actions.toNat : ℚ)))
    rw [sub_add_cancel] at triangle
    have product : |numerical64 eps * (allSum / (actions.toNat : ℚ))| ≤ 8000 := by
      rw [abs_mul]
      have bound := mul_le_mul rateExact allMeanSize (abs_nonneg _) (by norm_num)
      linarith
    linarith
  have total := binary64_add_finite_error
    (((Binary64.ofUInt64 1).sub eps).mul (tied.div (Binary64.ofUInt64 tiedCount.toUInt64)))
    (eps.mul (all.div (Binary64.ofUInt64 actions))) first.1 second.1
    (le_trans (abs_add_le _ _) (by linarith))
  have totalClose : |numerical64 ((((Binary64.ofUInt64 1).sub eps).mul
      (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
        (eps.mul (all.div (Binary64.ofUInt64 actions)))) -
      ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
        numerical64 eps * (allSum / (actions.toNat : ℚ)))| ≤ 1 / 16777216 := by
    have split : numerical64 ((((Binary64.ofUInt64 1).sub eps).mul
        (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
          (eps.mul (all.div (Binary64.ofUInt64 actions)))) -
        ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
          numerical64 eps * (allSum / (actions.toNat : ℚ))) =
        (numerical64 ((((Binary64.ofUInt64 1).sub eps).mul
          (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
            (eps.mul (all.div (Binary64.ofUInt64 actions)))) -
          (numerical64 (((Binary64.ofUInt64 1).sub eps).mul
            (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))) +
            numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions))))) +
        ((numerical64 (((Binary64.ofUInt64 1).sub eps).mul
            (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))) -
            (1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ))) +
          (numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions))) -
            numerical64 eps * (allSum / (actions.toNat : ℚ)))) := by ring
    rw [split]
    have outer := abs_add_le
      (numerical64 ((((Binary64.ofUInt64 1).sub eps).mul
        (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
          (eps.mul (all.div (Binary64.ofUInt64 actions)))) -
        (numerical64 (((Binary64.ofUInt64 1).sub eps).mul
          (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))) +
          numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions)))))
      ((numerical64 (((Binary64.ofUInt64 1).sub eps).mul
          (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))) -
          (1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ))) +
        (numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions))) -
          numerical64 eps * (allSum / (actions.toNat : ℚ))))
    have inner := abs_add_le
      (numerical64 (((Binary64.ofUInt64 1).sub eps).mul
        (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))) -
        (1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)))
      (numerical64 (eps.mul (all.div (Binary64.ofUInt64 actions))) -
        numerical64 eps * (allSum / (actions.toNat : ℚ)))
    have last := total.2
    linarith
  have wideSize : |numerical64 ((((Binary64.ofUInt64 1).sub eps).mul
      (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
        (eps.mul (all.div (Binary64.ofUInt64 actions))))| ≤ 8192 := by
    have triangle := abs_add_le
      (numerical64 ((((Binary64.ofUInt64 1).sub eps).mul
        (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
          (eps.mul (all.div (Binary64.ofUInt64 actions)))) -
        ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
          numerical64 eps * (allSum / (actions.toNat : ℚ))))
      ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
        numerical64 eps * (allSum / (actions.toNat : ℚ)))
    rw [sub_add_cancel] at triangle
    linarith
  have narrowed := narrow_error _ total.1 wideSize
  have ordered : numerical32 lower ≤ numerical32 upper := le_trans between.1 between.2
  have value := saturate_numeric _ lower upper narrowed.1 lowerFinite upperFinite ordered
  have closer := clamp_closer
    (numerical32 (Conversion.narrow ((((Binary64.ofUInt64 1).sub eps).mul
      (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
        (eps.mul (all.div (Binary64.ofUInt64 actions))))))
    (numerical32 lower) (numerical32 upper)
    ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
      numerical64 eps * (allSum / (actions.toNat : ℚ))) between.1 between.2
  refine ⟨(saturate_hull _ lower upper lowerFinite upperFinite).1, ?_⟩
  unfold meanWord
  rw [value]
  refine le_trans closer ?_
  have chain := abs_sub_le
    (numerical32 (Conversion.narrow ((((Binary64.ofUInt64 1).sub eps).mul
      (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
        (eps.mul (all.div (Binary64.ofUInt64 actions))))))
    (numerical64 ((((Binary64.ofUInt64 1).sub eps).mul
      (tied.div (Binary64.ofUInt64 tiedCount.toUInt64))).add
        (eps.mul (all.div (Binary64.ofUInt64 actions)))))
    ((1 - numerical64 eps) * (tiedSum / (tiedCount : ℚ)) +
      numerical64 eps * (allSum / (actions.toNat : ℚ)))
  unfold meanRadius
  linarith [narrowed.2]

/-! ## The sandwich -/

/-- The convex combination the mean approximates: `(1 − ε)` times the greatest action
value plus `ε` times the mean of all action values, in exact arithmetic over the
stored words. It is convex in the action values. -/
def greedyMean (snapshot : PolicySnapshot count) : ℚ :=
  (1 - numerical32 snapshot.epsilon.value) * numerical32 snapshot.best +
    numerical32 snapshot.epsilon.value *
      ((snapshot.values.toList.map numerical32).sum / (count.word.toNat : ℚ))

/-- How far the tie-window mean can fall below `greedyMean`: the tie window, at most
`2^(-19)`, plus the rounding of the threshold subtraction, plus `meanRadius`. -/
def meanSlack : ℚ := 1 / 524288 + 1 / 2048 + meanRadius

/-- The executed mean is the closing arithmetic of the executed accumulation. -/
theorem expected_eq (snapshot : PolicySnapshot count) :
    snapshot.expected = meanWord
      (snapshot.values.toList.foldl (fun lo value : Binary32 =>
        if value.less lo then value else lo) (snapshot.values.get (firstAction count)))
      snapshot.best (Conversion.widen snapshot.epsilon.value)
      (snapshot.values.toList.foldl (fun (x : Binary64 × Binary64 × Nat) (v : Binary32) =>
        match x with
        | (all, tied, n) => (all.add (Conversion.widen v),
          if (snapshot.best.sub tieWindow).lessOrEqual v then tied.add (Conversion.widen v)
          else tied,
          if (snapshot.best.sub tieWindow).lessOrEqual v then n + 1 else n))
        (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0)).1
      (snapshot.values.toList.foldl (fun (x : Binary64 × Binary64 × Nat) (v : Binary32) =>
        match x with
        | (all, tied, n) => (all.add (Conversion.widen v),
          if (snapshot.best.sub tieWindow).lessOrEqual v then tied.add (Conversion.widen v)
          else tied,
          if (snapshot.best.sub tieWindow).lessOrEqual v then n + 1 else n))
        (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0)).2.1
      (snapshot.values.toList.foldl (fun (x : Binary64 × Binary64 × Nat) (v : Binary32) =>
        match x with
        | (all, tied, n) => (all.add (Conversion.widen v),
          if (snapshot.best.sub tieWindow).lessOrEqual v then tied.add (Conversion.widen v)
          else tied,
          if (snapshot.best.sub tieWindow).lessOrEqual v then n + 1 else n))
        (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0)).2.2
      count.word := rfl

/-- The contract of the executed tie-window mean. For at most eight finite action
values of magnitude at most 8000, the executed nominal policy mean is finite and lies
between `greedyMean` less `meanSlack` and `greedyMean` plus `meanRadius`. The lower
side carries the tie window: the greedy part averages every action within the window
of the maximum, so it can fall below the maximum by the window and by the rounding of
its threshold. -/
theorem expected_sandwich (snapshot : PolicySnapshot count) (small : count.word.toNat ≤ 8)
    (bounded : ∀ action, (snapshot.values.get action).Finite ∧
      |numerical32 (snapshot.values.get action)| ≤ 8000) :
    snapshot.expected.Finite ∧
      greedyMean snapshot - meanSlack ≤ numerical32 snapshot.expected ∧
      numerical32 snapshot.expected ≤ greedyMean snapshot + meanRadius := by
  have wordsBounded : ∀ word ∈ snapshot.values.toList,
      word.Finite ∧ |numerical32 word| ≤ 8000 := by
    intro word inside
    obtain ⟨action, rfl⟩ := (snapshot_member snapshot word).mp inside
    exact bounded action
  have length : snapshot.values.toList.length = count.word.toNat := Vector.length_toList
  have greatest := best_spec snapshot fun action => (bounded action).1
  obtain ⟨top, topSame⟩ := greatest.1
  have bestFinite : snapshot.best.Finite := topSame ▸ (bounded top).1
  have bestSize : |numerical32 snapshot.best| ≤ 8000 := topSame ▸ (bounded top).2
  have least := least_spec snapshot fun action => (bounded action).1
  obtain ⟨bottom, bottomSame⟩ := least.1
  have tieFinite : tieWindow.Finite := by decide
  have tieValue : numerical32 tieWindow = 8796093 * (2 : ℚ) ^ (-43 : Int) := by
    change (1 : ℚ) * 8796093 * (2 : ℚ) ^ (-43 : Int) = _
    ring
  have tieLower : 0 ≤ numerical32 tieWindow := by rw [tieValue]; norm_num
  have tieUpper : numerical32 tieWindow ≤ 1 / 524288 := by rw [tieValue]; norm_num
  have bestBounds := abs_le.mp bestSize
  have difference : |numerical32 snapshot.best - numerical32 tieWindow| ≤ 8192 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have threshold := binary32_rounded_sub_wide snapshot.best tieWindow bestFinite tieFinite
    (by linarith)
  have thresholdError := binary32_sub_sum_error snapshot.best tieWindow bestFinite tieFinite
    threshold.1 difference
  have thresholdUpper : numerical32 (snapshot.best.sub tieWindow) ≤ numerical32 snapshot.best :=
    Rounded.mono threshold.2 (binary32_rounded_exact _ bestFinite) (by linarith)
  have thresholdLower : numerical32 snapshot.best - 1 / 524288 - 1 / 2048 ≤
      numerical32 (snapshot.best.sub tieWindow) := by
    linarith [(abs_le.mp thresholdError).1]
  have zeroFinite : (Binary64.ofUInt64 0).Finite := by decide
  have zeroValue : numerical64 (Binary64.ofUInt64 0) = 0 := by
    have value := numerical64_ofUInt64 0 (by decide)
    exact_mod_cast value
  have spec := totals_spec (snapshot.best.sub tieWindow) snapshot.values.toList wordsBounded
    (Binary64.ofUInt64 0) (Binary64.ofUInt64 0) 0 0 0 0 (by omega) zeroFinite zeroFinite
    (by rw [zeroValue]; norm_num) (by rw [zeroValue]; norm_num) (by norm_num) (by norm_num)
  obtain ⟨allFinite, tiedFinite, allClose, tiedClose, tiedCount⟩ := spec
  rw [Nat.zero_add] at allClose tiedClose tiedCount
  rw [zero_add] at allClose tiedClose
  have few : ((snapshot.values.toList.length : Nat) : ℚ) ≤ 8 := by
    rw [length]
    exact_mod_cast small
  have radius : (0 : ℚ) ≤ wideRadius := by unfold wideRadius; norm_num
  have allNear := le_trans allClose (mul_le_mul_of_nonneg_right few radius)
  have tiedNear := le_trans tiedClose (mul_le_mul_of_nonneg_right few radius)
  have bestMember : snapshot.best ∈ snapshot.values.toList :=
    (snapshot_member snapshot _).mpr ⟨top, topSame⟩
  have bestTied : snapshot.best ∈ snapshot.values.toList.filter fun word =>
      (snapshot.best.sub tieWindow).lessOrEqual word := by
    refine List.mem_filter.mpr ⟨bestMember, ?_⟩
    rw [finite_lessOrEqual _ _ threshold.1 bestFinite]
    exact decide_eq_true thresholdUpper
  have tiedPositive : 1 ≤ (snapshot.values.toList.filter fun word =>
      (snapshot.best.sub tieWindow).lessOrEqual word).length := List.length_pos_of_mem bestTied
  have tiedSmall : (snapshot.values.toList.filter fun word =>
      (snapshot.best.sub tieWindow).lessOrEqual word).length ≤ 8 :=
    le_trans (List.length_filter_le _ _) (by rw [length]; exact small)
  have wordRange : ∀ word ∈ snapshot.values.toList,
      numerical32 (snapshot.values.get bottom) ≤ numerical32 word ∧
        numerical32 word ≤ numerical32 snapshot.best := by
    intro word inside
    obtain ⟨action, rfl⟩ := (snapshot_member snapshot word).mp inside
    have low := least.2 action
    rw [bottomSame] at low
    exact ⟨low, greatest.2 action⟩
  have tiedRange : ∀ word ∈ snapshot.values.toList.filter (fun word =>
      (snapshot.best.sub tieWindow).lessOrEqual word),
      max (numerical32 (snapshot.values.get bottom))
          (numerical32 (snapshot.best.sub tieWindow)) ≤ numerical32 word ∧
        numerical32 word ≤ numerical32 snapshot.best := by
    intro word inside
    have parts := List.mem_filter.mp inside
    have range := wordRange word parts.1
    have above := parts.2
    rw [finite_lessOrEqual _ _ threshold.1 (wordsBounded word parts.1).1] at above
    exact ⟨max_le range.1 (of_decide_eq_true above), range.2⟩
  have allSums := sum_between snapshot.values.toList _ _ wordRange
  have tiedSums := sum_between _ _ _ tiedRange
  have actionsPositive : (0 : ℚ) < (count.word.toNat : ℚ) := by
    exact_mod_cast count.positive
  have tiedCast : (0 : ℚ) < ((snapshot.values.toList.filter fun word =>
      (snapshot.best.sub tieWindow).lessOrEqual word).length : ℚ) := by
    exact_mod_cast tiedPositive
  rw [length] at allSums
  have allBetween : numerical32 (snapshot.values.get bottom) ≤
        (snapshot.values.toList.map numerical32).sum / (count.word.toNat : ℚ) ∧
      (snapshot.values.toList.map numerical32).sum / (count.word.toNat : ℚ) ≤
        numerical32 snapshot.best :=
    ⟨(le_div_iff₀ actionsPositive).mpr (by linarith [allSums.1]),
      (div_le_iff₀ actionsPositive).mpr (by linarith [allSums.2])⟩
  have tiedBetween : max (numerical32 (snapshot.values.get bottom))
        (numerical32 (snapshot.best.sub tieWindow)) ≤
        ((snapshot.values.toList.filter fun word =>
          (snapshot.best.sub tieWindow).lessOrEqual word).map numerical32).sum /
          ((snapshot.values.toList.filter fun word =>
            (snapshot.best.sub tieWindow).lessOrEqual word).length : ℚ) ∧
      ((snapshot.values.toList.filter fun word =>
          (snapshot.best.sub tieWindow).lessOrEqual word).map numerical32).sum /
          ((snapshot.values.toList.filter fun word =>
            (snapshot.best.sub tieWindow).lessOrEqual word).length : ℚ) ≤
        numerical32 snapshot.best :=
    ⟨(le_div_iff₀ tiedCast).mpr (by linarith [tiedSums.1]),
      (div_le_iff₀ tiedCast).mpr (by linarith [tiedSums.2])⟩
  have rateBounds := CurrentModels.interval_numeric SwiftTd.exploreRange snapshot.epsilon
  have rateLower : numerical32 SwiftTd.exploreRange.lower = 0 := by decide
  have rateUpper : numerical32 SwiftTd.exploreRange.upper = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  rw [rateLower, rateUpper] at rateBounds
  have rateFinite : snapshot.epsilon.value.Finite := snapshot.epsilon.legal.1
  have rateWide := numerical_widen_exact snapshot.epsilon.value rateFinite
  have key : ∀ (all tied : Binary64) (tiedWords : Nat), all.Finite → tied.Finite →
      |numerical64 all - (snapshot.values.toList.map numerical32).sum| ≤ 8 * wideRadius →
      |numerical64 tied - ((snapshot.values.toList.filter fun word =>
        (snapshot.best.sub tieWindow).lessOrEqual word).map numerical32).sum| ≤
          8 * wideRadius →
      tiedWords = (snapshot.values.toList.filter fun word =>
        (snapshot.best.sub tieWindow).lessOrEqual word).length →
      (meanWord (snapshot.values.toList.foldl (fun lo value : Binary32 =>
          if value.less lo then value else lo) (snapshot.values.get (firstAction count)))
        snapshot.best (Conversion.widen snapshot.epsilon.value) all tied tiedWords
        count.word).Finite ∧
      |numerical32 (meanWord (snapshot.values.toList.foldl (fun lo value : Binary32 =>
          if value.less lo then value else lo) (snapshot.values.get (firstAction count)))
        snapshot.best (Conversion.widen snapshot.epsilon.value) all tied tiedWords
        count.word) -
        ((1 - numerical32 snapshot.epsilon.value) *
          (((snapshot.values.toList.filter fun word =>
            (snapshot.best.sub tieWindow).lessOrEqual word).map numerical32).sum /
            ((snapshot.values.toList.filter fun word =>
              (snapshot.best.sub tieWindow).lessOrEqual word).length : ℚ)) +
          numerical32 snapshot.epsilon.value *
            ((snapshot.values.toList.map numerical32).sum / (count.word.toNat : ℚ)))| ≤
        meanRadius := by
    intro all tied tiedWords allFinite tiedFinite allNear tiedNear same
    subst same
    have result := meanWord_spec
      (snapshot.values.toList.foldl (fun lo value : Binary32 =>
        if value.less lo then value else lo) (snapshot.values.get (firstAction count)))
      snapshot.best (Conversion.widen snapshot.epsilon.value) all tied
      (snapshot.values.toList.filter fun word =>
        (snapshot.best.sub tieWindow).lessOrEqual word).length count.word
      (snapshot.values.toList.map numerical32).sum
      ((snapshot.values.toList.filter fun word =>
        (snapshot.best.sub tieWindow).lessOrEqual word).map numerical32).sum
      (bottomSame ▸ (bounded bottom).1) bestFinite (bottomSame ▸ (bounded bottom).2) bestSize
      (Conversion.widen_finite _ rateFinite) (by rw [rateWide]; exact rateBounds) allFinite
      tiedFinite allNear tiedNear tiedPositive tiedSmall count.positive small
      (by rw [bottomSame]; exact ⟨le_trans (le_max_left _ _) tiedBetween.1, tiedBetween.2⟩)
      (by rw [bottomSame]; exact allBetween)
    rw [rateWide] at result
    exact result
  have mean := key _ _ _ allFinite tiedFinite allNear tiedNear tiedCount
  rw [expected_eq]
  refine ⟨mean.1, ?_, ?_⟩
  · have near := (abs_le.mp mean.2).1
    have tiedLow := le_trans (le_max_right _ _) tiedBetween.1
    have complement : 0 ≤ 1 - numerical32 snapshot.epsilon.value := by linarith [rateBounds.2]
    have scaled := mul_le_mul_of_nonneg_left tiedLow complement
    have slack : (1 - numerical32 snapshot.epsilon.value) *
        (numerical32 snapshot.best - 1 / 524288 - 1 / 2048) ≤
        (1 - numerical32 snapshot.epsilon.value) *
          numerical32 (snapshot.best.sub tieWindow) :=
      mul_le_mul_of_nonneg_left thresholdLower complement
    unfold greedyMean meanSlack
    nlinarith [rateBounds.1]
  · have near := (abs_le.mp mean.2).2
    have complement : 0 ≤ 1 - numerical32 snapshot.epsilon.value := by linarith [rateBounds.2]
    have scaled := mul_le_mul_of_nonneg_left tiedBetween.2 complement
    unfold greedyMean
    linarith

end AcornVerif.CurrentPolicyMean
