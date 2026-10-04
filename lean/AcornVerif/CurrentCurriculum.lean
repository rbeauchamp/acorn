/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Curriculum
import AcornVerif.CurrentGoals
import Mathlib.Data.Int.CardIntervalMod

/-!
# Executed curriculum targets

`rawStandardCurriculum` places its two reach targets by a hash of the curriculum
seed and never consults the terrain. These theorems state where the targets lie,
for every seed and side.

Each target lies in a fixed square window around the campaign center
(`reach_targets`), and for a side of at least 54 every position of both goal boxes
is inside the campaign box (`goal_box_in_world`); the standard configuration admits
sides from 64. Each single target coordinate takes each value of its window on
`2 ^ 64 / m` or one more of the `2 ^ 64` seeds, where `m` is the window's width
(`coordinate_seed_count`): the seed-to-hash map is a bijection of the 64-bit words
(`hash2_injective`).

The count is over seeds, not a probability: it is a distribution only for a seed
drawn uniformly. It concerns one coordinate; nothing is proved about the joint
distribution of a target's two coordinates or of the two targets. Nothing here
shows that a goal box is enterable or reachable.
-/
namespace AcornVerif.CurrentCurriculum
open Acorn Acorn.Host
open AcornVerif.CurrentGoals

/-! ## The seed hash is a bijection -/

/-- The finalizer's first xor-shift loses no word. -/
theorem shift30_injective (left right : UInt64)
    (h : left ^^^ (left >>> 30) = right ^^^ (right >>> 30)) : left = right := by
  apply UInt64.toBitVec_inj.mp
  apply Word.xor_shiftRight_injective (shift := 30) (by decide)
  have bits := congrArg UInt64.toBitVec h
  change left.toBitVec ^^^ (left.toBitVec >>> 30) =
    right.toBitVec ^^^ (right.toBitVec >>> 30) at bits
  exact bits

/-- The finalizer's second xor-shift loses no word. -/
theorem shift27_injective (left right : UInt64)
    (h : left ^^^ (left >>> 27) = right ^^^ (right >>> 27)) : left = right := by
  apply UInt64.toBitVec_inj.mp
  apply Word.xor_shiftRight_injective (shift := 27) (by decide)
  have bits := congrArg UInt64.toBitVec h
  change left.toBitVec ^^^ (left.toBitVec >>> 27) =
    right.toBitVec ^^^ (right.toBitVec >>> 27) at bits
  exact bits

/-- The finalizer's last xor-shift loses no word. -/
theorem shift31_injective (left right : UInt64)
    (h : left ^^^ (left >>> 31) = right ^^^ (right >>> 31)) : left = right := by
  apply UInt64.toBitVec_inj.mp
  apply Word.xor_shiftRight_injective (shift := 31) (by decide)
  have bits := congrArg UInt64.toBitVec h
  change left.toBitVec ^^^ (left.toBitVec >>> 31) =
    right.toBitVec ^^^ (right.toBitVec >>> 31) at bits
  exact bits

/-- The SplitMix finalizer is injective: each xor-shift and each odd multiplier is.
The multipliers' inverses modulo 2^64 are the witnesses. -/
theorem mixFinal_injective (left right : UInt64) (h : Rng.mixFinal left = Rng.mixFinal right) :
    left = right := by
  have second := shift31_injective _ _ h
  have firstMixed := Word.multiplier_injective 0x94d049bb133111eb 0x319642b2d24d8ec3
    (by decide) _ _ second
  have first := shift27_injective _ _ firstMixed
  have mixed := Word.multiplier_injective 0xbf58476d1ce4e5b9 0x96de1b173f119089
    (by decide) _ _ first
  exact shift30_injective _ _ mixed

/-- The incrementing mixer is injective on the 64-bit words. -/
theorem mix64_injective (left right : UInt64) (h : Rng.mix64 left = Rng.mix64 right) :
    left = right :=
  (UInt64.add_left_inj Rng.increment).mp (mixFinal_injective _ _ h)

/-- For a fixed second word and salt, the coordinate hash is injective in its first
word, hence a bijection of the 64-bit words. -/
theorem hash2_injective (second salt left right : UInt64)
    (h : Rng.hash2 left second salt = Rng.hash2 right second salt) : left = right := by
  have outer := mix64_injective _ _ h
  have inner := mix64_injective _ _ outer
  have first := mix64_injective _ _ (Word.xor_word_injective _ _ _ inner)
  rw [UInt64.xor_comm (salt ^^^ Rng.increment) left,
    UInt64.xor_comm (salt ^^^ Rng.increment) right] at first
  exact Word.xor_word_injective _ _ _ first

/-- Each residue of the seed hash modulo `modulus` is taken on `2 ^ 64 / modulus` seeds,
or one more for the low residues. The finite set is a specification, not an enumeration. -/
theorem draw_seed_count (second salt : UInt64) (modulus draw : ℕ) (positive : 0 < modulus)
    (small : modulus < 2 ^ 64) (inside : draw < modulus) :
    ((Finset.range (2 ^ 64)).filter (fun seed =>
      (Rng.hash2 seed.toUInt64 second salt % modulus.toUInt64).toNat = draw)).card =
      2 ^ 64 / modulus + if draw < 2 ^ 64 % modulus then 1 else 0 := by
  have width : modulus.toUInt64.toNat = modulus := UInt64.toNat_ofNat_of_lt' small
  have residue (seed : ℕ) : (Rng.hash2 seed.toUInt64 second salt % modulus.toUInt64).toNat =
      (Rng.hash2 seed.toUInt64 second salt).toNat % modulus := by
    rw [UInt64.toNat_mod, width]
  have injective : ∀ a ∈ Finset.range (2 ^ 64), ∀ b ∈ Finset.range (2 ^ 64),
      (Rng.hash2 a.toUInt64 second salt).toNat = (Rng.hash2 b.toUInt64 second salt).toNat →
        a = b := by
    intro a ha b hb same
    have words := congrArg UInt64.toNat
      (hash2_injective second salt _ _ (UInt64.toNat_inj.mp same))
    rwa [show a.toUInt64 = UInt64.ofNat a from rfl, show b.toUInt64 = UInt64.ofNat b from rfl,
      UInt64.toNat_ofNat_of_lt' (Finset.mem_range.mp ha),
      UInt64.toNat_ofNat_of_lt' (Finset.mem_range.mp hb)] at words
  have surjective := Finset.surj_on_of_inj_on_of_card_le
    (s := Finset.range (2 ^ 64)) (t := Finset.range (2 ^ 64))
    (fun seed _ => (Rng.hash2 seed.toUInt64 second salt).toNat)
    (fun seed _ => Finset.mem_range.mpr (UInt64.toNat_lt _))
    (fun a b ha hb same => injective a ha b hb same) (le_refl _)
  have count : ((Finset.range (2 ^ 64)).filter (fun word => Nat.ModEq modulus word draw)).card =
      2 ^ 64 / modulus + if draw < 2 ^ 64 % modulus then 1 else 0 := by
    rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ positive,
      Nat.mod_eq_of_lt inside]
  rw [← count]
  apply Finset.card_bij (fun seed _ => (Rng.hash2 seed.toUInt64 second salt).toNat)
  · intro seed member
    rw [Finset.mem_filter] at member ⊢
    refine ⟨Finset.mem_range.mpr (UInt64.toNat_lt _), ?_⟩
    have drawn := member.2
    rw [residue] at drawn
    unfold Nat.ModEq
    rw [drawn, Nat.mod_eq_of_lt inside]
  · intro a ha b hb same
    exact injective a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 same
  · intro word member
    rw [Finset.mem_filter] at member
    obtain ⟨seed, bounded, rfl⟩ := surjective word member.1
    refine ⟨seed, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨bounded, ?_⟩
    have congruent := member.2
    unfold Nat.ModEq at congruent
    rw [Nat.mod_eq_of_lt inside] at congruent
    rw [residue]
    exact congruent

/-! ## Target windows -/

/-- A curriculum coordinate is the center, plus a hash draw below twice the radius,
minus the radius. -/
theorem curriculumCoordinate_val (side : Coordinate) (seed tag : UInt64) (radius : Fin 121)
    (positive : 0 < radius.val) :
    (curriculumCoordinate side seed tag radius positive).val =
      side.val.tdiv 2 +
        ((Rng.hash2 seed tag 0xabcd % (2 * radius.val).toUInt64).toNat : Int) - radius.val :=
  rfl

/-- The modulus word of a curriculum radius is exactly twice the radius. -/
theorem radius_modulus (radius : Fin 121) : (2 * radius.val).toUInt64.toNat = 2 * radius.val :=
  UInt64.toNat_ofNat_of_lt' (show 2 * radius.val < 2 ^ 64 by have := radius.isLt; omega)

/-- Every curriculum coordinate lies in the window of its radius around the center. -/
theorem curriculumCoordinate_window (side : Coordinate) (seed tag : UInt64) (radius : Fin 121)
    (positive : 0 < radius.val) :
    side.val.tdiv 2 - radius.val ≤ (curriculumCoordinate side seed tag radius positive).val ∧
      (curriculumCoordinate side seed tag radius positive).val < side.val.tdiv 2 + radius.val := by
  have draw : (Rng.hash2 seed tag 0xabcd % (2 * radius.val).toUInt64).toNat < 2 * radius.val := by
    rw [UInt64.toNat_mod, radius_modulus]
    exact Nat.mod_lt _ (by omega)
  rw [curriculumCoordinate_val]
  omega

/-- Single-coordinate uniformity over seeds. For a fixed tag and radius, each value of
the window is the coordinate on `2 ^ 64 / (2 r)` of the `2 ^ 64` seeds, or one more for
the low offsets: no two values' seed counts differ by more than one. -/
theorem coordinate_seed_count (side : Coordinate) (tag : UInt64) (radius : Fin 121)
    (positive : 0 < radius.val) (offset : ℕ) (inside : offset < 2 * radius.val) :
    ((Finset.range (2 ^ 64)).filter (fun seed =>
      (curriculumCoordinate side seed.toUInt64 tag radius positive).val =
        side.val.tdiv 2 - radius.val + offset)).card =
      2 ^ 64 / (2 * radius.val) + if offset < 2 ^ 64 % (2 * radius.val) then 1 else 0 := by
  refine Eq.trans (congrArg Finset.card ?_) (draw_seed_count tag 0xabcd (2 * radius.val)
    offset (by omega) (by have := radius.isLt; omega) inside)
  apply Finset.filter_congr
  intro seed _
  rw [curriculumCoordinate_val]
  omega

/-- The near radius of the standard curriculum, between 12 and 40. -/
def nearRadius (side : Coordinate) : Nat := min 40 (max 12 (side.val.tdiv 12).toNat)

/-- The far radius of the standard curriculum, between 24 and 120. -/
def farRadius (side : Coordinate) : Nat := min 120 (max 24 (side.val.tdiv 6).toNat)

/-- A position in the square window of a radius around the campaign center. -/
def InWindow (side : Coordinate) (radius : Nat) (target : Position) : Prop :=
  side.val.tdiv 2 - radius ≤ target.x.val ∧ target.x.val < side.val.tdiv 2 + radius ∧
    side.val.tdiv 2 - radius ≤ target.y.val ∧ target.y.val < side.val.tdiv 2 + radius

/-- A target whose two coordinates are curriculum coordinates of one radius lies in
that radius's window. -/
theorem target_window (side : Coordinate) (seed first second : UInt64) (radius : Fin 121)
    (positive : 0 < radius.val) :
    InWindow side radius.val ⟨curriculumCoordinate side seed first radius positive,
      curriculumCoordinate side seed second radius positive⟩ :=
  ⟨(curriculumCoordinate_window side seed first radius positive).1,
    (curriculumCoordinate_window side seed first radius positive).2,
    (curriculumCoordinate_window side seed second radius positive).1,
    (curriculumCoordinate_window side seed second radius positive).2⟩

/-- Goals 3 and 7 of the standard curriculum are its reach goals, and for every seed
and side their targets lie in the near and the far window. -/
theorem reach_targets (side : Coordinate) (seed : UInt64) :
    ∃ near far : Position,
      (rawStandardCurriculum side seed)[3]? = some (Goal.reach near, 1) ∧
      (rawStandardCurriculum side seed)[7]? = some (Goal.reach far, 3) ∧
      InWindow side (nearRadius side) near ∧ InWindow side (farRadius side) far :=
  ⟨_, _, rfl, rfl, target_window side seed 1 2 _ _, target_window side seed 3 4 _ _⟩

/-- For a nonnegative side the near window lies inside the far one. -/
theorem nearRadius_le_far (side : Coordinate) (nonnegative : 0 ≤ side.val) :
    nearRadius side ≤ farRadius side := by
  unfold nearRadius farRadius
  rw [Int.tdiv_eq_ediv_of_nonneg nonnegative, Int.tdiv_eq_ediv_of_nonneg nonnegative]
  omega

/-- For a side of at least 54, every position of a goal box whose target lies in a
window no wider than the far one is inside the campaign box. The standard configuration
admits sides from 64 (`WorldConfig.standard_bounds`). -/
theorem goal_box_in_world (side : Coordinate) (large : 54 ≤ side.val) (radius : Nat)
    (narrow : radius ≤ farRadius side) (target position : Position)
    (window : InWindow side radius target) (box : InGoalBox target position) :
    0 ≤ position.x.val ∧ position.x.val < side.val ∧
      0 ≤ position.y.val ∧ position.y.val < side.val := by
  have half : side.val.tdiv 2 = side.val / 2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have sixth : side.val.tdiv 6 = side.val / 6 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  unfold farRadius at narrow
  unfold InWindow at window
  unfold InGoalBox at box
  simp only [FeatureConstants.reachRadius] at box
  rw [sixth] at narrow
  rw [half] at window
  omega

/-- Both reach goals' boxes are inside the campaign box of every standard
configuration, for every seed. -/
theorem standard_goal_boxes (worldSeed : UInt64) (side : Coordinate) (config : WorldConfig)
    (admitted : WorldConfig.standard worldSeed side = .ok config) (target position : Position)
    (window : InWindow side (nearRadius side) target ∨ InWindow side (farRadius side) target)
    (box : InGoalBox target position) :
    0 ≤ position.x.val ∧ position.x.val < side.val ∧
      0 ≤ position.y.val ∧ position.y.val < side.val := by
  have bounds := (WorldConfig.standard_bounds worldSeed side config admitted).2.1
  have large : 54 ≤ side.val := by
    change (64 : Int) ≤ side.val at bounds
    omega
  rcases window with near | far
  · exact goal_box_in_world side large _ (nearRadius_le_far side (by omega)) target position
      near box
  · exact goal_box_in_world side large _ (Nat.le_refl _) target position far box

end AcornVerif.CurrentCurriculum
