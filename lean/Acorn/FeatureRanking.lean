/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.Features
import Acorn.Provenance

/-!
# Learned assignment identity and score-block ranking

Sutton, Machado, Holland, Szepesvari, Timbers, Tanner and White,
*Reward-Respecting Subtasks for Model-Based Reinforcement Learning*,
Artificial Intelligence 324 (2023), 104001, section 2, equation (4),
https://arxiv.org/pdf/2202.03466v4.
Acorn's PAR-12 adaptation uses the magnitude of Demon 0's stored weight as
attainment bonus, with one minimum-unit representative per exact score block.
A slot indicator can be activated by any hash alias; it is not unit activation.
-/
namespace Acorn.Features

/-- Assignment identity binds a bank unit and its stored objective. The feature
slot is derived from the receiving seed and dimension, never an independent field. -/
inductive Assignment (config : Config) where
  /-- Neutral fallback before differentiated candidates exist. -/
  | neutral
  /-- Selected unit with a finite nonnegative Demon-0-horizon bonus. -/
  | selected (unit : Fin config.units.count) (bonus : Prediction .g99)

instance (config : Config) : Provenance (Assignment config) := ⟨none⟩

/-- Exact objective identity, including the sign bit of a stored zero bonus. -/
def Assignment.same {config : Config} : Assignment config → Assignment config → Bool
  | .neutral, .neutral => true
  | .selected unit bonus, .selected other otherBonus =>
    unit == other && bonus.value.bits == otherBonus.value.bits
  | _, _ => false

/-- Identity comparison is equality of the complete stored assignment. -/
theorem Assignment.same_iff {config : Config} (left right : Assignment config) :
    left.same right = true ↔ left = right := by
  cases left with
  | neutral => cases right <;> simp [Assignment.same]
  | selected unit bonus =>
    cases right with
    | neutral => simp [Assignment.same]
    | selected other otherBonus =>
      cases bonus with | mk value legal =>
        cases otherBonus with | mk otherValue otherLegal =>
          cases value; cases otherValue
          simp [Assignment.same, Binary32.mk.injEq]

/-- Optional feature lookup cannot disagree with the selected unit. -/
def Assignment.feature (dimension : Dimension) {config : Config} : Assignment config →
    Option (FeatIdx dimension)
  | .neutral => none
  | .selected unit _ => some (unitFeature dimension config unit)

/-- The Boolean hashed-slot potential, preserving collision semantics. -/
def Assignment.potential {dimension : Dimension} {config : Config}
    (assignment : Assignment config) (active : SwiftTd.ActiveSet dimension) : Bool :=
  match assignment.feature dimension with
  | none => false
  | some feature => decide (feature ∈ active.indices)

/-- The exact stored bonus word; neutral uses positive zero. -/
def Assignment.bonus {config : Config} : Assignment config → Binary32
  | .neutral => .zero
  | .selected _ bonus => bonus.value

/-- Ordered machine stopping-value recipe. -/
def Assignment.stoppingValue {config : Config} (assignment : Assignment config)
    (estimate potential : Binary32) : Binary32 := estimate.add (assignment.bonus.mul potential)

/-- Four durable words of one assignment. -/
structure AssignmentWords where
  /-- Neutral or selected tag. -/
  tag : UInt32
  /-- Bank unit. -/
  unit : UInt32
  /-- Receiving feature slot. -/
  feature : UInt32
  /-- Original bonus bits. -/
  bonus : UInt32
  deriving DecidableEq

/-- Exact word image, including canonical neutral sentinels. -/
def Assignment.wordsUsing {dimension : Dimension} {config : Config}
    (slot : Fin config.units.count → FeatIdx dimension) : Assignment config → AssignmentWords
  | .neutral => ⟨0, 0, 0, 0⟩
  | .selected unit bonus =>
    ⟨1, unit.val.toUInt32, (slot unit).val.toUInt32, bonus.value.bits⟩

/-- Identity-or-refusal restoration. Present weights are deliberately not read:
the bonus belongs to the assignment time, not the restore time. -/
def Assignment.admitUsing (dimension : Dimension) (config : Config)
    (slot : Fin config.units.count → FeatIdx dimension) (raw : AssignmentWords) :
    Option (Assignment config) :=
  if raw.tag == 0 then
    if raw.unit == 0 && raw.feature == 0 && raw.bonus == 0 then some .neutral else none
  else if raw.tag == 1 then
    if h : raw.unit.toNat < config.units.count then
      let unit : Fin config.units.count := ⟨raw.unit.toNat, h⟩
      if (slot unit).val == raw.feature.toNat then do
        let bonus ← Prediction.admit .g99 ⟨raw.bonus⟩
        some (.selected unit bonus)
      else none
    else none
  else none

/-- Every bank-relative objective round-trips through its actual durable words.
The bonus word, including either zero sign, is retained without reranking. -/
theorem Assignment.wordsUsing_roundtrip (dimension : Dimension) {config : Config}
    (slot : Fin config.units.count → FeatIdx dimension) (assignment : Assignment config) :
    Assignment.admitUsing dimension config slot (Assignment.wordsUsing slot assignment) = some assignment := by
  cases assignment with
  | neutral => simp [Assignment.admitUsing, Assignment.wordsUsing]
  | selected unit bonus =>
    have unitBound : unit.val < 2 ^ 32 := by
      have := unit.isLt
      have := config.units.bounded
      omega
    have unitExact : unit.val.toUInt32.toNat = unit.val := Nat.mod_eq_of_lt unitBound
    have slotBound : (slot unit).val < 2 ^ 32 :=
      Nat.lt_trans (slot unit).isLt dimension.wordBound
    have slotExact : (slot unit).val.toUInt32.toNat =
        (slot unit).val := Nat.mod_eq_of_lt slotBound
    have slotCheck : ((slot unit).val ==
        (slot unit).val.toUInt32.toNat) = true := by
      rw [slotExact]
      exact beq_self_eq_true _
    simp only [Assignment.wordsUsing, Assignment.admitUsing,
      show ((1 : UInt32) == 0) = false from rfl, beq_self_eq_true, Bool.false_eq_true,
      ↓reduceIte, unitExact, unit.isLt, ↓reduceDIte, Fin.eta, slotCheck]
    have admitted : Prediction.admit .g99 bonus.value = some bonus := Bounded32.admit_self bonus
    exact congrArg (fun result : Option (Prediction .g99) =>
      result.bind (fun stored => some (Assignment.selected unit stored))) admitted

/-- Canonical assignment words derive their slot from the receiving bank. -/
def Assignment.words (dimension : Dimension) {config : Config} : Assignment config → AssignmentWords :=
  Assignment.wordsUsing (unitFeature dimension config)

/-- Canonical admission binds raw identities to the actual bank slot function. -/
def Assignment.admit (dimension : Dimension) (config : Config) : AssignmentWords → Option (Assignment config) :=
  Assignment.admitUsing dimension config (unitFeature dimension config)

/-- The executing bank codec preserves every legal stored objective exactly. -/
theorem Assignment.words_roundtrip (dimension : Dimension) {config : Config}
    (assignment : Assignment config) :
    Assignment.admit dimension config (assignment.words dimension) = some assignment :=
  Assignment.wordsUsing_roundtrip dimension (unitFeature dimension config) assignment

/-- Magnitude removes only the sign bit, preserving the unsigned magnitude. -/
theorem abs_magnitude (value : Binary32) : value.abs.magnitude = value.magnitude := by
  simp [Binary32.abs, Binary32.magnitude, UInt32.and_assoc]

/-- Absolute-value storage has no sign bit. -/
theorem abs_nonnegative (value : Binary32) : value.abs.negative = false := by
  simp [Binary32.abs, Binary32.negative, UInt32.and_assoc]
  change value.bits &&& (0 : UInt32) = 0
  simp

/-- A legal Demon-0 weight's magnitude is a legal assignment bonus without projection. -/
theorem weight_bonus_legal (weight : Weight (.discounted .g99)) :
    Discount.g99.predictionRange.Contains weight.value.abs := by
  have legal := weight_legal weight
  change weight.value.Finite ∧
    -(Discount.g99.horizon.magnitude : Int) ≤ weight.value.key ∧
    weight.value.key ≤ (Discount.g99.horizon.magnitude : Int) at legal
  change weight.value.abs.Finite ∧ 0 ≤ weight.value.abs.key ∧
    weight.value.abs.key ≤ (Discount.g99.horizon.magnitude : Int)
  have magnitude := abs_magnitude weight.value
  have key : weight.value.abs.key = (weight.value.magnitude : Int) := by
    simp [Binary32.key, abs_nonnegative, magnitude]
  refine ⟨by simpa [Binary32.Finite, magnitude] using legal.1, by rw [key]; omega, ?_⟩
  rw [key]
  cases sign : weight.value.negative <;> simp [Binary32.key, sign] at legal <;> omega

/-- A positive score candidate with a receiver-bound unit identity. -/
structure Candidate (config : Config) where
  /-- Bank unit. -/
  unit : Fin config.units.count
  /-- Exact absolute weight word. -/
  score : Prediction .g99
  /-- Zero scores cannot enter ranking. -/
  positive : 0 < score.value.key

/-- The current weight produces its exact nonzero magnitude or is absent. -/
def candidateOfWeight {dimension : Dimension} (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) (unit : Fin config.units.count) :
    Option (Candidate config) :=
  let weight := weights.get (unitFeature dimension config unit)
  let score : Prediction .g99 := ⟨weight.value.abs, weight_bonus_legal weight⟩
  letI := Binary32.positiveDecidable score.value
  if positive : 0 < score.value.key then some ⟨unit, score, positive⟩ else none

/-- Exact positive score-block key. Positive finite float order is unsigned bit order. -/
def Candidate.key {config : Config} (candidate : Candidate config) : Nat :=
  candidate.score.value.bits.toNat

/-- Better score wins; within a score block the smaller unit wins. -/
def Candidate.Dominates {config : Config} (left right : Candidate config) : Prop :=
  right.key ≤ left.key ∧ (right.key = left.key → left.unit.val ≤ right.unit.val)

instance {config : Config} (left right : Candidate config) : Decidable (left.Dominates right) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Reflexive total ranking relation. -/
theorem Candidate.dominates_refl {config : Config} (candidate : Candidate config) :
    candidate.Dominates candidate := ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩

/-- Ranking dominance composes without any floating arithmetic. -/
theorem Candidate.dominates_trans {config : Config} (a b c : Candidate config)
    (ab : a.Dominates b) (bc : b.Dominates c) : a.Dominates c := by
  unfold Candidate.Dominates at *
  refine ⟨Nat.le_trans bc.1 ab.1, ?_⟩
  intro same
  have sameAB : b.key = a.key := by omega
  have sameBC : c.key = b.key := by omega
  exact Nat.le_trans (ab.2 sameAB) (bc.2 sameBC)

/-- Exactly one of the compared candidates is returned. -/
def Candidate.pick {config : Config} (left right : Candidate config) : Candidate config :=
  if left.Dominates right then left else right

/-- The selected candidate dominates both inputs. -/
theorem Candidate.pick_dominates {config : Config} (left right : Candidate config) :
    (left.pick right).Dominates left ∧ (left.pick right).Dominates right := by
  unfold Candidate.pick
  split
  · exact ⟨left.dominates_refl, ‹left.Dominates right›⟩
  · rename_i h
    refine ⟨?_, right.dominates_refl⟩
    unfold Candidate.Dominates at *
    by_cases same : right.key = left.key
    · have tie : ¬left.unit.val ≤ right.unit.val := fun le => h ⟨by omega, fun _ => le⟩
      exact ⟨by omega, fun _ => by omega⟩
    · have order : left.key < right.key := by
        by_cases order : left.key < right.key
        · exact order
        · exact False.elim (h ⟨by omega, fun equality => False.elim (same equality)⟩)
      exact ⟨by omega, fun equality => by omega⟩

/-- One full scan finds the best remaining score-block representative. -/
def best {config : Config} : List (Candidate config) → Option (Candidate config)
  | [] => none
  | head :: tail => some (tail.foldl Candidate.pick head)

/-- Every scan winner is one of its inputs. -/
theorem fold_pick_mem {config : Config} (items : List (Candidate config)) (start : Candidate config) :
    items.foldl Candidate.pick start ∈ start :: items := by
  induction items generalizing start with
  | nil => simp
  | cons head tail ih =>
    have member := ih (start.pick head)
    rcases List.mem_cons.mp member with same | member
    · change tail.foldl Candidate.pick (start.pick head) ∈ start :: head :: tail
      rw [same]
      unfold Candidate.pick
      split <;> simp
    · simp only [List.foldl_cons]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)

/-- Folded winners retain dominance of every already dominated candidate. -/
theorem fold_pick_dominates {config : Config} (items : List (Candidate config))
    (start target : Candidate config) (before : start.Dominates target) :
    (items.foldl Candidate.pick start).Dominates target := by
  induction items generalizing start with
  | nil => exact before
  | cons head tail ih =>
    exact ih (start.pick head) (Candidate.dominates_trans _ _ _ (Candidate.pick_dominates start head).1 before)

/-- Complete maximum and canonical representative characterization of the executed scan. -/
theorem best_spec {config : Config} (items : List (Candidate config)) (winner : Candidate config)
    (found : best items = some winner) : winner ∈ items ∧
      ∀ candidate ∈ items, winner.Dominates candidate := by
  cases items with
  | nil => simp [best] at found
  | cons head tail =>
    have same : tail.foldl Candidate.pick head = winner := by simpa [best] using found
    subst winner
    clear found
    refine ⟨fold_pick_mem tail head, ?_⟩
    intro candidate member
    induction tail generalizing head with
    | nil => simpa using (show head.Dominates candidate from by
        have : candidate = head := by simpa using member
        subst candidate
        exact head.dominates_refl)
    | cons next tail ih =>
      rcases List.mem_cons.mp member with same | member
      · subst candidate
        exact fold_pick_dominates tail _ _ (Candidate.pick_dominates head next).1
      · rcases List.mem_cons.mp member with same | member
        · subst candidate
          exact fold_pick_dominates tail _ _ (Candidate.pick_dominates head next).2
        · exact ih (head.pick next) (List.mem_cons_of_mem _ member)

/-- Remove the entire chosen block, including every unit/slot collision in it. -/
def withoutBlock {config : Config} (items : List (Candidate config)) (chosen : Candidate config) :
    List (Candidate config) := items.filter (fun candidate => candidate.key != chosen.key)

/-- At most `count` complete score blocks, ordered by repeated maximum selection.
There are at most the fixed skill-count scans, rather than sorting the entire bank. -/
def ranked {config : Config} : Nat → List (Candidate config) → List (Candidate config)
  | 0, _ => []
  | count + 1, items => match best items with
    | none => []
    | some chosen => chosen :: ranked count (withoutBlock items chosen)

/-- Ranking never manufactures a candidate absent from the receiving weights. -/
theorem ranked_subset {config : Config} (count : Nat) (items : List (Candidate config))
    (candidate : Candidate config) (member : candidate ∈ ranked count items) : candidate ∈ items := by
  induction count generalizing items with
  | zero => simp [ranked] at member
  | succ count ih =>
    unfold ranked at member
    split at member
    · simp at member
    · rename_i chosen found
      rcases List.mem_cons.mp member with same | member
      · subst candidate
        exact (best_spec items chosen found).1
      · exact (List.mem_filter.mp (ih _ member)).1

/-- The work/result bound is independent of score ties and bank contents. -/
theorem ranked_length {config : Config} (count : Nat) (items : List (Candidate config)) :
    (ranked count items).length ≤ count := by
  induction count generalizing items with
  | zero => simp [ranked]
  | succ count ih =>
    unfold ranked
    split
    · simp
    · simpa using Nat.succ_le_succ (ih _)

/-- Selected score blocks strictly decrease; ties cannot occupy another slot. -/
theorem ranked_strict {config : Config} (count : Nat) (items : List (Candidate config)) :
    (ranked count items).Pairwise (fun left right => right.key < left.key) := by
  induction count generalizing items with
  | zero => simp [ranked]
  | succ count ih =>
    unfold ranked
    split
    · simp
    · rename_i chosen found
      rw [List.pairwise_cons]
      refine ⟨?_, ih _⟩
      intro candidate member
      have remaining := ranked_subset count (withoutBlock items chosen) candidate member
      have filtered := List.mem_filter.mp remaining
      have distinct : candidate.key ≠ chosen.key := by simpa using filtered.2
      have dominates := (best_spec items chosen found).2 candidate filtered.1
      have bound := dominates.1
      omega

/-- Rank current bank candidates, then fill unoccupied skill slots with neutral identities. -/
def rankAssignments (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    Vector (Assignment config) Acorn.FeatureConstants.skillCount :=
  let candidates := (List.finRange config.units.count).filterMap (candidateOfWeight config weights)
  let chosen := ranked Acorn.FeatureConstants.skillCount candidates
  Vector.ofFn fun index => match chosen[index.val]? with
    | none => .neutral
    | some candidate => .selected candidate.unit candidate.score

end Acorn.Features
