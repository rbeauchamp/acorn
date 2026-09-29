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
Artificial Intelligence 324 (2023), 104001, section 2, equation (4), p. 8,
https://arxiv.org/pdf/2202.03466v4.
Acorn's PAR-12 adaptation ranks units whose signed Demon-0 weight is positive,
with one minimum-unit representative per exact score block. The weight word of
a selected unit becomes its attainment bonus, standing in for the source's bonus
weight, "one of its largest values". The bonus is held while the unit stays
ranked, and objective identity is the unit alone, so refresh never discards the
knowledge of a retained unit. A slot indicator can be activated by any hash
alias; it is not unit activation.
-/
namespace Acorn.Features

/-- A held attainment bonus: a positive Demon-0 weight word, fixed when its unit
is selected. A nonpositive weight predicts no additional reward to attain. -/
structure Bonus where
  /-- Selection-time weight word within the Demon-0 prediction range. -/
  weight : Prediction .g99
  /-- The signed word is strictly positive. -/
  positive : 0 < weight.value.key

/-- The exact held bonus word. -/
def Bonus.value (bonus : Bonus) : Binary32 := bonus.weight.value

/-- Every held bonus is finite and strictly positive. -/
theorem Bonus.finite_positive (bonus : Bonus) : bonus.value.Finite ∧ 0 < bonus.value.key :=
  ⟨bonus.weight.legal.1, bonus.positive⟩

/-- A prediction word is a bonus exactly when it is positive. -/
def Bonus.ofWeight (weight : Prediction .g99) : Option Bonus :=
  letI := Binary32.positiveDecidable weight.value
  if positive : 0 < weight.value.key then some ⟨weight, positive⟩ else none

/-- Durable bonus admission is identity or refusal, including refusal of either zero. -/
def Bonus.admit (raw : Binary32) : Option Bonus :=
  (Prediction.admit .g99 raw).bind Bonus.ofWeight

/-- Every held bonus round-trips through its exact word. -/
theorem Bonus.admit_self (bonus : Bonus) : Bonus.admit bonus.value = some bonus := by
  have admitted : Prediction.admit .g99 bonus.value = some bonus.weight :=
    Bounded32.admit_self bonus.weight
  have positive : Bonus.ofWeight bonus.weight = some bonus := dite_eq_left bonus.positive
  rw [Bonus.admit, admitted, Option.bind_some, positive]

/-- Assignment identity binds a bank unit; its held bonus is payload, not identity.
The feature slot is derived from the receiving seed and dimension, never an
independent field. -/
inductive Assignment (config : Config) where
  /-- Neutral fallback before differentiated candidates exist. -/
  | neutral
  /-- Selected unit with the positive bonus held since its selection. -/
  | selected (unit : Fin config.units.count) (bonus : Bonus)

instance (config : Config) : Provenance (Assignment config) := ⟨none⟩

/-- Objective identity: the selected unit, or none for the neutral fallback. -/
def Assignment.identity {config : Config} : Assignment config → Option (Fin config.units.count)
  | .neutral => none
  | .selected unit _ => some unit

/-- Identity comparison reads the selected unit only, never the bonus word. -/
def Assignment.same {config : Config} : Assignment config → Assignment config → Bool
  | .neutral, .neutral => true
  | .selected unit _, .selected other _ => unit == other
  | _, _ => false

/-- Identity comparison is equality of selected units. -/
theorem Assignment.same_iff {config : Config} (left right : Assignment config) :
    left.same right = true ↔ left.identity = right.identity := by
  cases left <;> cases right <;> simp [Assignment.same, Assignment.identity]

/-- Every assignment has its own identity. -/
theorem Assignment.same_refl {config : Config} (assignment : Assignment config) :
    assignment.same assignment = true := (Assignment.same_iff _ _).mpr rfl

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

/-- The exact held bonus word; neutral uses positive zero. -/
def Assignment.bonus {config : Config} : Assignment config → Binary32
  | .neutral => .zero
  | .selected _ bonus => bonus.value

/-- Equation (4) with an indicator feature: the attained stopping value adds the
held bonus to the estimate, and an unattained feature leaves the estimate unchanged. -/
def Assignment.stoppingValue {config : Config} (assignment : Assignment config)
    (estimate : Binary32) (attained : Bool) : Binary32 :=
  if attained then estimate.add assignment.bonus else estimate

/-- Four durable words of one assignment. -/
structure AssignmentWords where
  /-- Neutral or selected tag. -/
  tag : UInt32
  /-- Bank unit. -/
  unit : UInt32
  /-- Receiving feature slot. -/
  feature : UInt32
  /-- Held bonus bits. -/
  bonus : UInt32
  deriving DecidableEq

/-- Exact word image, including canonical neutral sentinels. -/
def Assignment.wordsUsing {dimension : Dimension} {config : Config}
    (slot : Fin config.units.count → FeatIdx dimension) : Assignment config → AssignmentWords
  | .neutral => ⟨0, 0, 0, 0⟩
  | .selected unit bonus =>
    ⟨1, unit.val.toUInt32, (slot unit).val.toUInt32, bonus.value.bits⟩

/-- Identity-or-refusal restoration. Present weights are deliberately not read:
the bonus belongs to the selection time, not the restore time. -/
def Assignment.admitUsing (dimension : Dimension) (config : Config)
    (slot : Fin config.units.count → FeatIdx dimension) (raw : AssignmentWords) :
    Option (Assignment config) :=
  if raw.tag == 0 then
    if raw.unit == 0 && raw.feature == 0 && raw.bonus == 0 then some .neutral else none
  else if raw.tag == 1 then
    if h : raw.unit.toNat < config.units.count then
      let unit : Fin config.units.count := ⟨raw.unit.toNat, h⟩
      if (slot unit).val == raw.feature.toNat then
        (Bonus.admit ⟨raw.bonus⟩).map (Assignment.selected unit)
      else none
    else none
  else none

/-- Every bank-relative objective round-trips through its actual durable words.
The held bonus word is retained without reranking. -/
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
    exact congrArg (fun result : Option Bonus => result.map (Assignment.selected unit))
      (Bonus.admit_self bonus)

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

/-- A positive legal Demon-0 weight is a legal prediction word without projection. -/
theorem weight_bonus_legal (weight : Weight (.discounted .g99)) (positive : 0 < weight.value.key) :
    Discount.g99.predictionRange.Contains weight.value := by
  have legal := weight_legal weight
  change weight.value.Finite ∧
    -(Discount.g99.horizon.magnitude : Int) ≤ weight.value.key ∧
    weight.value.key ≤ (Discount.g99.horizon.magnitude : Int) at legal
  change weight.value.Finite ∧ 0 ≤ weight.value.key ∧
    weight.value.key ≤ (Discount.g99.horizon.magnitude : Int)
  exact ⟨legal.1, Int.le_of_lt positive, legal.2.2⟩

/-- A positive score candidate with a receiver-bound unit identity. -/
structure Candidate (config : Config) where
  /-- Bank unit. -/
  unit : Fin config.units.count
  /-- Exact positive weight word, held as the bonus if this unit is selected. -/
  score : Bonus

/-- The current weight enters ranking exactly when its signed word is positive. -/
def candidateOfWeight {dimension : Dimension} (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) (unit : Fin config.units.count) :
    Option (Candidate config) :=
  let weight := weights.get (unitFeature dimension config unit)
  letI := Binary32.positiveDecidable weight.value
  if positive : 0 < weight.value.key then
    some ⟨unit, ⟨⟨weight.value, weight_bonus_legal weight positive⟩, positive⟩⟩
  else none

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

/-- The current top score blocks, each represented by its minimum unit. -/
def rankedCandidates (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) : List (Candidate config) :=
  ranked Acorn.FeatureConstants.skillCount
    ((List.finRange config.units.count).filterMap (candidateOfWeight config weights))

/-- Whether an objective is the given unit. -/
def Assignment.holds {config : Config} (unit : Fin config.units.count) :
    Assignment config → Bool
  | .neutral => false
  | .selected held _ => held == unit

/-- A held objective is retained exactly when its unit is still ranked. -/
def Assignment.retained {config : Config} (chosen : List (Candidate config))
    (assignment : Assignment config) : Bool :=
  chosen.any fun candidate => assignment.holds candidate.unit

/-- Ranked candidates whose unit no slot holds, in rank order. -/
def entrants {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) : List (Candidate config) :=
  chosen.filter fun candidate =>
    (List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
      !held[slot.val].holds candidate.unit

/-- Unretained slots before this one; each takes an earlier entrant. -/
def openBefore {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount) : Nat :=
  ((List.finRange Acorn.FeatureConstants.skillCount).filter fun other =>
    decide (other.val < slot.val) && !held[other.val].retained chosen).length

/-- Slot-stable ranking. A slot whose unit is still ranked keeps its exact objective
and held bonus; every other slot takes the next entrant in slot order, or neutral. -/
def rankAssignments (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    Vector (Assignment config) Acorn.FeatureConstants.skillCount :=
  let chosen := rankedCandidates dimension config weights
  let arriving := entrants held chosen
  Vector.ofFn fun slot =>
    if held[slot.val].retained chosen then held[slot.val]
    else match arriving[openBefore held chosen slot]? with
      | none => .neutral
      | some candidate => .selected candidate.unit candidate.score

/-- A slot whose unit is still ranked receives exactly its held objective. -/
theorem rankAssignments_retained (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (retained : held[slot.val].retained (rankedCandidates dimension config weights) = true) :
    (rankAssignments dimension config weights held)[slot.val] = held[slot.val] := by
  simp [rankAssignments, retained]

/-- A target with its slot's identity is that slot's exact held objective: an
entrant is never a unit some slot already holds. -/
theorem rankAssignments_same (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (same : held[slot.val].same (rankAssignments dimension config weights held)[slot.val] = true) :
    (rankAssignments dimension config weights held)[slot.val] = held[slot.val] := by
  revert same
  simp only [rankAssignments, Vector.getElem_ofFn]
  split
  · intro _
    rfl
  · split
    · intro same
      cases current : held[slot.val] with
      | neutral => rfl
      | selected unit bonus => simp [current, Assignment.same] at same
    · rename_i candidate found
      intro same
      exfalso
      have fresh := List.all_eq_true.mp (List.mem_filter.mp (List.mem_of_getElem? found)).2
        slot (List.mem_finRange slot)
      cases current : held[slot.val] with
      | neutral => simp [current, Assignment.same] at same
      | selected unit bonus =>
        simp only [current, Assignment.holds, Bool.not_eq_true'] at fresh
        simp only [current, Assignment.same] at same
        simp_all

end Acorn.Features
