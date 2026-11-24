import Acorn.FeatureConstants
import Acorn.Features
import Acorn.Provenance

namespace Acorn.Features

structure Bonus where
  weight : Prediction .g99
  positive : 0 < weight.value.key

def Bonus.value (bonus : Bonus) : Binary32 := bonus.weight.value

theorem Bonus.finite_positive (bonus : Bonus) : bonus.value.Finite ∧ 0 < bonus.value.key :=
  ⟨bonus.weight.legal.1, bonus.positive⟩

def Bonus.ofWeight (weight : Prediction .g99) : Option Bonus :=
  letI := Binary32.positiveDecidable weight.value
  if positive : 0 < weight.value.key then some ⟨weight, positive⟩ else none

def Bonus.max (held current : Bonus) : Bonus :=
  if held.value.bits.toNat < current.value.bits.toNat then current else held

theorem Bonus.le_max (held current : Bonus) :
    held.value.bits.toNat ≤ (held.max current).value.bits.toNat ∧
      current.value.bits.toNat ≤ (held.max current).value.bits.toNat := by
  unfold Bonus.max
  split <;> omega

def Bonus.admit (raw : Binary32) : Option Bonus :=
  (Prediction.admit .g99 raw).bind Bonus.ofWeight

theorem Bonus.admit_self (bonus : Bonus) : Bonus.admit bonus.value = some bonus := by
  have admitted : Prediction.admit .g99 bonus.value = some bonus.weight :=
    Bounded32.admit_self bonus.weight
  have positive : Bonus.ofWeight bonus.weight = some bonus := dite_eq_left bonus.positive
  rw [Bonus.admit, admitted, Option.bind_some, positive]

theorem Bonus.admit_value {raw : Binary32} {bonus : Bonus}
    (admitted : Bonus.admit raw = some bonus) : bonus.value = raw := by
  unfold Bonus.admit at admitted
  cases weight : Prediction.admit .g99 raw with
  | none =>
    rw [weight] at admitted
    simp at admitted
  | some held =>
    rw [weight] at admitted
    change Bonus.ofWeight held = some bonus at admitted
    by_cases positive : 0 < held.value.key
    · rw [show Bonus.ofWeight held = some ⟨held, positive⟩ from dite_eq_left positive] at admitted
      cases admitted
      exact (Bounded32.admit_exact _ _ _ weight).1
    · rw [show Bonus.ofWeight held = none from dite_eq_right positive] at admitted
      contradiction

inductive Assignment (config : Config) where
  | neutral
  | selected (unit : Fin config.units.count) (bonus : Bonus)

instance (config : Config) : Provenance (Assignment config) := ⟨none⟩

def Assignment.identity {config : Config} : Assignment config → Option (Fin config.units.count)
  | .neutral => none
  | .selected unit _ => some unit

def Assignment.same {config : Config} : Assignment config → Assignment config → Bool
  | .neutral, .neutral => true
  | .selected unit _, .selected other _ => unit == other
  | _, _ => false

theorem Assignment.same_iff {config : Config} (left right : Assignment config) :
    left.same right = true ↔ left.identity = right.identity := by
  cases left <;> cases right <;> simp [Assignment.same, Assignment.identity]

theorem Assignment.same_refl {config : Config} (assignment : Assignment config) :
    assignment.same assignment = true := (Assignment.same_iff _ _).mpr rfl

def Assignment.feature (dimension : Dimension) {config : Config} : Assignment config →
    Option (FeatIdx dimension)
  | .neutral => none
  | .selected unit _ => some (unitFeature dimension config unit)

def Assignment.potentialCosted {dimension : Dimension} {config : Config}
    (assignment : Assignment config) (active : SwiftTd.ActiveSet dimension) : Costed Bool :=
  Costed.charge .assignmentPotential
    (match assignment.feature dimension with
    | none => Costed.pure false
    | some feature => Costed.mem feature active.indices dimension.wordBound)

def Assignment.potential {dimension : Dimension} {config : Config}
    (assignment : Assignment config) (active : SwiftTd.ActiveSet dimension) : Bool :=
  (assignment.potentialCosted active).val

theorem Assignment.potential_def {dimension : Dimension} {config : Config}
    (assignment : Assignment config) (active : SwiftTd.ActiveSet dimension) :
    assignment.potential active =
      match assignment.feature dimension with
      | none => false
      | some feature => decide (feature ∈ active.indices) := by
  unfold Assignment.potential Assignment.potentialCosted
  cases assignment.feature dimension <;> rfl

def Assignment.bonus {config : Config} : Assignment config → Binary32
  | .neutral => .zero
  | .selected _ bonus => bonus.value

def Assignment.stoppingValue {config : Config} (assignment : Assignment config)
    (estimate : Binary32) (attained : Bool) : Binary32 :=
  if attained then estimate.add assignment.bonus else estimate

structure AssignmentWords where
  tag : UInt32
  unit : UInt32
  feature : UInt32
  bonus : UInt32
  deriving DecidableEq

def Assignment.wordsUsing {dimension : Dimension} {config : Config}
    (slot : Fin config.units.count → FeatIdx dimension) : Assignment config → AssignmentWords
  | .neutral => ⟨0, 0, 0, 0⟩
  | .selected unit bonus =>
    ⟨1, unit.val.toUInt32, (slot unit).val.toUInt32, bonus.value.bits⟩

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

theorem Assignment.admitUsing_words (dimension : Dimension) {config : Config}
    (slot : Fin config.units.count → FeatIdx dimension) (raw : AssignmentWords)
    (assignment : Assignment config)
    (admitted : Assignment.admitUsing dimension config slot raw = some assignment) :
    raw = Assignment.wordsUsing slot assignment := by
  obtain ⟨tag, unit, feature, bonus⟩ := raw
  unfold Assignment.admitUsing at admitted
  split at admitted
  · rename_i neutral
    split at admitted
    · rename_i blank
      cases admitted
      simp only [beq_iff_eq, Bool.and_eq_true] at neutral blank
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := blank
      subst neutral
      rfl
    · contradiction
  · split at admitted
    · rename_i selected
      split at admitted
      · rename_i bound
        dsimp only at admitted
        split at admitted
        · rename_i slotted
          cases held : Bonus.admit ⟨bonus⟩ with
          | none =>
            rw [held] at admitted
            simp at admitted
          | some value =>
            rw [held] at admitted
            cases admitted
            simp only [beq_iff_eq] at selected slotted
            subst selected
            have unitWord : unit.toNat.toUInt32 = unit :=
              UInt32.toNat_inj.mp (Nat.mod_eq_of_lt unit.toNat_lt)
            have featureWord : (slot ⟨unit.toNat, bound⟩).val.toUInt32 = feature := by
              rw [slotted]
              exact UInt32.toNat_inj.mp (Nat.mod_eq_of_lt feature.toNat_lt)
            have bonusWord : value.value.bits = bonus :=
              congrArg Binary32.bits (Bonus.admit_value held)
            simp only [Assignment.wordsUsing, unitWord, featureWord, bonusWord]
        · contradiction
      · contradiction
    · contradiction

def Assignment.words (dimension : Dimension) {config : Config} : Assignment config → AssignmentWords :=
  Assignment.wordsUsing (unitFeature dimension config)

def Assignment.admit (dimension : Dimension) (config : Config) : AssignmentWords → Option (Assignment config) :=
  Assignment.admitUsing dimension config (unitFeature dimension config)

theorem Assignment.words_roundtrip (dimension : Dimension) {config : Config}
    (assignment : Assignment config) :
    Assignment.admit dimension config (assignment.words dimension) = some assignment :=
  Assignment.wordsUsing_roundtrip dimension (unitFeature dimension config) assignment

theorem Assignment.admit_words (dimension : Dimension) {config : Config} (raw : AssignmentWords)
    (assignment : Assignment config)
    (admitted : Assignment.admit dimension config raw = some assignment) :
    raw = assignment.words dimension :=
  Assignment.admitUsing_words dimension (unitFeature dimension config) raw assignment admitted

theorem weight_bonus_legal (weight : Weight (.discounted .g99)) (positive : 0 < weight.value.key) :
    Discount.g99.predictionRange.Contains weight.value := by
  have legal := weight_legal weight
  change weight.value.Finite ∧
    -(Discount.g99.horizon.magnitude : Int) ≤ weight.value.key ∧
    weight.value.key ≤ (Discount.g99.horizon.magnitude : Int) at legal
  change weight.value.Finite ∧ 0 ≤ weight.value.key ∧
    weight.value.key ≤ (Discount.g99.horizon.magnitude : Int)
  exact ⟨legal.1, Int.le_of_lt positive, legal.2.2⟩

structure Candidate (config : Config) where
  unit : Fin config.units.count
  score : Bonus

def candidateOfWeight {dimension : Dimension} (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) (unit : Fin config.units.count) :
    Option (Candidate config) :=
  let weight := weights.get (unitFeature dimension config unit)
  letI := Binary32.positiveDecidable weight.value
  if positive : 0 < weight.value.key then
    some ⟨unit, ⟨⟨weight.value, weight_bonus_legal weight positive⟩, positive⟩⟩
  else none

def Candidate.key {config : Config} (candidate : Candidate config) : Nat :=
  candidate.score.value.bits.toNat

def Candidate.Dominates {config : Config} (left right : Candidate config) : Prop :=
  right.key ≤ left.key ∧ (right.key = left.key → left.unit.val ≤ right.unit.val)

instance {config : Config} (left right : Candidate config) : Decidable (left.Dominates right) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Candidate.dominates_refl {config : Config} (candidate : Candidate config) :
    candidate.Dominates candidate := ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩

theorem Candidate.dominates_trans {config : Config} (a b c : Candidate config)
    (ab : a.Dominates b) (bc : b.Dominates c) : a.Dominates c := by
  unfold Candidate.Dominates at *
  refine ⟨Nat.le_trans bc.1 ab.1, ?_⟩
  intro same
  have sameAB : b.key = a.key := by omega
  have sameBC : c.key = b.key := by omega
  exact Nat.le_trans (ab.2 sameAB) (bc.2 sameBC)

def Candidate.pick {config : Config} (left right : Candidate config) : Candidate config :=
  if left.Dominates right then left else right

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

def best {config : Config} : List (Candidate config) → Option (Candidate config)
  | [] => none
  | head :: tail => some (tail.foldl Candidate.pick head)

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

theorem fold_pick_dominates {config : Config} (items : List (Candidate config))
    (start target : Candidate config) (before : start.Dominates target) :
    (items.foldl Candidate.pick start).Dominates target := by
  induction items generalizing start with
  | nil => exact before
  | cons head tail ih =>
    exact ih (start.pick head) (Candidate.dominates_trans _ _ _ (Candidate.pick_dominates start head).1 before)

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

def withoutBlock {config : Config} (items : List (Candidate config)) (chosen : Candidate config) :
    List (Candidate config) := items.filter (fun candidate => candidate.key != chosen.key)

def ranked {config : Config} : Nat → List (Candidate config) → List (Candidate config)
  | 0, _ => []
  | count + 1, items => match best items with
    | none => []
    | some chosen => chosen :: ranked count (withoutBlock items chosen)

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

theorem ranked_length {config : Config} (count : Nat) (items : List (Candidate config)) :
    (ranked count items).length ≤ count := by
  induction count generalizing items with
  | zero => simp [ranked]
  | succ count ih =>
    unfold ranked
    split
    · simp
    · simpa using Nat.succ_le_succ (ih _)

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

def rankedCandidates (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) : List (Candidate config) :=
  ranked Acorn.FeatureConstants.skillCount
    ((List.finRange config.units.count).filterMap (candidateOfWeight config weights))

def Assignment.Distinct {config : Config}
    (table : Vector (Assignment config) Acorn.FeatureConstants.skillCount) : Prop :=
  ∀ left right : Fin Acorn.FeatureConstants.skillCount, ∀ unit : Fin config.units.count,
    table[left.val].identity = some unit → table[right.val].identity = some unit → left = right

theorem Assignment.Distinct.mono {config : Config}
    {table other : Vector (Assignment config) Acorn.FeatureConstants.skillCount}
    (distinct : Assignment.Distinct table)
    (named : ∀ (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count),
      other[slot.val].identity = some unit → table[slot.val].identity = some unit) :
    Assignment.Distinct other :=
  fun left right unit leftNamed rightNamed =>
    distinct left right unit (named left unit leftNamed) (named right unit rightNamed)

def Assignment.distinct {config : Config}
    (table : Vector (Assignment config) Acorn.FeatureConstants.skillCount) : Bool :=
  (List.finRange Acorn.FeatureConstants.skillCount).all fun left =>
    (List.finRange Acorn.FeatureConstants.skillCount).all fun right =>
      left == right || !(table[left.val].identity.isSome &&
        table[left.val].identity == table[right.val].identity)

theorem Assignment.distinct_iff {config : Config}
    (table : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    Assignment.distinct table = true ↔ Assignment.Distinct table := by
  simp only [Assignment.distinct, List.all_eq_true, List.mem_finRange, forall_const]
  constructor
  · intro check left right unit leftNamed rightNamed
    have pair := check left right
    rw [leftNamed, rightNamed] at pair
    simpa using pair
  · intro distinct left right
    cases leftNamed : table[left.val].identity with
    | none => simp
    | some unit =>
      cases rightNamed : table[right.val].identity with
      | none => simp
      | some other =>
        by_cases same : unit = other
        · subst same
          simp [distinct left right unit leftNamed rightNamed]
        · simp [same]

def Assignment.holds {config : Config} (unit : Fin config.units.count) :
    Assignment config → Bool
  | .neutral => false
  | .selected held _ => held == unit

def Assignment.retain {config : Config} (chosen : List (Candidate config)) :
    Assignment config → Option (Assignment config)
  | .neutral => none
  | .selected unit bonus => (chosen.find? (·.unit == unit)).map fun candidate =>
      .selected unit (bonus.max candidate.score)

def kept {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount) :
    Option (Assignment config) :=
  if (List.finRange Acorn.FeatureConstants.skillCount).any (fun other =>
      decide (other.val < slot.val) && held[other.val].same held[slot.val]) then none
  else held[slot.val].retain chosen

def entrants {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) : List (Candidate config) :=
  chosen.filter fun candidate =>
    (List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
      !held[slot.val].holds candidate.unit

def openBefore {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount) : Nat :=
  ((List.finRange Acorn.FeatureConstants.skillCount).filter fun other =>
    decide (other.val < slot.val) && (kept held chosen other).isNone).length

def rankAssignments (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    Vector (Assignment config) Acorn.FeatureConstants.skillCount :=
  let chosen := rankedCandidates dimension config weights
  let arriving := entrants held chosen
  Vector.ofFn fun slot =>
    match kept held chosen slot with
    | some assignment => assignment
    | none => match arriving[openBefore held chosen slot]? with
      | none => .neutral
      | some candidate => .selected candidate.unit candidate.score

theorem rankAssignments_retained (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count) (bonus : Bonus)
    (holds : held[slot.val] = .selected unit bonus)
    (ranked : unit ∈ (rankedCandidates dimension config weights).map (·.unit))
    (first : ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
      held[other.val].identity ≠ some unit) :
    ∃ raised : Bonus, (rankAssignments dimension config weights held)[slot.val] =
      .selected unit raised ∧ bonus.value.bits.toNat ≤ raised.value.bits.toNat := by
  obtain ⟨candidate, member, named⟩ := List.mem_map.mp ranked
  have earlier : (List.finRange Acorn.FeatureConstants.skillCount).any (fun other =>
      decide (other.val < slot.val) && held[other.val].same held[slot.val]) = false := by
    rw [List.any_eq_false]
    intro other _ both
    simp only [Bool.and_eq_true, decide_eq_true_eq] at both
    exact first other both.1 (by
      rw [(Assignment.same_iff _ _).mp both.2, holds]
      rfl)
  obtain ⟨found, foundMember⟩ : ∃ found,
      (rankedCandidates dimension config weights).find? (·.unit == unit) = some found := by
    cases search : (rankedCandidates dimension config weights).find? (·.unit == unit) with
    | none =>
      exact absurd (by simpa using named) (List.find?_eq_none.mp search candidate member)
    | some found => exact ⟨found, rfl⟩
  have keeps : kept held (rankedCandidates dimension config weights) slot =
      some (.selected unit (bonus.max found.score)) := by
    unfold kept
    rw [earlier]
    simp only [Bool.false_eq_true, ↓reduceIte, holds, Assignment.retain, foundMember,
      Option.map_some]
  refine ⟨bonus.max found.score, ?_, (Bonus.le_max bonus found.score).1⟩
  simp only [rankAssignments, Vector.getElem_ofFn, keeps]

theorem rankedCandidates_key (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) (candidate : Candidate config)
    (member : candidate ∈ rankedCandidates dimension config weights) :
    candidate.key = (weights.get (unitFeature dimension config candidate.unit)).value.bits.toNat := by
  obtain ⟨unit, _, found⟩ := List.mem_filterMap.mp (ranked_subset _ _ candidate member)
  unfold candidateOfWeight at found
  dsimp only at found
  split at found
  · cases found
    rfl
  · contradiction

theorem kept_spec {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount)
    (assignment : Assignment config) (keeps : kept held chosen slot = some assignment) :
    assignment.identity = held[slot.val].identity ∧
      ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
        held[other.val].same held[slot.val] = false := by
  unfold kept at keeps
  split at keeps
  · contradiction
  · rename_i fresh
    refine ⟨?_, fun other before => ?_⟩
    · cases current : held[slot.val] with
      | neutral => simp [current, Assignment.retain] at keeps
      | selected unit bonus =>
        simp only [current, Assignment.retain, Option.map_eq_some_iff] at keeps
        obtain ⟨_, _, named⟩ := keeps
        rw [← named]
        rfl
    · have earlier := List.any_eq_false.mp (Bool.eq_false_iff.mpr fresh) other
        (List.mem_finRange other)
      simpa [before] using earlier

theorem openBefore_lt {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (left right : Fin Acorn.FeatureConstants.skillCount)
    (order : left.val < right.val) (unkept : kept held chosen left = none) :
    openBefore held chosen left < openBefore held chosen right := by
  let before (slot : Fin Acorn.FeatureConstants.skillCount) :=
    fun other : Fin Acorn.FeatureConstants.skillCount =>
      decide (other.val < slot.val) && (kept held chosen other).isNone
  have nested : ((List.finRange Acorn.FeatureConstants.skillCount).filter (before right)).filter
      (before left) = (List.finRange Acorn.FeatureConstants.skillCount).filter (before left) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro other _
    by_cases earlier : other.val < left.val
    · simp [before, earlier, Nat.lt_trans earlier order]
    · simp [before, earlier]
  change ((List.finRange Acorn.FeatureConstants.skillCount).filter (before left)).length <
    ((List.finRange Acorn.FeatureConstants.skillCount).filter (before right)).length
  rw [← nested, List.length_filter_lt_length_iff_exists]
  exact ⟨left, List.mem_filter.mpr ⟨List.mem_finRange left, by simp [before, order, unkept]⟩,
    by simp [before]⟩

theorem rankAssignments_source (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count)
    (named : (rankAssignments dimension config weights held)[slot.val].identity = some unit) :
    (∃ assignment, kept held (rankedCandidates dimension config weights) slot = some assignment ∧
        held[slot.val].identity = some unit) ∨
      (kept held (rankedCandidates dimension config weights) slot = none ∧
        ∃ candidate, (entrants held (rankedCandidates dimension config weights))[openBefore held
          (rankedCandidates dimension config weights) slot]? = some candidate ∧
            candidate.unit = unit) := by
  simp only [rankAssignments, Vector.getElem_ofFn] at named
  cases keeps : kept held (rankedCandidates dimension config weights) slot with
  | some assignment =>
    simp only [keeps] at named
    exact Or.inl ⟨assignment, rfl, (kept_spec held _ slot assignment keeps).1 ▸ named⟩
  | none =>
    simp only [keeps] at named
    refine Or.inr ⟨rfl, ?_⟩
    cases arriving : (entrants held (rankedCandidates dimension config weights))[openBefore held
        (rankedCandidates dimension config weights) slot]? with
    | none => simp [arriving, Assignment.identity] at named
    | some candidate =>
      simp only [arriving, Assignment.identity, Option.some.injEq] at named
      exact ⟨candidate, rfl, named⟩

theorem rankAssignments_ordered (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (left right : Fin Acorn.FeatureConstants.skillCount) (order : left.val < right.val)
    (unit : Fin config.units.count)
    (leftNamed : (rankAssignments dimension config weights held)[left.val].identity = some unit)
    (rightNamed : (rankAssignments dimension config weights held)[right.val].identity = some unit) :
    False := by
  have absent (candidate : Candidate config) (index : Nat)
      (found : (entrants held (rankedCandidates dimension config weights))[index]? = some candidate)
      (slot : Fin Acorn.FeatureConstants.skillCount) (holds : held[slot.val].identity = some unit)
      (same : candidate.unit = unit) : False := by
    have fresh := (List.all_eq_true.mp (List.mem_filter.mp (List.mem_of_getElem? found)).2) slot
      (List.mem_finRange slot)
    cases current : held[slot.val] with
    | neutral => simp [current, Assignment.identity] at holds
    | selected other bonus =>
      simp only [current, Assignment.identity, Option.some.injEq] at holds
      simp [current, Assignment.holds, holds, same] at fresh
  rcases rankAssignments_source dimension config weights held left unit leftNamed with
      ⟨leftKept, leftKeeps, leftHolds⟩ | ⟨leftOpen, leftCandidate, leftFound, leftSame⟩ <;>
    rcases rankAssignments_source dimension config weights held right unit rightNamed with
      ⟨rightKept, rightKeeps, rightHolds⟩ | ⟨_, rightCandidate, rightFound, rightSame⟩
  · have repeated := (kept_spec held _ right rightKept rightKeeps).2 left order
    rw [(Assignment.same_iff _ _).mpr (leftHolds.trans rightHolds.symm)] at repeated
    contradiction
  · exact absent rightCandidate _ rightFound left leftHolds rightSame
  · exact absent leftCandidate _ leftFound right rightHolds leftSame
  · have later := openBefore_lt held (rankedCandidates dimension config weights) left right order
      leftOpen
    obtain ⟨leftBound, leftEntry⟩ := List.getElem?_eq_some_iff.mp leftFound
    obtain ⟨rightBound, rightEntry⟩ := List.getElem?_eq_some_iff.mp rightFound
    have ordered : (entrants held (rankedCandidates dimension config weights)).Pairwise
        (fun earlier later => later.key < earlier.key) :=
      (ranked_strict _ _).sublist List.filter_sublist
    have strict := List.pairwise_iff_getElem.mp ordered _ _ leftBound rightBound later
    rw [leftEntry, rightEntry] at strict
    have leftKey := rankedCandidates_key dimension config weights leftCandidate
      (List.mem_filter.mp (List.mem_of_getElem? leftFound)).1
    have rightKey := rankedCandidates_key dimension config weights rightCandidate
      (List.mem_filter.mp (List.mem_of_getElem? rightFound)).1
    rw [leftKey, rightKey, leftSame, rightSame] at strict
    exact Nat.lt_irrefl _ strict

theorem rankAssignments_distinct (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    Assignment.Distinct (rankAssignments dimension config weights held) := by
  intro left right unit leftNamed rightNamed
  rcases Nat.lt_trichotomy left.val right.val with order | same | order
  · exact (rankAssignments_ordered dimension config weights held left right order unit
      leftNamed rightNamed).elim
  · exact Fin.ext same
  · exact (rankAssignments_ordered dimension config weights held right left order unit
      rightNamed leftNamed).elim

theorem sorted_below {count : Nat} (slots : List (Fin count))
    (sorted : slots.Pairwise (· < ·)) (index : Nat) (bound : index < slots.length) :
    (slots.filter fun other => decide (other.val < slots[index].val)).length = index := by
  induction slots generalizing index with
  | nil => exact absurd bound (Nat.not_lt_zero _)
  | cons head tail ih =>
    rw [List.pairwise_cons] at sorted
    cases index with
    | zero =>
      have empty : ((head :: tail).filter fun other => decide (other.val < head.val)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro other member
        rcases List.mem_cons.mp member with same | later
        · simp [same]
        · have above := Fin.lt_def.mp (sorted.1 other later)
          simp only [decide_eq_true_eq]
          omega
      simp only [List.getElem_cons_zero, empty, List.length_nil]
    | succ index =>
      have inside : index < tail.length := Nat.lt_of_succ_lt_succ bound
      have below : head.val < (tail[index]'inside).val :=
        Fin.lt_def.mp (sorted.1 _ (List.getElem_mem inside))
      simp only [List.getElem_cons_succ]
      rw [List.filter_cons_of_pos (by simpa using below), List.length_cons,
        ih sorted.2 index inside]

theorem filter_partition {α : Type} (keep drop : α → Bool) (items : List α)
    (complement : ∀ item ∈ items, drop item = !keep item) :
    (items.filter keep).length + (items.filter drop).length = items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    have rest := ih fun item member => complement item (List.mem_cons_of_mem _ member)
    have here := complement head List.mem_cons_self
    cases test : keep head <;> simp [test, here] <;> omega

theorem injective_length {α β : Type} [DecidableEq β] (image : α → β) (items : List α)
    (targets : List β)
    (distinct : items.Pairwise fun left right => image left ≠ image right)
    (inside : ∀ item ∈ items, image item ∈ targets) : items.length ≤ targets.length := by
  induction items generalizing targets with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    rw [List.pairwise_cons] at distinct
    have member := inside head List.mem_cons_self
    have rest := ih (targets.erase (image head)) distinct.2 (by
      intro item later
      exact (List.mem_erase_of_ne (fun same => distinct.1 item later same.symm)).mpr
        (inside item (List.mem_cons_of_mem _ later)))
    rw [List.length_erase_of_mem member] at rest
    have positive := List.length_pos_of_mem member
    simp only [List.length_cons]
    omega

theorem Assignment.holds_iff {config : Config} (unit : Fin config.units.count)
    (assignment : Assignment config) :
    assignment.holds unit = true ↔ assignment.identity = some unit := by
  cases assignment <;> simp [Assignment.holds, Assignment.identity]

theorem held_iff {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (unit : Fin config.units.count) :
    ((List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
      !held[slot.val].holds unit) = false ↔
      ∃ slot : Fin Acorn.FeatureConstants.skillCount, held[slot.val].identity = some unit := by
  rw [List.all_eq_false]
  constructor
  · rintro ⟨slot, _, holds⟩
    exact ⟨slot, (Assignment.holds_iff unit _).mp (by simpa using holds)⟩
  · rintro ⟨slot, named⟩
    exact ⟨slot, List.mem_finRange slot, by simp [(Assignment.holds_iff unit _).mpr named]⟩

theorem first_holder {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (unit : Fin config.units.count) (slot : Fin Acorn.FeatureConstants.skillCount)
    (holds : held[slot.val].identity = some unit) :
    ∃ first : Fin Acorn.FeatureConstants.skillCount, held[first.val].identity = some unit ∧
      ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < first.val →
        held[other.val].identity ≠ some unit := by
  suffices search : ∀ limit : Nat, ∀ slot : Fin Acorn.FeatureConstants.skillCount,
      slot.val < limit → held[slot.val].identity = some unit →
      ∃ first : Fin Acorn.FeatureConstants.skillCount, held[first.val].identity = some unit ∧
        ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < first.val →
          held[other.val].identity ≠ some unit from
    search (slot.val + 1) slot (Nat.lt_succ_self _) holds
  intro limit
  induction limit with
  | zero => exact fun slot below => absurd below (Nat.not_lt_zero _)
  | succ limit ih =>
    intro slot below holds
    by_cases earlier : ∃ other : Fin Acorn.FeatureConstants.skillCount,
        other.val < slot.val ∧ held[other.val].identity = some unit
    · obtain ⟨other, before, named⟩ := earlier
      exact ih other (by omega) named
    · exact ⟨slot, holds, fun other before named => earlier ⟨other, before, named⟩⟩

theorem kept_ranked {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount)
    (assignment : Assignment config) (keeps : kept held chosen slot = some assignment) :
    ∃ unit bonus candidate, held[slot.val] = .selected unit bonus ∧ candidate ∈ chosen ∧
      candidate.unit = unit ∧ assignment = .selected unit (bonus.max candidate.score) := by
  unfold kept at keeps
  split at keeps
  · contradiction
  · cases current : held[slot.val] with
    | neutral => simp [current, Assignment.retain] at keeps
    | selected unit bonus =>
      simp only [current, Assignment.retain, Option.map_eq_some_iff] at keeps
      obtain ⟨candidate, found, named⟩ := keeps
      exact ⟨unit, bonus, candidate, rfl, List.mem_of_find?_eq_some found,
        by simpa using List.find?_some found, named.symm⟩

theorem kept_first {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount)
    (candidate : Candidate config) (member : candidate ∈ chosen)
    (holds : held[slot.val].identity = some candidate.unit)
    (first : ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
      held[other.val].identity ≠ some candidate.unit) :
    (kept held chosen slot).isSome = true := by
  have earlier : (List.finRange Acorn.FeatureConstants.skillCount).any (fun other =>
      decide (other.val < slot.val) && held[other.val].same held[slot.val]) = false := by
    rw [List.any_eq_false]
    intro other _ both
    simp only [Bool.and_eq_true, decide_eq_true_eq] at both
    exact first other both.1 (by rw [(Assignment.same_iff _ _).mp both.2, holds])
  cases current : held[slot.val] with
  | neutral => simp [current, Assignment.identity] at holds
  | selected unit bonus =>
    have same : unit = candidate.unit := by simpa [current, Assignment.identity] using holds
    have found : (chosen.find? (·.unit == unit)).isSome = true :=
      List.find?_isSome.mpr ⟨candidate, member, by simp [same]⟩
    unfold kept
    rw [earlier]
    simp only [Bool.false_eq_true, ↓reduceIte, current, Assignment.retain, Option.isSome_map, found]

theorem open_slot {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (index : Nat)
    (bound : index < ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
      (kept held chosen slot).isNone).length) :
    ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      kept held chosen slot = none ∧ openBefore held chosen slot = index := by
  have sorted : ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
      (kept held chosen slot).isNone).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange _).filter _
  have position := sorted_below _ sorted index bound
  rw [List.filter_filter] at position
  exact ⟨_, by simpa using (List.mem_filter.mp (List.getElem_mem bound)).2, position⟩

theorem openBefore_bound {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount)
    (unkept : kept held chosen slot = none) :
    openBefore held chosen slot < ((List.finRange Acorn.FeatureConstants.skillCount).filter
      fun other => (kept held chosen other).isNone).length := by
  have nested : ((List.finRange Acorn.FeatureConstants.skillCount).filter fun other =>
      decide (other.val < slot.val) && (kept held chosen other).isNone) =
        ((List.finRange Acorn.FeatureConstants.skillCount).filter fun other =>
          (kept held chosen other).isNone).filter fun other => decide (other.val < slot.val) := by
    rw [List.filter_filter]
  unfold openBefore
  rw [nested, List.length_filter_lt_length_iff_exists]
  exact ⟨slot, List.mem_filter.mpr ⟨List.mem_finRange slot, by simp [unkept]⟩, by simp⟩

theorem slots_partition {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) :
    ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
        (kept held chosen slot).isNone).length +
      ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
        (kept held chosen slot).isSome).length = Acorn.FeatureConstants.skillCount := by
  have split := filter_partition (fun slot => (kept held chosen slot).isNone)
    (fun slot => (kept held chosen slot).isSome)
    (List.finRange Acorn.FeatureConstants.skillCount)
    (fun slot _ => (Option.not_isNone _).symm)
  rw [List.length_finRange] at split
  exact split

theorem entrants_partition {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) :
    (entrants held chosen).length + (chosen.filter fun candidate =>
      !(List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
        !held[slot.val].holds candidate.unit).length = chosen.length :=
  filter_partition _ _ chosen fun _ _ => rfl

theorem kept_le_held {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) :
    ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
        (kept held chosen slot).isSome).length ≤
      (chosen.filter fun candidate =>
        !(List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
          !held[slot.val].holds candidate.unit).length := by
  have bound := injective_length
    (fun slot : Fin Acorn.FeatureConstants.skillCount => held[slot.val].identity)
    ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
      (kept held chosen slot).isSome)
    ((chosen.filter fun candidate =>
      !(List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
        !held[slot.val].holds candidate.unit).map fun candidate => some candidate.unit)
    (by
      refine ((List.pairwise_lt_finRange _).filter _).imp_of_mem ?_
      intro left right _ rightKept order same
      obtain ⟨assignment, keeps⟩ := Option.isSome_iff_exists.mp (List.mem_filter.mp rightKept).2
      have repeated := (kept_spec held chosen right assignment keeps).2 left (Fin.lt_def.mp order)
      rw [(Assignment.same_iff _ _).mpr same] at repeated
      contradiction)
    (by
      intro slot slotKept
      obtain ⟨assignment, keeps⟩ := Option.isSome_iff_exists.mp (List.mem_filter.mp slotKept).2
      obtain ⟨unit, bonus, candidate, current, member, named, _⟩ :=
        kept_ranked held chosen slot assignment keeps
      refine List.mem_map.mpr ⟨candidate, List.mem_filter.mpr ⟨member, ?_⟩, ?_⟩
      · have holder : ∃ other : Fin Acorn.FeatureConstants.skillCount,
            held[other.val].identity = some candidate.unit :=
          ⟨slot, by rw [current, named]; rfl⟩
        simp [(held_iff held candidate.unit).mpr holder]
      · rw [current, named]
        rfl)
  simpa using bound

theorem held_le_kept {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config))
    (distinct : chosen.Pairwise fun left right => left.unit ≠ right.unit) :
    (chosen.filter fun candidate =>
        !(List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
          !held[slot.val].holds candidate.unit).length ≤
      ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
        (kept held chosen slot).isSome).length := by
  have bound : (chosen.filter fun candidate =>
      !(List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
        !held[slot.val].holds candidate.unit).length ≤
      (((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
        (kept held chosen slot).isSome).map fun slot => held[slot.val].identity).length := by
    refine injective_length (fun candidate : Candidate config => some candidate.unit) _ _
      ((distinct.filter _).imp fun differs same => differs (Option.some.inj same)) ?_
    intro candidate heldCandidate
    obtain ⟨member, rejected⟩ := List.mem_filter.mp heldCandidate
    obtain ⟨slot, named⟩ := (held_iff held candidate.unit).mp (by simpa using rejected)
    obtain ⟨first, holds, before⟩ := first_holder held candidate.unit slot named
    exact List.mem_map.mpr ⟨first, List.mem_filter.mpr ⟨List.mem_finRange first,
      kept_first held chosen first candidate member holds before⟩, holds⟩
  simpa using bound

theorem entrants_le_open {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config))
    (short : chosen.length ≤ Acorn.FeatureConstants.skillCount) :
    (entrants held chosen).length ≤ ((List.finRange Acorn.FeatureConstants.skillCount).filter
      fun slot => (kept held chosen slot).isNone).length := by
  have slots := slots_partition held chosen
  have candidates := entrants_partition held chosen
  have keeps := kept_le_held held chosen
  omega

theorem open_le_entrants {config : Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config))
    (full : chosen.length = Acorn.FeatureConstants.skillCount)
    (distinct : chosen.Pairwise fun left right => left.unit ≠ right.unit) :
    ((List.finRange Acorn.FeatureConstants.skillCount).filter
      fun slot => (kept held chosen slot).isNone).length ≤ (entrants held chosen).length := by
  have slots := slots_partition held chosen
  have candidates := entrants_partition held chosen
  have holds := held_le_kept held chosen distinct
  omega

theorem rankedCandidates_units (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    (rankedCandidates dimension config weights).Pairwise fun left right =>
      left.unit ≠ right.unit := by
  refine (ranked_strict Acorn.FeatureConstants.skillCount
    ((List.finRange config.units.count).filterMap (candidateOfWeight config weights))).imp_of_mem ?_
  intro left right leftMember rightMember lower same
  rw [rankedCandidates_key dimension config weights left leftMember,
    rankedCandidates_key dimension config weights right rightMember, same] at lower
  exact Nat.lt_irrefl _ lower

theorem rankAssignments_entrant (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount) (index : Nat)
    (bound : index < (entrants held (rankedCandidates dimension config weights)).length) :
    ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      (rankAssignments dimension config weights held)[slot.val] =
        .selected (entrants held (rankedCandidates dimension config weights))[index].unit
          (entrants held (rankedCandidates dimension config weights))[index].score := by
  have room := entrants_le_open held (rankedCandidates dimension config weights)
    (ranked_length _ _)
  obtain ⟨slot, unkept, position⟩ := open_slot held (rankedCandidates dimension config weights) index
    (Nat.lt_of_lt_of_le bound room)
  exact ⟨slot, by simp only [rankAssignments, Vector.getElem_ofFn, unkept, position,
    List.getElem?_eq_getElem bound]⟩

theorem rankAssignments_covers (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (candidate : Candidate config) (member : candidate ∈ rankedCandidates dimension config weights) :
    ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      (rankAssignments dimension config weights held)[slot.val].identity = some candidate.unit := by
  cases arriving : (List.finRange Acorn.FeatureConstants.skillCount).all fun slot =>
      !held[slot.val].holds candidate.unit with
  | true =>
    have entrant : candidate ∈ entrants held (rankedCandidates dimension config weights) :=
      List.mem_filter.mpr ⟨member, arriving⟩
    obtain ⟨index, bound, entry⟩ := List.mem_iff_getElem.mp entrant
    obtain ⟨slot, taken⟩ := rankAssignments_entrant dimension config weights held index bound
    exact ⟨slot, by rw [taken, entry]; rfl⟩
  | false =>
    obtain ⟨slot, named⟩ := (held_iff held candidate.unit).mp arriving
    obtain ⟨first, holds, before⟩ := first_holder held candidate.unit slot named
    cases current : held[first.val] with
    | neutral => simp [current, Assignment.identity] at holds
    | selected unit bonus =>
      have same : unit = candidate.unit := by simpa [current, Assignment.identity] using holds
      subst same
      obtain ⟨raised, target, _⟩ := rankAssignments_retained dimension config weights held first
        candidate.unit bonus current (List.mem_map.mpr ⟨candidate, member, rfl⟩) before
      exact ⟨first, by rw [target]; rfl⟩

theorem rankAssignments_ranked (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count)
    (named : (rankAssignments dimension config weights held)[slot.val].identity = some unit) :
    unit ∈ (rankedCandidates dimension config weights).map (·.unit) := by
  rcases rankAssignments_source dimension config weights held slot unit named with
    ⟨assignment, keeps, holds⟩ | ⟨_, candidate, found, same⟩
  · obtain ⟨heldUnit, bonus, candidate, current, member, source, _⟩ :=
      kept_ranked held _ slot assignment keeps
    have same : heldUnit = unit := by simpa [current, Assignment.identity] using holds
    exact List.mem_map.mpr ⟨candidate, member, source.trans same⟩
  · exact List.mem_map.mpr
      ⟨candidate, (List.mem_filter.mp (List.mem_of_getElem? found)).1, same⟩

theorem rankAssignments_full (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (full : (rankedCandidates dimension config weights).length = Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    ∃ unit bonus, (rankAssignments dimension config weights held)[slot.val] = .selected unit bonus := by
  cases keeps : kept held (rankedCandidates dimension config weights) slot with
  | some assignment =>
    obtain ⟨unit, bonus, candidate, _, _, _, shape⟩ := kept_ranked held _ slot assignment keeps
    exact ⟨unit, bonus.max candidate.score,
      by simp only [rankAssignments, Vector.getElem_ofFn, keeps, shape]⟩
  | none =>
    have position := openBefore_bound held (rankedCandidates dimension config weights) slot keeps
    have room := open_le_entrants held (rankedCandidates dimension config weights) full
      (rankedCandidates_units dimension config weights)
    have inside : openBefore held (rankedCandidates dimension config weights) slot <
        (entrants held (rankedCandidates dimension config weights)).length := Nat.lt_of_lt_of_le position room
    exact ⟨((entrants held (rankedCandidates dimension config weights))[openBefore held
        (rankedCandidates dimension config weights) slot]'inside).unit,
      ((entrants held (rankedCandidates dimension config weights))[openBefore held
        (rankedCandidates dimension config weights) slot]'inside).score,
      by simp only [rankAssignments, Vector.getElem_ofFn, keeps, List.getElem?_eq_getElem inside]⟩

theorem rankAssignments_count (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
      (rankAssignments dimension config weights held)[slot.val].identity.isSome).length =
        (rankedCandidates dimension config weights).length := by
  have upper : ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
      (rankAssignments dimension config weights held)[slot.val].identity.isSome).length ≤
        ((rankedCandidates dimension config weights).map fun candidate =>
          some candidate.unit).length := by
    refine injective_length
      (fun slot : Fin Acorn.FeatureConstants.skillCount =>
        (rankAssignments dimension config weights held)[slot.val].identity) _ _ ?_ ?_
    · refine ((List.nodup_finRange _).filter _).imp_of_mem ?_
      intro left right leftHolds _ differs same
      obtain ⟨unit, named⟩ := Option.isSome_iff_exists.mp (List.mem_filter.mp leftHolds).2
      exact differs (rankAssignments_distinct dimension config weights held left right unit named
        (same ▸ named))
    · intro slot holds
      obtain ⟨unit, named⟩ := Option.isSome_iff_exists.mp (List.mem_filter.mp holds).2
      obtain ⟨candidate, member, source⟩ := List.mem_map.mp
        (rankAssignments_ranked dimension config weights held slot unit named)
      exact List.mem_map.mpr ⟨candidate, member, by rw [named, source]⟩
  have lower : (rankedCandidates dimension config weights).length ≤
      (((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
        (rankAssignments dimension config weights held)[slot.val].identity.isSome).map fun slot =>
          (rankAssignments dimension config weights held)[slot.val].identity).length := by
    refine injective_length (fun candidate : Candidate config => some candidate.unit) _ _
      ((rankedCandidates_units dimension config weights).imp fun differs same =>
        differs (Option.some.inj same)) ?_
    intro candidate member
    obtain ⟨slot, named⟩ := rankAssignments_covers dimension config weights held candidate member
    exact List.mem_map.mpr ⟨slot, List.mem_filter.mpr ⟨List.mem_finRange slot, by simp [named]⟩,
      named⟩
  simp only [List.length_map] at upper lower
  omega

end Acorn.Features
