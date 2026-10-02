/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.Features

/-!
# Ranked feature subset of an option's expectation model

Sutton, Bowling and Pilarski, *The Alberta Plan for AI Research*,
arXiv:2208.11173v3 (2023), Step 8(d), p. 9, asks for "a ranking of features used
both for feature finding and to determine which features are included in the
environment model". The transition part of an option model predicts only the
feature slots held here, from only those slots and one constant input: the last
position holds no slot and is active in every input.

The width follows from a memory budget, not a tuned constant: it is the largest
power of two `k` for which the transition parts of all options together,
`skillCount · k²` weights, fit in one weight vector of the receiving dimension.
`rankWidth_budget` and `rankWidth_maximal` state both halves.

A position keeps its slot while that slot stays ranked, so the weights learned
for it survive a change of subset; a position whose slot leaves the ranking takes
the next entrant or stays vacant. A slot is held at one position only and the last
position holds none: both are fields of the structure, kept by every construction. Positions index a second, smaller dimension, so
each row of the transition part is an ordinary learner over that dimension.
-/
namespace Acorn.Features

/-- Double the width while the doubled width still fits the budget: all options'
transition parts, `skillCount · (2k)²` weights, within one weight vector. The doubled
width `2 ^ (e + 1)` is written as a shift, which the executing code evaluates on
machine words. -/
def rankExponentFrom (capacity : Nat) : Nat → Nat → Nat
  | 0, exponent => exponent
  | fuel + 1, exponent =>
    if Acorn.FeatureConstants.skillCount *
        ((1 <<< (exponent + 1)) * (1 <<< (exponent + 1))) ≤ capacity then
      rankExponentFrom capacity fuel (exponent + 1)
    else exponent

/-- The search adds at most its fuel to the exponent. -/
theorem rankExponentFrom_le (capacity : Nat) (fuel exponent : Nat) :
    rankExponentFrom capacity fuel exponent ≤ exponent + fuel := by
  induction fuel generalizing exponent with
  | zero => simp [rankExponentFrom]
  | succ fuel ih =>
    unfold rankExponentFrom
    split
    · have := ih (exponent + 1)
      omega
    · omega

/-- Base-two logarithm of the ranked width. Fifteen doublings reach every budget a
feature index can address, since `skillCount · 4¹⁶` exceeds `2³²`. -/
def rankExponent (dimension : Dimension) : Nat := rankExponentFrom dimension.capacity 15 0

/-- Number of positions of an option's transition part: two to the exponent, as a
shift. -/
def rankWidth (dimension : Dimension) : Nat := 1 <<< rankExponent dimension

/-- The width is two to the exponent. -/
theorem rankWidth_eq (dimension : Dimension) :
    rankWidth dimension = 2 ^ rankExponent dimension := Nat.one_shiftLeft _

/-- The ranked positions as a feature space of their own: each row of a transition
part is a learner over this dimension. -/
abbrev rankDimension (dimension : Dimension) : Dimension where
  capacity := rankWidth dimension
  positive := by rw [rankWidth_eq]; exact Nat.two_pow_pos _
  powerOfTwo := ⟨rankExponent dimension, rankWidth_eq dimension⟩
  wordBound := by
    have bound := rankExponentFrom_le dimension.capacity 15 0
    rw [rankWidth_eq]
    exact Nat.pow_lt_pow_right (by decide) (by unfold rankExponent; omega)

/-- One position of the ranked subset. -/
abbrev RankIdx (dimension : Dimension) := FeatIdx (rankDimension dimension)

/-- Storage budget: once a dimension has one weight per option, the transition parts
of all options together hold at most one weight vector's worth of weights. -/
theorem rankWidth_budget (dimension : Dimension)
    (room : Acorn.FeatureConstants.skillCount ≤ dimension.capacity) :
    Acorn.FeatureConstants.skillCount * (rankWidth dimension * rankWidth dimension) ≤
      dimension.capacity := by
  have search : ∀ (fuel exponent : Nat),
      Acorn.FeatureConstants.skillCount * (2 ^ exponent * 2 ^ exponent) ≤ dimension.capacity →
      Acorn.FeatureConstants.skillCount *
        (2 ^ rankExponentFrom dimension.capacity fuel exponent *
          2 ^ rankExponentFrom dimension.capacity fuel exponent) ≤ dimension.capacity := by
    intro fuel
    induction fuel with
    | zero => intro exponent fits; simpa [rankExponentFrom] using fits
    | succ fuel ih =>
      intro exponent fits
      unfold rankExponentFrom
      split
      · rename_i wider
        rw [Nat.one_shiftLeft] at wider
        exact ih (exponent + 1) wider
      · exact fits
  rw [rankWidth_eq]
  exact search 15 0 (by simpa using room)

/-- The width is the largest such power of two: the doubled width, `2 ^ (e + 1)` for
the width `2 ^ e`, exceeds the budget for every dimension a feature index can address. -/
theorem rankWidth_maximal (dimension : Dimension) :
    dimension.capacity < Acorn.FeatureConstants.skillCount *
      (2 ^ (rankExponent dimension + 1) * 2 ^ (rankExponent dimension + 1)) := by
  have search : ∀ (fuel exponent : Nat), exponent + fuel = 15 →
      dimension.capacity < Acorn.FeatureConstants.skillCount *
        (2 ^ (rankExponentFrom dimension.capacity fuel exponent + 1) *
          2 ^ (rankExponentFrom dimension.capacity fuel exponent + 1)) := by
    intro fuel
    induction fuel with
    | zero =>
      intro exponent full
      have last : exponent = 15 := by omega
      subst last
      show dimension.capacity <
        Acorn.FeatureConstants.skillCount * (2 ^ (15 + 1) * 2 ^ (15 + 1))
      exact Nat.lt_of_lt_of_le dimension.wordBound (by decide)
    | succ fuel ih =>
      intro exponent full
      unfold rankExponentFrom
      split
      · exact ih (exponent + 1) (by omega)
      · rename_i narrower
        rw [Nat.one_shiftLeft] at narrower
        exact Nat.lt_of_not_le narrower
  exact search 15 0 rfl

/-- Enter one position in the table: its slot's entry becomes the position plus one. -/
def tabulateStep {dimension : Dimension}
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity)
    (table : Vector Nat dimension.capacity) (position : RankIdx dimension) :
    Vector Nat dimension.capacity :=
  match slots[position.val] with
  | some feature => table.set feature.val (position.val + 1) feature.isLt
  | none => table

/-- The position of each ranked slot plus one, and zero elsewhere. A slot held at
two positions resolves to the later one. -/
def tabulate {dimension : Dimension}
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity) :
    Vector Nat dimension.capacity :=
  (List.finRange (rankDimension dimension).capacity).foldl (tabulateStep slots)
    (Vector.replicate dimension.capacity 0)

/-- A table entry names a position that holds the slot. -/
def Tabulated {dimension : Dimension}
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity)
    (table : Vector Nat dimension.capacity) (feature : FeatIdx dimension) : Prop :=
  ∃ position : RankIdx dimension,
    table[feature.val] = position.val + 1 ∧ slots[position.val] = some feature

/-- Entering a position keeps every slot's entry naming a position that holds it. -/
theorem tabulateStep_keeps {dimension : Dimension}
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity)
    (table : Vector Nat dimension.capacity) (position : RankIdx dimension)
    (feature : FeatIdx dimension) (good : Tabulated slots table feature) :
    Tabulated slots (tabulateStep slots table position) feature := by
  unfold tabulateStep
  split
  · rename_i other held
    by_cases same : other = feature
    · subst same
      exact ⟨position, by simp, held⟩
    · obtain ⟨found, entry, holds⟩ := good
      have different : other.val ≠ feature.val := fun equal => same (Fin.ext equal)
      exact ⟨found, by rw [Vector.getElem_set_ne _ _ different]; exact entry, holds⟩
  · exact good

/-- Entering a position makes its slot's entry name a position that holds it. -/
theorem tabulateStep_enters {dimension : Dimension}
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity)
    (table : Vector Nat dimension.capacity) (position : RankIdx dimension)
    (feature : FeatIdx dimension) (held : slots[position.val] = some feature) :
    Tabulated slots (tabulateStep slots table position) feature := by
  simp only [tabulateStep, held]
  exact ⟨position, by simp, held⟩

/-- After entering a list of positions, every slot one of them holds has an entry
naming a position that holds it. -/
theorem tabulate_fold {dimension : Dimension}
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity)
    (positions : List (RankIdx dimension)) :
    ∀ (table : Vector Nat dimension.capacity) (feature : FeatIdx dimension),
      (Tabulated slots table feature ∨
        ∃ position ∈ positions, slots[position.val] = some feature) →
      Tabulated slots (positions.foldl (tabulateStep slots) table) feature := by
  induction positions with
  | nil =>
    intro table feature source
    rcases source with good | ⟨_, member, _⟩
    · exact good
    · simp at member
  | cons head rest ih =>
    intro table feature source
    apply ih
    rcases source with good | ⟨position, member, held⟩
    · exact Or.inl (tabulateStep_keeps slots table head feature good)
    · rcases List.mem_cons.mp member with same | later
      · rw [← same]
        exact Or.inl (tabulateStep_enters slots table position feature held)
      · exact Or.inr ⟨position, later, held⟩

/-- Two entries of a slot list never name one slot. -/
def SlotsDistinct {α : Type} (first second : Option α) : Prop :=
  ∀ slot, first = some slot → second ≠ some slot

/-- Pairwise-distinct entries hold each slot at one index only. -/
theorem distinct_index {α : Type} {size : Nat} (slots : Vector (Option α) size)
    (distinct : slots.toList.Pairwise SlotsDistinct) (first second : Fin size) (slot : α)
    (left : slots[first.val] = some slot) (right : slots[second.val] = some slot) :
    first = second := by
  have pairs := List.pairwise_iff_getElem.mp distinct
  apply Fin.ext
  rcases Nat.lt_trichotomy first.val second.val with lower | same | higher
  · exact absurd (by simpa using right)
      (pairs first.val second.val (by simp) (by simp) lower slot (by simpa using left))
  · exact same
  · exact absurd (by simpa using left)
      (pairs second.val first.val (by simp) (by simp) higher slot (by simpa using right))

/-- Entries that hold each slot at one index only are pairwise distinct. -/
theorem index_distinct {α : Type} {size : Nat} (slots : Vector (Option α) size)
    (unique : ∀ (first second : Fin size) (slot : α), slots[first.val] = some slot →
      slots[second.val] = some slot → first = second) :
    slots.toList.Pairwise SlotsDistinct := by
  rw [List.pairwise_iff_getElem]
  intro first second firstBound secondBound lower slot left right
  have firstInside : first < size := by simpa using firstBound
  have secondInside : second < size := by simpa using secondBound
  have same := unique ⟨first, firstInside⟩ ⟨second, secondInside⟩ slot (by simpa using left)
    (by simpa using right)
  have equal : first = second := congrArg Fin.val same
  omega

/-- The feature slots an expectation model predicts, in a fixed position order, with
the lookup table from slot to position. -/
structure RankedFeatures (dimension : Dimension) where
  /-- Slot modeled at each position; a vacant position models nothing. -/
  slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity
  /-- Each ranked slot's position plus one; zero for every other slot. -/
  table : Vector Nat dimension.capacity
  /-- The table is the one built from the slots, at every construction. -/
  tabulated : table = tabulate slots
  /-- The last position holds no slot: it is the bias of every row's input. -/
  reserved : slots[(rankDimension dimension).capacity - 1]'(Nat.sub_lt
    (rankDimension dimension).positive (by decide)) = none
  /-- No slot is modeled at two positions. -/
  distinct : slots.toList.Pairwise SlotsDistinct

variable {dimension : Dimension}

/-- The only constructor: the table is built from the slots, the last position is
vacant and no slot is held twice. -/
def RankedFeatures.ofSlots
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity)
    (reserved : slots[(rankDimension dimension).capacity - 1]'(Nat.sub_lt
      (rankDimension dimension).positive (by decide)) = none)
    (distinct : slots.toList.Pairwise SlotsDistinct) :
    RankedFeatures dimension := ⟨slots, tabulate slots, rfl, reserved, distinct⟩

/-- No slot is ranked: fresh, released and restored models start here. -/
def RankedFeatures.empty (dimension : Dimension) : RankedFeatures dimension :=
  .ofSlots (Vector.replicate _ none) (by simp) (by
    apply index_distinct
    intro first second slot left
    simp at left)

/-- A slot is modeled at one position only, in every ranking: the structure carries it. -/
theorem RankedFeatures.slot_unique (ranked : RankedFeatures dimension)
    (first second : RankIdx dimension) (feature : FeatIdx dimension)
    (left : ranked.slots[first.val] = some feature)
    (right : ranked.slots[second.val] = some feature) : first = second :=
  distinct_index ranked.slots ranked.distinct first second feature left right

/-- Position of a slot, read from the table and checked against the slots, so a
returned position holds that slot whatever the table contains. The bound is read from
the stored slots, so a lookup evaluates no width. -/
def RankedFeatures.position (ranked : RankedFeatures dimension) (feature : FeatIdx dimension) :
    Option (RankIdx dimension) :=
  if inside : 0 < ranked.table[feature.val] ∧
      ranked.table[feature.val] - 1 < ranked.slots.toArray.size then
    if ranked.slots[ranked.table[feature.val] - 1]'(ranked.slots.size_toArray ▸ inside.2) =
        some feature then
      some ⟨ranked.table[feature.val] - 1, ranked.slots.size_toArray ▸ inside.2⟩
    else none
  else none

/-- A returned position holds exactly the slot that was looked up. -/
theorem RankedFeatures.position_slot (ranked : RankedFeatures dimension)
    (feature : FeatIdx dimension) (position : RankIdx dimension)
    (found : ranked.position feature = some position) :
    ranked.slots[position.val] = some feature := by
  unfold RankedFeatures.position at found
  split at found
  · split at found
    · rename_i holds
      cases found
      exact holds
    · contradiction
  · contradiction

/-- Every held slot is found: the lookup returns a position, and by `position_slot`
that position holds the slot. Two positions holding one slot resolve to one of them. -/
theorem RankedFeatures.position_complete (ranked : RankedFeatures dimension)
    (position : RankIdx dimension) (feature : FeatIdx dimension)
    (held : ranked.slots[position.val] = some feature) :
    ∃ found : RankIdx dimension, ranked.position feature = some found := by
  have good : Tabulated ranked.slots ranked.table feature := by
    rw [ranked.tabulated]
    exact tabulate_fold ranked.slots _ _ feature
      (Or.inr ⟨position, List.mem_finRange position, held⟩)
  obtain ⟨found, entry, holds⟩ := good
  have index : ranked.table[feature.val] - 1 = found.val := by
    rw [entry]
    omega
  have bound : ranked.table[feature.val] - 1 < (rankDimension dimension).capacity := by
    rw [index]
    exact found.isLt
  have inside : 0 < ranked.table[feature.val] ∧
      ranked.table[feature.val] - 1 < ranked.slots.toArray.size :=
    ⟨by rw [entry]; exact Nat.succ_pos _, ranked.slots.size_toArray.symm ▸ bound⟩
  refine ⟨⟨ranked.table[feature.val] - 1, bound⟩, ?_⟩
  have stored : ranked.slots[ranked.table[feature.val] - 1]'bound = some feature := by
    simp only [index]
    exact holds
  unfold RankedFeatures.position
  split
  · rfl
  · rename_i outside
    exact absurd inside outside

/-- The ranked positions active in a frame, in the frame's own feature order. Two
distinct active slots never share a position, so the result is a binary feature set
over the ranked dimension. -/
def RankedFeatures.active (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) : SwiftTd.ActiveSet (rankDimension dimension) :=
  ⟨features.indices.filterMap ranked.position, by
    apply List.Pairwise.filterMap ranked.position ?_ features.nodup
    intro first second different left foundLeft right foundRight same
    apply different
    have held := ranked.position_slot first left foundLeft
    rw [same, ranked.position_slot second right foundRight] at held
    exact (Option.some.inj held).symm⟩

/-- Every active ranked slot contributes a position holding it. -/
theorem RankedFeatures.active_complete (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) (position : RankIdx dimension)
    (feature : FeatIdx dimension) (held : ranked.slots[position.val] = some feature)
    (active : feature ∈ features.indices) :
    ∃ found : RankIdx dimension, found ∈ (ranked.active features).indices ∧
      ranked.slots[found.val] = some feature := by
  obtain ⟨found, located⟩ := ranked.position_complete position feature held
  exact ⟨found, List.mem_filterMap.mpr ⟨feature, active, located⟩,
    ranked.position_slot feature found located⟩

/-- Every active position holds an active slot of the frame. -/
theorem RankedFeatures.active_sound (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) (position : RankIdx dimension)
    (member : position ∈ (ranked.active features).indices) :
    ∃ feature ∈ features.indices, ranked.slots[position.val] = some feature := by
  obtain ⟨feature, active, located⟩ := List.mem_filterMap.mp member
  exact ⟨feature, active, ranked.position_slot feature position located⟩

/-- A frame activates at most as many positions as it has active features. -/
theorem RankedFeatures.active_length (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.active features).indices.length ≤ features.indices.length :=
  List.length_filterMap_le _ _

/-- The reserved last position. It holds no slot (`RankedFeatures.bias_vacant`) and is
active in every row's input, so a row can predict a slot's mean activity at a frame
whose ranked slots say nothing: without it every row would predict zero there. -/
def RankedFeatures.bias (dimension : Dimension) : RankIdx dimension :=
  ⟨(rankDimension dimension).capacity - 1,
    Nat.sub_lt (rankDimension dimension).positive (by decide)⟩

/-- The bias position holds no slot, in every ranking: the structure carries it. -/
theorem RankedFeatures.bias_vacant (ranked : RankedFeatures dimension) :
    ranked.slots[(RankedFeatures.bias dimension).val] = none := ranked.reserved

/-- The input every row of a transition part reads at a frame: the active ranked
positions, then the always-active bias position. -/
def RankedFeatures.input (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) : SwiftTd.ActiveSet (rankDimension dimension) :=
  insert (ranked.active features) (RankedFeatures.bias dimension)

/-- The bias is in every input, and every other input position is an active one. -/
theorem RankedFeatures.input_membership (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) (position : RankIdx dimension) :
    position ∈ (ranked.input features).indices ↔
      position ∈ (ranked.active features).indices ∨ position = RankedFeatures.bias dimension :=
  mem_insert _ _ _

/-- An input has at most one position more than the frame has active features. -/
theorem RankedFeatures.input_length (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.input features).indices.length ≤ features.indices.length + 1 :=
  Nat.le_trans (insert_length _ _) (Nat.add_le_add_right (ranked.active_length features) 1)

/-- An expected feature value: a discounted probability that a binary feature holds
when an option stops, so it is a finite word in `[0, 1]` at storage. -/
def expectationRange : Interval32 where
  lower := .zero
  upper := Binary32.one
  lowerFinite := by decide
  upperFinite := by decide
  ordered := by decide

/-- One predicted feature value of an expectation model. -/
abbrev Expectation := Bounded32 expectationRange

/-- The feature is absent. -/
def Expectation.absent : Expectation := Bounded32.project expectationRange .zero

/-- The feature is present. -/
def Expectation.present : Expectation := Bounded32.project expectationRange Binary32.one

/-- The ranked features of an observed frame as expected values: one at each active
position and zero elsewhere. This is the vector a transition part is trained toward,
and the argument at which the value function's ranked part is read for a real frame. -/
def RankedFeatures.indicator (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Vector Expectation (rankDimension dimension).capacity :=
  (ranked.active features).indices.foldl
    (fun seen position => seen.set position.val Expectation.present position.isLt)
    (Vector.replicate _ Expectation.absent)

/-- Every occupied position with its slot, in position order. -/
def RankedFeatures.occupied (ranked : RankedFeatures dimension) :
    List (RankIdx dimension × FeatIdx dimension) :=
  (List.finRange (rankDimension dimension).capacity).filterMap fun position =>
    (ranked.slots[position.val]).map fun feature => (position, feature)

/-- There are at most as many occupied positions as positions. -/
theorem RankedFeatures.occupied_length (ranked : RankedFeatures dimension) :
    ranked.occupied.length ≤ (rankDimension dimension).capacity := by
  have bound := List.length_filterMap_le
    (fun position : RankIdx dimension =>
      (ranked.slots[position.val]).map fun feature => (position, feature))
    (List.finRange (rankDimension dimension).capacity)
  simpa [RankedFeatures.occupied] using bound

/-- Fill each vacant position with the next entrant, in order; a held position is
kept, and positions past the last entrant stay vacant. -/
def fillVacant {α : Type} : List (Option α) → List α → List (Option α)
  | [], _ => []
  | some held :: rest, entrants => some held :: fillVacant rest entrants
  | none :: rest, [] => none :: fillVacant rest []
  | none :: rest, entrant :: later => some entrant :: fillVacant rest later

/-- Filling changes no position count. -/
theorem fillVacant_length {α : Type} (slots : List (Option α)) (entrants : List α) :
    (fillVacant slots entrants).length = slots.length := by
  induction slots generalizing entrants with
  | nil => simp [fillVacant]
  | cons slot rest ih =>
    cases slot with
    | some held => simp [fillVacant, ih]
    | none => cases entrants <;> simp [fillVacant, ih]

/-- Every entry of a filled list is an entry of the slots or a placed entrant. -/
theorem fillVacant_mem {α : Type} (slots : List (Option α)) (entrants : List α)
    (entry : Option α) (member : entry ∈ fillVacant slots entrants) :
    entry ∈ slots ∨ ∃ entrant ∈ entrants, entry = some entrant := by
  induction slots generalizing entrants with
  | nil => simp [fillVacant] at member
  | cons slot rest ih =>
    cases slot with
    | some held =>
      simp only [fillVacant, List.mem_cons] at member
      rcases member with same | later
      · exact Or.inl (by simp [same])
      · rcases ih entrants later with inside | ⟨entrant, isEntrant, same⟩
        · exact Or.inl (List.mem_cons_of_mem _ inside)
        · exact Or.inr ⟨entrant, isEntrant, same⟩
    | none =>
      cases entrants with
      | nil =>
        simp only [fillVacant, List.mem_cons] at member
        rcases member with same | later
        · exact Or.inl (by simp [same])
        · rcases ih [] later with inside | ⟨entrant, isEntrant, _⟩
          · exact Or.inl (List.mem_cons_of_mem _ inside)
          · simp at isEntrant
      | cons entrant others =>
        simp only [fillVacant, List.mem_cons] at member
        rcases member with same | later
        · exact Or.inr ⟨entrant, by simp, same⟩
        · rcases ih others later with inside | ⟨other, isEntrant, same⟩
          · exact Or.inl (List.mem_cons_of_mem _ inside)
          · exact Or.inr ⟨other, List.mem_cons_of_mem _ isEntrant, same⟩

/-- Filling keeps the entries distinct when the entrants are distinct and none of them
is already held. -/
theorem fillVacant_distinct {α : Type} (slots : List (Option α)) (entrants : List α)
    (distinct : slots.Pairwise SlotsDistinct) (fresh : entrants.Nodup)
    (apart : ∀ entrant ∈ entrants, some entrant ∉ slots) :
    (fillVacant slots entrants).Pairwise SlotsDistinct := by
  induction slots generalizing entrants with
  | nil => simp [fillVacant]
  | cons slot rest ih =>
    rw [List.pairwise_cons] at distinct
    have restApart : ∀ entrant ∈ entrants, some entrant ∉ rest :=
      fun entrant member inside => apart entrant member (List.mem_cons_of_mem _ inside)
    cases slot with
    | some held =>
      simp only [fillVacant]
      rw [List.pairwise_cons]
      refine ⟨?_, ih entrants distinct.2 fresh restApart⟩
      intro entry member named same equal
      cases same
      rcases fillVacant_mem rest entrants entry member with inside | ⟨entrant, isEntrant, placed⟩
      · exact distinct.1 entry inside held rfl equal
      · rw [equal] at placed
        cases placed
        exact apart held isEntrant (by simp)
    | none =>
      cases entrants with
      | nil =>
        simp only [fillVacant]
        rw [List.pairwise_cons]
        refine ⟨?_, ih [] distinct.2 fresh restApart⟩
        intro entry _ named same
        cases same
      | cons entrant others =>
        simp only [fillVacant]
        rw [List.pairwise_cons]
        have parts := List.nodup_cons.mp fresh
        refine ⟨?_, ih others distinct.2 parts.2
          (fun other member => restApart other (List.mem_cons_of_mem _ member))⟩
        intro entry member named same equal
        cases same
        rcases fillVacant_mem rest others entry member with inside | ⟨other, isOther, placed⟩
        · exact restApart entrant (by simp) (equal ▸ inside)
        · rw [equal] at placed
          cases placed
          exact parts.1 isOther

/-- A kept entry is the entry it was. -/
theorem kept_source {α : Type} (keep : α → Bool) (entry : Option α) (slot : α)
    (kept : entry.filter keep = some slot) : entry = some slot := by
  cases entry with
  | none => simp at kept
  | some held =>
    simp only [Option.filter] at kept
    split at kept
    · exact kept
    · cases kept

/-- Position-stable merge of held slots with a ranking: a held slot that is still
ranked keeps its position, and every other position takes the next ranked slot that
no position holds, in rank order, or becomes vacant. -/
def mergeSlots {α : Type} [BEq α] (held : List (Option α)) (order : List α) : List (Option α) :=
  fillVacant (held.map fun slot => slot.filter fun feature => order.contains feature)
    (order.filter fun feature => !held.contains (some feature))

/-- Merging changes no position count. -/
theorem mergeSlots_length {α : Type} [BEq α] (held : List (Option α)) (order : List α) :
    (mergeSlots held order).length = held.length := by
  simp [mergeSlots, fillVacant_length]

/-- Merging distinct held slots with a ranking of distinct slots keeps them distinct. -/
theorem mergeSlots_distinct {α : Type} [BEq α] [LawfulBEq α] (held : List (Option α))
    (order : List α) (distinct : held.Pairwise SlotsDistinct) (fresh : order.Nodup) :
    (mergeSlots held order).Pairwise SlotsDistinct := by
  unfold mergeSlots
  apply fillVacant_distinct
  · refine distinct.map _ ?_
    intro first second apart slot kept equal
    exact apart slot (kept_source _ first slot kept) (kept_source _ second slot equal)
  · exact fresh.sublist List.filter_sublist
  · intro entrant member inside
    have absent := (List.mem_filter.mp member).2
    obtain ⟨original, isHeld, kept⟩ := List.mem_map.mp inside
    rw [kept_source _ original entrant kept] at isHeld
    simp [isHeld] at absent

/-- The slots after installing a ranking: the merge runs over every position but the
last, which stays vacant for the bias. -/
def RankedFeatures.merged (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension)) :
    Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity :=
  ⟨(mergeSlots ranked.slots.toList.dropLast order ++ [none]).toArray, by
    simpa [mergeSlots_length] using Nat.sub_add_cancel (rankDimension dimension).positive⟩

/-- The merge leaves the last position vacant. -/
theorem RankedFeatures.merged_reserved (ranked : RankedFeatures dimension)
    (order : List (FeatIdx dimension)) :
    (ranked.merged order)[(rankDimension dimension).capacity - 1]'(Nat.sub_lt
      (rankDimension dimension).positive (by decide)) = none := by
  have length : (mergeSlots ranked.slots.toList.dropLast order).length =
      (rankDimension dimension).capacity - 1 := by
    simp [mergeSlots_length]
  simp [RankedFeatures.merged, ← length]

/-- The merge of a ranking of distinct slots holds no slot twice. -/
theorem RankedFeatures.merged_distinct (ranked : RankedFeatures dimension)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) :
    (ranked.merged order).toList.Pairwise SlotsDistinct := by
  have held : ranked.slots.toList.dropLast.Pairwise SlotsDistinct :=
    ranked.distinct.sublist (List.dropLast_sublist _)
  have merge := mergeSlots_distinct ranked.slots.toList.dropLast order held fresh
  change (mergeSlots ranked.slots.toList.dropLast order ++ [none]).Pairwise SlotsDistinct
  rw [List.pairwise_append]
  refine ⟨merge, by simp, ?_⟩
  intro first _ second last slot _ equal
  rw [List.mem_singleton.mp last] at equal
  cases equal

/-- Install a ranking of distinct slots, keeping the position of every slot that stays
ranked. A ranking that changes no position returns the receiver, so the lookup table is
rebuilt only when a slot enters or leaves. -/
def RankedFeatures.rerank (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension))
    (fresh : order.Nodup) : RankedFeatures dimension :=
  if ranked.merged order = ranked.slots then ranked
  else .ofSlots (ranked.merged order) (ranked.merged_reserved order)
    (ranked.merged_distinct order fresh)

/-- Whether or not a position changed, the slots after a ranking are the merge. -/
theorem RankedFeatures.rerank_slots (ranked : RankedFeatures dimension)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) :
    (ranked.rerank order fresh).slots = ranked.merged order := by
  unfold RankedFeatures.rerank
  split
  · rename_i same
    exact same.symm
  · rfl

/-- Every position that holds a slot, in position order. -/
def RankedFeatures.holding (ranked : RankedFeatures dimension) (feature : FeatIdx dimension) :
    List (RankIdx dimension) :=
  (List.finRange (rankDimension dimension).capacity).filter fun position =>
    ranked.slots[position.val] == some feature

/-- Clear the given positions of a slot vector. -/
def clearSlots {dimension : Dimension}
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity)
    (positions : List (RankIdx dimension)) :
    Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity :=
  positions.foldl (fun current position => current.set position.val none position.isLt) slots

/-- A cleared position is vacant and every other position keeps its slot. -/
theorem clearSlots_get {dimension : Dimension}
    (positions : List (RankIdx dimension)) :
    ∀ (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity)
      (position : RankIdx dimension),
      (clearSlots slots positions)[position.val] =
        if position ∈ positions then none else slots[position.val] := by
  induction positions with
  | nil => intro slots position; simp [clearSlots]
  | cons head rest ih =>
    intro slots position
    have step := ih (slots.set head.val none head.isLt) position
    simp only [clearSlots, List.foldl_cons] at step ⊢
    rw [step]
    by_cases later : position ∈ rest
    · simp [later]
    · by_cases same : position = head
      · subst same
        simp [later]
      · have different : head.val ≠ position.val := fun equal => same (Fin.ext equal.symm)
        simp [later, same, Vector.getElem_set_ne _ _ different]

/-- Vacate positions: their slots are no longer modeled. -/
def RankedFeatures.vacate (ranked : RankedFeatures dimension)
    (positions : List (RankIdx dimension)) : RankedFeatures dimension :=
  .ofSlots (clearSlots ranked.slots positions) (by
    have cleared := clearSlots_get positions ranked.slots (RankedFeatures.bias dimension)
    have vacant := ranked.reserved
    change (clearSlots ranked.slots positions)[(RankedFeatures.bias dimension).val] = none
    rw [cleared]
    split
    · rfl
    · exact vacant) (by
    apply index_distinct
    intro first second slot left right
    rw [clearSlots_get positions ranked.slots first] at left
    rw [clearSlots_get positions ranked.slots second] at right
    split at left
    · cases left
    · split at right
      · cases right
      · exact ranked.slot_unique first second slot left right)

/-- After vacating every position that holds a slot, no position holds it. -/
theorem RankedFeatures.vacate_holding (ranked : RankedFeatures dimension)
    (feature : FeatIdx dimension) (position : RankIdx dimension) :
    (ranked.vacate (ranked.holding feature)).slots[position.val] ≠ some feature := by
  have cleared := clearSlots_get (ranked.holding feature) ranked.slots position
  change (clearSlots ranked.slots (ranked.holding feature))[position.val] ≠ some feature
  rw [cleared]
  split
  · simp
  · rename_i absent
    intro held
    exact absent (List.mem_filter.mpr ⟨List.mem_finRange position, by simp [held]⟩)

/-- Positions whose slot differs between two rankings: the rows and input columns
whose learned weights describe a slot that is no longer there. -/
def RankedFeatures.changed (before after : RankedFeatures dimension) : List (RankIdx dimension) :=
  (List.finRange (rankDimension dimension).capacity).filter fun position =>
    after.slots[position.val] != before.slots[position.val]

end Acorn.Features
