/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.FeatureLifecycle

/-!
# Assignment refresh at the free dispatch boundary

Ranked assignments use the actual stored Demon-0 weights. Objective identity is
the selected unit: a slot whose unit is still ranked keeps its policy, model,
prediction cache, meta-controller row and held bonus bit-identical, and only a
slot whose unit left the ranking is reinstalled. An ending activation retains
the replaced owner for terminal credit. The activation payload is parametric:
refresh neither reads nor rewrites it. Continuing activations do not inhabit
this free-boundary interface.
-/
namespace Acorn.Features

/-- Coalesced requests separate process-local cycles from durable pending work. -/
structure Refresh where
  /-- Largest process cycle observed. -/
  cycle : UInt64
  /-- Unconsumed ranking work. -/
  pending : Bool
  deriving DecidableEq

/-- Cold restoration preserves work and resets the process-local cycle key. -/
def Refresh.cold (pending : Bool) : Refresh := ⟨0, pending⟩

/-- Achievements and newer cycles coalesce without acknowledging prior work. -/
def Refresh.request (state : Refresh) (cycle : UInt64) (achieved : Bool) : Refresh :=
  ⟨max state.cycle cycle, state.pending || achieved || decide (state.cycle < cycle)⟩

/-- Taking work clears only the pending flag. -/
def Refresh.take (state : Refresh) : Bool × Refresh := (state.pending, { state with pending := false })

/-- Any outstanding request survives every additional request. -/
theorem Refresh.request_preserves_pending (state : Refresh) (cycle : UInt64) (achieved : Bool)
    (pending : state.pending = true) : (state.request cycle achieved).pending = true := by
  simp [Refresh.request, pending]

/-- Request coalescing has the exact disjunctive event semantics. -/
theorem Refresh.request_pending (state : Refresh) (cycle : UInt64) (achieved : Bool) :
    (state.request cycle achieved).pending = true ↔
      state.pending = true ∨ achieved = true ∨ state.cycle < cycle := by
  simp [Refresh.request, or_assoc]

/-- Acknowledgement is idempotent and retains the cycle key. -/
theorem Refresh.take_once (state : Refresh) :
    state.take.2.take.1 = false ∧ state.take.2.cycle = state.cycle := ⟨rfl, rfl⟩

/-- Raw process-local model prediction words. Their producer's numeric theorems
are separate from these lifecycle operations, which hold for arbitrary words. -/
structure ModelCache where
  /-- Cached reward estimate. -/
  reward : Binary32
  /-- Cached continuation estimate. -/
  continuation : Binary32
  /-- Cached duration estimate. -/
  duration : Binary32
  deriving DecidableEq

/-- Current fresh model cache: zero reward/continuation and one-step duration. -/
def ModelCache.initial : ModelCache := ⟨.zero, .zero, .one⟩

/-- An ending activation's payload travels with its original learner owner. -/
structure Closing (config : Config) (criterion : Criterion) (dimension : Dimension)
    (payload : Type) where
  /-- Table slot that owned the ending activation. -/
  slot : Fin Acorn.FeatureConstants.skillCount
  /-- Uninterpreted activation and terminal-reason state. -/
  activation : payload
  /-- Detached owner when refresh replaces that slot before terminal credit. -/
  oldOwner : Option (Skill config criterion dimension)

/-- Complete state changed by ranking, admitted only at a free dispatch boundary.
Unchanged temporal caches can be carried by the surrounding dispatcher without
being mistaken for encodings of the new projection bank. -/
structure FreeDispatch (shape : PatchShape) (config : Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) (payload : Type) where
  /-- Receiver-owned representation and all consumers, with Demon 0 fixed to G99. -/
  lifecycle : Lifecycle shape config criterion dimension (.g99 :: discounts)
  /-- Coalesced ranking work. -/
  refresh : Refresh
  /-- Exactly one current model prediction per option table slot. -/
  predictions : Vector ModelCache Acorn.FeatureConstants.skillCount
  /-- Optional ending activation awaiting its remaining terminal credit. -/
  closing : Option (Closing config criterion dimension payload)

/-- Meta action zero delegates to primitives; subsequent actions name skills. -/
def metaOfSkill (slot : Fin Acorn.FeatureConstants.skillCount) :
    Fin Acorn.FeatureConstants.metaActionCount :=
  ⟨slot.val + 1, by have := slot.isLt; simp [Acorn.FeatureConstants.skillCount,
    Acorn.FeatureConstants.metaActionCount] at *; omega⟩

/-- Learned identity compares selected units; declared targets always require replacement. -/
def Interest.sameAssignment {config : Config} (interest : Interest config)
    (target : Assignment config) : Bool :=
  match interest with
  | .learned prior => prior.same target
  | .declared _ _ => false

/-- Matching a target is equality of learned unit identity, never of its bonus or slot. -/
theorem Interest.sameAssignment_iff {config : Config} (interest : Interest config)
    (target : Assignment config) : interest.sameAssignment target = true ↔
      ∃ prior, interest = .learned prior ∧ prior.identity = target.identity := by
  cases interest <;> simp [Interest.sameAssignment, Assignment.same_iff]

/-- The learned objective a slot holds; a declared choice holds none. -/
def Interest.held {config : Config} : Interest config → Assignment config
  | .learned assignment => assignment
  | .declared _ _ => .neutral

/-- A target that equals the held objective whenever their identities match leaves
no unchanged slot with a different stored objective. -/
theorem Interest.compatible {config : Config} (interest : Interest config)
    (target : Assignment config)
    (exactWhenSame : interest.held.same target = true → target = interest.held) :
    interest.sameAssignment target = true → interest = .learned target := by
  cases interest with
  | learned prior =>
    intro same
    exact congrArg Interest.learned (exactWhenSame same).symm
  | declared origin tag =>
    intro same
    simp [Interest.sameAssignment] at same

/-- A slot whose unit changed atomically receives its target, fresh policy/model and fresh
cache. The closing payload is retained, with the original owner detached at the same write. -/
def FreeDispatch.install {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    FreeDispatch shape config criterion dimension discounts payload :=
  let previous := state.lifecycle.consumers.skills[slot.val]
  if previous.interest.sameAssignment target then state else
    { state with
      lifecycle := { state.lifecycle with consumers := { state.lifecycle.consumers with
        skills := state.lifecycle.consumers.skills.set slot.val
          (Skill.initial config criterion dimension (.learned target)) slot.isLt
        metaController := state.lifecycle.consumers.metaController.resetAction (metaOfSkill slot) } }
      predictions := state.predictions.set slot.val ModelCache.initial slot.isLt
      closing := state.closing.map fun ending =>
        if ending.slot == slot then
          { ending with oldOwner := some (ending.oldOwner.getD previous) } else ending }

/-- Demon 0 is selected structurally from its immutable horizon-indexed bank. -/
def DemonBank.rankingWeights {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension (.g99 :: discounts)) : WeightArray (.discounted .g99) dimension :=
  match bank with | .cons learner _ => learner.state.weights

/-- Consume one coalesced request and install the slot-stable ranking in slot order. -/
def FreeDispatch.refreshRanked {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    FreeDispatch shape config criterion dimension discounts payload :=
  let (pending, refresh) := state.refresh.take
  let state := { state with refresh }
  if pending then
    let targets := rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
      (state.lifecycle.consumers.skills.map (·.interest.held))
    (List.finRange Acorn.FeatureConstants.skillCount).foldl
      (fun current slot => current.install slot targets[slot.val]) state
  else state

/-- Unchanged unit identity prevents any learner, cache or pending-credit mutation. -/
theorem FreeDispatch.install_same {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (same : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = true) :
    state.install slot target = state := by
  simp [FreeDispatch.install, same]

/-- A changed unit identity clears its cache at the write boundary. -/
theorem FreeDispatch.install_cache {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (changed : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = false) :
    (state.install slot target).predictions[slot.val] = ModelCache.initial := by
  simp [FreeDispatch.install, changed]

/-- A compatible target is installed exactly, including the unchanged branch. -/
theorem FreeDispatch.install_target {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (compatible : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = true →
      state.lifecycle.consumers.skills[slot.val].interest = .learned target) :
    (state.install slot target).lifecycle.consumers.skills[slot.val].interest = .learned target := by
  cases same : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target with
  | false => simp [FreeDispatch.install, same, Skill.initial]
  | true =>
    rw [FreeDispatch.install_same state slot target same]
    exact compatible same

/-- A closing slot keeps its first detached learner across every further replacement;
when no owner is detached yet, the current table learner becomes that owner. -/
theorem FreeDispatch.install_closing_owner {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (ending : Closing config criterion dimension payload) (closing : state.closing = some ending)
    (owns : ending.slot = slot)
    (changed : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = false) :
    (state.install slot target).closing =
      some { ending with
        oldOwner := some (ending.oldOwner.getD state.lifecycle.consumers.skills[slot.val]) } := by
  simp [FreeDispatch.install, changed, closing, owns]

/-- Once terminal credit has an owner, even repeated installation at the same
slot cannot replace it with a learner belonging to a later objective. -/
theorem FreeDispatch.install_retains_owner {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (ending : Closing config criterion dimension payload) (closing : state.closing = some ending)
    (owner : Skill config criterion dimension) (detached : ending.oldOwner = some owner) :
    (state.install slot target).closing = some ending := by
  simp only [FreeDispatch.install]
  split
  · exact closing
  · simp only [closing, Option.map_some]
    split
    · simp only [detached, Option.getD_some]
      congr 1
      cases ending
      simp_all
    · rfl

/-- Installation preserves the projection/history owner regardless of target identity. -/
theorem FreeDispatch.install_representation {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (state.install slot target).lifecycle.representation = state.lifecycle.representation := by
  simp only [FreeDispatch.install]
  split <;> rfl

/-- Updating one option cannot mutate another option or its cached model values. -/
theorem FreeDispatch.install_other {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot other : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (different : other ≠ slot) :
    (state.install slot target).lifecycle.consumers.skills[other.val] =
        state.lifecycle.consumers.skills[other.val] ∧
      (state.install slot target).predictions[other.val] = state.predictions[other.val] := by
  have values : other.val ≠ slot.val := fun equal => different (Fin.ext equal)
  simp only [FreeDispatch.install]
  split
  · exact ⟨rfl, rfl⟩
  · simp [Ne.symm values]

/-- Installing targets cannot consume another refresh, change ranking weights,
or alter primitive-controller storage. -/
theorem FreeDispatch.install_preserves {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (state.install slot target).refresh = state.refresh ∧
      (state.install slot target).lifecycle.consumers.demons = state.lifecycle.consumers.demons ∧
      (state.install slot target).lifecycle.consumers.control = state.lifecycle.consumers.control := by
  simp only [FreeDispatch.install]
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The actual installation fold preserves its representation and refresh owner. -/
theorem FreeDispatch.fold_preserves {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    let result := slots.foldl (fun current slot => current.install slot targets[slot.val]) state
    result.refresh = state.refresh ∧ result.lifecycle.representation = state.lifecycle.representation := by
  induction slots generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons slot rest ih =>
    have rest := ih (state.install slot targets[slot.val])
    exact ⟨rest.1.trans (state.install_preserves slot targets[slot.val]).1,
      rest.2.trans (state.install_representation slot targets[slot.val])⟩

/-- Installing a compatible vector preserves targets already installed and
establishes every target named by the fold, for arbitrary slot order and aliases. -/
theorem FreeDispatch.fold_target {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (compatible : ∀ index : Fin Acorn.FeatureConstants.skillCount,
      state.lifecycle.consumers.skills[index.val].interest.sameAssignment targets[index.val] = true →
        state.lifecycle.consumers.skills[index.val].interest = .learned targets[index.val])
    (covered : slot ∈ slots ∨ state.lifecycle.consumers.skills[slot.val].interest = .learned targets[slot.val]) :
    (slots.foldl (fun current next => current.install next targets[next.val]) state).lifecycle.consumers.skills[slot.val].interest = .learned targets[slot.val] := by
  induction slots generalizing state with
  | nil => simpa using covered
  | cons next rest ih =>
    apply ih
    · intro index
      by_cases same : index = next
      · subst index
        intro _
        exact state.install_target next targets[next.val] (compatible next)
      · rw [(state.install_other next index targets[next.val] same).1]
        exact compatible index
    · by_cases same : slot = next
      · subst next
        exact Or.inr (state.install_target slot targets[slot.val] (compatible slot))
      · rcases covered with member | already
        · exact Or.inl ((List.mem_cons.mp member).resolve_left same)
        · exact Or.inr (by rw [(state.install_other next slot targets[next.val] same).1]; exact already)

/-- Installing one slot cannot mutate another slot's meta-controller row. -/
theorem FreeDispatch.install_meta_other {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot other : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (different : other ≠ slot) :
    (state.install slot target).lifecycle.consumers.metaController.learners[(metaOfSkill other).val] =
      state.lifecycle.consumers.metaController.learners[(metaOfSkill other).val] := by
  have values : (metaOfSkill slot).val ≠ (metaOfSkill other).val := by
    intro equal
    exact different (Fin.ext (by simp only [metaOfSkill] at equal; omega))
  simp only [FreeDispatch.install]
  split
  · rfl
  · simp [Controller.resetAction, values]

/-- A slot already holding its target keeps its skill, cache and meta-controller row
bit-identical through the whole installation fold, for arbitrary slot order. -/
theorem FreeDispatch.fold_retains {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (keeps : state.lifecycle.consumers.skills[slot.val].interest = .learned targets[slot.val]) :
    (slots.foldl (fun current next => current.install next targets[next.val]) state).lifecycle.consumers.skills[slot.val] =
        state.lifecycle.consumers.skills[slot.val] ∧
      (slots.foldl (fun current next => current.install next targets[next.val]) state).predictions[slot.val] =
        state.predictions[slot.val] ∧
      (slots.foldl (fun current next => current.install next targets[next.val]) state).lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] =
        state.lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] := by
  induction slots generalizing state with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons next rest ih =>
    simp only [List.foldl_cons]
    by_cases same : next = slot
    · subst next
      have unchanged : state.install slot targets[slot.val] = state :=
        state.install_same slot targets[slot.val]
          (by rw [keeps]; exact Assignment.same_refl targets[slot.val])
      simp only [unchanged]
      exact ih state keeps
    · have other := state.install_other next slot targets[next.val] (Ne.symm same)
      have row := state.install_meta_other next slot targets[next.val] (Ne.symm same)
      have after := ih (state.install next targets[next.val]) (by rw [other.1]; exact keeps)
      exact ⟨after.1.trans other.1, after.2.1.trans other.2, after.2.2.trans row⟩

/-- A free-boundary refresh acknowledges exactly the pending work and preserves
projection identity, whether or not that work required any target replacement. -/
theorem FreeDispatch.refresh_conserves {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    state.refreshRanked.refresh = state.refresh.take.2 ∧
      state.refreshRanked.lifecycle.representation = state.lifecycle.representation := by
  by_cases pending : state.refresh.pending = true
  · simp only [FreeDispatch.refreshRanked, Refresh.take, pending, ↓reduceIte]
    exact FreeDispatch.fold_preserves _ _ _
  · simp [FreeDispatch.refreshRanked, Refresh.take, pending]

/-- Every option receives the slot-stable ranking computed from this receiver's
actual Demon-0 words and its held objectives. -/
theorem FreeDispatch.refresh_targets {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (pending : state.refresh.pending = true) (slot : Fin Acorn.FeatureConstants.skillCount) :
    state.refreshRanked.lifecycle.consumers.skills[slot.val].interest =
      .learned (rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
        (state.lifecycle.consumers.skills.map (·.interest.held)))[slot.val] := by
  simp only [FreeDispatch.refreshRanked, Refresh.take, pending, ↓reduceIte]
  apply FreeDispatch.fold_target
  · intro index
    apply Interest.compatible
    show (state.lifecycle.consumers.skills[index.val].interest.held.same
        (rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
          (state.lifecycle.consumers.skills.map (·.interest.held)))[index.val] = true →
      (rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
          (state.lifecycle.consumers.skills.map (·.interest.held)))[index.val] =
        state.lifecycle.consumers.skills[index.val].interest.held)
    have held : (state.lifecycle.consumers.skills.map (·.interest.held))[index.val] =
        state.lifecycle.consumers.skills[index.val].interest.held := by simp
    rw [← held]
    exact rankAssignments_same dimension config _ _ index
  · exact Or.inl (List.mem_finRange slot)

/-- T1: for every state and Demon-0 weight array, a slot whose unit is still ranked
keeps its policy, model, cached prediction and meta-controller row bit-identical. -/
theorem FreeDispatch.refresh_retains {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count) (bonus : Bonus)
    (holds : state.lifecycle.consumers.skills[slot.val].interest = .learned (.selected unit bonus))
    (ranked : unit ∈ (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).map (·.unit)) :
    state.refreshRanked.lifecycle.consumers.skills[slot.val] =
        state.lifecycle.consumers.skills[slot.val] ∧
      state.refreshRanked.predictions[slot.val] = state.predictions[slot.val] ∧
      state.refreshRanked.lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] =
        state.lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] := by
  by_cases pending : state.refresh.pending = true
  · simp only [FreeDispatch.refreshRanked, Refresh.take, pending, ↓reduceIte]
    apply FreeDispatch.fold_retains
    show state.lifecycle.consumers.skills[slot.val].interest =
      .learned (rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
        (state.lifecycle.consumers.skills.map (·.interest.held)))[slot.val]
    have held : (state.lifecycle.consumers.skills.map (·.interest.held))[slot.val] =
        .selected unit bonus := by simp [holds, Interest.held]
    have retained : Assignment.retained
        (rankedCandidates dimension config state.lifecycle.consumers.demons.rankingWeights)
        (state.lifecycle.consumers.skills.map
          (fun skill : Skill config criterion dimension => skill.interest.held))[slot.val] =
          true := by
      obtain ⟨candidate, member, named⟩ := List.mem_map.mp ranked
      rw [held]
      exact List.any_eq_true.mpr ⟨candidate, member, by simp [Assignment.holds, named]⟩
    rw [rankAssignments_retained dimension config _ _ slot retained, held]
    exact holds
  · simp [FreeDispatch.refreshRanked, Refresh.take, pending]

end Acorn.Features
