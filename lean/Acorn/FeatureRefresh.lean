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
the selected unit: the first slot holding a still-ranked unit keeps its policy,
model, prediction cache and meta-controller row bit-identical while its held bonus
can only rise; every other slot takes the next entrant or the neutral objective and
is reinstalled when its unit changes. No two slots hold the same unit. Retirement
releases a slot holding the replaced unit only at a free boundary. An ending
activation retains the replaced owner for terminal credit. The activation payload
is parametric: refresh neither reads nor rewrites it. Continuing activations do
not inhabit this free-boundary interface.

The assignment refresh runs at every free boundary and reads no host event (Sutton,
Bowling and Pilarski, *The Alberta Plan for AI Research*, arXiv:2208.11173v3 (2023),
p. 2: the meta-algorithms for constructing subtasks "operate on every time step").
After it the slots hold exactly the units of the ranked candidates
(`refresh_covers`, `refresh_ranked`): as many slots hold a unit as the ranking has
candidates (`refresh_occupancy`), and all do once it has one for each (`refresh_full`).
The refresh reads the Demon-0 weights as they stand when it runs. The full agent runs
it during selection, before the reward delivered with that decision is learned, so a
candidate that reward creates is installed at the next free dispatch
(`TemporalControl.select_assigns`).

The same ranking decides which feature slots every option's expectation model
reads and predicts (Sutton, Bowling and Pilarski, *The Alberta Plan for AI Research*,
arXiv:2208.11173v3 (2023), Step 8(d), p. 9): the ranked score blocks of positive
Demon-0 weight, one fewer than the ranked width, of which the first `skillCount` are
the subtask candidates. Every free boundary installs it in every model, after the
assignments; a slot that stays ranked keeps its position, its row and that row's
weights from every other retained slot.
-/
namespace Acorn.Features

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
    (discounts : List Discount) (payload : Type) where
  /-- Table slot that owned the ending activation. -/
  slot : Fin Acorn.FeatureConstants.skillCount
  /-- Uninterpreted activation and terminal-reason state. -/
  activation : payload
  /-- Detached owner when refresh replaces that slot before terminal credit. -/
  oldOwner : Option (Skill config criterion dimension discounts)

/-- Complete state changed by ranking, admitted only at a free dispatch boundary.
Unchanged temporal caches can be carried by the surrounding dispatcher without
being mistaken for encodings of the new projection bank. -/
structure FreeDispatch (shape : PatchShape) (config : Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) (payload : Type) where
  /-- Receiver-owned representation and all consumers, with Demon 0 fixed to G99. -/
  lifecycle : Lifecycle shape config criterion dimension (.g99 :: discounts)
  /-- Exactly one current model prediction per option table slot. -/
  predictions : Vector ModelCache Acorn.FeatureConstants.skillCount
  /-- Optional ending activation awaiting its remaining terminal credit. -/
  closing : Option (Closing config criterion dimension (.g99 :: discounts) payload)

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

/-- A slot whose unit is unchanged receives its target objective, including a raised
held bonus, and keeps its policy, model, cache and meta-controller row. A slot whose
unit changed atomically receives its target, fresh policy/model, a reset
meta-controller row and fresh cache. The closing payload is retained, with the
original owner detached at the same write. -/
def FreeDispatch.install {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    FreeDispatch shape config criterion dimension discounts payload :=
  let previous := state.lifecycle.consumers.skills[slot.val]
  if previous.interest.sameAssignment target then
    { state with
      lifecycle := { state.lifecycle with consumers := { state.lifecycle.consumers with
        skills := state.lifecycle.consumers.skills.set slot.val
          { previous with interest := .learned target } slot.isLt } } }
  else
    { state with
      lifecycle := { state.lifecycle with consumers := { state.lifecycle.consumers with
        skills := state.lifecycle.consumers.skills.set slot.val
          (Skill.initial config criterion dimension (.learned target)) slot.isLt
        metaController := state.lifecycle.consumers.metaController.resetAction (metaOfSkill slot) } }
      predictions := state.predictions.set slot.val ModelCache.initial slot.isLt
      closing := state.closing.map fun ending =>
        if ending.slot == slot then
          { ending with oldOwner := some (ending.oldOwner.getD previous) } else ending }

/-- Release every slot holding a replaced unit: it receives the neutral objective with
fresh policy and model and a reset meta-controller row, and the next free boundary
installs its entrant. -/
def Ensemble.release {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (unit : Fin config.units.count) : Ensemble config criterion dimension discounts :=
  { ensemble with
    skills := ensemble.skills.map fun skill =>
      if skill.interest.held.holds unit then Skill.initial config criterion dimension (.learned .neutral)
      else skill
    metaController := (List.finRange Acorn.FeatureConstants.skillCount).foldl (fun controller slot =>
      if ensemble.skills[slot.val].interest.held.holds unit then
        controller.resetAction (metaOfSkill slot)
      else controller) ensemble.metaController }

/-- After release, no slot holds the released unit. -/
theorem Ensemble.release_holds {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (unit : Fin config.units.count) (slot : Fin Acorn.FeatureConstants.skillCount) :
    (ensemble.release unit).skills[slot.val].interest.held.holds unit = false := by
  simp only [Ensemble.release, Vector.getElem_map]
  split
  · rfl
  · simp_all

/-- Releasing a unit no slot holds changes nothing. -/
theorem Ensemble.release_unheld {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (unit : Fin config.units.count) (unheld : ensemble.holds unit = false) :
    ensemble.release unit = ensemble := by
  have fresh (slot : Fin Acorn.FeatureConstants.skillCount) :
      ensemble.skills[slot.val].interest.held.holds unit = false := by
    have absent := List.any_eq_false.mp unheld ensemble.skills[slot.val] (by simp)
    simpa using absent
  have skills : ensemble.skills.map (fun skill =>
      if skill.interest.held.holds unit then Skill.initial config criterion dimension (.learned .neutral)
      else skill) = ensemble.skills := by
    ext index bound
    simp [fresh ⟨index, bound⟩]
  have rows (slots : List (Fin Acorn.FeatureConstants.skillCount)) :
      slots.foldl (fun controller slot =>
        if ensemble.skills[slot.val].interest.held.holds unit then
          controller.resetAction (metaOfSkill slot)
        else controller) ensemble.metaController = ensemble.metaController := by
    induction slots with
    | nil => rfl
    | cons slot rest ih =>
      simp only [List.foldl_cons, fresh slot, Bool.false_eq_true, ↓reduceIte]
      exact ih
  simp only [Ensemble.release, skills, rows]

/-- No two slots hold the same learned unit. -/
def Ensemble.Distinct {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts) : Prop :=
  Assignment.Distinct (ensemble.skills.map (·.interest.held))

/-- Feature retirement keeps every objective, so it keeps distinct held units. -/
theorem Ensemble.retire_distinct {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (feature : FeatIdx dimension) (distinct : ensemble.Distinct) : (ensemble.retire feature).Distinct := by
  apply Assignment.Distinct.mono distinct
  intro slot unit named
  simpa [Ensemble.retire, Skill.retire] using named

/-- Release only clears objectives, so it keeps distinct held units. -/
theorem Ensemble.release_distinct {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (unit : Fin config.units.count) (distinct : ensemble.Distinct) : (ensemble.release unit).Distinct := by
  apply Assignment.Distinct.mono distinct
  intro slot named held
  simp only [Ensemble.release, Vector.getElem_map] at held ⊢
  split at held
  · simp [Skill.initial, Interest.held, Assignment.identity] at held
  · exact held

/-- Demon 0 is selected structurally from its immutable horizon-indexed bank. -/
def DemonBank.rankingWeights {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension (.g99 :: discounts)) : WeightArray (.discounted .g99) dimension :=
  match bank with | .cons learner _ => learner.state.weights

/-- Install the slot-stable ranking of the current Demon-0 weights in slot order. -/
def FreeDispatch.refreshRanked {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    FreeDispatch shape config criterion dimension discounts payload :=
  let targets := rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
    (state.lifecycle.consumers.skills.map (·.interest.held))
  (List.finRange Acorn.FeatureConstants.skillCount).foldl
    (fun current slot => current.install slot targets[slot.val]) state

/-- The feature slots an expectation model reads and predicts: the slot of each
ranked score block of positive Demon-0 weight, in rank order, at most one fewer than
the ranked width because the last position is the bias. The slots are distinct
(`rankedSlots_nodup`). -/
def rankedSlots (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) : List (FeatIdx dimension) :=
  (ranked ((rankDimension dimension).capacity - 1)
    ((List.finRange config.units.count).filterMap (candidateOfWeight config weights))).map
    fun candidate => unitFeature dimension config candidate.unit

/-- A candidate's key is the weight word at its own slot. -/
theorem candidateOfWeight_key (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) (unit : Fin config.units.count)
    (candidate : Candidate config) (found : candidateOfWeight config weights unit = some candidate) :
    candidate.key = (weights.get (unitFeature dimension config candidate.unit)).value.bits.toNat := by
  unfold candidateOfWeight at found
  dsimp only at found
  split at found
  · cases found
    rfl
  · contradiction

/-- The ranked slots are distinct: ranked score blocks have strictly decreasing keys,
and a candidate's key is the weight word at its slot, so two candidates at one slot
would have one key. -/
theorem rankedSlots_nodup (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    (rankedSlots dimension config weights).Nodup := by
  unfold rankedSlots
  rw [List.Nodup, List.pairwise_map]
  refine (ranked_strict _ _).imp_of_mem ?_
  intro first second left right lower same
  obtain ⟨_, _, foundLeft⟩ := List.mem_filterMap.mp (ranked_subset _ _ first left)
  obtain ⟨_, _, foundRight⟩ := List.mem_filterMap.mp (ranked_subset _ _ second right)
  rw [candidateOfWeight_key dimension config weights _ first foundLeft,
    candidateOfWeight_key dimension config weights _ second foundRight, same] at lower
  exact Nat.lt_irrefl _ lower

/-- The work and result bound of the model ranking is the ranked width less the bias. -/
theorem rankedSlots_length (dimension : Dimension) (config : Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    (rankedSlots dimension config weights).length ≤ (rankDimension dimension).capacity - 1 := by
  simpa [rankedSlots] using ranked_length ((rankDimension dimension).capacity - 1)
    ((List.finRange config.units.count).filterMap (candidateOfWeight config weights))

/-- Install the current feature ranking in every option's expectation model. Only the
transition parts change; objectives, policies and full-width model learners are kept. -/
def FreeDispatch.rerankModels {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    FreeDispatch shape config criterion dimension discounts payload :=
  let order := rankedSlots dimension config state.lifecycle.consumers.demons.rankingWeights
  { state with lifecycle := { state.lifecycle with consumers := { state.lifecycle.consumers with
      skills := state.lifecycle.consumers.skills.map fun skill =>
        { skill with model := skill.model.rerank order (rankedSlots_nodup dimension config
          state.lifecycle.consumers.demons.rankingWeights) } } } }

/-- The complete free-boundary refresh: install the slot-stable assignment ranking
when the caller's subtasks are the ranked ones, then install the current feature
ranking in every option model. Both run at every free boundary, so neither waits for
an event that can precede the first reward. A caller with declared subtasks passes
`assign := false` and keeps them. Both merges are stable: a unit that stays ranked
keeps its slot, and a slot that stays ranked keeps its row. -/
def FreeDispatch.refreshModels {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) (assign : Bool) :
    FreeDispatch shape config criterion dimension discounts payload :=
  (if assign then state.refreshRanked else state).rerankModels

/-- The assigning refresh installs the assignment ranking, then the model ranking. -/
theorem FreeDispatch.refreshModels_assign {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    state.refreshModels true = state.refreshRanked.rerankModels := rfl

/-- The refresh of declared subtasks installs the model ranking only. -/
theorem FreeDispatch.refreshModels_keep {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    state.refreshModels false = state.rerankModels := rfl

/-- Reranking the models keeps the cache, closing owner, representation and every
non-skill consumer. `rerankModels_skill` gives each slot's objective, policy and
trajectory link. -/
theorem FreeDispatch.rerankModels_preserves {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    state.rerankModels.predictions = state.predictions ∧
      state.rerankModels.closing = state.closing ∧
      state.rerankModels.lifecycle.representation = state.lifecycle.representation ∧
      state.rerankModels.lifecycle.consumers.metaController =
        state.lifecycle.consumers.metaController ∧
      state.rerankModels.lifecycle.consumers.control = state.lifecycle.consumers.control ∧
      state.rerankModels.lifecycle.consumers.demons = state.lifecycle.consumers.demons :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reranking the models writes each slot's model and nothing else of the slot: the
model is the slot's own model reranked with the receiver's current ranking. -/
theorem FreeDispatch.rerankModels_skill {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    state.rerankModels.lifecycle.consumers.skills[slot.val] =
      { state.lifecycle.consumers.skills[slot.val] with
        model := state.lifecycle.consumers.skills[slot.val].model.rerank
          (rankedSlots dimension config state.lifecycle.consumers.demons.rankingWeights)
          (rankedSlots_nodup dimension config
            state.lifecycle.consumers.demons.rankingWeights) } := by
  simp [FreeDispatch.rerankModels]

/-- Reranking the models keeps distinct held units. -/
theorem FreeDispatch.rerankModels_distinct {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (distinct : state.lifecycle.consumers.Distinct) :
    state.rerankModels.lifecycle.consumers.Distinct := by
  apply Assignment.Distinct.mono distinct
  intro slot unit named
  simpa [FreeDispatch.rerankModels] using named

/-- Unchanged unit identity writes only the target objective: no learner, cache,
meta-controller row or pending-credit mutation. -/
theorem FreeDispatch.install_same {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (same : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = true) :
    (state.install slot target).lifecycle.consumers.skills[slot.val] =
        { state.lifecycle.consumers.skills[slot.val] with interest := .learned target } ∧
      (state.install slot target).predictions = state.predictions ∧
      (state.install slot target).lifecycle.consumers.metaController =
        state.lifecycle.consumers.metaController ∧
      (state.install slot target).closing = state.closing := by
  simp [FreeDispatch.install, same]

/-- A changed unit identity clears its cache at the write boundary. -/
theorem FreeDispatch.install_cache {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (changed : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = false) :
    (state.install slot target).predictions[slot.val] = ModelCache.initial := by
  simp [FreeDispatch.install, changed]

/-- A changed unit identity starts with no stored off-policy trajectory. -/
theorem FreeDispatch.install_unlinked {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (changed : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = false) :
    (state.install slot target).lifecycle.consumers.skills[slot.val].following = none := by
  simp [FreeDispatch.install, changed, Skill.initial]

/-- A changed unit identity asks its questions afresh. -/
theorem FreeDispatch.install_questions {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (changed : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = false) :
    (state.install slot target).lifecycle.consumers.skills[slot.val].questions =
      OptionQuestions.initial dimension (.g99 :: discounts) := by
  simp [FreeDispatch.install, changed, Skill.initial]

/-- A released slot asks its questions afresh. -/
theorem Ensemble.release_questions {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble config criterion dimension discounts)
    (unit : Fin config.units.count) (slot : Fin Acorn.FeatureConstants.skillCount)
    (held : ensemble.skills[slot.val].interest.held.holds unit = true) :
    (ensemble.release unit).skills[slot.val].questions = OptionQuestions.initial dimension discounts := by
  simp [Ensemble.release, held, Skill.initial]

/-- A released slot starts with no stored off-policy trajectory. -/
theorem Ensemble.release_unlinked {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (unit : Fin config.units.count) (slot : Fin Acorn.FeatureConstants.skillCount)
    (held : ensemble.skills[slot.val].interest.held.holds unit = true) :
    (ensemble.release unit).skills[slot.val].following = none := by
  simp [Ensemble.release, held, Skill.initial]

/-- Every installed slot has exactly its requested target, including the unchanged branch. -/
theorem FreeDispatch.install_target {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (state.install slot target).lifecycle.consumers.skills[slot.val].interest = .learned target := by
  cases same : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target with
  | false => simp [FreeDispatch.install, same, Skill.initial]
  | true => simp [FreeDispatch.install, same]

/-- A closing slot keeps its first detached learner across every further replacement;
when no owner is detached yet, the current table learner becomes that owner. -/
theorem FreeDispatch.install_closing_owner {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (ending : Closing config criterion dimension (.g99 :: discounts) payload) (closing : state.closing = some ending)
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
    (ending : Closing config criterion dimension (.g99 :: discounts) payload) (closing : state.closing = some ending)
    (owner : Skill config criterion dimension (.g99 :: discounts)) (detached : ending.oldOwner = some owner) :
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
  split <;> simp [Ne.symm values]

/-- Installing targets cannot change ranking weights or alter primitive-controller
storage. -/
theorem FreeDispatch.install_preserves {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (state.install slot target).lifecycle.consumers.demons = state.lifecycle.consumers.demons ∧
      (state.install slot target).lifecycle.consumers.control = state.lifecycle.consumers.control := by
  simp only [FreeDispatch.install]
  split <;> exact ⟨rfl, rfl⟩

/-- The actual installation fold preserves its representation owner. -/
theorem FreeDispatch.fold_preserves {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    (slots.foldl (fun current slot => current.install slot targets[slot.val])
      state).lifecycle.representation = state.lifecycle.representation := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot rest ih =>
    exact (ih (state.install slot targets[slot.val])).trans
      (state.install_representation slot targets[slot.val])

/-- The actual installation fold reads the Demon-0 weights and never writes a demon. -/
theorem FreeDispatch.fold_demons {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    (slots.foldl (fun current slot => current.install slot targets[slot.val])
      state).lifecycle.consumers.demons = state.lifecycle.consumers.demons := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot rest ih =>
    exact (ih (state.install slot targets[slot.val])).trans
      (state.install_preserves slot targets[slot.val]).1

/-- Installing the requested vector preserves targets already installed and
establishes every target named by the fold, for arbitrary slot order and aliases. -/
theorem FreeDispatch.fold_target {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (covered : slot ∈ slots ∨ state.lifecycle.consumers.skills[slot.val].interest = .learned targets[slot.val]) :
    (slots.foldl (fun current next => current.install next targets[next.val]) state).lifecycle.consumers.skills[slot.val].interest = .learned targets[slot.val] := by
  induction slots generalizing state with
  | nil => simpa using covered
  | cons next rest ih =>
    apply ih
    by_cases same : slot = next
    · subst next
      exact Or.inr (state.install_target slot targets[slot.val])
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

/-- A slot whose held unit is its target's unit keeps its policy, model, cache and
meta-controller row bit-identical through the whole installation fold, for arbitrary slot order. -/
theorem FreeDispatch.fold_retains {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (keeps : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment targets[slot.val] = true) :
    (slots.foldl (fun current next => current.install next targets[next.val]) state).lifecycle.consumers.skills[slot.val].policy =
        state.lifecycle.consumers.skills[slot.val].policy ∧
      (slots.foldl (fun current next => current.install next targets[next.val]) state).lifecycle.consumers.skills[slot.val].model =
        state.lifecycle.consumers.skills[slot.val].model ∧
      (slots.foldl (fun current next => current.install next targets[next.val]) state).predictions[slot.val] =
        state.predictions[slot.val] ∧
      (slots.foldl (fun current next => current.install next targets[next.val]) state).lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] =
        state.lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] := by
  induction slots generalizing state with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons next rest ih =>
    simp only [List.foldl_cons]
    by_cases same : next = slot
    · subst next
      have installed := state.install_same slot targets[slot.val] keeps
      have after := ih (state.install slot targets[slot.val]) (by
        rw [installed.1]
        exact Assignment.same_refl targets[slot.val])
      rw [installed.1] at after
      rw [installed.2.1, installed.2.2.1] at after
      exact after
    · have other := state.install_other next slot targets[next.val] (Ne.symm same)
      have row := state.install_meta_other next slot targets[next.val] (Ne.symm same)
      have after := ih (state.install next targets[next.val]) (by rw [other.1]; exact keeps)
      rw [other.1, other.2, row] at after
      exact after

/-- Installing the requested vector keeps the questions of a slot whose unit it keeps,
for arbitrary slot order and aliases. -/
theorem FreeDispatch.fold_questions {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (keeps : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment targets[slot.val] = true) :
    (slots.foldl (fun current next => current.install next targets[next.val]) state).lifecycle.consumers.skills[slot.val].questions =
      state.lifecycle.consumers.skills[slot.val].questions := by
  induction slots generalizing state with
  | nil => rfl
  | cons next rest ih =>
    simp only [List.foldl_cons]
    by_cases same : next = slot
    · subst next
      have installed := state.install_same slot targets[slot.val] keeps
      have after := ih (state.install slot targets[slot.val]) (by
        rw [installed.1]
        exact Assignment.same_refl targets[slot.val])
      rw [installed.1] at after
      exact after
    · have other := state.install_other next slot targets[next.val] (Ne.symm same)
      have after := ih (state.install next targets[next.val]) (by rw [other.1]; exact keeps)
      rw [other.1] at after
      exact after

/-- The assignment refresh preserves projection identity, whether or not it replaced
any target. -/
theorem FreeDispatch.refresh_conserves {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    state.refreshRanked.lifecycle.representation = state.lifecycle.representation := by
  unfold FreeDispatch.refreshRanked
  exact FreeDispatch.fold_preserves _ _ _

/-- Every option receives the slot-stable ranking computed from this receiver's
actual Demon-0 words and its held objectives. -/
theorem FreeDispatch.refresh_targets {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    state.refreshRanked.lifecycle.consumers.skills[slot.val].interest =
      .learned (rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
        (state.lifecycle.consumers.skills.map (·.interest.held)))[slot.val] := by
  unfold FreeDispatch.refreshRanked
  exact FreeDispatch.fold_target _ _ _ slot (Or.inl (List.mem_finRange slot))

/-- After the assignment refresh no two slots hold the same unit, whatever the held
input. -/
theorem FreeDispatch.refresh_distinct {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    state.refreshRanked.lifecycle.consumers.Distinct := by
  intro left right unit leftHolds rightHolds
  simp only [Vector.getElem_map] at leftHolds rightHolds
  rw [state.refresh_targets left] at leftHolds
  rw [state.refresh_targets right] at rightHolds
  exact rankAssignments_distinct dimension config _ _ left right unit leftHolds rightHolds

/-- Timing, one direction: after the assignment refresh every candidate of the
ranking is some slot's unit, for every state and Demon-0 weight array. A candidate
therefore waits for no later event: the free boundary at which the ranking first has
it is the boundary that installs it. -/
theorem FreeDispatch.refresh_covers {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (candidate : Candidate config)
    (member : candidate ∈ rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights) :
    ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      state.refreshRanked.lifecycle.consumers.skills[slot.val].interest.held.identity =
        some candidate.unit := by
  obtain ⟨slot, named⟩ := rankAssignments_covers dimension config
    state.lifecycle.consumers.demons.rankingWeights
    (state.lifecycle.consumers.skills.map (·.interest.held)) candidate member
  exact ⟨slot, by rw [state.refresh_targets slot]; exact named⟩

/-- Timing, the other direction: every unit a slot holds after the assignment
refresh is a candidate of the ranking, so a unit that left the ranking is held by no
slot. -/
theorem FreeDispatch.refresh_ranked {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count)
    (named : state.refreshRanked.lifecycle.consumers.skills[slot.val].interest.held.identity =
      some unit) :
    unit ∈ (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).map (·.unit) := by
  rw [state.refresh_targets slot] at named
  exact rankAssignments_ranked dimension config _ _ slot unit named

/-- Timing, the full table: after the assignment refresh at which the ranking has a
candidate for every slot, every slot holds a unit. With fewer candidates than slots,
`refresh_occupancy` gives one slot to each candidate and leaves the others neutral. -/
theorem FreeDispatch.refresh_full {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (full : (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).length = Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    ∃ unit bonus, state.refreshRanked.lifecycle.consumers.skills[slot.val].interest =
      .learned (.selected unit bonus) := by
  obtain ⟨unit, bonus, target⟩ := rankAssignments_full dimension config
    state.lifecycle.consumers.demons.rankingWeights
    (state.lifecycle.consumers.skills.map (·.interest.held)) full slot
  exact ⟨unit, bonus, by rw [state.refresh_targets slot, target]⟩

/-- Timing, the count: after the assignment refresh as many slots hold a unit as the
ranking has candidates, for every state and Demon-0 weight array. With one candidate one
slot holds a unit, with two candidates two do, and with three all do. -/
theorem FreeDispatch.refresh_occupancy {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
      state.refreshRanked.lifecycle.consumers.skills[slot.val].interest.held.identity.isSome).length =
        (rankedCandidates dimension config
          state.lifecycle.consumers.demons.rankingWeights).length := by
  rw [← rankAssignments_count dimension config state.lifecycle.consumers.demons.rankingWeights
    (state.lifecycle.consumers.skills.map (·.interest.held))]
  congr 1
  apply List.filter_congr
  intro slot _
  rw [state.refresh_targets slot]
  rfl

/-- The ranking's target for the first slot holding a still-ranked unit is that unit,
with a bonus at least the held one, so installing it changes no unit identity. -/
theorem FreeDispatch.refresh_keeps {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count) (bonus : Bonus)
    (holds : state.lifecycle.consumers.skills[slot.val].interest = .learned (.selected unit bonus))
    (ranked : unit ∈ (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).map (·.unit))
    (first : ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
      state.lifecycle.consumers.skills[other.val].interest.held.identity ≠ some unit) :
    ∃ raised : Bonus,
      (rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
        (state.lifecycle.consumers.skills.map (·.interest.held)))[slot.val] =
          .selected unit raised ∧
      bonus.value.bits.toNat ≤ raised.value.bits.toNat ∧
      state.lifecycle.consumers.skills[slot.val].interest.sameAssignment
        (rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
          (state.lifecycle.consumers.skills.map (·.interest.held)))[slot.val] = true := by
  have held : (state.lifecycle.consumers.skills.map
      (fun skill : Skill config criterion dimension (.g99 :: discounts) => skill.interest.held))[slot.val] =
        .selected unit bonus := by simp [holds, Interest.held]
  obtain ⟨raised, target, raises⟩ := rankAssignments_retained dimension config
    state.lifecycle.consumers.demons.rankingWeights _ slot unit bonus held ranked
    (fun other before => by simpa using first other before)
  refine ⟨raised, target, raises, ?_⟩
  rw [holds, target]
  simp [Interest.sameAssignment, Assignment.same]

/-- T1: for every state and Demon-0 weight array, the first slot holding a still-ranked
unit keeps its policy, model, cached prediction and meta-controller row bit-identical,
and keeps that unit with a held bonus that never decreases. -/
theorem FreeDispatch.refresh_retains {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count) (bonus : Bonus)
    (holds : state.lifecycle.consumers.skills[slot.val].interest = .learned (.selected unit bonus))
    (ranked : unit ∈ (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).map (·.unit))
    (first : ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
      state.lifecycle.consumers.skills[other.val].interest.held.identity ≠ some unit) :
    state.refreshRanked.lifecycle.consumers.skills[slot.val].policy =
        state.lifecycle.consumers.skills[slot.val].policy ∧
      state.refreshRanked.lifecycle.consumers.skills[slot.val].model =
        state.lifecycle.consumers.skills[slot.val].model ∧
      state.refreshRanked.predictions[slot.val] = state.predictions[slot.val] ∧
      state.refreshRanked.lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] =
        state.lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] ∧
      ∃ raised : Bonus, state.refreshRanked.lifecycle.consumers.skills[slot.val].interest =
        .learned (.selected unit raised) ∧ bonus.value.bits.toNat ≤ raised.value.bits.toNat := by
  obtain ⟨raised, target, raises, keeps⟩ := state.refresh_keeps slot unit bonus holds ranked first
  have kept := FreeDispatch.fold_retains (List.finRange Acorn.FeatureConstants.skillCount) _
    state slot keeps
  exact ⟨kept.1, kept.2.1, kept.2.2.1, kept.2.2.2, raised,
    (state.refresh_targets slot).trans (by rw [target]), raises⟩

/-- Assignment refresh reads the Demon-0 weights and never writes a demon. -/
theorem FreeDispatch.refresh_demons {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    state.refreshRanked.lifecycle.consumers.demons = state.lifecycle.consumers.demons := by
  unfold FreeDispatch.refreshRanked
  exact FreeDispatch.fold_demons _ _ _

/-- A refresh keeps the questions of the first slot holding a still-ranked unit, as it keeps
its policy and model, and the model reranking writes no question. -/
theorem FreeDispatch.refresh_questions {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) (assign : Bool)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count) (bonus : Bonus)
    (holds : state.lifecycle.consumers.skills[slot.val].interest = .learned (.selected unit bonus))
    (ranked : unit ∈ (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).map (·.unit))
    (first : ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
      state.lifecycle.consumers.skills[other.val].interest.held.identity ≠ some unit) :
    (state.refreshModels assign).lifecycle.consumers.skills[slot.val].questions =
      state.lifecycle.consumers.skills[slot.val].questions := by
  cases assign with
  | false => simp only [FreeDispatch.refreshModels_keep, FreeDispatch.rerankModels_skill]
  | true =>
    rw [FreeDispatch.refreshModels_assign, FreeDispatch.rerankModels_skill]
    obtain ⟨_, _, _, keeps⟩ := state.refresh_keeps slot unit bonus holds ranked first
    exact FreeDispatch.fold_questions (List.finRange Acorn.FeatureConstants.skillCount) _
      state slot keeps

/-- Every complete refresh, assigning or not, keeps distinct held units. -/
theorem FreeDispatch.refreshModels_distinct {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) (assign : Bool)
    (distinct : state.lifecycle.consumers.Distinct) :
    (state.refreshModels assign).lifecycle.consumers.Distinct := by
  cases assign with
  | false =>
    rw [FreeDispatch.refreshModels_keep]
    exact state.rerankModels_distinct distinct
  | true =>
    rw [FreeDispatch.refreshModels_assign]
    exact state.refreshRanked.rerankModels_distinct state.refresh_distinct

/-- The model reranking keeps every slot's objective, so the complete assigning refresh
holds the units the assignment refresh installed. -/
theorem FreeDispatch.refreshModels_interest {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (state.refreshModels true).lifecycle.consumers.skills[slot.val].interest =
      state.refreshRanked.lifecycle.consumers.skills[slot.val].interest := by
  simp only [FreeDispatch.refreshModels_assign, FreeDispatch.rerankModels_skill]

/-- Timing for the complete refresh: after any assigning free-boundary refresh every
candidate of the ranking is some slot's unit. -/
theorem FreeDispatch.refreshModels_covers {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (candidate : Candidate config)
    (member : candidate ∈ rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights) :
    ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      (state.refreshModels true).lifecycle.consumers.skills[slot.val].interest.held.identity =
        some candidate.unit := by
  obtain ⟨slot, named⟩ := state.refresh_covers candidate member
  exact ⟨slot, by rw [state.refreshModels_interest slot]; exact named⟩

/-- Timing for the complete refresh: after any assigning free-boundary refresh at
which the ranking has a candidate for every slot, every slot holds a unit. -/
theorem FreeDispatch.refreshModels_full {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (full : (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).length = Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    ∃ unit bonus, (state.refreshModels true).lifecycle.consumers.skills[slot.val].interest =
      .learned (.selected unit bonus) := by
  obtain ⟨unit, bonus, target⟩ := state.refresh_full full slot
  exact ⟨unit, bonus, by rw [state.refreshModels_interest slot, target]⟩

/-- T1 for the complete refresh: for every state and Demon-0 weight array, the first
slot holding a still-ranked unit keeps its policy, cached prediction and
meta-controller row bit-identical, and keeps that unit with a held bonus that never
decreases. Its model is `refreshModels_model`'s. -/
theorem FreeDispatch.refreshModels_retains {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) (assign : Bool)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count) (bonus : Bonus)
    (holds : state.lifecycle.consumers.skills[slot.val].interest = .learned (.selected unit bonus))
    (ranked : unit ∈ (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).map (·.unit))
    (first : ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
      state.lifecycle.consumers.skills[other.val].interest.held.identity ≠ some unit) :
    (state.refreshModels assign).lifecycle.consumers.skills[slot.val].policy =
        state.lifecycle.consumers.skills[slot.val].policy ∧
      (state.refreshModels assign).predictions[slot.val] = state.predictions[slot.val] ∧
      (state.refreshModels assign).lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] =
        state.lifecycle.consumers.metaController.learners[(metaOfSkill slot).val] ∧
      ∃ raised : Bonus, (state.refreshModels assign).lifecycle.consumers.skills[slot.val].interest =
        .learned (.selected unit raised) ∧ bonus.value.bits.toNat ≤ raised.value.bits.toNat := by
  cases assign with
  | false =>
    rw [FreeDispatch.refreshModels_keep]
    have reranked := state.rerankModels_skill slot
    refine ⟨?_, rfl, rfl, bonus, ?_, Nat.le_refl _⟩
    · simp only [reranked]
    · simp only [reranked]
      exact holds
  | true =>
    rw [FreeDispatch.refreshModels_assign]
    have kept := state.refresh_retains slot unit bonus holds ranked first
    obtain ⟨raised, interest, raises⟩ := kept.2.2.2.2
    have reranked := state.refreshRanked.rerankModels_skill slot
    refine ⟨?_, kept.2.2.1, kept.2.2.2.1, raised, ?_, raises⟩
    · rw [reranked]
      exact kept.1
    · rw [reranked]
      exact interest

/-- The retained slot's model across a refresh, assigning or not, is its own model with
the current feature ranking installed: its reward, continuation and duration learners
are untouched, and its transition part keeps the position and weights of every slot
that stays ranked. -/
theorem FreeDispatch.refreshModels_model {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) (assign : Bool)
    (slot : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count) (bonus : Bonus)
    (holds : state.lifecycle.consumers.skills[slot.val].interest = .learned (.selected unit bonus))
    (ranked : unit ∈ (rankedCandidates dimension config
      state.lifecycle.consumers.demons.rankingWeights).map (·.unit))
    (first : ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
      state.lifecycle.consumers.skills[other.val].interest.held.identity ≠ some unit) :
    (state.refreshModels assign).lifecycle.consumers.skills[slot.val].model =
      state.lifecycle.consumers.skills[slot.val].model.rerank
        (rankedSlots dimension config state.lifecycle.consumers.demons.rankingWeights)
        (rankedSlots_nodup dimension config
          state.lifecycle.consumers.demons.rankingWeights) := by
  cases assign with
  | false => simp only [FreeDispatch.refreshModels_keep, state.rerankModels_skill slot]
  | true =>
    have kept := (state.refresh_retains slot unit bonus holds ranked first).2.1
    rw [FreeDispatch.refreshModels_assign, state.refreshRanked.rerankModels_skill slot,
      state.refresh_demons, kept]

end Acorn.Features
