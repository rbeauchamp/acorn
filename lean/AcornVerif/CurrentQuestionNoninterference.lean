/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentAccounting

/-!
# The options' off-policy questions reach nothing else

Every option slot holds off-policy questions about its own policy (`Skill.questions`; Horde,
AAMAS 2011, §4; PAR-18). The completion boundary writes them (`askQuestions` in
`TemporalControl.finish`), the tester resets their weights at a replaced unit
(`Skill.retire`), an assignment refresh or a release gives a replaced slot fresh ones
(`Skill.initial`), and the checkpoint image stores them. This module proves, over the
executed definitions, that no other part of the agent's step reads them.

`forgetSkill` replaces a skill's questions by fresh ones and keeps every other field;
`forget` does so for every slot of a temporal state, and `forgetAgent` for an agent. Two
agents `Agree` when they are equal after that. The relation is stated by the one field it
leaves out, so every other component of the agent, including any added later, is part of
the agreement.

`actOrdered_agree` shows that from two agreeing agents the executed step returns the same
decision on every percept and agreeing agents, under each of the three step orders, in every
world interface, profile, criterion and planning selection; `act_agree` states the same of
`Agent.act`. `run_agree` carries it over every run of percepts with any step order at each
step, `stream_agree` along every unbounded stream, and `actRun_agree` over every run of
`Agent.act`: the two runs make the same decisions, so they take the same actions, and the
agents agree after every prefix in every learner, tester, model, demon and both random
streams (`agree_streams`). `executed_actions_agree` carries it to the closed loop of the
kernel.

The proof follows the executed step. Each operation that reads a slot reads its objective,
policy, model or off-policy trajectory and writes the skill back with its questions as they
were, so it commutes with forgetting the questions: the `_forget` lemmas from
`decideOption_forget` to `deferred_forget`. Every draw of the step reads a generator state
that forgetting the questions keeps, so both agents draw the same words. The planning boundary reads
each option's model only (`planningBoundary_forget`); the lemmas that take a planning boundary
assume this of it (`PlanReadsNoQuestion`), and `planningBoundary_unread` discharges it for
every configured selection, so the agent-level theorems carry no hypothesis. Two operations
write the questions from their own values: the completion boundary (`finish_forget`) and the
tester (`retireRuntime_forget`). Each reads them only to write them, so after either the
states still agree.

The statement is the behavioural part of retiring the questions: the agent without them is
this agent with the `questions` field and the operations that only maintain it deleted, and
this module shows that the deleted state reaches no decision and no other state. That the
deletion changes nothing else is a fact about the two trees, which no theorem in one tree
states.
-/

namespace AcornVerif.CurrentQuestionNoninterference
open Acorn Acorn.Features Acorn.Handcrafted

section Skills

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {discounts : List Discount} {mode : Bool}

/-- A skill with fresh questions in place of its own: everything of the skill but its
questions. -/
def forgetSkill (skill : Skill actions config criterion dimension discounts) :
    Skill actions config criterion dimension discounts :=
  { skill with questions := OptionQuestions.initial _ _ }

/-- Forgetting a skill's questions twice forgets them once. -/
theorem forgetSkill_idem (skill : Skill actions config criterion dimension discounts) :
    forgetSkill (forgetSkill skill) = forgetSkill skill :=
  rfl

/-- A fresh skill already has fresh questions. -/
theorem forgetSkill_initial (interest : Interest config) :
    forgetSkill (Skill.initial (actions := actions) (discounts := discounts) config criterion
      dimension interest) = Skill.initial config criterion dimension interest :=
  rfl

/-- The interest of a skill is not a question. -/
theorem forgetSkill_interest (skill : Skill actions config criterion dimension discounts) :
    (forgetSkill skill).interest = skill.interest :=
  rfl

/-- An option's stopping decision does not read its questions. -/
theorem decideOption_forget (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    (forgetSkill skill).decideOption activation features potential goal estimate rate =
      skill.decideOption activation features potential goal estimate rate := by
  rw [Skill.decideOption_def, Skill.decideOption_def]
  rfl

/-- An option's frozen policy does not read its questions. -/
theorem frozenPolicy_forget (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    (forgetSkill skill).frozenPolicy features rate = skill.frozenPolicy features rate := by
  rw [Skill.frozenPolicy_def, Skill.frozenPolicy_def]
  rfl

/-- An invocation start commutes with forgetting the questions. -/
theorem beginTemporal_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (forgetSkill skill).beginTemporal models features potential learning rate =
      ⟨forgetSkill (skill.beginTemporal models features potential learning rate).1,
        (skill.beginTemporal models features potential learning rate).2⟩ := by
  rw [Skill.beginTemporal_def, Skill.beginTemporal_def, Skill.beginOption_def,
    Skill.beginOption_def]
  cases learning <;> rfl

/-- An option step commutes with forgetting the questions. -/
theorem stepTemporal_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32)
    (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (forgetSkill skill).stepTemporal models activation next reward gain rng =
      (forgetSkill (skill.stepTemporal models activation next reward gain rng).1,
        (skill.stepTemporal models activation next reward gain rng).2) := by
  rw [Skill.stepTemporal_eq, Skill.stepTemporal_eq, Skill.optionStep_def, Skill.optionStep_def]
  dsimp only
  split <;> (try split) <;> rfl

/-- The credit of a drawn option decision commutes with forgetting the questions. -/
theorem creditTemporal_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (drawn : PersistentDecision actions)
    (reward : Binary32) (gain : RewardRate) :
    (forgetSkill skill).creditTemporal models activation next drawn reward gain =
      forgetSkill (skill.creditTemporal models activation next drawn reward gain) := by
  rw [Skill.creditTemporal_def, Skill.creditTemporal_def, Skill.optionCredit_def,
    Skill.optionCredit_def]
  dsimp only
  split <;> (try split) <;> rfl

/-- An option's terminal credit commutes with forgetting the questions. -/
theorem endTemporal_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate) :
    (forgetSkill skill).endTemporal models value features ending reward terminal gain =
      forgetSkill (skill.endTemporal models value features ending reward terminal gain) := by
  rw [Skill.endTemporal_def, Skill.endTemporal_def, Skill.terminateOption_def,
    Skill.terminateOption_def]
  dsimp only
  split <;> rfl

/-- The start of a followed trajectory commutes with forgetting the questions. -/
theorem startFollowing_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) :
    (forgetSkill skill).startFollowing models features potential rate action behaviour =
      forgetSkill (skill.startFollowing models features potential rate action behaviour) := by
  rw [Skill.startFollowing_def, Skill.startFollowing_def]
  rfl

/-- The stop of a followed trajectory commutes with forgetting the questions. -/
theorem stopFollowing_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (following : Following) (potential : Potential)
    (estimate reward : Binary32) (gain : RewardRate) :
    (forgetSkill skill).stopFollowing models value features following potential estimate reward
        gain =
      forgetSkill (skill.stopFollowing models value features following potential estimate reward
        gain) := by
  rw [Skill.stopFollowing_def, Skill.stopFollowing_def]
  rfl

/-- One followed frame of an option that is not executing commutes with forgetting the
questions. -/
theorem followTemporal_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32) (gain : RewardRate) :
    (forgetSkill skill).followTemporal models value features potential goal estimate rate action
        behaviour reward gain =
      forgetSkill (skill.followTemporal models value features potential goal estimate rate action
        behaviour reward gain) := by
  rw [Skill.followTemporal_def, Skill.followTemporal_def]
  change (match skill.following with
    | none => (forgetSkill skill).startFollowing models features potential rate action behaviour
    | some following =>
      match (forgetSkill skill).decideOption following.activation features potential goal
          estimate rate with
      | .continuing next => _
      | .ending _ => _) = _
  simp only [decideOption_forget]
  cases skill.following with
  | none => exact startFollowing_forget skill models features potential rate action behaviour
  | some following =>
    dsimp only
    cases skill.decideOption following.activation features potential goal estimate rate with
    | continuing next => rfl
    | ending reason => rw [stopFollowing_forget, startFollowing_forget]

/-- Settling a followed trajectory commutes with forgetting the questions. -/
theorem settleFollowing_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate) :
    (forgetSkill skill).settleFollowing models value features potential goal estimate rate reward
        gain =
      forgetSkill (skill.settleFollowing models value features potential goal estimate rate reward
        gain) := by
  rw [Skill.settleFollowing_def, Skill.settleFollowing_def]
  change (match skill.following with
    | none => forgetSkill skill
    | some following =>
      match (forgetSkill skill).decideOption following.activation features potential goal
          estimate rate with
      | .continuing next => _
      | .ending _ => _) = _
  simp only [decideOption_forget]
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    cases skill.decideOption following.activation features potential goal estimate rate with
    | continuing next => rfl
    | ending reason => rw [stopFollowing_forget]

/-- The settling of an invocation start commutes with forgetting the questions. -/
theorem settleTemporal_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) :
    (forgetSkill skill).settleTemporal models value features potential goal estimate rate reward
        gain learning =
      forgetSkill (skill.settleTemporal models value features potential goal estimate rate reward
        gain learning) := by
  rw [Skill.settleTemporal_def, Skill.settleTemporal_def]
  cases learning
  · rfl
  · exact settleFollowing_forget skill models value features potential goal estimate rate reward
      gain

/-- The writes of a start whose first action is drawn commute with forgetting the
questions. -/
theorem startTemporal_forget (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) (drawn : PersistentDecision actions) :
    (forgetSkill skill).startTemporal models value features potential goal estimate rate reward
        gain learning drawn =
      forgetSkill (skill.startTemporal models value features potential goal estimate rate reward
        gain learning drawn) := by
  rw [Skill.startTemporal_def, Skill.startTemporal_def]
  dsimp only
  rw [settleTemporal_forget, beginTemporal_forget, creditTemporal_forget]

/-- Retiring a feature slot of a skill reads its questions only to write them. -/
theorem retire_forget (skill : Skill actions config criterion dimension discounts)
    (feature : FeatIdx dimension) :
    forgetSkill ((forgetSkill skill).retire feature) = forgetSkill (skill.retire feature) := by
  cases skill
  rfl

end Skills

/-! ## Tables, lifecycles and free dispatches -/

section Storage

variable {shape : PatchShape} {actions : Word.Count} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}

/-- A table read through fresh questions is the fresh-question skill of the table's slot. -/
theorem get_forget {count : Nat}
    (skills : Vector (Skill actions config criterion dimension discounts) count)
    (slot : Fin count) :
    (skills.map forgetSkill).get slot = forgetSkill (skills.get slot) :=
  Vector.getElem_map forgetSkill slot.isLt

/-- Forgetting the questions twice forgets them once. -/
theorem map_forget_idem {count : Nat}
    (skills : Vector (Skill actions config criterion dimension discounts) count) :
    (skills.map forgetSkill).map forgetSkill = skills.map forgetSkill := by
  rw [Vector.map_map]
  rfl

/-- An ensemble with every slot's questions replaced by fresh ones. -/
def forgetEnsemble (ensemble : Ensemble actions config criterion dimension discounts) :
    Ensemble actions config criterion dimension discounts :=
  { ensemble with skills := ensemble.skills.map forgetSkill }

/-- A lifecycle with every slot's questions replaced by fresh ones. -/
def forgetLifecycle (lifecycle : Lifecycle shape actions config criterion dimension discounts) :
    Lifecycle shape actions config criterion dimension discounts :=
  { lifecycle with consumers := forgetEnsemble lifecycle.consumers }

/-- Forgetting the questions of a lifecycle twice forgets them once. -/
theorem forgetLifecycle_idem
    (lifecycle : Lifecycle shape actions config criterion dimension discounts) :
    forgetLifecycle (forgetLifecycle lifecycle) = forgetLifecycle lifecycle := by
  simp only [forgetLifecycle, forgetEnsemble, map_forget_idem]

/-- A closing record whose detached owner, if any, has fresh questions. -/
def forgetClosing (closing : Closing actions config criterion dimension discounts payload) :
    Closing actions config criterion dimension discounts payload :=
  { closing with oldOwner := closing.oldOwner.map forgetSkill }

/-- A free dispatch with fresh questions in every slot and in a detached owner. -/
def forgetFree (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    FreeDispatch shape actions config criterion dimension discounts payload :=
  { state with
    lifecycle := forgetLifecycle state.lifecycle
    closing := state.closing.map forgetClosing }

/-- A closing record's detached owner, taken when its slot is replaced, commutes with
forgetting the questions. -/
theorem detach_forget (closing : Option (Closing actions config criterion dimension discounts
      payload))
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (previous : Skill actions config criterion dimension discounts) :
    (closing.map forgetClosing).map (fun ending =>
        if ending.slot == slot then
          { ending with oldOwner := some (ending.oldOwner.getD (forgetSkill previous)) }
        else ending) =
      (closing.map fun ending =>
        if ending.slot == slot then
          { ending with oldOwner := some (ending.oldOwner.getD previous) }
        else ending).map forgetClosing := by
  cases closing with
  | none => rfl
  | some ending =>
    simp only [Option.map_some, forgetClosing]
    split
    · cases ending.oldOwner <;> rfl
    · rfl

/-- Installing an assignment commutes with forgetting the questions. -/
theorem install_forget
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (forgetFree state).install slot target = forgetFree (state.install slot target) := by
  unfold FreeDispatch.install
  by_cases same : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = true
  · simp only [forgetFree, forgetLifecycle, forgetEnsemble, Vector.getElem_map,
      forgetSkill_interest, same, ↓reduceIte, Vector.map_set]
    rfl
  · simp only [forgetFree, forgetLifecycle, forgetEnsemble, Vector.getElem_map,
      forgetSkill_interest, same, Bool.false_eq_true, ↓reduceIte, Vector.map_set]
    rw [detach_forget]
    rfl

/-- Installing a vector of assignments slot by slot commutes with forgetting the questions. -/
theorem installAll_forget (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slots : List (Fin Acorn.FeatureConstants.skillCount)) :
    ∀ state : FreeDispatch shape actions config criterion dimension discounts payload,
      slots.foldl (fun current slot => current.install slot targets[slot.val]) (forgetFree state) =
        forgetFree
          (slots.foldl (fun current slot => current.install slot targets[slot.val]) state) := by
  induction slots with
  | nil => intro state; rfl
  | cons slot rest ih =>
    intro state
    simp only [List.foldl_cons, install_forget]
    exact ih _

/-- The assignment refresh commutes with forgetting the questions: it reads every slot's
objective, never its questions. -/
theorem refreshRanked_forget
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    (forgetFree state).refreshRanked = forgetFree state.refreshRanked := by
  have held : (forgetFree state).lifecycle.consumers.skills.map (·.interest.held) =
      state.lifecycle.consumers.skills.map (·.interest.held) := by
    simp only [forgetFree, forgetLifecycle, forgetEnsemble, Vector.map_map]
    rfl
  unfold FreeDispatch.refreshRanked
  dsimp only
  rw [held]
  exact installAll_forget _ _ state

/-- The model ranking commutes with forgetting the questions. -/
theorem rerankModels_forget
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    (forgetFree state).rerankModels = forgetFree state.rerankModels := by
  simp only [FreeDispatch.rerankModels, forgetFree, forgetLifecycle, forgetEnsemble,
    Vector.map_map]
  rfl

/-- The complete free-boundary refresh commutes with forgetting the questions. -/
theorem refreshModels_forget
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (assign : Bool) :
    (forgetFree state).refreshModels assign = forgetFree (state.refreshModels assign) := by
  cases assign
  · exact rerankModels_forget state
  · rw [FreeDispatch.refreshModels_assign, FreeDispatch.refreshModels_assign,
      refreshRanked_forget, rerankModels_forget]

/-- Releasing a unit commutes with forgetting the questions. -/
theorem release_forget (ensemble : Ensemble actions config criterion dimension discounts)
    (unit : Fin config.units.count) :
    (forgetEnsemble ensemble).release unit = forgetEnsemble (ensemble.release unit) := by
  simp only [Ensemble.release, forgetEnsemble, Vector.getElem_map, forgetSkill_interest,
    Vector.map_map]
  congr 1
  apply congrArg (fun step => Vector.map step ensemble.skills)
  funext skill
  simp only [Function.comp_def, forgetSkill_interest]
  by_cases held : skill.interest.held.holds unit = true
  · simp only [held, ↓reduceIte]
    rfl
  · simp only [held, Bool.false_eq_true, ↓reduceIte]

/-- Releasing a list of units commutes with forgetting the questions. -/
theorem releaseAll_forget (units : List (Fin config.units.count)) :
    ∀ ensemble : Ensemble actions config criterion dimension discounts,
      (forgetEnsemble ensemble).releaseAll units = forgetEnsemble (ensemble.releaseAll units) := by
  induction units with
  | nil => intro ensemble; rfl
  | cons unit rest ih =>
    intro ensemble
    simp only [Ensemble.releaseAll, List.foldl_cons] at ih ⊢
    rw [release_forget]
    exact ih _

/-- The tester's stored learners are not questions. -/
theorem stored_forget (ensemble : Ensemble actions config criterion dimension discounts) :
    (forgetEnsemble ensemble).stored = ensemble.stored := by
  simp only [Ensemble.stored, forgetEnsemble, Vector.toList_map, List.flatMap_map]
  rfl

/-- Which units the slots hold does not read the questions. -/
theorem holds_forget (ensemble : Ensemble actions config criterion dimension discounts) :
    (forgetEnsemble ensemble).holds = ensemble.holds := by
  funext unit
  simp only [Ensemble.holds, forgetEnsemble, Vector.toList_map, List.any_map]
  rfl

/-- Eligibility does not read the questions. -/
theorem eligible_forget (lifecycle : Lifecycle shape actions config criterion dimension discounts) :
    (forgetLifecycle lifecycle).eligible = lifecycle.eligible := by
  funext free unit
  simp only [Lifecycle.eligible, Lifecycle.mature, forgetLifecycle, holds_forget]
  rfl

/-- The tester's candidate does not read the questions. -/
theorem candidate_forget (lifecycle : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) :
    (forgetLifecycle lifecycle).candidate free = lifecycle.candidate free := by
  have prefer : (forgetLifecycle lifecycle).prefer free = lifecycle.prefer free := by
    funext best unit
    simp only [Lifecycle.prefer, eligible_forget]
    rfl
  simp only [Lifecycle.candidate, prefer]

/-- One replacement reads the questions only to write them. -/
theorem replace_forget (lifecycle : Lifecycle shape actions config criterion dimension discounts)
    (unit : Fin config.units.count) :
    forgetLifecycle ((forgetLifecycle lifecycle).replace unit) =
      forgetLifecycle (lifecycle.replace unit) := by
  simp only [Lifecycle.replace, forgetLifecycle, forgetEnsemble, Ensemble.retire, Vector.map_map]
  congr 3

/-- The due replacements read the questions only to write them, and replace the same
units. -/
theorem replaceDue_forget (free : Bool) :
    ∀ (due : Nat) (lifecycle : Lifecycle shape actions config criterion dimension discounts),
      forgetLifecycle (Lifecycle.replaceDue free due (forgetLifecycle lifecycle)).1 =
          forgetLifecycle (Lifecycle.replaceDue free due lifecycle).1 ∧
        (Lifecycle.replaceDue free due (forgetLifecycle lifecycle)).2 =
          (Lifecycle.replaceDue free due lifecycle).2
  | 0, lifecycle => ⟨forgetLifecycle_idem lifecycle, rfl⟩
  | due + 1, lifecycle => by
    simp only [Lifecycle.replaceDue, candidate_forget]
    cases lifecycle.candidate free with
    | none => exact ⟨forgetLifecycle_idem lifecycle, rfl⟩
    | some unit =>
      dsimp only
      have direct := replaceDue_forget free due (lifecycle.replace unit)
      have moved := replaceDue_forget free due ((forgetLifecycle lifecycle).replace unit)
      rw [replace_forget] at moved
      exact ⟨moved.1.symm.trans direct.1, by rw [← moved.2, direct.2]⟩

/-- One tester step reads the questions only to write them, and replaces the same units. -/
theorem test_forget (lifecycle : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) :
    forgetLifecycle ((forgetLifecycle lifecycle).test free active).1 =
        forgetLifecycle (lifecycle.test free active).1 ∧
      ((forgetLifecycle lifecycle).test free active).2 = (lifecycle.test free active).2 := by
  have scored : (forgetLifecycle lifecycle).score active =
      forgetLifecycle (lifecycle.score active) := by
    simp only [Lifecycle.score, forgetLifecycle, stored_forget]
  have accrued : ((forgetLifecycle lifecycle).score active).accrued free =
      (lifecycle.score active).accrued free := by
    rw [scored]
    simp only [Lifecycle.accrued, Lifecycle.eligibleCount, eligible_forget]
    rfl
  have credited : ∀ credit, (forgetLifecycle (lifecycle.score active)).withCredit credit =
      forgetLifecycle ((lifecycle.score active).withCredit credit) := fun _ => rfl
  unfold Lifecycle.test
  dsimp only
  rw [accrued, scored, credited]
  exact replaceDue_forget free _ _

end Storage

/-! ## Planning -/

section Planning

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {discounts : List Discount}

/-- The configured planning boundary reads every option's model and no question. -/
theorem planningBoundary_forget (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    planningBoundary selection state (skills.map forgetSkill) features gain rate =
      planningBoundary selection state skills features gain rate := by
  have look : ∀ (current : PlanningResult criterion dimension)
      (point : SwiftTd.ActiveSet dimension) (slot : Fin Acorn.FeatureConstants.skillCount),
      current.lookAhead (skills.map forgetSkill) point gain rate slot =
        current.lookAhead skills point gain rate slot := by
    intro current point slot
    unfold PlanningResult.lookAhead
    rw [get_forget]
    rfl
  cases selection with
  | none => rfl
  | expectation =>
    simp only [planningBoundary, PlanningResult.backupAll, PlanningResult.sweepAll,
      PlanningResult.backup, PlanningResult.sweep, look]

end Planning

/-! ## The temporal state -/

section Control

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}

/-- Everything of a temporal state but the options' questions: the state with every slot's
questions replaced by fresh ones. Every other component, present or added later, is kept. -/
def forget (state : TemporalControl interface profile config criterion dimension) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with
      lifecycle := forgetLifecycle state.runtime.lifecycle } }

/-- Forgetting the questions twice forgets them once. -/
theorem forget_idem (state : TemporalControl interface profile config criterion dimension) :
    forget (forget state) = forget state := by
  simp only [forget, forgetLifecycle_idem]

/-- A slot of the forgotten table is the slot's skill with fresh questions. -/
theorem forget_get (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (forget state).runtime.lifecycle.consumers.skills.get slot =
      forgetSkill (state.runtime.lifecycle.consumers.skills.get slot) :=
  get_forget _ slot

/-- Writing a slot commutes with forgetting the questions. -/
theorem forget_withSkill (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (forget state).withSkill slot (forgetSkill skill) = forget (state.withSkill slot skill) := by
  simp only [forget, forgetLifecycle, forgetEnsemble, TemporalControl.withSkill, Vector.map_set]

/-- Advancing the deferred meta clock commutes with forgetting the questions. -/
theorem skipMeta_forget (state : TemporalControl interface profile config criterion dimension) :
    (forget state).skipMeta = forget state.skipMeta := by
  unfold TemporalControl.skipMeta
  split <;> rfl

/-- The reward-free preparation commutes with forgetting the questions: the model caches
read every option's model and no question. -/
theorem prepareDraw_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (forget state).prepareDraw models features = forget (state.prepareDraw models features) := by
  unfold TemporalControl.prepareDraw
  dsimp only
  split
  · simp only [forget, forgetLifecycle, forgetEnsemble, Vector.map_map]
    rfl
  · rfl

/-- Preparation commutes with forgetting the questions. -/
theorem prepareSelection_forget
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (forget state).prepareSelection models features reward =
      forget (state.prepareSelection models features reward) := by
  rw [TemporalControl.prepareSelection_owe, TemporalControl.prepareSelection_owe,
    prepareDraw_forget]
  unfold TemporalControl.oweReward
  split <;> rfl

/-- The owed reward commutes with forgetting the questions. -/
theorem oweReward_forget (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) :
    (forget state).oweReward reward = forget (state.oweReward reward) := by
  unfold TemporalControl.oweReward
  split <;> rfl

/-- Interrupting a held option commutes with forgetting the questions. -/
theorem interrupt_forget (state : TemporalControl interface profile config criterion dimension)
    (origin : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen))) :
    (forget state).interrupt origin =
      (forget (state.interrupt origin).1, (state.interrupt origin).2) := by
  cases origin with
  | none => rfl
  | some held =>
    obtain ⟨slot, activation⟩ := held
    unfold TemporalControl.interrupt
    dsimp only
    split
    · rw [forget_get, ← forget_withSkill]
      rfl
    · rfl

/-- A result whose state forgets its questions. -/
def forgetFirst {α : Type}
    (result : TemporalControl interface profile config criterion dimension × α) :
    TemporalControl interface profile config criterion dimension × α :=
  (forget result.1, result.2)

/-- The references are not questions. -/
theorem forget_references (state : TemporalControl interface profile config criterion dimension) :
    (forget state).runtime.references = state.runtime.references :=
  rfl

/-- The meta-controller is not a question. -/
theorem forget_metaController
    (state : TemporalControl interface profile config criterion dimension) :
    (forget state).runtime.lifecycle.consumers.metaController =
      state.runtime.lifecycle.consumers.metaController :=
  rfl

/-- The primitive controller is not a question. -/
theorem forget_control (state : TemporalControl interface profile config criterion dimension) :
    (forget state).runtime.lifecycle.consumers.control =
      state.runtime.lifecycle.consumers.control :=
  rfl

/-- The meta rate does not read the questions. -/
theorem forget_metaRate (state : TemporalControl interface profile config criterion dimension) :
    (forget state).metaRate = state.metaRate :=
  rfl

/-- The options' rate source does not read the questions. -/
theorem forget_skillRate (state : TemporalControl interface profile config criterion dimension) :
    (forget state).skillRate = state.skillRate :=
  rfl

/-- The current value function does not read the questions. -/
theorem forget_valueFunction
    (state : TemporalControl interface profile config criterion dimension) :
    (forget state).valueFunction = state.valueFunction :=
  rfl

/-- The reward rate is not a question. -/
theorem forget_average (state : TemporalControl interface profile config criterion dimension) :
    (forget state).average = state.average :=
  rfl

/-- Writing the occupancy commutes with forgetting the questions. -/
theorem forget_withPhase (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen))) :
    (forget state).withPhase phase = forget (state.withPhase phase) :=
  rfl

/-- Clearing the planning errors commutes with forgetting the questions. -/
theorem forget_withoutPlanning
    (state : TemporalControl interface profile config criterion dimension) :
    (forget state).withoutPlanning = forget state.withoutPlanning :=
  rfl

/-- A served step of a committed run commutes with forgetting the questions. -/
theorem serve_forget (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (forget state).serve features = (state.serve features).map forgetFirst := by
  unfold TemporalControl.serve
  dsimp only [forget_references]
  cases state.runtime.references.phase with
  | idle => rfl
  | option slot activation => rfl
  | exploring committed =>
    dsimp only
    cases committed.run.serve with
    | none => rfl
    | some pair =>
      simp only [bind, Option.bind, pure, Option.map_some, interrupt_forget, forget_withPhase]
      split <;> split <;>
        simp only [skipMeta_forget, forget_withoutPlanning, forgetFirst] <;> rfl

/-- A served step that draws first commutes with forgetting the questions. -/
theorem serveDraw_forget (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (forget state).serveDraw features = (state.serveDraw features).map forgetFirst := by
  unfold TemporalControl.serveDraw
  dsimp only [forget_references]
  cases state.runtime.references.phase with
  | idle => rfl
  | option slot activation => rfl
  | exploring committed =>
    dsimp only
    cases committed.run.serve with
    | none => rfl
    | some pair =>
      simp only [bind, Option.bind, pure, Option.map_some, interrupt_forget, forget_withPhase]
      split <;> simp only [forget_withoutPlanning, forgetFirst] <;> rfl

/-- An option step commutes with forgetting the questions. -/
theorem stepOption_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool)
    (ended : Option EndEvent) :
    (forget state).stepOption models slot activation next reward metaValues metaDecision started
        ended =
      forgetFirst (state.stepOption models slot activation next reward metaValues metaDecision
        started ended) := by
  rw [TemporalControl.stepOption_eq, TemporalControl.stepOption_eq]
  dsimp only
  rw [forget_get, stepTemporal_forget]
  dsimp only
  rw [forget_withSkill]
  rfl

/-- Terminal credit of an option commutes with forgetting the questions, of the slot and
of a detached owner. -/
theorem closeOption_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (forget state).closeOption models features (forgetClosing closing) reward terminal =
      forgetFirst (state.closeOption models features closing reward terminal) := by
  rw [TemporalControl.closeOption_eq, TemporalControl.closeOption_eq]
  dsimp only [forgetClosing]
  cases closing.oldOwner with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [forget_get, endTemporal_forget, forget_withSkill]
    rfl
  | some old => rfl

/-- The free-boundary refresh commutes with forgetting the questions, of the table and of a
closing record's detached owner. -/
theorem refreshFree_forget (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) :
    (forget state).refreshFree (closing.map forgetClosing) =
      (forget (state.refreshFree closing).1, (state.refreshFree closing).2.map forgetClosing) := by
  have free := refreshModels_forget (⟨state.runtime.lifecycle,
    state.runtime.references.modelPredictions, closing⟩ : FreeDispatch interface.symbols
      interface.actions config criterion dimension interface.signals
      (EndingPayload (profile.mode != .frozen))) profile.ranksSubtasks
  unfold TemporalControl.refreshFree
  dsimp only
  simp only [forgetFree] at free
  rw [show (forget state).runtime.lifecycle = forgetLifecycle state.runtime.lifecycle from rfl,
    forget_references, free]
  rfl

/-- A planning boundary that reads no question: forgetting the questions of the table it is
given changes nothing it returns. -/
def PlanReadsNoQuestion
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout) : Prop :=
  ∀ result skills features gain rate,
    plan result (skills.map forgetSkill) features gain rate = plan result skills features gain rate

/-- Every configured planning boundary reads no question. -/
theorem planningBoundary_unread (planning : PlanningSelection) :
    PlanReadsNoQuestion (interface := interface) (config := config) (criterion := criterion)
      (dimension := dimension) (planningBoundary planning) :=
  fun result skills features gain rate =>
    planningBoundary_forget planning result skills features gain rate

/-- A planning boundary that reads no question commutes with forgetting the questions. -/
theorem planFree_forget (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (unread : PlanReadsNoQuestion plan) (features : SwiftTd.ActiveSet dimension) :
    (forget state).planFree plan features = forget (state.planFree plan features) := by
  unfold TemporalControl.planFree
  dsimp only
  split
  · rfl
  · rw [show (forget state).runtime.lifecycle.consumers.skills =
      state.runtime.lifecycle.consumers.skills.map forgetSkill from rfl, unread]
    rfl

/-- The meta draw commutes with forgetting the questions. -/
theorem drawMeta_forget (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (forget state).drawMeta features = forgetFirst (state.drawMeta features) :=
  rfl

/-- Meta credit commutes with forgetting the questions. -/
theorem learnMeta_forget (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    (forget state).learnMeta features decision = forget (state.learnMeta features decision) := by
  rw [TemporalControl.learnMeta_eq, TemporalControl.learnMeta_eq]
  split <;> rfl

/-- Dispatch of a drawn meta action commutes with forgetting the questions. -/
theorem dispatchMeta_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    (forget state).dispatchMeta models features declared reward goal decision ended =
      (state.dispatchMeta models features declared reward goal decision ended).map
        forgetFirst := by
  rw [TemporalControl.dispatchMeta_eq, TemporalControl.dispatchMeta_eq, learnMeta_forget]
  generalize state.learnMeta features decision = learned
  cases skillOfMeta decision.action with
  | none => rfl
  | some slot =>
    dsimp only
    rw [forget_get]
    simp only [forgetSkill_interest]
    cases (learned.runtime.lifecycle.consumers.skills.get slot).interest.potential features
        declared with
    | none => rfl
    | some potential =>
      simp only [bind, Option.bind, pure, Option.map_some]
      rw [settleTemporal_forget, beginTemporal_forget]
      dsimp only
      rw [forget_withSkill, stepOption_forget]
      rfl

/-- A free dispatch commutes with forgetting the questions, for every planning boundary that
reads no question. -/
theorem atBoundary_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (unread : PlanReadsNoQuestion plan) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) :
    (forget state).atBoundary models plan features declared reward goal
        (closing.map forgetClosing) ended =
      (state.atBoundary models plan features declared reward goal closing ended).map
        forgetFirst := by
  unfold TemporalControl.atBoundary
  simp only [refreshFree_forget, planFree_forget (unread := unread), drawMeta_forget]
  generalize state.refreshFree closing = refreshed
  obtain ⟨free, owner⟩ := refreshed
  generalize (free.planFree plan features).drawMeta features = drawn
  cases owner with
  | none =>
    exact dispatchMeta_forget drawn.1 models features declared reward goal drawn.2 ended
  | some held =>
    simp only [Option.map_some, forgetFirst, closeOption_forget]
    exact dispatchMeta_forget _ models features declared reward goal drawn.2 _

/-- Selection commutes with forgetting the questions: it reads none of them and writes none
of them, for every model operation and every planning boundary that reads no question. -/
theorem select_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (unread : PlanReadsNoQuestion plan) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) :
    (forget state).selectWithOperations models plan features declared reward goal =
      (state.selectWithOperations models plan features declared reward goal).map forgetFirst := by
  unfold TemporalControl.selectWithOperations
  rw [prepareSelection_forget]
  generalize state.prepareSelection models features reward = prepared
  dsimp only
  rw [serve_forget]
  cases prepared.serve features with
  | some result => rfl
  | none =>
    simp only [Option.map_none]
    split
    · rfl
    · simp only [forget_withPhase, forget_references]
      cases prepared.runtime.references.phase with
      | idle =>
        exact atBoundary_forget (prepared.withPhase .idle) models plan unread features declared
          reward goal none none
      | exploring committed =>
        exact atBoundary_forget (prepared.withPhase .idle) models plan unread features declared
          reward goal none none
      | option slot activation =>
        generalize prepared.withPhase .idle = free
        dsimp only
        rw [forget_get]
        simp only [forgetSkill_interest, decideOption_forget, forget_metaController,
          forget_metaRate, forget_skillRate]
        cases (free.runtime.lifecycle.consumers.skills.get slot).interest.potential features
            declared with
        | none => rfl
        | some potential =>
          simp only [bind, Option.bind]
          cases (free.runtime.lifecycle.consumers.skills.get slot).decideOption activation
              features potential goal
              (comparisonValue criterion
                (free.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
                  features free.metaRate))
              free.skillRate with
          | continuing next =>
            simp only [forget_withoutPlanning, stepOption_forget, forgetFirst, skipMeta_forget,
              pure, Option.map_some]
          | ending reason =>
            cases criterion with
            | differential =>
              exact atBoundary_forget free models plan unread features declared reward goal
                (some ⟨slot, ⟨activation, potential, reason⟩, none⟩) none
            | discounted =>
              have closed := closeOption_forget free models features
                ⟨slot, ⟨activation, potential, reason⟩, none⟩ reward
                (comparisonValue .discounted
                  (free.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
                    features free.metaRate))
              rw [show forgetClosing (⟨slot, ⟨activation, potential, reason⟩, none⟩ :
                Closing interface.actions config .discounted dimension interface.layout
                  (EndingPayload (profile.mode != .frozen))) =
                    ⟨slot, ⟨activation, potential, reason⟩, none⟩ from rfl] at closed
              dsimp only
              rw [closed]
              exact atBoundary_forget _ models plan unread features declared reward goal none _

/-! ### The operations after selection -/

/-- The stopping estimate does not read the questions. -/
theorem forget_stoppingEstimate
    (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) :
    (forget state).stoppingEstimate decision = state.stoppingEstimate decision :=
  rfl

/-- The executing slot does not read the questions. -/
theorem forget_activeSlot (state : TemporalControl interface profile config criterion dimension) :
    (forget state).activeSlot = state.activeSlot :=
  rfl

/-- The value an interrupted option's span closes toward does not read the questions. -/
theorem takeoverValue_forget
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (forget state).takeoverValue features declared goal decision =
      state.takeoverValue features declared goal decision := by
  unfold TemporalControl.takeoverValue
  simp only [forget_get, forget_stoppingEstimate, forget_skillRate]
  rfl

/-- One slot's share of a followed frame commutes with forgetting the questions. -/
theorem followSlot_forget (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat) (reward : Binary32)
    (gain : RewardRate) (executing : Bool)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    followSlot models value features declared goal estimate rate action behaviour reward gain
        executing (forgetSkill skill) =
      forgetSkill (followSlot models value features declared goal estimate rate action behaviour
        reward gain executing skill) := by
  rw [followSlot_def, followSlot_def]
  cases executing
  · simp only [Bool.false_eq_true, ↓reduceIte, forgetSkill_interest]
    cases skill.interest.potential features declared with
    | none => rfl
    | some potential =>
      exact followTemporal_forget skill models value features potential goal estimate rate action
        behaviour reward gain
  · rfl

/-- An indexed map over the table commutes with forgetting the questions when each slot's
step does. -/
theorem mapFinIdx_forget {count : Nat}
    (skills : Vector (Skill interface.actions config criterion dimension interface.layout) count)
    (step : (index : Nat) →
      Skill interface.actions config criterion dimension interface.layout → index < count →
        Skill interface.actions config criterion dimension interface.layout)
    (commutes : ∀ index skill bound,
      step index (forgetSkill skill) bound = forgetSkill (step index skill bound)) :
    (skills.map forgetSkill).mapFinIdx step = (skills.mapFinIdx step).map forgetSkill := by
  apply Vector.ext
  intro index bound
  simp only [Vector.getElem_mapFinIdx, Vector.getElem_map, commutes]

/-- Off-policy option learning commutes with forgetting the questions. -/
theorem followOptions_forget
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (forget state).followOptions models features declared reward goal decision =
      forget (state.followOptions models features declared reward goal decision) := by
  rw [TemporalControl.followOptions_eq, TemporalControl.followOptions_eq]
  simp only [forget_valueFunction, forget_stoppingEstimate, forget_skillRate, forget_average,
    forget_activeSlot]
  split
  · simp only [forget, forgetLifecycle, forgetEnsemble]
    rw [mapFinIdx_forget]
    intro index skill bound
    exact followSlot_forget _ _ _ _ _ _ _ _ _ _ _ _ skill
  · rfl

/-- Closing an interrupted option's span commutes with forgetting the questions. -/
theorem closeSpan_forget (state : TemporalControl interface profile config criterion dimension)
    (continuation : Option Binary32) :
    (forget state).closeSpan continuation = forget (state.closeSpan continuation) := by
  cases continuation with
  | none => rfl
  | some value =>
    rw [TemporalControl.closeSpan_eq, TemporalControl.closeSpan_eq]
    rfl

/-- Asking the questions writes the questions and nothing else: after it, every slot is the
same whatever questions it held. -/
theorem askQuestions_forget
    (skills : Vector (Skill interface.actions config criterion dimension interface.layout)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (cumulants : Features.Cumulants interface.layout)
    (decision : TemporalDecision interface.actions) :
    (askQuestions (skills.map forgetSkill) features cumulants decision).map forgetSkill =
      (askQuestions skills features cumulants decision).map forgetSkill := by
  apply Vector.ext
  intro index bound
  simp only [Vector.getElem_map]
  rw [askQuestions_get (index := ⟨index, bound⟩),
    askQuestions_get (index := ⟨index, bound⟩)]
  simp only [Vector.getElem_map]
  rfl

/-- **The completion boundary reads the questions only to write them.** From two states that
agree in everything but the questions it returns states that agree in everything but the
questions, in every profile. -/
theorem finish_forget (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    forget ((forget state).finish features observation reward decision) =
      forget (state.finish features observation reward decision) := by
  rw [TemporalControl.finish_eq, TemporalControl.finish_eq]
  by_cases asks : (profile.usesHierarchy && profile.mode != .frozen) = true
  · simp only [asks, ↓reduceIte, forget, forgetLifecycle, forgetEnsemble]
    rw [askQuestions_forget]
    rfl
  · simp only [asks, Bool.false_eq_true, ↓reduceIte, forget, forgetLifecycle, forgetEnsemble,
      map_forget_idem]
    rfl

/-- The learning part reads the questions only to write them. -/
theorem learn_forget (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    forget ((forget state).learn features observation reward goal decision) =
      forget (state.learn features observation reward goal decision) := by
  unfold TemporalControl.learn
  simp only [takeoverValue_forget, followOptions_forget, closeSpan_forget, finish_forget]

/-- **The local transition reads the questions only to write them.** From a state and the
same state with its questions forgotten it returns the same decision and states that agree in
everything but the questions, and it refuses both or neither. -/
theorem step_forget (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool) :
    ((forget state).step planning features observation reward goal).map forgetFirst =
      (state.step planning features observation reward goal).map forgetFirst := by
  rw [TemporalControl.step_parts, TemporalControl.step_parts]
  unfold TemporalControl.select
  rw [select_forget _ _ _ (planningBoundary_unread planning)]
  cases state.selectWithOperations (modelOperations criterion dimension)
      (planningBoundary planning) features observation.declared reward goal with
  | none => rfl
  | some result =>
    simp only [Option.map_some, forgetFirst, learn_forget]

/-! ### Selection that draws first -/

/-- The writes a draw-first selection owes, with the detached owner of a closing option, if
any, holding fresh questions. -/
def forgetOwed : Owed interface profile config criterion dimension →
    Owed interface profile config criterion dimension
  | .settled => .settled
  | .served skip => .served skip
  | .continuing slot activation next drawn => .continuing slot activation next drawn
  | .boundary closing decision start =>
    .boundary (closing.map fun held => (forgetClosing held.1, held.2)) decision start

/-- A draw-first result whose state and owed record forget their questions. -/
def forgetDrawn (result : TemporalControl interface profile config criterion dimension ×
    Owed interface profile config criterion dimension × TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension ×
      Owed interface profile config criterion dimension × TemporalDecision interface.actions :=
  (forget result.1, forgetOwed result.2.1, result.2.2)

/-- `CurrentAccounting.drawDispatch` commutes with forgetting the questions. -/
theorem drawDispatch_forget (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (owed : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)) × Binary32))
    (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    CurrentAccounting.drawDispatch (forget state) features declared
        (owed.map fun held => (forgetClosing held.1, held.2)) decision ended =
      (CurrentAccounting.drawDispatch state features declared owed decision ended).map
        forgetDrawn := by
  unfold CurrentAccounting.drawDispatch
  cases skillOfMeta decision.action with
  | none => rfl
  | some slot =>
    dsimp only
    rw [forget_get]
    simp only [forgetSkill_interest, frozenPolicy_forget, forget_skillRate]
    cases (state.runtime.lifecycle.consumers.skills.get slot).interest.potential features
        declared with
    | none => rfl
    | some potential => rfl

/-- A free dispatch that draws first commutes with forgetting the questions, for every
planning boundary that reads no question. -/
theorem drawBoundary_forget (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (unread : PlanReadsNoQuestion plan) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32) :
    (forget state).drawBoundary plan features declared (closing.map forgetClosing) estimate =
      (state.drawBoundary plan features declared closing estimate).map forgetDrawn := by
  rw [CurrentAccounting.drawBoundary_dispatch, CurrentAccounting.drawBoundary_dispatch]
  simp only [refreshFree_forget, planFree_forget (unread := unread), drawMeta_forget]
  generalize state.refreshFree closing = refreshed
  obtain ⟨free, owner⟩ := refreshed
  generalize (free.planFree plan features).drawMeta features = drawn
  cases owner with
  | none => exact drawDispatch_forget drawn.1 features declared none drawn.2 none
  | some held =>
    dsimp only [forgetFirst, Option.map_some]
    exact drawDispatch_forget drawn.1 features declared
      (some (held, terminalValue criterion drawn.2 estimate)) drawn.2 (some (closingEvent held))

/-- `CurrentAccounting.drawOption` commutes with forgetting the questions. -/
theorem drawOption_forget (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (unread : PlanReadsNoQuestion plan) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen)) :
    CurrentAccounting.drawOption (forget state) plan features declared goal slot activation =
      (CurrentAccounting.drawOption state plan features declared goal slot activation).map
        forgetDrawn := by
  unfold CurrentAccounting.drawOption
  rw [forget_get]
  simp only [forgetSkill_interest, decideOption_forget, forget_metaController, forget_metaRate,
    forget_skillRate]
  cases (state.runtime.lifecycle.consumers.skills.get slot).interest.potential features
      declared with
  | none => rfl
  | some potential =>
    simp only [bind, Option.bind]
    cases (state.runtime.lifecycle.consumers.skills.get slot).decideOption activation
        features potential goal
        (comparisonValue criterion
          (state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
            features state.metaRate))
        state.skillRate with
    | continuing next => rfl
    | ending reason =>
      exact drawBoundary_forget state plan unread features declared
        (some ⟨slot, ⟨activation, potential, reason⟩, none⟩) _

/-- `CurrentAccounting.drawFree` commutes with forgetting the questions. -/
theorem drawFree_forget (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (unread : PlanReadsNoQuestion plan) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) :
    CurrentAccounting.drawFree (forget state) plan features declared goal =
      (CurrentAccounting.drawFree state plan features declared goal).map forgetDrawn := by
  unfold CurrentAccounting.drawFree
  split
  · rfl
  · dsimp only [forget_references]
    cases state.runtime.references.phase with
    | idle =>
      exact drawBoundary_forget (state.withPhase .idle) plan unread features declared none .zero
    | exploring committed =>
      exact drawBoundary_forget (state.withPhase .idle) plan unread features declared none .zero
    | option slot activation =>
      exact drawOption_forget (state.withPhase .idle) plan unread features declared goal slot
        activation

/-- Selection that draws before it credits commutes with forgetting the questions, for every
model operation and every planning boundary that reads no question. -/
theorem drawFirst_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (unread : PlanReadsNoQuestion plan) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) :
    (forget state).drawFirst models plan features declared goal =
      (state.drawFirst models plan features declared goal).map forgetDrawn := by
  rw [CurrentAccounting.drawFirst_dispatch, CurrentAccounting.drawFirst_dispatch,
    prepareDraw_forget, serveDraw_forget]
  cases (state.prepareDraw models features).serveDraw features with
  | some result => rfl
  | none => exact drawFree_forget _ plan unread features declared goal

/-- The executing option's credit commutes with forgetting the questions. -/
theorem creditOption_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation)
    (drawn : PersistentDecision interface.actions) (reward : Binary32) :
    (forget state).creditOption models slot activation next drawn reward =
      forget (state.creditOption models slot activation next drawn reward) := by
  rw [TemporalControl.creditOption_eq, TemporalControl.creditOption_eq, forget_get,
    creditTemporal_forget, forget_average, forget_withSkill]

/-- The start of a drawn option commutes with forgetting the questions. -/
theorem startOption_forget (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (start : StartDraw interface) (goal : Bool) (estimate reward : Binary32) :
    (forget state).startOption models features start goal estimate reward =
      forget (state.startOption models features start goal estimate reward) := by
  rw [TemporalControl.startOption_eq, TemporalControl.startOption_eq, forget_get,
    startTemporal_forget, forget_valueFunction, forget_skillRate, forget_average,
    forget_withSkill]

/-- The owed writes commute with forgetting the questions. -/
theorem settle_forget (state : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (goal : Bool) :
    (forget state).settle (forgetOwed owed) models features reward goal =
      forget (state.settle owed models features reward goal) := by
  cases owed with
  | settled => rfl
  | served skip =>
    cases skip <;> simp only [forgetOwed, TemporalControl.settle, oweReward_forget,
      skipMeta_forget, Bool.false_eq_true, ↓reduceIte]
  | continuing slot activation next drawn =>
    simp only [forgetOwed, TemporalControl.settle, oweReward_forget, creditOption_forget,
      skipMeta_forget]
  | boundary closing decision start =>
    cases closing with
    | none =>
      cases start <;> simp only [forgetOwed, TemporalControl.settle, oweReward_forget,
        Option.map_none, learnMeta_forget, startOption_forget]
    | some held =>
      cases start <;> simp only [forgetOwed, TemporalControl.settle, oweReward_forget,
        Option.map_some, closeOption_forget, forgetFirst, learnMeta_forget, startOption_forget]

/-- Planning after the action commutes with forgetting the questions. -/
theorem planAfter_forget (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (decision : TemporalDecision interface.actions) :
    (forget state).planAfter planning features decision =
      forget (state.planAfter planning features decision) := by
  unfold TemporalControl.planAfter
  split
  · exact planFree_forget state _ (planningBoundary_unread planning) features
  · rfl

/-- The deferred work of every step order commutes with forgetting the questions. -/
theorem deferred_forget (state : TemporalControl interface profile config criterion dimension)
    (order : StepOrder) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (owed : Owed interface profile config criterion dimension) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (forget state).deferred order planning features (forgetOwed owed) reward goal decision =
      forget (state.deferred order planning features owed reward goal decision) := by
  cases order
  · rfl
  · exact planAfter_forget state planning features decision
  · simp only [TemporalControl.deferred, settle_forget, planAfter_forget]

/-! ### The tester -/

/-- Releasing the replaced units after a test commutes with forgetting the questions. -/
theorem releaseTested_forget
    (tested : Lifecycle interface.symbols interface.actions config criterion dimension
      interface.layout)
    (units : List (Fin config.units.count)) :
    forgetLifecycle { tested with consumers := tested.consumers.releaseAll units } =
      { forgetLifecycle tested with
        consumers := (forgetLifecycle tested).consumers.releaseAll units } := by
  simp only [forgetLifecycle, releaseAll_forget]

/-- **The tester reads the questions only to write them.** -/
theorem retireRuntime_forget
    (state : TemporalControl interface profile config criterion dimension)
    (active : Vector Bool config.units.count) :
    forget { forget state with runtime := (forget state).runtime.retire active } =
      forget { state with runtime := state.runtime.retire active } := by
  have tested := test_forget state.runtime.lifecycle state.runtime.references.phase.free active
  unfold FeatureRuntime.retire
  simp only [forget]
  rw [releaseTested_forget, releaseTested_forget, tested.1, tested.2]

end Control

/-! ## The agent -/

section Agent

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- Forgetting the questions keeps every declared option source and every held unit. -/
theorem forget_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) : (forget state).Aligned := by
  refine ⟨fun slot => ?_, ?_⟩
  · have held := aligned.1 slot
    simpa only [forget, forgetLifecycle, forgetEnsemble, Vector.getElem_map,
      forgetSkill_interest] using held
  · have distinct := aligned.2
    simpa only [Ensemble.Distinct, forget, forgetLifecycle, forgetEnsemble, Vector.map_map,
      Function.comp_def, forgetSkill_interest] using distinct

/-- Everything of an agent but the options' questions: the agent whose temporal state has
fresh questions in every slot. -/
def forgetAgent (state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  { state with
    control := forget state.control
    aligned := forget_aligned state.control state.aligned
    episodes := state.episodes }

/-- **Two agents agree in everything but the options' questions**: they are the same agent
once every option's questions are replaced by fresh ones. Every other component of the
agent, present or added later, is part of the agreement; the questions are the one field
it leaves out (`forgetSkill`). -/
def Agree (first second : Agent interface profile config criterion dimension planning) :
    Prop :=
  forgetAgent first = forgetAgent second

/-- Agreement is equality of the temporal states with their questions forgotten: an agent is
its temporal state (`Agent.ext_control`). -/
theorem agree_iff (first second : Agent interface profile config criterion dimension planning) :
    Agree first second ↔ forget first.control = forget second.control :=
  ⟨fun same => congrArg Agent.control same, fun same => Agent.ext_control same⟩

/-- An agent agrees with the same agent whose questions are fresh, so the relation holds
between agents whose questions differ. -/
theorem agree_forget (state : Agent interface profile config criterion dimension planning) :
    Agree state (forgetAgent state) :=
  (agree_iff _ _).mpr (forget_idem state.control).symm

/-- Agreeing agents hold the same two random streams: the action generator and the feature
generator's state, which the representation's progress carries. -/
theorem agree_streams (first second : Agent interface profile config criterion dimension planning)
    (same : Agree first second) :
    first.control.runtime.references.rng = second.control.runtime.references.rng ∧
      first.control.runtime.lifecycle.representation =
        second.control.runtime.lifecycle.representation := by
  have control := (agree_iff first second).mp same
  exact ⟨congrArg (fun state => state.runtime.references.rng) control,
    congrArg (fun state => state.runtime.lifecycle.representation) control⟩

/-- The clock advance keeps the agreement. -/
theorem advance_agree (first second : Agent interface profile config criterion dimension planning)
    (same : forget first.control = forget second.control) :
    forget first.advanceClock.control = forget second.advanceClock.control := by
  have moved : ∀ state : Agent interface profile config criterion dimension planning,
      forget state.advanceClock.control = (forgetAgent state).advanceClock.control :=
    fun _ => rfl
  rw [moved, moved,
    Agent.ext_control (left := forgetAgent first) (right := forgetAgent second) same]

/-- The encoding of a frame reads no question: agreeing agents give the same features and
unit outputs. -/
theorem frame_agree (first second : Agent interface profile config criterion dimension planning)
    (same : forget first.control = forget second.control) (observation : Frame interface) :
    (first.frame observation).active = (second.frame observation).active ∧
      (first.frame observation).units = (second.frame observation).units := by
  have references : first.control.runtime.references = second.control.runtime.references :=
    congrArg (fun state => state.runtime.references) same
  have representation : first.control.runtime.lifecycle.representation =
      second.control.runtime.lifecycle.representation :=
    congrArg (fun state => state.runtime.lifecycle.representation) same
  refine ⟨?_, ?_⟩
  · rw [(first.frame observation).fresh, (second.frame observation).fresh]
    simp only [Agent.words_def]
    rw [references, representation]
  · rw [(first.frame observation).freshUnits, (second.frame observation).freshUnits,
      representation]

/-- The tester keeps the agreement. -/
theorem retire_agree (first second : Agent interface profile config criterion dimension planning)
    (same : forget first.control = forget second.control)
    (units : Vector Bool config.units.count) :
    forget (first.retire units).control = forget (second.retire units).control := by
  unfold Agent.retire
  split
  · exact same
  · change forget { first.control with runtime := first.control.runtime.retire units } =
      forget { second.control with runtime := second.control.runtime.retire units }
    rw [← retireRuntime_forget first.control, ← retireRuntime_forget second.control, same]

/-- Two chosen values with one order, percept, encoding and decision, whose temporal states
and owed records agree in everything but the questions, reach agreeing temporal states. -/
theorem chosen_agree (left right : Chosen interface profile config criterion dimension planning)
    (order : left.order = right.order) (percept : left.percept = right.percept)
    (features : left.features = right.features) (decision : left.decision = right.decision)
    (owed : forgetOwed left.owed = forgetOwed right.owed)
    (control : forget left.control = forget right.control) :
    forget left.learned.control = forget right.learned.control := by
  change forget ((left.control.deferred left.order planning left.features left.owed
      left.percept.reward left.percept.frame.achieved left.decision).learn left.features
      left.percept.frame left.percept.reward left.percept.frame.achieved left.decision) =
    forget ((right.control.deferred right.order planning right.features right.owed
      right.percept.reward right.percept.frame.achieved right.decision).learn right.features
      right.percept.frame right.percept.reward right.percept.frame.achieved right.decision)
  rw [← learn_forget (left.control.deferred _ _ _ _ _ _ _),
    ← learn_forget (right.control.deferred _ _ _ _ _ _ _),
    ← deferred_forget left.control, ← deferred_forget right.control,
    ← order, ← percept, ← features, ← decision, owed, control]

/-- **At every step order the agent's step reads the options' questions only to write them.**
Two agents that agree in everything but the questions return the same decision on every
percept, and agents that agree in everything but the questions after it, under each of the
three orders, in every world interface, profile, criterion and planning selection. -/
theorem actOrdered_agree
    (first second : Agent interface profile config criterion dimension planning)
    (same : Agree first second) (order : StepOrder) (percept : Percept interface) :
    (first.actOrdered order percept).2 = (second.actOrdered order percept).2 ∧
      Agree (first.actOrdered order percept).1 (second.actOrdered order percept).1 := by
  rw [agree_iff] at same ⊢
  have advanced := advance_agree first second same
  have encoded := frame_agree first.advanceClock second.advanceClock advanced percept.frame
  have finished : ∀ decision : (first.choose order percept).decision =
        (second.choose order percept).decision,
      (first.choose order percept).units = (second.choose order percept).units →
      forget (first.choose order percept).learned.control =
        forget (second.choose order percept).learned.control →
      (first.actOrdered order percept).2 = (second.actOrdered order percept).2 ∧
        forget (first.actOrdered order percept).1.control =
          forget (second.actOrdered order percept).1.control := by
    intro decision units learned
    refine ⟨decision, ?_⟩
    change forget ((first.choose order percept).learned.retire
        (first.choose order percept).units).control =
      forget ((second.choose order percept).learned.retire
        (second.choose order percept).units).control
    rw [units]
    exact retire_agree _ _ learned _
  have selected : ∀ selects : order ≠ .actThenLearn,
      (first.actOrdered order percept).2 = (second.actOrdered order percept).2 ∧
        forget (first.actOrdered order percept).1.control =
          forget (second.actOrdered order percept).1.control := by
    intro selects
    obtain ⟨leftChosen, leftOrder, leftPercept, leftFeatures, leftUnits, leftOwed⟩ :=
      first.choose_selected order selects percept
    obtain ⟨rightChosen, rightOrder, rightPercept, rightFeatures, rightUnits, rightOwed⟩ :=
      second.choose_selected order selects percept
    have leftMoved : (forget first.advanceClock.control).select (firstPlanning order planning)
        (first.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
        percept.frame.achieved =
          (first.advanceClock.control.select (firstPlanning order planning)
            (first.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
            percept.frame.achieved).map forgetFirst :=
      select_forget _ _ _ (planningBoundary_unread _) _ _ _ _
    have rightMoved : (forget second.advanceClock.control).select (firstPlanning order planning)
        (second.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
        percept.frame.achieved =
          (second.advanceClock.control.select (firstPlanning order planning)
            (second.advanceClock.frame percept.frame).active percept.frame.declared
            percept.reward percept.frame.achieved).map forgetFirst :=
      select_forget _ _ _ (planningBoundary_unread _) _ _ _ _
    rw [leftChosen, Option.map_some, advanced, encoded.1] at leftMoved
    rw [rightChosen, Option.map_some] at rightMoved
    have moved := Option.some.inj (leftMoved.symm.trans rightMoved)
    have control := congrArg Prod.fst moved
    have decision := congrArg Prod.snd moved
    dsimp only [forgetFirst] at control decision
    exact finished decision (leftUnits.trans (encoded.2.trans rightUnits.symm))
      (chosen_agree _ _ (leftOrder.trans rightOrder.symm) (leftPercept.trans rightPercept.symm)
        (leftFeatures.trans (encoded.1.trans rightFeatures.symm)) decision
        (by rw [leftOwed, rightOwed]) control)
  cases order with
  | learnThenAct => exact selected (by decide)
  | planAfterAct => exact selected (by decide)
  | actThenLearn =>
    obtain ⟨leftChosen, leftOrder, leftPercept, leftFeatures, leftUnits⟩ :=
      first.choose_drawn percept
    obtain ⟨rightChosen, rightOrder, rightPercept, rightFeatures, rightUnits⟩ :=
      second.choose_drawn percept
    have leftMoved := drawFirst_forget first.advanceClock.control
      (modelOperations criterion dimension) (planningBoundary .none)
      (planningBoundary_unread _) (first.advanceClock.frame percept.frame).active
      percept.frame.declared percept.frame.achieved
    have rightMoved := drawFirst_forget second.advanceClock.control
      (modelOperations criterion dimension) (planningBoundary .none)
      (planningBoundary_unread _) (second.advanceClock.frame percept.frame).active
      percept.frame.declared percept.frame.achieved
    rw [leftChosen, Option.map_some, advanced, encoded.1] at leftMoved
    rw [rightChosen, Option.map_some] at rightMoved
    have moved := Option.some.inj (leftMoved.symm.trans rightMoved)
    have control := congrArg Prod.fst moved
    have rest := congrArg Prod.snd moved
    have owed := congrArg Prod.fst rest
    have decision := congrArg Prod.snd rest
    dsimp only [forgetDrawn] at control owed decision
    exact finished decision (leftUnits.trans (encoded.2.trans rightUnits.symm))
      (chosen_agree _ _ (leftOrder.trans rightOrder.symm) (leftPercept.trans rightPercept.symm)
        (leftFeatures.trans (encoded.1.trans rightFeatures.symm)) decision owed control)

/-- **The full decision reads the options' questions only to write them.** Two agents that
agree in everything but the questions return the same decision on every percept, and agents
that agree in everything but the questions after it. `Agent.act` is the step under
`learnThenAct` (`Agent.act_parts`). -/
theorem act_agree (first second : Agent interface profile config criterion dimension planning)
    (same : Agree first second) (percept : Percept interface) :
    (first.act percept).2 = (second.act percept).2 ∧
      Agree (first.act percept).1 (second.act percept).1 := by
  rw [Agent.act_parts, Agent.act_parts]
  exact actOrdered_agree first second same .learnThenAct percept

/-! ## Every run -/

/-- The agent after a run of percepts, each stepped under its own step order. -/
def after : Agent interface profile config criterion dimension planning →
    List (StepOrder × Percept interface) →
      Agent interface profile config criterion dimension planning
  | state, [] => state
  | state, step :: rest => after (state.actOrdered step.1 step.2).1 rest

/-- The decisions of a run of percepts, each stepped under its own step order, in order. -/
def decisions : Agent interface profile config criterion dimension planning →
    List (StepOrder × Percept interface) → List (TemporalDecision interface.actions)
  | _, [] => []
  | state, step :: rest =>
    (state.actOrdered step.1 step.2).2 :: decisions (state.actOrdered step.1 step.2).1 rest

/-- **The options' questions reach nothing else, on every run.** For every percept stream,
with every step order at every step, two agents that agree in everything but the questions
make the same decisions at every step, so they take the same actions, and they agree in
everything but the questions after every prefix of the run: every learner, tester, model,
demon and both random streams (`agree_streams`). -/
theorem run_agree :
    ∀ (steps : List (StepOrder × Percept interface))
      (first second : Agent interface profile config criterion dimension planning),
      Agree first second →
        decisions first steps = decisions second steps ∧
          Agree (after first steps) (after second steps)
  | [], _, _, same => ⟨rfl, same⟩
  | step :: rest, first, second, same => by
    have stepped := actOrdered_agree first second same step.1 step.2
    have later := run_agree rest _ _ stepped.2
    exact ⟨by simp only [decisions, stepped.1, later.1], later.2⟩

/-- Along every unbounded stream of percepts, each with its own step order, the first `time`
steps of the two runs make the same decisions and leave agents that agree in everything but
the questions, at every time. -/
theorem stream_agree (stream : ℕ → StepOrder × Percept interface)
    (first second : Agent interface profile config criterion dimension planning)
    (same : Agree first second) (time : ℕ) :
    decisions first (List.ofFn fun step : Fin time => stream step) =
        decisions second (List.ofFn fun step : Fin time => stream step) ∧
      Agree (after first (List.ofFn fun step : Fin time => stream step))
        (after second (List.ofFn fun step : Fin time => stream step)) :=
  run_agree _ first second same

/-- The agent after `Agent.act` on each percept of a list. -/
def actAfter : Agent interface profile config criterion dimension planning →
    List (Percept interface) → Agent interface profile config criterion dimension planning
  | state, [] => state
  | state, percept :: rest => actAfter (state.act percept).1 rest

/-- The decisions of `Agent.act` on each percept of a list, in order. -/
def actDecisions : Agent interface profile config criterion dimension planning →
    List (Percept interface) → List (TemporalDecision interface.actions)
  | _, [] => []
  | state, percept :: rest => (state.act percept).2 :: actDecisions (state.act percept).1 rest

/-- The same of `Agent.act` run on every percept list: the two runs make the same decisions
and the agents agree in everything but the questions after it. -/
theorem actRun_agree :
    ∀ (percepts : List (Percept interface))
      (first second : Agent interface profile config criterion dimension planning),
      Agree first second →
        actDecisions first percepts = actDecisions second percepts ∧
          Agree (actAfter first percepts) (actAfter second percepts)
  | [], _, _, same => ⟨rfl, same⟩
  | percept :: rest, first, second, same => by
    have stepped := act_agree first second same percept
    have later := actRun_agree rest _ _ stepped.2
    exact ⟨by simp only [actDecisions, stepped.1, later.1], later.2⟩

/-! ## The closed loop -/

/-- The executed agent's actions do not read the options' questions: from two agent states
that agree in everything but the questions, the executed agent takes the same action at
every time, in every world over its interface and from every start state. -/
theorem executed_actions_agree
    (first second : Agent interface profile config criterion dimension planning)
    (same : Agree first second) (world : Kernel.World interface) (start : world.State)
    (time : ℕ) :
    Kernel.actionAt world (CurrentGridWorld.executedAgent first) start time =
      Kernel.actionAt world (CurrentGridWorld.executedAgent second) start time :=
  related_actions (first := CurrentGridWorld.executedAgent first)
    (second := CurrentGridWorld.executedAgent second)
    (fun (left right : Agent interface profile config criterion dimension planning) =>
      Agree left right)
    same
    (fun left right percept held =>
      ⟨congrArg TemporalDecision.action (act_agree left right held percept).1,
        (act_agree left right held percept).2⟩)
    world start time

end Agent

end AcornVerif.CurrentQuestionNoninterference
