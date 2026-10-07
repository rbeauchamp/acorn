/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.StepParts

/-!
# The draw-first selection against selection

`TemporalControl.drawFirst` and `TemporalControl.settle` are the dispatch of
`TemporalControl.selectWithOperations` with every draw before every write that reads
the reward (`Acorn.Handcrafted.DrawFirst`). This module states where the two give one
result and where they differ. Every statement is about the executed definitions.

**Where they agree** (`selectWithOperations_settle`). For every state, frame and reward
word: when the draw-first decision starts no option, and no option closes at a free
dispatch under the discounted criterion, selection returns the settled state and the
same decision. The proof moves each owed write past the draws, which read neither the
meta span nor an option the write touches. `Agent.actThenLearn_planAfterAct` carries
it to the whole step: on such a percept the step under `actThenLearn` is the step
under `planAfterAct`, with the same next agent and decision.

**Where they differ.** The two excluded cases, and no other.

- *An option starts.* Selection credits and starts the option and then draws
  (`dispatchMeta_start`): the first action is the persistent draw from the policy the
  start froze, after the terminal credit, the meta credit, the settlement and the
  invocation start. The draw-first dispatch draws it from the frozen policy of the
  option the assignment refresh left, before each of those (`drawBoundary_start`). Both
  then make the writes of the start with `TemporalControl.startOption`
  (`TemporalControl.settle_started`), and the drawn decision is the input that this
  difference changes.
- *An option closes at a free dispatch under the discounted criterion.* Selection
  credits the closing option and then refreshes the assignments. The draw-first
  dispatch refreshes first, because the refresh precedes the draws, and credits the
  owner the refresh retained. The differential criterion has that order in both. Where
  the closing option is kept and the meta draw selects it again, the state that
  `startOption` is given differs as well, by this difference.

What the draws that both make read is stated for the draw-first dispatch itself:
`drawBoundary_meta` and `drawBoundary_unplanned` for the meta draw, and
`drawFirst_assigns` for the assignment refresh that precedes it.

The order of choice and update is that of J. B. Travnik, K. W. Mathewson, R. S. Sutton
and P. M. Pilarski, *Reactive Reinforcement Learning in Asynchronous Environments*,
Frontiers in Robotics and AI 5:79 (2018), Algorithm 1 (section 2) and Algorithm 2
(section 3); PAR-20 declares what Acorn adds to it.
-/
namespace AcornVerif.DrawFirst
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-! ## The owed reward commutes with every write a draw makes -/

/-- In a learning hierarchy the owed reward is one write of the meta span. -/
theorem oweReward_learning (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) (learning : (profile.usesHierarchy && profile.mode != .frozen) = true) :
    state.oweReward reward = state.withGap (state.gap.accumulate reward criterion.rule.gamma) := by
  simp only [TemporalControl.oweReward, learning, ↓reduceIte]

/-- Outside a learning hierarchy nothing is owed for the reward. -/
theorem oweReward_idle (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) (idle : (profile.usesHierarchy && profile.mode != .frozen) = false) :
    state.oweReward reward = state := by
  simp only [TemporalControl.oweReward, idle, Bool.false_eq_true, ↓reduceIte]

/-- The owed reward commutes with the assignment refresh. -/
theorem refreshFree_owe (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    (state.oweReward reward).refreshFree closing =
      ((state.refreshFree closing).1.oweReward reward, (state.refreshFree closing).2) := by
  unfold TemporalControl.oweReward
  split <;> rfl

/-- The owed reward commutes with planning. -/
theorem planFree_owe (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) :
    (state.oweReward reward).planFree plan features =
      (state.planFree plan features).oweReward reward := by
  unfold TemporalControl.oweReward
  split <;> rfl

/-- The owed reward commutes with the meta draw. -/
theorem drawMeta_owe (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) (features : SwiftTd.ActiveSet dimension) :
    (state.oweReward reward).drawMeta features =
      ((state.drawMeta features).1.oweReward reward, (state.drawMeta features).2) := by
  unfold TemporalControl.oweReward
  split <;> rfl

/-- The owed reward commutes with a fresh primitive choice. -/
theorem choosePrimitive_owe (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) (features : SwiftTd.ActiveSet dimension)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    (state.oweReward reward).choosePrimitive features metaValues metaDecision ended =
      ((state.choosePrimitive features metaValues metaDecision ended).1.oweReward reward,
        (state.choosePrimitive features metaValues metaDecision ended).2) := by
  unfold TemporalControl.oweReward
  split <;> rfl

/-- Meta credit commutes with a fresh primitive choice. -/
theorem choosePrimitive_learnMeta (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    (state.learnMeta features decision).choosePrimitive features metaValues metaDecision ended =
      ((state.choosePrimitive features metaValues metaDecision ended).1.learnMeta features decision,
        (state.choosePrimitive features metaValues metaDecision ended).2) := by
  simp only [TemporalControl.learnMeta_eq]
  split <;> rfl

/-- Terminal credit commutes with a fresh primitive choice. -/
theorem choosePrimitive_close (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    (state.closeOption models features closing reward terminal).1.choosePrimitive features
        metaValues metaDecision ended =
      (((state.choosePrimitive features metaValues metaDecision ended).1.closeOption models
          features closing reward terminal).1,
        (state.choosePrimitive features metaValues metaDecision ended).2) := by
  simp only [TemporalControl.closeOption_eq]
  cases closing.oldOwner <;> rfl

/-- Terminal credit records the closing event, whatever the state and the reward. -/
theorem closeOption_closing (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).2 = closingEvent closing := rfl

/-! ## A free dispatch -/

/-- **A free dispatch that starts no option.** For every state, frame and reward word:
when the draw-first dispatch starts no option, and a closing activation is supplied only
under the differential criterion, the free dispatch of selection on the state that owes
the reward returns the settled state and the same decision. -/
theorem atBoundary_settle (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (drawn : state.drawBoundary plan features declared closing estimate =
      some (next, owed, decision))
    (unstarted : decision.started = none)
    (sampled : closing.isSome = true → criterion = .differential) :
    (state.oweReward reward).atBoundary models plan features declared reward goal closing none =
      some (next.settle owed models features reward goal, decision) := by
  have slots := state.refresh_episode_slot closing
  unfold TemporalControl.drawBoundary at drawn
  unfold TemporalControl.atBoundary
  rw [refreshFree_owe]
  dsimp only at drawn ⊢
  rw [planFree_owe, drawMeta_owe]
  generalize state.refreshFree closing = fresh at drawn slots ⊢
  generalize (fresh.1.planFree plan features).drawMeta features = met at drawn ⊢
  dsimp only at drawn ⊢
  cases selected : skillOfMeta met.2.action with
  | some slot =>
    simp only [selected] at drawn
    cases potential : (met.1.runtime.lifecycle.consumers.skills.get slot).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at drawn
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at drawn
      cases drawn
      cases unstarted
  | none =>
    simp only [selected] at drawn
    cases drawn
    cases retained : fresh.2 with
    | none =>
      simp only [TemporalControl.dispatchMeta_eq, selected, pure, Option.some.injEq]
      rw [choosePrimitive_learnMeta, choosePrimitive_owe]
      rfl
    | some owner =>
      have supplied : closing.isSome = true := by
        rw [retained] at slots
        cases closing with
        | none => cases slots
        | some given => rfl
      cases criterion with
      | discounted => cases sampled supplied
      | differential =>
        simp only [TemporalControl.dispatchMeta_eq, selected, pure, Option.some.injEq]
        rw [choosePrimitive_learnMeta, choosePrimitive_close, choosePrimitive_owe]
        rfl

/-! ## A served step and a continuing option -/

/-- **A served step.** For every state and reward word, serving a run from the state
that owes the reward is serving it with the draw-first step and settling. -/
theorem serve_settle (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (goal : Bool) :
    (state.oweReward reward).serve features =
      (state.serveDraw features).map fun result =>
        (result.1.settle (.served result.2.1) models features reward goal, result.2.2) := by
  have phase : (state.oweReward reward).runtime.references.phase =
      state.runtime.references.phase := by
    unfold TemporalControl.oweReward
    split <;> rfl
  unfold TemporalControl.serve TemporalControl.serveDraw
  rw [phase]
  cases state.runtime.references.phase with
  | idle => rfl
  | option slot activation => rfl
  | exploring committed =>
    dsimp only
    cases committed.run.serve with
    | none => rfl
    | some pair =>
      obtain ⟨action, rest⟩ := pair
      simp only [bind, Option.bind, pure, Option.map_some, Option.some.injEq]
      cases held : committed.origin with
      | none =>
        by_cases learning : (profile.usesHierarchy && profile.mode != .frozen) = true
        · simp only [TemporalControl.settle, TemporalControl.skipMeta, oweReward_learning _ _ learning,
            learning, TemporalControl.interrupt, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte, Bool.not_false] <;> (repeat' split) <;> rfl
        · have idle : (profile.usesHierarchy && profile.mode != .frozen) = false := by
            simpa using learning
          simp only [TemporalControl.settle, TemporalControl.skipMeta, oweReward_idle _ _ idle,
            idle, TemporalControl.interrupt, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            Bool.not_false] <;> (repeat' split) <;> rfl
      | some origin =>
        obtain ⟨slot, activation⟩ := origin
        by_cases learning : (profile.usesHierarchy && profile.mode != .frozen) = true
        · simp only [TemporalControl.settle, oweReward_learning _ _ learning,
            TemporalControl.interrupt, Option.isSome_some, ↓reduceIte, Bool.not_true,
            Bool.false_eq_true] <;> (repeat' split) <;> rfl
        · have idle : (profile.usesHierarchy && profile.mode != .frozen) = false := by
            simpa using learning
          simp only [TemporalControl.settle, oweReward_idle _ _ idle,
            TemporalControl.interrupt, Option.isSome_some, ↓reduceIte, Bool.not_true,
            Bool.false_eq_true] <;> (repeat' split) <;> rfl

/-- The option a write put in a slot is the option read from that slot. -/
theorem withSkill_get (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (state.withSkill slot skill).runtime.lifecycle.consumers.skills.get slot = skill := by
  change (state.runtime.lifecycle.consumers.skills.set slot.val skill slot.isLt)[slot.val] = skill
  exact Vector.getElem_set_self _

/-- Two writes of one slot leave the second. -/
theorem withSkill_twice (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (first second : Skill interface.actions config criterion dimension interface.layout) :
    (state.withSkill slot first).withSkill slot second = state.withSkill slot second := by
  simp [TemporalControl.withSkill, Vector.set_set]

/-- **The option step is its draw, its occupancy write and its credit.** For every
state, activation, continuation and reward word: the executed option step returns the
credit of the persistent draw from the continuation's frozen policy, with occupancy and
the generator after that draw, and the decision of that draw. -/
theorem stepOption_credit (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation)
    (reward : Binary32) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool) (ended : Option EndEvent) :
    state.stepOption models slot activation next reward metaValues metaDecision started ended =
      let drawn := next.policy.drawPersistent state.runtime.references.rng
      let credited := (state.creditOption models slot activation next drawn.1 reward).withPhase
        (Occupancy.afterOption slot (activation.advance next) drawn.1.run)
      ({ credited with runtime := { credited.runtime with references :=
          { credited.runtime.references with rng := drawn.2 } } },
        ⟨.option slot, drawn.1.action, next.policy.values, drawn.1.probabilities,
          drawn.1.explored, metaValues, metaDecision, if started then some slot else none,
          ended⟩) := by
  simp only [TemporalControl.stepOption_eq, TemporalControl.creditOption_eq]
  rfl

/-! ## The whole dispatch -/

/-- **Selection is the draw-first dispatch followed by the owed writes, where no option
starts and no terminal credit crosses a refresh.** For every state, model interface,
planning function, frame and reward word: when the draw-first decision starts no
option, and it does not both record a meta decision and end an option under the
discounted criterion, selection returns the settled state and the same decision. -/
theorem selectWithOperations_settle
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (drawn : state.drawFirst models plan features declared goal = some (next, owed, decision))
    (unstarted : decision.started = none)
    (uncrossed : criterion = .discounted → decision.metaDecision.isSome = true →
      decision.ended = none) :
    state.selectWithOperations models plan features declared reward goal =
      some (next.settle owed models features reward goal, decision) := by
  unfold TemporalControl.selectWithOperations
  rw [TemporalControl.prepareSelection_owe]
  unfold TemporalControl.drawFirst at drawn
  generalize state.prepareDraw models features = prepared at drawn ⊢
  dsimp only at drawn ⊢
  rw [serve_settle prepared models features reward goal]
  have phase : (prepared.oweReward reward).runtime.references.phase =
      prepared.runtime.references.phase := by
    unfold TemporalControl.oweReward
    split <;> rfl
  have idled : (prepared.oweReward reward).withPhase .idle =
      (prepared.withPhase .idle).oweReward reward := by
    unfold TemporalControl.oweReward
    split <;> rfl
  cases served : prepared.serveDraw features with
  | some result =>
    simp only [served] at drawn
    cases drawn
    rfl
  | none =>
    simp only [served, Option.map_none] at drawn ⊢
    by_cases hierarchy : profile.usesHierarchy = true
    · simp only [hierarchy, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at drawn ⊢
      rw [phase, idled]
      cases occupancy : prepared.runtime.references.phase with
      | idle =>
        simp only [occupancy] at drawn ⊢
        exact atBoundary_settle (prepared.withPhase .idle) models plan features declared reward
          goal none .zero next owed decision drawn unstarted (fun supplied => by cases supplied)
      | exploring committed =>
        simp only [occupancy] at drawn ⊢
        exact atBoundary_settle (prepared.withPhase .idle) models plan features declared reward
          goal none .zero next owed decision drawn unstarted (fun supplied => by cases supplied)
      | option slot activation =>
        simp only [occupancy] at drawn ⊢
        have reads : ((prepared.withPhase .idle).oweReward reward).runtime.lifecycle =
              (prepared.withPhase .idle).runtime.lifecycle ∧
            ((prepared.withPhase .idle).oweReward reward).metaRate =
              (prepared.withPhase .idle).metaRate ∧
            ((prepared.withPhase .idle).oweReward reward).skillRate =
              (prepared.withPhase .idle).skillRate := by
          unfold TemporalControl.oweReward
          split <;> exact ⟨rfl, rfl, rfl⟩
        rw [reads.1, reads.2.1, reads.2.2]
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at drawn
        | some value =>
          simp only [potential, bind, Option.bind] at drawn ⊢
          cases choice : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
              slot).decideOption activation features value goal
              (comparisonValue criterion
                ((prepared.withPhase .idle).runtime.lifecycle.consumers.metaController.snapshot
                  (count := metaCount) features (prepared.withPhase .idle).metaRate))
              (prepared.withPhase .idle).skillRate with
          | continuing continuation =>
            simp only [choice, pure, Option.some.injEq] at drawn ⊢
            cases drawn
            rw [stepOption_credit]
            by_cases learning : (profile.usesHierarchy && profile.mode != .frozen) = true
            · simp only [TemporalControl.settle, TemporalControl.skipMeta, learning, ↓reduceIte,
                oweReward_learning _ _ learning, TemporalControl.creditOption_eq]
              rfl
            · have idle : (profile.usesHierarchy && profile.mode != .frozen) = false := by
                simpa using learning
              simp only [TemporalControl.settle, TemporalControl.skipMeta, idle,
                Bool.false_eq_true, ↓reduceIte, oweReward_idle _ _ idle,
                TemporalControl.creditOption_eq]
              rfl
          | ending reason =>
            simp only [choice] at drawn ⊢
            have traced := (prepared.withPhase .idle).drawBoundary_episodes next plan features
              declared _ _ owed decision drawn
            cases criterion with
            | differential =>
              exact atBoundary_settle (prepared.withPhase .idle) models plan features declared
                reward goal _ _ next owed decision drawn unstarted (fun _ => rfl)
            | discounted =>
              have ended := uncrossed rfl traced.2.2.2
              rw [ended] at traced
              cases traced.2.2.1
    · have primitive : profile.usesHierarchy = false := by simpa using hierarchy
      have idle : (profile.usesHierarchy && profile.mode != .frozen) = false := by
        simp [primitive]
      simp only [primitive, Bool.not_false, ↓reduceIte] at drawn ⊢
      cases drawn
      rw [oweReward_idle _ _ idle]
      rfl

/-! ## The whole step -/

/-- **Under `actThenLearn` the step is the step under `planAfterAct` wherever no option
starts and no terminal credit crosses a refresh.** For every agent state and percept, in
every world: when the decision of the first part starts no option, and it does not both
record a meta decision and end an option under the discounted criterion, the two orders
return the same next agent and the same decision. -/
theorem actThenLearn_planAfterAct
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface)
    (unstarted : (state.choose .actThenLearn percept).decision.started = none)
    (uncrossed : criterion = .discounted →
      (state.choose .actThenLearn percept).decision.metaDecision.isSome = true →
      (state.choose .actThenLearn percept).decision.ended = none) :
    state.actOrdered .actThenLearn percept = state.actOrdered .planAfterAct percept := by
  have settled := selectWithOperations_settle state.advanceClock.control
    (modelOperations criterion dimension) (planningBoundary .none)
    (state.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
    percept.frame.achieved _ _ _ (state.choose_drawn percept).1 unstarted uncrossed
  have selected : state.advanceClock.control.selectWithOperations
      (modelOperations criterion dimension) (planningBoundary .none)
      (state.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
      percept.frame.achieved = some ((state.choose .planAfterAct percept).control,
        (state.choose .planAfterAct percept).decision) :=
    (state.choose_selected .planAfterAct (by decide) percept).1
  have same := Option.some.inj (settled.symm.trans selected)
  have controls := congrArg Prod.fst same
  have decisions := congrArg Prod.snd same
  dsimp only at controls decisions
  refine Prod.ext ?_ decisions
  refine Agent.retire_control (state.choose .actThenLearn percept).learned
    (state.choose .planAfterAct percept).learned ?_
    (state.advanceClock.frame percept.frame).units
  change (((state.choose .actThenLearn percept).control.settle
          (state.choose .actThenLearn percept).owed (modelOperations criterion dimension)
          (state.advanceClock.frame percept.frame).active percept.reward
          percept.frame.achieved).planAfter planning
        (state.advanceClock.frame percept.frame).active
        (state.choose .actThenLearn percept).decision).learn
      (state.advanceClock.frame percept.frame).active percept.frame percept.reward
      percept.frame.achieved (state.choose .actThenLearn percept).decision =
    ((state.choose .planAfterAct percept).control.planAfter planning
        (state.advanceClock.frame percept.frame).active
        (state.choose .planAfterAct percept).decision).learn
      (state.advanceClock.frame percept.frame).active percept.frame percept.reward
      percept.frame.achieved (state.choose .planAfterAct percept).decision
  rw [controls, decisions]

/-! ## Where the two differ: the first action of an option that starts -/

/-- **What the first action of an option reads when the draw is first.** For every free
dispatch that draws first and whose decision starts an option: the option is the one
the drawn meta action names, and the action, the reported values and masses and the
exploration flag are those of the persistent draw from that option's frozen policy in
the state after the assignment refresh, the supplied planning and the meta draw, at the
generator the meta draw left. That option is the one the refresh left: planning and the
meta draw write no option. No terminal credit, meta credit, settlement or invocation
start precedes the draw. -/
theorem drawBoundary_start (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) (slot : Fin Acorn.FeatureConstants.skillCount)
    (drawn : state.drawBoundary plan features declared closing estimate =
      some (next, owed, decision))
    (started : decision.started = some slot) :
    let met := ((state.refreshFree closing).1.planFree plan features).drawMeta features
    let skill := (state.refreshFree closing).1.runtime.lifecycle.consumers.skills.get slot
    let policy := skill.frozenPolicy features met.1.skillRate
    let first := policy.drawPersistent met.1.runtime.references.rng
    skillOfMeta met.2.action = some slot ∧
      decision.source = .option slot ∧ decision.action = first.1.action ∧
      decision.values = policy.values ∧ decision.probabilities = first.1.probabilities ∧
      decision.explored = first.1.explored ∧
      next.runtime.references.rng = first.2 ∧
      ∃ potential closed, skill.interest.potential features declared = some potential ∧
        owed = .boundary closed met.2 (some ⟨slot, potential, first.1⟩) := by
  unfold TemporalControl.drawBoundary at drawn
  dsimp only at drawn ⊢
  generalize state.refreshFree closing = fresh at drawn ⊢
  have options : ((fresh.1.planFree plan features).drawMeta features).1.runtime.lifecycle.consumers.skills =
      fresh.1.runtime.lifecycle.consumers.skills := rfl
  generalize (fresh.1.planFree plan features).drawMeta features = met at drawn options ⊢
  cases selected : skillOfMeta met.2.action with
  | none =>
    simp only [selected] at drawn
    cases drawn
    cases started
  | some chosen =>
    simp only [selected] at drawn
    cases potential : (met.1.runtime.lifecycle.consumers.skills.get chosen).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at drawn
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at drawn
      cases drawn
      cases started
      rw [← options]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, value, _, potential, rfl⟩

/-- **What the meta draw reads when the draw is first.** For every free dispatch that
draws first and every planning parameter, the meta decision the dispatch records is the
draw from the meta-controller of the state after the assignment refresh and that
planning, at the supplied features and that state's meta rate. No write that reads the
reward precedes it. -/
theorem drawBoundary_meta (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (drawn : state.drawBoundary plan features declared closing estimate =
      some (next, owed, decision)) :
    decision.metaDecision =
      some (((state.refreshFree closing).1.planFree plan features).drawMeta features).2 := by
  unfold TemporalControl.drawBoundary at drawn
  dsimp only at drawn
  generalize ((state.refreshFree closing).1.planFree plan features).drawMeta features = met
    at drawn ⊢
  cases selected : skillOfMeta met.2.action with
  | none =>
    simp only [selected] at drawn
    cases drawn
    rfl
  | some chosen =>
    simp only [selected] at drawn
    cases potential : (met.1.runtime.lifecycle.consumers.skills.get chosen).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at drawn
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at drawn
      cases drawn
      rfl

/-- **The meta draw of the order that acts before it learns.** For every free dispatch
that draws first with the no-planning boundary, which is the one `Agent.choose` runs
under `actThenLearn`: the meta decision is drawn from the frozen meta-controller of the
refreshed state, at that state's meta rate. It is the statement
`TemporalControl.atBoundary_unplanned` makes for selection without planning. -/
theorem drawBoundary_unplanned (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (drawn : state.drawBoundary (planningBoundary .none) features declared closing estimate =
      some (next, owed, decision)) :
    ∃ met : PolicyDecision metaCount, decision.metaDecision = some met ∧
      met.snapshot = (state.refreshFree closing).1.runtime.lifecycle.consumers.metaController.snapshot
        (count := metaCount) features (state.refreshFree closing).1.metaRate := by
  refine ⟨_, drawBoundary_meta state (planningBoundary .none) features declared closing estimate
    next owed decision drawn, ?_⟩
  have kept := (state.refreshFree closing).1.planFree_none features
  rw [TemporalControl.drawMeta_snapshot, kept.1, kept.2]

/-- A free dispatch that draws first leaves each slot the objective its refresh
installed: the draws write no option. -/
theorem drawBoundary_interest (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (drawn : state.drawBoundary plan features declared closing estimate =
      some (next, owed, decision)) :
    next.runtime.lifecycle.consumers.skills =
      (state.refreshFree closing).1.runtime.lifecycle.consumers.skills := by
  unfold TemporalControl.drawBoundary at drawn
  dsimp only at drawn
  have options : (((state.refreshFree closing).1.planFree plan features).drawMeta
      features).1.runtime.lifecycle.consumers.skills =
        (state.refreshFree closing).1.runtime.lifecycle.consumers.skills := rfl
  generalize ((state.refreshFree closing).1.planFree plan features).drawMeta features = met
    at drawn options
  cases selected : skillOfMeta met.2.action with
  | none =>
    simp only [selected] at drawn
    cases drawn
    exact options
  | some chosen =>
    simp only [selected] at drawn
    cases potential : (met.1.runtime.lifecycle.consumers.skills.get chosen).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at drawn
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at drawn
      cases drawn
      exact options

/-- **The assignment refresh precedes the draws when the draw is first.** With learned
subtasks, every draw-first decision that draws a meta decision is taken with the
slot-stable ranking installed: each slot's objective is the ranking's assignment for the
Demon-0 weights and the objectives the decision started from. It is the statement
`TemporalControl.select_assigns` makes for selection; the dispatch takes no reward, so no
part of the percept's reward reaches the refresh. -/
theorem drawFirst_assigns (state : TemporalControl interface profile config criterion dimension)
    (learned : profile.ranksSubtasks = true)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.drawFirst models plan features declared goal = some (next, owed, decision))
    (drawn : decision.metaDecision.isSome = true)
    (index : Fin Acorn.FeatureConstants.skillCount) :
    next.runtime.lifecycle.consumers.skills[index.val].interest =
      .learned (rankAssignments dimension config
        (DemonBank.rankingWeights (discounts := interface.signals)
          state.runtime.lifecycle.consumers.demons)
        (state.runtime.lifecycle.consumers.skills.map (·.interest.held)))[index.val] := by
  have boundary : ∀ (origin : TemporalControl interface profile config criterion dimension)
      (closing : Option (Closing interface.actions config criterion dimension interface.layout
        (EndingPayload (profile.mode != .frozen)))) (estimate : Binary32),
      origin.drawBoundary plan features declared closing estimate = some (next, owed, decision) →
      next.runtime.lifecycle.consumers.skills[index.val].interest =
        .learned (rankAssignments dimension config
          (DemonBank.rankingWeights (discounts := interface.signals)
            origin.runtime.lifecycle.consumers.demons)
          (origin.runtime.lifecycle.consumers.skills.map (·.interest.held)))[index.val] := by
    intro origin closing estimate dispatched
    rw [drawBoundary_interest origin plan features declared closing estimate next owed decision
      dispatched, origin.refreshFree_assigns learned closing]
    exact (FreeDispatch.refreshModels_interest _ index).trans (FreeDispatch.refresh_targets _ index)
  have prepared : (state.prepareDraw models features).runtime.lifecycle = state.runtime.lifecycle := by
    unfold TemporalControl.prepareDraw
    dsimp only
    split <;> rfl
  unfold TemporalControl.drawFirst at executed
  rw [← prepared]
  generalize state.prepareDraw models features = ready at executed ⊢
  dsimp only at executed
  cases served : ready.serveDraw features with
  | some result =>
    simp only [served] at executed
    cases executed
    rw [(ready.serveDraw_undrawn result.1 features result.2.1 result.2.2 served).1] at drawn
    contradiction
  | none =>
    simp only [served] at executed
    split at executed
    · cases executed
      rw [TemporalControl.choosePrimitive_meta] at drawn
      contradiction
    · split at executed
      · exact boundary (ready.withPhase .idle) none .zero executed
      · exact boundary (ready.withPhase .idle) none .zero executed
      · rename_i slot activation phase
        cases potential : ((ready.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          split at executed
          · simp only [pure, Option.some.injEq] at executed
            cases executed
            contradiction
          · exact boundary (ready.withPhase .idle) _ _ executed

/-- **What the first action of an option reads in selection.** For every dispatch of a
drawn meta decision that names an option with a supplied potential: selection makes the
meta credit, settles and starts the option, and then draws. The first action is the
persistent draw from the policy the start froze, and the returned state is the one
`TemporalControl.startOption` returns for that draw, with occupancy and the generator
after it. So the draw-first dispatch and selection make the writes of a start with one
function, `startOption` (`TemporalControl.settle_started`), at two drawn decisions. -/
theorem dispatchMeta_start (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : PolicyDecision metaCount) (ended : Option EndEvent)
    (slot : Fin Acorn.FeatureConstants.skillCount) (potential : Potential)
    (selected : skillOfMeta decision.action = some slot)
    (admitted : ((state.learnMeta features decision).runtime.lifecycle.consumers.skills.get
      slot).interest.potential features declared = some potential) :
    let learned := state.learnMeta features decision
    let begun := ((learned.runtime.lifecycle.consumers.skills.get slot).settleTemporal models
      learned.valueFunction features potential goal (comparisonValue criterion decision.snapshot)
      learned.skillRate reward learned.average.rate (profile.mode != .frozen)).beginTemporal models
        features potential (profile.mode != .frozen) learned.skillRate
    let first := begun.2.2.policy.drawPersistent learned.runtime.references.rng
    let started := (learned.startOption models features ⟨slot, potential, first.1⟩ goal
      (comparisonValue criterion decision.snapshot) reward).withPhase
        (Occupancy.afterOption slot (OptionActivation.first _ potential) first.1.run)
    state.dispatchMeta models features declared reward goal decision ended =
      some ({ started with runtime := { started.runtime with references :=
          { started.runtime.references with rng := first.2 } } },
        ⟨.option slot, first.1.action, begun.2.2.policy.values, first.1.probabilities,
          first.1.explored, decision.snapshot.values, some decision, some slot, ended⟩) := by
  rw [TemporalControl.dispatchMeta_eq]
  simp only [selected, admitted, bind, Option.bind, pure, Option.some.injEq]
  rw [stepOption_credit]
  simp only [TemporalControl.creditOption_eq, TemporalControl.startOption_eq, withSkill_get,
    withSkill_twice]
  rfl

end AcornVerif.DrawFirst
