import Acorn.Handcrafted.StepParts

namespace AcornVerif.DrawFirst
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

theorem oweReward_learning (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) (learning : (profile.usesHierarchy && profile.mode != .frozen) = true) :
    state.oweReward reward = state.withGap (state.gap.accumulate reward criterion.rule.gamma) := by
  simp only [TemporalControl.oweReward, learning, ↓reduceIte]

theorem oweReward_idle (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) (idle : (profile.usesHierarchy && profile.mode != .frozen) = false) :
    state.oweReward reward = state := by
  simp only [TemporalControl.oweReward, idle, Bool.false_eq_true, ↓reduceIte]

theorem refreshFree_owe (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    (state.oweReward reward).refreshFree closing =
      ((state.refreshFree closing).1.oweReward reward, (state.refreshFree closing).2) := by
  unfold TemporalControl.oweReward
  split <;> rfl

theorem planFree_owe (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) :
    (state.oweReward reward).planFree plan features =
      (state.planFree plan features).oweReward reward := by
  unfold TemporalControl.oweReward
  split <;> rfl

theorem drawMeta_owe (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) (features : SwiftTd.ActiveSet dimension) :
    (state.oweReward reward).drawMeta features =
      ((state.drawMeta features).1.oweReward reward, (state.drawMeta features).2) := by
  unfold TemporalControl.oweReward
  split <;> rfl

theorem choosePrimitive_owe (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) (features : SwiftTd.ActiveSet dimension)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    (state.oweReward reward).choosePrimitive features metaValues metaDecision ended =
      ((state.choosePrimitive features metaValues metaDecision ended).1.oweReward reward,
        (state.choosePrimitive features metaValues metaDecision ended).2) := by
  unfold TemporalControl.oweReward
  split <;> rfl

theorem choosePrimitive_learnMeta (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    (state.learnMeta features decision).choosePrimitive features metaValues metaDecision ended =
      ((state.choosePrimitive features metaValues metaDecision ended).1.learnMeta features decision,
        (state.choosePrimitive features metaValues metaDecision ended).2) := by
  simp only [TemporalControl.learnMeta_eq]
  split <;> rfl

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

theorem closeOption_closing (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).2 = closingEvent closing := rfl

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

theorem withSkill_get (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (state.withSkill slot skill).runtime.lifecycle.consumers.skills.get slot = skill := by
  change (state.runtime.lifecycle.consumers.skills.set slot.val skill slot.isLt)[slot.val] = skill
  exact Vector.getElem_set_self _

theorem withSkill_twice (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (first second : Skill interface.actions config criterion dimension interface.layout) :
    (state.withSkill slot first).withSkill slot second = state.withSkill slot second := by
  simp [TemporalControl.withSkill, Vector.set_set]

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
  simp only [TemporalControl.stepOption_eq, TemporalControl.creditOption_eq,
    Skill.stepTemporal_credit]

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

inductive Dispatch where
  | selection
  | drawFirst

def sampled : Criterion → Bool
  | .differential => true
  | .discounted => false

def placed (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen)))
    (rng : Rng.Xoshiro256) : TemporalControl interface profile config criterion dimension :=
  let state := state.withPhase phase
  { state with runtime := { state.runtime with references :=
    { state.runtime.references with rng := rng } } }

def boundaryForm (mode : Dispatch)
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) (terminal : PolicyDecision metaCount → Binary32) :
    Option (TemporalControl interface profile config criterion dimension ×
      TemporalDecision interface.actions) :=
  let fresh := state.refreshFree closing
  let met := (fresh.1.planFree plan features).drawMeta features
  let owing := met.1.oweReward reward
  let credited := match fresh.2 with
    | none => owing
    | some retained => (owing.closeOption models features retained reward (terminal met.2)).1
  let event := match fresh.2 with
    | none => ended
    | some retained => some (closingEvent retained)
  let learned := credited.learnMeta features met.2
  match skillOfMeta met.2.action with
  | none => some (learned.choosePrimitive features met.2.snapshot.values (some met.2) event)
  | some slot =>
    match (learned.runtime.lifecycle.consumers.skills.get slot).interest.potential features
        declared with
    | none => none
    | some potential =>
      let estimate := comparisonValue criterion met.2.snapshot
      let policy := match mode with
        | .selection =>
          (((learned.runtime.lifecycle.consumers.skills.get slot).settleTemporal models
            learned.valueFunction features potential goal estimate learned.skillRate reward
            learned.average.rate (profile.mode != EvaluationMode.frozen)).beginTemporal models
              features potential (profile.mode != EvaluationMode.frozen) learned.skillRate).2.2.policy
        | .drawFirst =>
          (met.1.runtime.lifecycle.consumers.skills.get slot).frozenPolicy features met.1.skillRate
      let first := policy.drawPersistent learned.runtime.references.rng
      some (placed (learned.startOption models features ⟨slot, potential, first.1⟩ goal estimate
            reward)
          (Occupancy.afterOption slot
            (OptionActivation.first (profile.mode != .frozen) potential) first.1.run) first.2,
        ⟨.option slot, first.1.action, policy.values, first.1.probabilities, first.1.explored,
          met.2.snapshot.values, some met.2, some slot, event⟩)

def dispatchForm (mode : Dispatch)
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) :
    Option (TemporalControl interface profile config criterion dimension ×
      TemporalDecision interface.actions) :=
  let prepared := state.prepareDraw models features
  match prepared.serveDraw features with
  | some result =>
    some (result.1.settle (.served result.2.1) models features reward goal, result.2.2)
  | none =>
    if !profile.usesHierarchy then
      some ((prepared.withPhase .idle).choosePrimitive features (Vector.replicate _ .zero) none
        none)
    else
      let free := prepared.withPhase .idle
      match prepared.runtime.references.phase with
      | .idle | .exploring _ =>
        boundaryForm mode free models plan features declared reward goal none none
          (·.continuation)
      | .option slot activation =>
        match (free.runtime.lifecycle.consumers.skills.get slot).interest.potential features
            declared with
        | none => none
        | some potential =>
          let metaPolicy := free.runtime.lifecycle.consumers.metaController.snapshot
            (count := metaCount) features free.metaRate
          let estimate := comparisonValue criterion metaPolicy
          match (free.runtime.lifecycle.consumers.skills.get slot).decideOption activation features
              potential goal estimate free.skillRate with
          | .continuing next =>
            let drawn := next.policy.drawPersistent free.runtime.references.rng
            some ((placed free.withoutPlanning
                  (Occupancy.afterOption slot (activation.advance next) drawn.1.run)
                  drawn.2).settle (.continuing slot activation next drawn.1) models features
                reward goal,
              ⟨.option slot, drawn.1.action, next.policy.values, drawn.1.probabilities,
                drawn.1.explored, metaPolicy.values, none, none, none⟩)
          | .ending reason =>
            let closing : Closing interface.actions config criterion dimension interface.layout
                (EndingPayload (profile.mode != .frozen)) :=
              ⟨slot, ⟨activation, potential, reason⟩, none⟩
            if sampled criterion then
              boundaryForm mode free models plan features declared reward goal (some closing)
                none (·.continuation)
            else
              match mode with
              | .selection =>
                boundaryForm mode (free.closeOption models features closing reward estimate).1
                  models plan features declared reward goal none (some (closingEvent closing))
                  (·.continuation)
              | .drawFirst =>
                boundaryForm mode free models plan features declared reward goal (some closing)
                  none (fun _ => estimate)

theorem oweReward_placed (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen)))
    (rng : Rng.Xoshiro256) (reward : Binary32) :
    (placed state phase rng).oweReward reward = placed (state.oweReward reward) phase rng := by
  unfold TemporalControl.oweReward
  split <;> rfl

theorem closeOption_placed (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen)))
    (rng : Rng.Xoshiro256) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    ((placed state phase rng).closeOption models features closing reward terminal).1 =
      placed (state.closeOption models features closing reward terminal).1 phase rng := by
  simp only [TemporalControl.closeOption_eq]
  cases closing.oldOwner <;> rfl

theorem learnMeta_placed (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen)))
    (rng : Rng.Xoshiro256) (features : SwiftTd.ActiveSet dimension)
    (decision : PolicyDecision metaCount) :
    (placed state phase rng).learnMeta features decision =
      placed (state.learnMeta features decision) phase rng := by
  simp only [TemporalControl.learnMeta_eq]
  split <;> rfl

theorem startOption_placed (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen)))
    (rng : Rng.Xoshiro256) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (start : StartDraw interface) (goal : Bool)
    (estimate reward : Binary32) :
    (placed state phase rng).startOption models features start goal estimate reward =
      placed (state.startOption models features start goal estimate reward) phase rng := by
  simp only [TemporalControl.startOption_eq]
  rfl

theorem settled_placed (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen)))
    (rng : Rng.Xoshiro256) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (retained : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (reward terminal : Binary32) (decision : PolicyDecision metaCount)
    (start : StartDraw interface) (goal : Bool) (estimate : Binary32) :
    ((match retained with
        | none => (placed state phase rng).oweReward reward
        | some closing => (((placed state phase rng).oweReward reward).closeOption models features
            closing reward terminal).1).learnMeta features decision).startOption models features
        start goal estimate reward =
      placed (((match retained with
        | none => state.oweReward reward
        | some closing => ((state.oweReward reward).closeOption models features closing reward
            terminal).1).learnMeta features decision).startOption models features start goal
        estimate reward) phase rng := by
  cases retained with
  | none =>
    dsimp only
    rw [oweReward_placed, learnMeta_placed, startOption_placed]
  | some closing =>
    dsimp only
    rw [oweReward_placed, closeOption_placed, learnMeta_placed, startOption_placed]

theorem closeOption_owe (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal owed : Binary32) :
    ((state.oweReward owed).closeOption models features closing reward terminal).1 =
      (state.closeOption models features closing reward terminal).1.oweReward owed := by
  by_cases learning : (profile.usesHierarchy && profile.mode != .frozen) = true
  · rw [oweReward_learning _ _ learning, oweReward_learning _ _ learning]
    simp only [TemporalControl.closeOption_eq]
    cases closing.oldOwner <;> rfl
  · have idle : (profile.usesHierarchy && profile.mode != .frozen) = false := by
      simpa using learning
    rw [oweReward_idle _ _ idle, oweReward_idle _ _ idle]

theorem credited_reads (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (retained : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (reward terminal : Binary32) (decision : PolicyDecision metaCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    let credited := match retained with
      | none => state.oweReward reward
      | some closing => ((state.oweReward reward).closeOption models features closing reward
          terminal).1
    ((credited.learnMeta features decision).runtime.lifecycle.consumers.skills.get slot).interest =
        (state.runtime.lifecycle.consumers.skills.get slot).interest ∧
      (credited.learnMeta features decision).runtime.references.rng =
        state.runtime.references.rng := by
  have owed : ((state.oweReward reward).runtime.lifecycle.consumers.skills.get slot).interest =
        (state.runtime.lifecycle.consumers.skills.get slot).interest ∧
      (state.oweReward reward).runtime.references.rng = state.runtime.references.rng := by
    unfold TemporalControl.oweReward
    split <;> exact ⟨rfl, rfl⟩
  cases retained with
  | none =>
    exact ⟨((state.oweReward reward).learnMeta_interest features decision slot).trans owed.1,
      ((state.oweReward reward).learnMeta_framed (state.oweReward reward) ⟨rfl, rfl, rfl⟩
        features decision).2.2.trans owed.2⟩
  | some closing =>
    exact ⟨((TemporalControl.learnMeta_interest _ features decision slot).trans
        ((state.oweReward reward).closeOption_interest models features closing reward terminal
          slot).1).trans owed.1,
      ((TemporalControl.learnMeta_framed _ _
        ((state.oweReward reward).closeOption_framed (state.oweReward reward) ⟨rfl, rfl, rfl⟩
          models features closing reward terminal) features decision).2.2).trans owed.2⟩

theorem atBoundary_form (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) :
    (state.oweReward reward).atBoundary models plan features declared reward goal closing ended =
      boundaryForm .selection state models plan features declared reward goal closing ended
        (·.continuation) := by
  unfold TemporalControl.atBoundary boundaryForm
  rw [refreshFree_owe]
  dsimp only
  rw [planFree_owe, drawMeta_owe]
  generalize state.refreshFree closing = fresh
  generalize (fresh.1.planFree plan features).drawMeta features = met
  dsimp only
  cases retained : fresh.2 with
  | none =>
    dsimp only
    cases selected : skillOfMeta met.2.action with
    | none => simp only [TemporalControl.dispatchMeta_eq, selected, pure]
    | some slot =>
      cases admitted : (((met.1.oweReward reward).learnMeta features met.2).runtime.lifecycle.consumers.skills.get
          slot).interest.potential features declared with
      | none => simp only [TemporalControl.dispatchMeta_eq, selected, admitted, bind, Option.bind]
      | some potential =>
        rw [dispatchMeta_start (met.1.oweReward reward) models features declared reward goal met.2
          ended slot potential selected admitted]
        simp only [admitted]
        rfl
  | some owner =>
    dsimp only
    cases selected : skillOfMeta met.2.action with
    | none => simp only [TemporalControl.dispatchMeta_eq, selected, pure]; rfl
    | some slot =>
      cases admitted : ((((met.1.oweReward reward).closeOption models features owner reward
          met.2.continuation).1.learnMeta features met.2).runtime.lifecycle.consumers.skills.get
          slot).interest.potential features declared with
      | none => simp only [TemporalControl.dispatchMeta_eq, selected, admitted, bind, Option.bind]
      | some potential =>
        rw [dispatchMeta_start _ models features declared reward goal met.2 _ slot potential
          selected admitted]
        simp only [admitted]
        rfl

theorem drawBoundary_form (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32) :
    (state.drawBoundary plan features declared closing estimate).map (fun result =>
        (result.1.settle result.2.1 models features reward goal, result.2.2)) =
      boundaryForm .drawFirst state models plan features declared reward goal closing none
        (fun met => terminalValue criterion met estimate) := by
  unfold TemporalControl.drawBoundary boundaryForm
  dsimp only
  generalize state.refreshFree closing = fresh
  generalize (fresh.1.planFree plan features).drawMeta features = met
  have reads := credited_reads met.1 models features fresh.2 reward
    (terminalValue criterion met.2 estimate) met.2
  cases selected : skillOfMeta met.2.action with
  | none =>
    dsimp only
    cases retained : fresh.2 with
    | none =>
      simp only [Option.map_some, Option.map_none, TemporalControl.settle]
      rw [choosePrimitive_learnMeta, choosePrimitive_owe]
    | some owner =>
      simp only [Option.map_some, TemporalControl.settle]
      rw [choosePrimitive_learnMeta, choosePrimitive_close, choosePrimitive_owe]
  | some slot =>
    dsimp only
    have same := reads slot
    dsimp only at same
    rw [same.1]
    cases admitted : (met.1.runtime.lifecycle.consumers.skills.get slot).interest.potential features
        declared with
    | none => simp only [bind, Option.bind, Option.map_none]
    | some potential =>
      simp only [bind, Option.bind, pure, Option.map_some, TemporalControl.settle_started]
      rw [same.2]
      cases retained : fresh.2 with
      | none =>
        exact congrArg some (Prod.ext
          (settled_placed met.1 _ _ models features none reward .zero met.2 _ goal _) rfl)
      | some owner =>
        exact congrArg some (Prod.ext
          (settled_placed met.1 _ _ models features (some owner) reward _ met.2 _ goal _) rfl)

theorem boundaryForm_terminal (mode : Dispatch)
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (ended : Option EndEvent) (first second : PolicyDecision metaCount → Binary32) :
    boundaryForm mode state models plan features declared reward goal none ended first =
      boundaryForm mode state models plan features declared reward goal none ended second := by
  have retained : (state.refreshFree none).2 = none :=
    Option.map_eq_none_iff.mp (state.refresh_episode_slot none)
  unfold boundaryForm
  dsimp only
  rw [retained]

theorem selectWithOperations_form
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) :
    state.selectWithOperations models plan features declared reward goal =
      dispatchForm .selection state models plan features declared reward goal := by
  unfold TemporalControl.selectWithOperations dispatchForm
  rw [TemporalControl.prepareSelection_owe]
  generalize state.prepareDraw models features = prepared
  dsimp only
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
  | some result => rfl
  | none =>
    simp only [Option.map_none]
    by_cases hierarchy : profile.usesHierarchy = true
    · simp only [hierarchy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [phase, idled]
      cases occupancy : prepared.runtime.references.phase with
      | idle =>
        exact atBoundary_form (prepared.withPhase .idle) models plan features declared reward goal
          none none
      | exploring committed =>
        exact atBoundary_form (prepared.withPhase .idle) models plan features declared reward goal
          none none
      | option slot activation =>
        dsimp only
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
        | none => simp only [bind, Option.bind]
        | some value =>
          simp only [bind, Option.bind]
          cases choice : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
              slot).decideOption activation features value goal
              (comparisonValue criterion
                ((prepared.withPhase .idle).runtime.lifecycle.consumers.metaController.snapshot
                  (count := metaCount) features (prepared.withPhase .idle).metaRate))
              (prepared.withPhase .idle).skillRate with
          | continuing continuation =>
            simp only [pure, Option.some.injEq]
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
            dsimp only
            cases criterion with
            | differential =>
              simp only [sampled, ↓reduceIte]
              exact atBoundary_form (prepared.withPhase .idle) models plan features declared
                reward goal _ none
            | discounted =>
              simp only [sampled, Bool.false_eq_true, ↓reduceIte]
              rw [closeOption_owe]
              exact atBoundary_form _ models plan features declared reward goal none _
    · have primitive : profile.usesHierarchy = false := by simpa using hierarchy
      have idle : (profile.usesHierarchy && profile.mode != .frozen) = false := by
        simp [primitive]
      simp only [primitive, Bool.not_false, ↓reduceIte]
      rw [oweReward_idle _ _ idle]
      rfl

theorem drawFirst_form
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) :
    (state.drawFirst models plan features declared goal).map (fun result =>
        (result.1.settle result.2.1 models features reward goal, result.2.2)) =
      dispatchForm .drawFirst state models plan features declared reward goal := by
  unfold TemporalControl.drawFirst dispatchForm
  generalize state.prepareDraw models features = prepared
  dsimp only
  cases served : prepared.serveDraw features with
  | some result => rfl
  | none =>
    simp only
    by_cases hierarchy : profile.usesHierarchy = true
    · simp only [hierarchy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases occupancy : prepared.runtime.references.phase with
      | idle =>
        dsimp only
        rw [drawBoundary_form (prepared.withPhase .idle) models plan features declared reward goal
          none .zero]
        exact boundaryForm_terminal _ _ models plan features declared reward goal none _ _
      | exploring committed =>
        dsimp only
        rw [drawBoundary_form (prepared.withPhase .idle) models plan features declared reward goal
          none .zero]
        exact boundaryForm_terminal _ _ models plan features declared reward goal none _ _
      | option slot activation =>
        dsimp only
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp only [bind, Option.bind, Option.map_none]
        | some value =>
          simp only [bind, Option.bind]
          cases choice : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
              slot).decideOption activation features value goal
              (comparisonValue criterion
                ((prepared.withPhase .idle).runtime.lifecycle.consumers.metaController.snapshot
                  (count := metaCount) features (prepared.withPhase .idle).metaRate))
              (prepared.withPhase .idle).skillRate with
          | continuing continuation => rfl
          | ending reason =>
            dsimp only
            rw [drawBoundary_form (prepared.withPhase .idle) models plan features declared reward
              goal _ _]
            cases criterion with
            | differential =>
              simp only [sampled, ↓reduceIte]
              rfl
            | discounted =>
              simp only [sampled, Bool.false_eq_true, ↓reduceIte]
              rfl
    · have primitive : profile.usesHierarchy = false := by simpa using hierarchy
      simp only [primitive, Bool.not_false, ↓reduceIte]
      rfl

theorem closeOption_frozen (state : TemporalControl interface profile config criterion dimension)
    (frozen : profile.mode = .frozen) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1 = state := by
  obtain ⟨mode, credit, rate, subtasks⟩ := profile
  cases frozen
  rw [TemporalControl.closeOption_eq]
  dsimp only
  cases closing.oldOwner with
  | some owner => rfl
  | none =>
    cases state with
    | mk runtime credit creditMatches average rate lifetime =>
      cases runtime with
      | mk lifecycle references =>
        cases lifecycle with
        | mk representation consumers =>
          cases consumers with
          | mk control metaController skills demons =>
            have kept : skills.set closing.slot.val (skills.get closing.slot) closing.slot.isLt =
                skills := by
              apply Vector.ext
              intro position inside
              by_cases here : closing.slot.val = position
              · subst here
                simp only [Vector.getElem_set_self]
                rfl
              · simp only [Vector.getElem_set_ne closing.slot.isLt inside here]
            simp only [Option.getD_none, TemporalControl.withSkill]
            exact congrArg (fun table => (⟨⟨⟨representation, ⟨control, metaController, table,
              demons⟩⟩, references⟩, credit, creditMatches, average, rate, lifetime⟩ :
                TemporalControl interface ⟨.frozen, _, _, _⟩ config criterion dimension)) kept

theorem boundaryForm_frozen (state : TemporalControl interface profile config criterion dimension)
    (frozen : profile.mode = .frozen) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) (terminal : PolicyDecision metaCount → Binary32) :
    boundaryForm .selection state models plan features declared reward goal closing ended terminal =
      boundaryForm .drawFirst state models plan features declared reward goal closing ended
        terminal := by
  have idle : (profile.usesHierarchy && profile.mode != .frozen) = false := by
    simp [frozen]
  have learned : ∀ (origin : TemporalControl interface profile config criterion dimension)
      (retained : Option (Closing interface.actions config criterion dimension interface.layout
        (EndingPayload (profile.mode != .frozen)))) (value : Binary32)
      (decision : PolicyDecision metaCount),
      (match retained with
        | none => origin.oweReward reward
        | some owner => ((origin.oweReward reward).closeOption models features owner reward
            value).1).learnMeta features decision = origin := by
    intro origin retained value decision
    have credited : (match retained with
        | none => origin.oweReward reward
        | some owner => ((origin.oweReward reward).closeOption models features owner reward
            value).1) = origin := by
      cases retained with
      | none => exact oweReward_idle origin reward idle
      | some owner =>
        dsimp only
        rw [oweReward_idle origin reward idle]
        exact closeOption_frozen origin frozen models features owner reward value
    rw [credited, TemporalControl.learnMeta_eq]
    simp [frozen]
  unfold boundaryForm
  dsimp only
  generalize state.refreshFree closing = fresh
  generalize (fresh.1.planFree plan features).drawMeta features = met
  rw [learned met.1 fresh.2 (terminal met.2) met.2]
  cases skillOfMeta met.2.action with
  | none => rfl
  | some slot =>
    dsimp only
    cases (met.1.runtime.lifecycle.consumers.skills.get slot).interest.potential features
        declared with
    | none => rfl
    | some potential =>
      dsimp only
      have same : (((met.1.runtime.lifecycle.consumers.skills.get slot).settleTemporal models
            met.1.valueFunction features potential goal (comparisonValue criterion met.2.snapshot)
            met.1.skillRate reward met.1.average.rate
            (profile.mode != EvaluationMode.frozen)).beginTemporal models features potential
              (profile.mode != EvaluationMode.frozen) met.1.skillRate).2.2.policy =
          (met.1.runtime.lifecycle.consumers.skills.get slot).frozenPolicy features
            met.1.skillRate := by
        obtain ⟨mode, credit, rate, subtasks⟩ := profile
        cases frozen
        rfl
      rw [same]

end AcornVerif.DrawFirst
