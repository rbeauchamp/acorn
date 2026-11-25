import Acorn.Host.AgentAdmission
import AcornVerif.CurrentLifetime
import AcornVerif.CurrentModels

namespace AcornVerif.CurrentAgent
open Acorn Acorn.Features Acorn.Handcrafted
open CurrentLifetime CurrentFeatureConsumers CurrentLearner

def DemonSums : {discounts : List Discount} → Lifetime.DemonRecords discounts → Prop
  | [], .nil => True
  | discount :: _, .cons head tail => Lifetime.LegalSum (.squaredError discount)
    head.durable.squaredError.count
      head.durable.squaredError.sum ∧ DemonSums tail

theorem demon_sums {discounts : List Discount} (state : Lifetime.DemonRecords discounts) :
  DemonSums state := by
  induction state with
  | nil => trivial
  | cons head tail ih => exact ⟨stored_sum_legal head.durable.squaredError, ih⟩

def LifetimeSums (state : Lifetime.Stats demonLayout) : Prop :=
  Lifetime.LegalSum .reward state.reward.count state.reward.sum ∧
  (∀ slot : Fin 4, Lifetime.LegalSum .reward state.rewardByFamily[slot.val].count
    state.rewardByFamily[slot.val].sum) ∧
  (∀ slot : Fin Acorn.FeatureConstants.historyBins, Lifetime.LegalSum .reward
    state.rewardHistory[slot.val].count state.rewardHistory[slot.val].sum) ∧
  DemonSums state.demons ∧
  (∀ slot : Fin Acorn.FeatureConstants.historyBins, Lifetime.LegalSum (.squaredError .g99)
    state.errorHistory[slot.val].count state.errorHistory[slot.val].sum)

theorem lifetime_sums (state : Lifetime.Stats demonLayout) : LifetimeSums state :=
  ⟨stored_sum_legal _, fun _ => stored_sum_legal _, fun _ => stored_sum_legal _,
    demon_sums _, fun _ => stored_sum_legal _⟩

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

structure Invariant (state : Agent Grid.interface profile config criterion dimension planning) :
    Prop where
  sources : state.control.Aligned
  episodes : state.control.Episodes
  sums : LifetimeSums state.control.lifetime
  history : (∀ unit : Fin config.units.count,
      (state.control.runtime.lifecycle.representation.progress.units[unit.val]).birth.toNat ≤
        state.clock.toNat) ∧
    Recent state.clock state.control.runtime.lifecycle.representation.progress.last
  learners : ∀ reader ∈ state.control.runtime.lifecycle.consumers.readers,
    ScheduleInv reader.2.state reader.2.phase ∧ reader.2.state.eligibleCount ≤
      dimension.capacity

theorem invariant (state : Agent Grid.interface profile config criterion dimension planning) :
    Invariant state
  :=
  ⟨state.aligned, state.episodes, lifetime_sums _,
    ⟨state.control.runtime.lifecycle.representation.progress.born,
      state.control.runtime.lifecycle.representation.progress.recent⟩,
    fun reader _ => ⟨managed_schedule reader.2, managed_capacity reader.2⟩⟩

theorem initialization (construction : AgentConstruction) :
    Invariant construction.initial.agent :=
  invariant _

def EdgeContract (before : Agent Grid.interface profile config criterion dimension planning)
    (event : AgentInput config criterion dimension)
    (after : Agent Grid.interface profile config criterion dimension planning) : Prop :=
  match event with
  | .act observation result =>
    ∃ (next : TemporalControl Grid.interface profile config criterion dimension)
      (aligned : next.Aligned) (episodes : next.Episodes)
      (decision : TemporalDecision Grid.actions),
      before.advanceClock.control.step planning
        (before.advanceClock.frame
          (Grid.frame profile.taskMode observation result.events.done)).active
        (Grid.frame profile.taskMode observation result.events.done) result.reward
        result.events.done = some (next, decision) ∧
      after = (Agent.mk next aligned episodes).retire
        (before.advanceClock.frame
          (Grid.frame profile.taskMode observation result.events.done)).units ∧
      after.observe.decision = some decision ∧ decision.action.val <
        Acorn.FeatureConstants.primitiveCount
  | .environment _ _ => after.control.runtime = before.control.runtime ∧
      after.control.credit = before.control.credit ∧ after.control.average =
        before.control.average
  | .attempt _ _ _ _ => after.control.runtime = before.control.runtime ∧
      after.control.credit = before.control.credit ∧ after.control.average =
        before.control.average
  | .clear => after = Agent.initial Grid.interface profile config criterion dimension planning
  | .stop => after = before

theorem edge_contract
    (before after : Agent Grid.interface profile config criterion dimension planning)
    (event : AgentInput config criterion dimension) (stopped : Bool)
    (executed : before.input event = (after, stopped)) : EdgeContract before event after :=
      by
  cases event with
  | act observation result =>
    cases executed
    obtain ⟨next, aligned, episodes, actual, replacement⟩ := before.act_execution
      (Grid.percept profile.taskMode observation result.reward result.events.done)
    exact ⟨next, aligned, episodes, _, actual, replacement,
      before.act_decision
        (Grid.percept profile.taskMode observation result.reward result.events.done),
      (before.act (Grid.percept profile.taskMode observation result.reward
        result.events.done)).2.action.isLt⟩
  | environment family reward =>
    cases executed
    exact ⟨rfl, rfl, rfl⟩
  | attempt family cycle steps achieved =>
    cases executed
    exact before.attempt_continuity _ _ _ _
  | clear => cases executed; rfl
  | stop => cases executed; rfl

inductive SafePath : Agent Grid.interface profile config criterion dimension planning →
    List (AgentInput config criterion dimension) →
      Agent Grid.interface profile config criterion dimension planning → Bool → Prop where
  | nil (state : Agent Grid.interface profile config criterion dimension planning)
      (valid : Invariant state) :
      SafePath state [] state false
  | stopped (state next : Agent Grid.interface profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (rest : List (AgentInput config criterion
        dimension))
      (valid : Invariant state) (nextValid : Invariant next) (contract : EdgeContract state
        event next)
      (executed : state.input event = (next, true)) : SafePath state (event :: rest) next
        true
  | continued (state next finalState : Agent Grid.interface profile config criterion dimension
        planning)
      (event : AgentInput config criterion dimension) (rest : List (AgentInput config criterion
        dimension))
      (stopped : Bool) (valid : Invariant state) (contract : EdgeContract state event next)
      (executed : state.input event = (next, false)) (tail : SafePath next rest finalState
        stopped) :
      SafePath state (event :: rest) finalState stopped

theorem path_safe {state finalState : Agent Grid.interface profile config criterion dimension
      planning}
    {events : List (AgentInput config criterion dimension)} {stopped : Bool}
    (path : AgentPath state events finalState stopped) : SafePath state events finalState
      stopped := by
  induction path with
  | nil state => exact .nil state (invariant state)
  | stopped state next event rest step =>
    exact .stopped state next event rest (invariant state) (invariant next)
      (edge_contract state next event true step) step
  | continued state next finalState event rest stopped step tail ih =>
    exact .continued state next finalState event rest stopped (invariant state)
      (edge_contract state next event false step) step ih

theorem native_prefix (admitted : DefaultConstruction)
    (events : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    SafePath admitted.construction.initial.agent events
      (AgentConstruction.execute admitted events).1.agent
      (AgentConstruction.execute admitted events).2 :=
  path_safe (admitted.construction.initial.agent.prefix_path events)

theorem learner_storage (state : Agent Grid.interface profile config criterion dimension planning) :
    (state.control.runtime.lifecycle.consumers.readers.map
      (fun reader => reader.2.state.eligibleCount)).sum ≤
      (Acorn.FeatureConstants.primitiveCount + Acorn.FeatureConstants.metaActionCount +
        Acorn.FeatureConstants.skillCount * (Acorn.FeatureConstants.primitiveCount + 3) +
          demonLayout.length) *
          dimension.capacity := ensemble_capacity _

end AcornVerif.CurrentAgent
