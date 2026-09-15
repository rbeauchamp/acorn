/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission
import AcornVerif.CurrentLifetime
import AcornVerif.CurrentModels

/-!
# Current full-agent finite-prefix contracts

All constructed states carry source alignment, managed learner admission and
activation/episode ownership. Lifetime totals use the proved machine arithmetic;
representation identity and bounded history are supplied by their current owners.
Every finite-prefix edge calls the same receiver-bound transition as the native
consumer. The contracts cover finite-prefix safety, scheduling and observations.
-/
namespace AcornVerif.CurrentAgent
open Acorn Acorn.Features Acorn.Handcrafted
open CurrentLifetime CurrentFeatureConsumers CurrentLearner

/-- Every current channel's stored settled-error sum satisfies its own horizon invariant. -/
def DemonSums : {discounts : List Discount} → Lifetime.DemonRecords discounts → Prop
  | [], .nil => True
  | discount :: _, .cons head tail => Lifetime.LegalSum (.squaredError discount)
    head.durable.squaredError.count
      head.durable.squaredError.sum ∧ DemonSums tail

/-- Channel recursion derives legality from the actual horizon-indexed stored types. -/
theorem demon_sums {discounts : List Discount} (state : Lifetime.DemonRecords discounts) :
  DemonSums state := by
  induction state with
  | nil => trivial
  | cons head tail ih => exact ⟨stored_sum_legal head.durable.squaredError, ih⟩

/-- Complete lifetime numeric contract, including every family and history bucket. -/
def LifetimeSums (state : Lifetime.Stats demonLayout) : Prop :=
  Lifetime.LegalSum .reward state.reward.count state.reward.sum ∧
  (∀ slot : Fin 4, Lifetime.LegalSum .reward state.rewardByFamily[slot.val].count
    state.rewardByFamily[slot.val].sum) ∧
  (∀ slot : Fin Acorn.FeatureConstants.historyBins, Lifetime.LegalSum .reward
    state.rewardHistory[slot.val].count state.rewardHistory[slot.val].sum) ∧
  DemonSums state.demons ∧
  (∀ slot : Fin Acorn.FeatureConstants.historyBins, Lifetime.LegalSum (.squaredError .g99)
    state.errorHistory[slot.val].count state.errorHistory[slot.val].sum)

/-- Every admitted lifetime state has numeric legality, independently of elapsed lifetime. -/
theorem lifetime_sums (state : Lifetime.Stats demonLayout) : LifetimeSums state :=
  ⟨stored_sum_legal _, fun _ => stored_sum_legal _, fun _ => stored_sum_legal _,
    demon_sums _, fun _ => stored_sum_legal _⟩

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

/-- Decision-bearing state contracts over the actual composed storage. -/
structure Invariant (state : Agent profile config criterion dimension planning) : Prop where
  /-- All option objectives have their actual observation producer. -/
  sources : state.control.Aligned
  /-- Completed episodes, duration and outstanding invocation agree. -/
  episodes : state.control.Episodes
  /-- All reward and settled-error totals satisfy their count-indexed numeric bounds. -/
  sums : LifetimeSums state.control.lifetime
  /-- Chronology, resource capacity and clock bounds hold for the owned representation. -/
  history : LegalHistory config state.clock
    state.control.runtime.lifecycle.representation.progress.events
  /-- Every current learner obeys its core numeric and phase-specific eligibility contract. -/
  learners : ∀ reader ∈ state.control.runtime.lifecycle.consumers.readers,
    ScheduleInv reader.2.state reader.2.phase ∧ reader.2.state.eligibleCount ≤
      dimension.capacity

/-- State admission closes each component premise; no application-internal bridge is assumed. -/
theorem invariant (state : Agent profile config criterion dimension planning) : Invariant state
  :=
  ⟨state.aligned, state.episodes, lifetime_sums _,
    state.control.runtime.lifecycle.representation.progress.legal,
    fun reader _ => ⟨managed_schedule reader.2, managed_capacity reader.2⟩⟩

/-- The actual cold constructor satisfies the complete state invariant in every admitted
  configuration. -/
theorem initialization (construction : AgentConstruction) : Invariant construction.initial :=
  invariant _

/-- Per-edge observations constrain actual action execution and non-action isolation. -/
def EdgeContract (before : Agent profile config criterion dimension planning)
    (event : AgentInput config criterion dimension)
    (after : Agent profile config criterion dimension planning) : Prop :=
  match event with
  | .act observation result =>
    ∃ (next : TemporalControl profile config criterion dimension) (aligned : next.Aligned)
      (episodes : next.Episodes) (decision : TemporalDecision),
      before.advanceClock.control.step planning (before.advanceClock.frame observation).active
        observation result.reward result.events.done = some (next, decision) ∧
      after = (Agent.mk next aligned episodes).retire ∧
      after.observe.decision = some decision ∧ decision.action.val <
        Acorn.FeatureConstants.primitiveCount
  | .environment _ _ => after.control.runtime = before.control.runtime ∧
      after.control.credit = before.control.credit ∧ after.control.average =
        before.control.average
  | .attempt _ _ _ _ => after.control.runtime.references = before.control.runtime.references ∧
      after.control.runtime.lifecycle = before.control.runtime.lifecycle ∧
      after.control.credit = before.control.credit ∧ after.control.average =
        before.control.average
  | .clear => after = Agent.initial profile config criterion dimension planning
  | .restore image => before.restore image = some after
  | .stop => after = before

/-- Every accepted public input satisfies its algorithm and observation contract. -/
theorem edge_contract (before after : Agent profile config criterion dimension planning)
    (event : AgentInput config criterion dimension) (stopped : Bool)
    (executed : before.input event = .ok (after, stopped)) : EdgeContract before event after :=
      by
  cases event with
  | act observation result =>
    cases executed
    obtain ⟨next, aligned, episodes, actual, replacement⟩ :=
      before.act_execution observation result.reward result.events.done
    exact ⟨next, aligned, episodes, _, actual, replacement,
      before.act_decision observation result.reward result.events.done,
      (before.act observation result.reward result.events.done).2.action.isLt⟩
  | environment family reward =>
    cases executed
    exact ⟨rfl, rfl, rfl⟩
  | attempt family cycle steps achieved =>
    cases executed
    exact before.attempt_continuity _ _ _ _
  | clear => cases executed; rfl
  | stop => cases executed; rfl
  | restore image =>
    unfold Agent.input at executed
    cases restored : before.restore image with
    | none => simp [restored] at executed
    | some next =>
      simp only [restored, Except.ok.injEq, Prod.mk.injEq] at executed
      rcases executed with ⟨rfl, rfl⟩
      exact restored

/-- Safety at every intermediate receiver, with actual action/observation relations on each
  edge. -/
inductive SafePath : Agent profile config criterion dimension planning →
    List (AgentInput config criterion dimension) →
      Agent profile config criterion dimension planning → Bool → Prop where
  /-- Empty prefixes retain the complete current invariant. -/
  | nil (state : Agent profile config criterion dimension planning) (valid : Invariant state) :
      SafePath state [] state false
  /-- Stop retains its exact boundary receiver and ignores the unconsumed suffix. -/
  | stopped (state next : Agent profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (rest : List (AgentInput config criterion
        dimension))
      (valid : Invariant state) (nextValid : Invariant next) (contract : EdgeContract state
        event next)
      (executed : state.input event = .ok (next, true)) : SafePath state (event :: rest) next
        true
  /-- Each actual continuing edge carries its algorithm relation into the next safe receiver. -/
  | continued (state next finalState : Agent profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (rest : List (AgentInput config criterion
        dimension))
      (stopped : Bool) (valid : Invariant state) (contract : EdgeContract state event next)
      (executed : state.input event = .ok (next, false)) (tail : SafePath next rest finalState
        stopped) :
      SafePath state (event :: rest) finalState stopped

/-- Induction lifts the meaningful state and edge contracts through every intermediate prefix.
-/
theorem path_safe {state finalState : Agent profile config criterion dimension planning}
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

/-- Native prefix execution has the same complete safety and observation contract at every edge.
-/
theorem native_prefix (construction : AgentConstruction) (finalState : construction.State)
    (events : List (AgentInput construction.config construction.criterion
      construction.dimension))
    (stopped : Bool) (executed : construction.execute events = .ok (finalState, stopped)) :
    SafePath construction.initial events finalState stopped :=
  path_safe (construction.initial.prefix_path finalState events stopped executed)

/-- Aggregate learner eligibility storage is bounded by current readers and capacity,
  independently of experience length. -/
theorem learner_storage (state : Agent profile config criterion dimension planning) :
    (state.control.runtime.lifecycle.consumers.readers.map
      (fun reader => reader.2.state.eligibleCount)).sum ≤
      (Acorn.FeatureConstants.primitiveCount + Acorn.FeatureConstants.metaActionCount +
        Acorn.FeatureConstants.skillCount * (Acorn.FeatureConstants.primitiveCount + 3) +
          demonLayout.length) *
          dimension.capacity := ensemble_capacity _

end AcornVerif.CurrentAgent
