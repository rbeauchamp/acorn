/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.AgentEpisodes

/-!
# Current full-agent composition

One receiver owns representation, every learner, temporal references, lifetime
observations and both random streams. Encoding consumes the preceding prediction
cache and the current bank. The actual temporal dispatcher executes policy,
model and planning updates; retirement follows all consumers of the frame.
No supervisor or replay buffer is part of this action-selection interface.
Native arithmetic, compiler/runtime and allocation retain their declared trust.
-/
namespace Acorn.Handcrafted
open Features

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

/-- Execute the existing local transition once. Its totality proof closes the
potential-source premise; the proof and its existential witnesses are erased. -/
def TemporalControl.alignedStep (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    { result : TemporalControl profile config criterion dimension × TemporalDecision //
      state.step planning features observation reward goal = some result ∧ result.1.Aligned } :=
  match executed : state.step planning features observation reward goal with
  | none => False.elim (by
      obtain ⟨next, decision, accepted, _⟩ := state.step_total aligned planning features observation reward goal
      rw [executed] at accepted
      contradiction)
  | some result => ⟨result, rfl, by
      obtain ⟨next, decision, accepted, valid⟩ := state.step_total aligned planning features observation reward goal
      have same := Option.some.inj (executed.symm.trans accepted)
      cases same
      exact valid⟩

/-- Current state with immutable profile, feature configuration, criterion,
dimension and planning selection. The stored table closes the declared-source seam. -/
structure Agent (profile : FeatureProfile) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (planning : PlanningSelection) where
  /-- The single composed storage owner, including all observer aggregates. -/
  control : TemporalControl profile config criterion dimension
  /-- Every declared option source has an actual matching observation producer. -/
  aligned : control.Aligned
  /-- Episode accounting agrees with the sole active invocation and immutable hierarchy mode. -/
  episodes : control.Episodes

/-- Complete cold initialization reuses the current component constructors. -/
def Agent.initial (profile : FeatureProfile) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (planning : PlanningSelection) : Agent profile config criterion dimension planning :=
  ⟨TemporalControl.initial profile config criterion dimension,
    TemporalControl.initial_aligned profile config criterion dimension,
    TemporalControl.initial_episodes profile config criterion dimension⟩

/-- The representation owns the only lifetime decision clock. -/
def Agent.clock (state : Agent profile config criterion dimension planning) : UInt64 :=
  state.control.runtime.lifecycle.representation.progress.clock

/-- Advance the owned clock once, including frozen and primitive-only profiles. -/
def Agent.advanceClock (state : Agent profile config criterion dimension planning) :
    Agent profile config criterion dimension planning :=
  ⟨{ state.control with runtime := { state.control.runtime with
      lifecycle := state.control.runtime.lifecycle.advance } }, state.aligned, state.episodes⟩

/-- Materialize a frame from this exact receiver, old cache and complete observation. -/
def Agent.frame (state : Agent profile config criterion dimension planning) (observation : Host.Observation) :
    EncodingFrame dimension state.control.runtime.lifecycle.representation.bank
      (observationWords observation (feedbackPredictions state.control.runtime.references.demonPredictions)
        profile.taskMode) (observationPatch observation) :=
  state.control.runtime.encodeCurrent
    (observationWords observation (feedbackPredictions state.control.runtime.references.demonPredictions)
      profile.taskMode) (observationPatch observation)

/-- Receiver-bound retirement preserves the admitted interest family on every branch. -/
theorem TemporalControl.retire_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) : ({ state with runtime := state.runtime.retire }).Aligned := by
  unfold FeatureRuntime.retire
  split
  · exact aligned
  · rename_i unit lifecycle accepted
    obtain ⟨room, eligible, _, same⟩ :=
      (Lifecycle.success_iff state.runtime.lifecycle unit lifecycle).mp accepted
    subst lifecycle
    exact state.runtime.lifecycle.consumers.retire_aligned aligned _

/-- Retirement retains episode observations and the active invocation reference together. -/
theorem TemporalControl.retire_episodes (state : TemporalControl profile config criterion dimension)
    (valid : state.Episodes) : ({ state with runtime := state.runtime.retire }).Episodes := by
  unfold TemporalControl.Episodes TemporalControl.activeSlot
  rw [state.runtime.retire_references.1]
  exact valid

/-- Frozen execution cannot retire a feature; learning scans only after all frame consumers. -/
@[noinline] def Agent.retire (state : Agent profile config criterion dimension planning) :
    Agent profile config criterion dimension planning :=
  if profile.mode == .frozen then state else
    ⟨{ state.control with runtime := state.control.runtime.retire },
      state.control.retire_aligned state.aligned, state.control.retire_episodes state.episodes⟩

/-- The actual full decision: clock, current-bank encoding, temporal learning and
observation, then receiver-owned retirement. The returned decision is the one credited. -/
def Agent.act (state : Agent profile config criterion dimension planning)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    Agent profile config criterion dimension planning × TemporalDecision :=
  let prepared := state.advanceClock
  let frame := prepared.frame observation
  let result := prepared.control.alignedStep prepared.aligned planning frame.active observation reward goal
  let next : Agent profile config criterion dimension planning :=
    ⟨result.1.1, result.2.2, prepared.control.step_episodes result.1.1 prepared.episodes planning
      frame.active observation reward goal result.1.2 result.2.1⟩
  (next.retire, result.1.2)

/-- Environment accounting has no access to the policy-selection algorithms. -/
def Agent.recordEnvironment (state : Agent profile config criterion dimension planning)
    (family : Fin 4) (reward : Binary32) : Agent profile config criterion dimension planning :=
  ⟨{ state.control with lifetime := state.control.lifetime.recordEnvironment state.clock family reward }, state.aligned, state.episodes⟩

/-- Process exit discards unavailable evaluation futures without changing learned state. -/
def Agent.censorObservations (state : Agent profile config criterion dimension planning) :
    Agent profile config criterion dimension planning :=
  ⟨{ state.control with lifetime := state.control.lifetime.censor }, state.aligned, state.episodes⟩

/-- Attempts request ranking and record their actual outcome without resetting
the pending action, previous reward, active option, exploration or learner trajectories. -/
def Agent.recordAttempt (state : Agent profile config criterion dimension planning)
    (family : Fin 4) (cycle steps : UInt64) (achieved : Bool) : Agent profile config criterion dimension planning :=
  ⟨{ state.control.request cycle achieved with
      lifetime := state.control.lifetime.recordAttempt family cycle steps achieved }, state.aligned, state.episodes⟩

/-- Explicit clear is fresh construction, including both seeded streams and all observations. -/
def Agent.clear (_state : Agent profile config criterion dimension planning) :
    Agent profile config criterion dimension planning := Agent.initial profile config criterion dimension planning

/-- A structurally admitted image supplies knowledge, durable observations and gain.
Byte parsing and transactional filesystem delivery belong to the persistence owner. -/
structure AgentImage (config : Features.Config) (criterion : Criterion) (dimension : Dimension) where
  /-- Receiver-relative feature history, identities and primary knowledge. -/
  features : FeatureImage config criterion dimension demonLayout
  /-- Saved host-time reward rate. -/
  gain : RewardRate
  /-- Complete durable observation projection, excluding process-local futures. -/
  lifetime : Lifetime.Durable demonLayout
  /-- The durable episode projection admits no impossible completion or empty duration. -/
  episodes : Lifetime.OptionsValid lifetime.options none

/-- Installation resets process-local references and models, retaining admitted
knowledge, assignment identities, durable gain and lifetime observations. -/
private def Agent.install (state : Agent profile config criterion dimension planning)
    (image : AgentImage config criterion dimension) : Agent profile config criterion dimension planning :=
  ⟨{ state.control with
      runtime := state.control.runtime.restore image.features none
      credit := profile.credit.initial
      creditMatches := by cases profile.credit <;> rfl
      average := state.control.average.restore image.gain
      rate := RateState.initial profile.rate
      lifetime := { image.lifetime.restore with
        agreementStarted := some image.features.progress.clock
        agreementLastClock := some image.features.progress.clock } }, by
    intro slot
    simp [FeatureRuntime.restore, Ensemble.restore, Interest.Aligned], by
    constructor
    · intro slot
      exact image.episodes slot
    · intro _; rfl⟩

/-- Profile refusal precedes installation. No partial replacement is returned. -/
def Agent.restore (state : Agent profile config criterion dimension planning)
    (image : AgentImage config criterion dimension) : Option (Agent profile config criterion dimension planning) :=
  if profile.checkpointSupported then some (state.install image) else none

/-- Unsupported profiles cannot restore even a structurally legal image. -/
theorem Agent.restore_refuses (state : Agent profile config criterion dimension planning)
    (image : AgentImage config criterion dimension) (unsupported : profile.checkpointSupported = false) :
    state.restore image = none := by simp [Agent.restore, unsupported]

/-- Successful restoration has one exact durable/transient boundary, for every receiver. -/
theorem Agent.restore_components (state : Agent profile config criterion dimension planning)
    (image : AgentImage config criterion dimension) (supported : profile.checkpointSupported = true) :
    ∃ restored, state.restore image = some restored ∧
      restored.control.runtime = state.control.runtime.restore image.features none ∧
      restored.control.credit = profile.credit.initial ∧
      restored.control.average.rate = image.gain ∧
      restored.control.rate = RateState.initial profile.rate ∧
      restored.control.lifetime = { image.lifetime.restore with
        agreementStarted := some image.features.progress.clock
        agreementLastClock := some image.features.progress.clock } := by
  refine ⟨state.install image, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp [Agent.restore, supported]

/-- Source alignment remains closed under the actual full transition, including retirement. -/
theorem Agent.act_aligned (state : Agent profile config criterion dimension planning)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    (state.act observation reward goal).1.control.Aligned := (state.act observation reward goal).1.aligned

end Acorn.Handcrafted
