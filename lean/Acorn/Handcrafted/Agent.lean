/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.AgentEpisodes

/-!
# Current full-agent composition

One receiver owns representation, every learner, temporal references, lifetime
observations and both random streams, for every world interface. Its only input is a
percept: a frame and the reward of the preceding transition. Encoding consumes the
frame's words and symbols, the preceding prediction cache and the current bank. The actual temporal dispatcher executes policy,
model and planning updates; the tester follows all consumers of the frame.
No supervisor or replay buffer is part of this action-selection interface.
Native arithmetic, compiler/runtime and allocation retain their declared trust.
-/
namespace Acorn.Handcrafted
open Features

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- Execute the existing local transition once. Its totality proof closes the
potential-source premise; the proof and its existential witnesses are erased. -/
def TemporalControl.alignedStep (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool) :
    { result : TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions //
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

/-- Current state with immutable world interface, profile, feature configuration,
criterion, dimension and planning selection. The stored table closes the
declared-source seam. -/
structure Agent (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) where
  /-- The single composed storage owner, including all observer aggregates. -/
  control : TemporalControl interface profile config criterion dimension
  /-- Every declared option source has an actual matching observation producer. -/
  aligned : control.Aligned
  /-- Episode accounting agrees with the sole active invocation and immutable hierarchy mode. -/
  episodes : control.Episodes

/-- Complete cold initialization reuses the current component constructors. -/
def Agent.initial (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) :
    Agent interface profile config criterion dimension planning :=
  ⟨TemporalControl.initial interface profile config criterion dimension,
    TemporalControl.initial_aligned interface profile config criterion dimension,
    TemporalControl.initial_episodes interface profile config criterion dimension⟩

/-- The representation owns the only lifetime decision clock. -/
def Agent.clock (state : Agent interface profile config criterion dimension planning) : UInt64 :=
  state.control.runtime.lifecycle.representation.progress.clock

/-- Advance the owned clock once, including frozen and primitive-only profiles. -/
def Agent.advanceClock (state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with runtime := { state.control.runtime with
      lifecycle := state.control.runtime.lifecycle.advance } }, state.aligned, state.episodes⟩

/-- The words the coder reads at a frame: the world's, then the feedback of the
predictions this receiver stored at the preceding step. -/
def Agent.words (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) : List SensorWord :=
  observation.words ++
    feedbackWords interface.layout state.control.runtime.references.demonPredictions.words 0

/-- No word of the frame shares a channel with a feedback word. The coder's two word
sources are therefore distinct as words; their hashed feature slots can still
collide, as any two hashed words' can. -/
theorem Agent.words_disjoint (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    ∀ world ∈ observation.words, ∀ feedback ∈ feedbackWords interface.layout
      state.control.runtime.references.demonPredictions.words 0,
        world.channel ≠ feedback.channel := by
  intro world held feedback produced same
  have clear := observation.clear world held
  rw [same, feedbackWords_reserved _ feedback produced] at clear
  cases clear

/-- Encode one frame with this exact receiver's old cache and current bank: the coder
reads the frame's words and the feedback, and the generated units read its symbols. -/
def Agent.frame (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    EncodingFrame dimension state.control.runtime.lifecycle.representation.bank
      (state.words observation) observation.symbols :=
  state.control.runtime.encodeCurrent (state.words observation) observation.symbols

/-- In every world the coder reads at most the interface's word count plus one
feedback word per prediction question. -/
theorem Agent.words_length (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.words observation).length ≤ interface.words + interface.layout.length := by
  have feedback := feedbackWords_length interface.layout
    state.control.runtime.references.demonPredictions.words 0
  have world := observation.bounded
  simp only [Agent.words, List.length_append]
  omega

/-- In every world the active features of one frame are bounded by a function of the
interface and the feature configuration alone. -/
theorem Agent.frame_length (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.frame observation).active.indices.length ≤
      config.tilings.toNat * (interface.words + interface.layout.length) + config.units.count := by
  have words := Nat.mul_le_mul_left config.tilings.toNat (state.words_length observation)
  rw [(state.frame observation).fresh]
  exact Nat.le_trans (encode_length dimension _ (state.words observation) observation.symbols)
    (Nat.add_le_add_right words _)

/-- Releasing any list of units preserves the admitted interest family and distinct units. -/
theorem Ensemble.releaseAll_admitted (units : List (Fin config.units.count)) :
    ∀ (ensemble : Ensemble interface.actions config criterion dimension interface.layout),
      ensemble.Aligned → ensemble.Distinct →
        (ensemble.releaseAll units).Aligned ∧ (ensemble.releaseAll units).Distinct := by
  induction units with
  | nil => intro ensemble aligned distinct; exact ⟨aligned, distinct⟩
  | cons head rest ih =>
    intro ensemble aligned distinct
    exact ih _ (Ensemble.release_aligned _ aligned head) (Ensemble.release_distinct _ head distinct)

/-- The tester preserves the admitted interest family on every branch. -/
theorem TemporalControl.retire_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (active : Vector Bool config.units.count) :
    ({ state with runtime := state.runtime.retire active }).Aligned := by
  have tested := state.runtime.lifecycle.test_preserves state.runtime.references.phase.free active
    (fun ensemble => ensemble.Aligned ∧ ensemble.Distinct)
    (fun ensemble feature held =>
      ⟨ensemble.retire_aligned held.1 feature, Ensemble.retire_distinct _ feature held.2⟩) aligned
  exact Ensemble.releaseAll_admitted
    (state.runtime.lifecycle.test state.runtime.references.phase.free active).2 _ tested.1 tested.2

/-- The tester retains episode observations and the active invocation reference together. -/
theorem TemporalControl.retire_episodes (state : TemporalControl interface profile config criterion dimension)
    (valid : state.Episodes) (active : Vector Bool config.units.count) :
    ({ state with runtime := state.runtime.retire active }).Episodes := by
  unfold TemporalControl.Episodes TemporalControl.activeSlot
  rw [state.runtime.retire_references active]
  exact valid

/-- Frozen execution runs no tester; learning tests only after all frame consumers,
reading the frame's own unit outputs. -/
@[noinline] def Agent.retire (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) : Agent interface profile config criterion dimension planning :=
  if profile.mode == .frozen then state else
    ⟨{ state.control with runtime := state.control.runtime.retire active },
      state.control.retire_aligned state.aligned active,
      state.control.retire_episodes state.episodes active⟩

/-- The actual full decision from one percept: clock, current-bank encoding, temporal
learning and observation, then the receiver-owned tester on the same frame. The
returned decision is the one credited. Its action is one of the interface's. -/
def Agent.act (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    Agent interface profile config criterion dimension planning ×
      TemporalDecision interface.actions :=
  let prepared := state.advanceClock
  let frame := prepared.frame percept.frame
  let result := prepared.control.alignedStep prepared.aligned planning frame.active percept.frame
    percept.reward percept.frame.achieved
  let next : Agent interface profile config criterion dimension planning :=
    ⟨result.1.1, result.2.2, prepared.control.step_episodes result.1.1 prepared.episodes planning
      frame.active percept.frame percept.reward percept.frame.achieved result.1.2 result.2.1⟩
  (next.retire frame.units, result.1.2)

/-- Environment accounting has no access to the policy-selection algorithms. -/
def Agent.recordEnvironment (state : Agent interface profile config criterion dimension planning)
    (family : Fin 4) (reward : Binary32) : Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with lifetime := state.control.lifetime.recordEnvironment state.clock family reward }, state.aligned, state.episodes⟩

/-- Process exit discards unavailable evaluation futures without changing learned state. -/
def Agent.censorObservations (state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with lifetime := state.control.lifetime.censor }, state.aligned, state.episodes⟩

/-- Attempts record their actual outcome as an observation only: no learner, pending
action, previous reward, active option, exploration or learner trajectory reads it. -/
def Agent.recordAttempt (state : Agent interface profile config criterion dimension planning)
    (family : Fin 4) (cycle steps : UInt64) (achieved : Bool) : Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with
      lifetime := state.control.lifetime.recordAttempt family cycle steps achieved }, state.aligned, state.episodes⟩

/-- Explicit clear is fresh construction, including both seeded streams and all observations. -/
def Agent.clear (_state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  Agent.initial interface profile config criterion dimension planning

/-- A structurally admitted image supplies knowledge, durable observations and gain.
Byte parsing and transactional filesystem delivery belong to the persistence owner. -/
structure AgentImage (interface : Interface) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) where
  /-- Receiver-relative feature history, identities and primary knowledge. -/
  features : FeatureImage interface.actions config criterion dimension interface.layout
  /-- Saved host-time reward rate. -/
  gain : RewardRate
  /-- Complete durable observation projection, excluding process-local futures. -/
  lifetime : Lifetime.Durable interface.layout
  /-- The durable episode projection admits no impossible completion or empty duration. -/
  episodes : Lifetime.OptionsValid lifetime.options none

/-- Installation resets process-local references and models, retaining admitted
knowledge, assignment identities, durable gain and lifetime observations. -/
private def Agent.install (state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface config criterion dimension) : Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with
      runtime := state.control.runtime.restore image.features none
      credit := profile.credit.initial
      creditMatches := by cases profile.credit <;> rfl
      average := state.control.average.restore image.gain
      rate := RateState.initial profile.rate
      lifetime := { image.lifetime.restore with
        agreementStarted := some image.features.progress.clock
        agreementLastClock := some image.features.progress.clock } },
    ⟨fun slot => by simp [FeatureRuntime.restore, Ensemble.restore, Interest.Aligned],
      Ensemble.restore_distinct _ _ _ image.features.distinct⟩, by
    constructor
    · intro slot
      exact image.episodes slot
    · intro _; rfl⟩

/-- Profile refusal precedes installation. No partial replacement is returned. -/
def Agent.restore (state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface config criterion dimension) : Option (Agent interface profile config criterion dimension planning) :=
  if profile.checkpointSupported then some (state.install image) else none

/-- Unsupported profiles cannot restore even a structurally legal image. -/
theorem Agent.restore_refuses (state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface config criterion dimension) (unsupported : profile.checkpointSupported = false) :
    state.restore image = none := by simp [Agent.restore, unsupported]

/-- Successful restoration has one exact durable/transient boundary, for every receiver. -/
theorem Agent.restore_components (state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface config criterion dimension) (supported : profile.checkpointSupported = true) :
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
theorem Agent.act_aligned (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (state.act percept).1.control.Aligned := (state.act percept).1.aligned

end Acorn.Handcrafted
