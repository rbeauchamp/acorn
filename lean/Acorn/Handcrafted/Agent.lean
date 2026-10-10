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
    feedbackWords interface.feedback interface.layout
      state.control.runtime.references.demonPredictions.words 0

/-- No word of the frame shares a channel with a feedback word. The coder's two word
sources are therefore distinct as words; their hashed feature slots can still
collide, as any two hashed words' can. -/
theorem Agent.words_disjoint (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    ∀ world ∈ observation.words, ∀ feedback ∈ feedbackWords interface.feedback interface.layout
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
  have feedback := feedbackWords_length interface.feedback interface.layout
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

/-- A new session of the predictive-agreement evaluator, at the agent's clock. The durable
observations stay; the evaluator's pending futures and its session statistics start empty,
as at the clock of a cold start. A host begins a session after it loads an image, so the
evaluator measures the forecasts of one process. No learner, reference or decision reads
the evaluator, and the learned state is unchanged. -/
def Agent.beginSession (state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with lifetime := { state.control.lifetime.durable.restore with
      agreementStarted := some state.clock
      agreementLastClock := some state.clock } }, state.aligned, state.episodes⟩

/-- The exact image of an agent: every field of its temporal state, with the two invariants
that every agent carries. It holds no planning selection, which is an index of the agent's
type and no stored value. Byte parsing and transactional filesystem delivery belong to the
persistence owner. -/
structure AgentImage (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) where
  /-- Every field of the agent's state. -/
  control : TemporalControl interface profile config criterion dimension
  /-- Every declared option source has an actual matching observation producer. -/
  aligned : control.Aligned
  /-- Episode accounting agrees with the sole active invocation and immutable hierarchy mode. -/
  episodes : control.Episodes

/-- The image of an agent. -/
def Agent.image (state : Agent interface profile config criterion dimension planning) :
    AgentImage interface profile config criterion dimension :=
  ⟨state.control, state.aligned, state.episodes⟩

/-- The agent of an image, under a planning selection. -/
def AgentImage.agent (image : AgentImage interface profile config criterion dimension)
    (planning : PlanningSelection) : Agent interface profile config criterion dimension planning :=
  ⟨image.control, image.aligned, image.episodes⟩

/-- An agent is the agent of its image. -/
theorem Agent.image_agent (state : Agent interface profile config criterion dimension planning) :
    state.image.agent planning = state := rfl

/-- Restoration replaces the receiver by the agent of the image, every field of it. A
profile that cannot restore is refused first; no partial replacement is returned. -/
def Agent.restore (_state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface profile config criterion dimension) :
    Option (Agent interface profile config criterion dimension planning) :=
  if profile.checkpointSupported then some (image.agent planning) else none

/-- Unsupported profiles cannot restore even a structurally legal image. -/
theorem Agent.restore_refuses (state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface profile config criterion dimension) (unsupported : profile.checkpointSupported = false) :
    state.restore image = none := by simp [Agent.restore, unsupported]

/-- **Restoration is exact.** For every receiver and image of a profile that restores, the
restored agent is the agent of the image: no field of the receiver remains. -/
theorem Agent.restore_exact (state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface profile config criterion dimension) (supported : profile.checkpointSupported = true) :
    state.restore image = some (image.agent planning) := by
  simp [Agent.restore, supported]

/-- Restoring the image of an agent into any receiver returns that agent. -/
theorem Agent.restore_image (state source : Agent interface profile config criterion dimension planning)
    (supported : profile.checkpointSupported = true) : state.restore source.image = some source :=
  state.restore_exact source.image supported

/-- Source alignment remains closed under the actual full transition, including retirement. -/
theorem Agent.act_aligned (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (state.act percept).1.control.Aligned := (state.act percept).1.aligned

end Acorn.Handcrafted
