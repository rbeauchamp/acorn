import Acorn.Handcrafted.AgentEpisodes

namespace Acorn.Handcrafted
open Features

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

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

structure Agent (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) where
  control : TemporalControl interface profile config criterion dimension
  aligned : control.Aligned
  episodes : control.Episodes

def Agent.initial (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) :
    Agent interface profile config criterion dimension planning :=
  ⟨TemporalControl.initial interface profile config criterion dimension,
    TemporalControl.initial_aligned interface profile config criterion dimension,
    TemporalControl.initial_episodes interface profile config criterion dimension⟩

def Agent.clock (state : Agent interface profile config criterion dimension planning) : UInt64 :=
  state.control.runtime.lifecycle.representation.progress.clock

def Agent.advanceClock (state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with runtime := { state.control.runtime with
      lifecycle := state.control.runtime.lifecycle.advance } }, state.aligned, state.episodes⟩

def Agent.wordsCosted (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) : Costed (List SensorWord) := do
  let frameWords := observation.words
  let stored ← state.control.runtime.references.demonPredictions.wordsCosted
  let feedback ← feedbackWordsCosted interface.feedback interface.layout stored 0
  Costed.append frameWords feedback

def Agent.words (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) : List SensorWord :=
  (state.wordsCosted observation).val

theorem Agent.words_def (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    state.words observation =
      observation.words ++
        feedbackWords interface.feedback interface.layout
          state.control.runtime.references.demonPredictions.words 0 := rfl

theorem Agent.words_disjoint (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    ∀ world ∈ observation.words, ∀ feedback ∈ feedbackWords interface.feedback interface.layout
      state.control.runtime.references.demonPredictions.words 0,
        world.channel ≠ feedback.channel := by
  intro world held feedback produced same
  have clear := observation.clear world held
  rw [same, feedbackWords_reserved _ feedback produced] at clear
  cases clear

def Agent.frameCosted (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    Costed (EncodingFrame dimension state.control.runtime.lifecycle.representation.bank
      (state.words observation) observation.symbols) := do
  let read ← Costed.attach (state.wordsCosted observation)
  Eq.ndrec (motive := fun words => Costed (EncodingFrame dimension
      state.control.runtime.lifecycle.representation.bank words observation.symbols))
    (state.control.runtime.encodeCurrentCosted read.val observation.symbols) read.property

def Agent.frame (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    EncodingFrame dimension state.control.runtime.lifecycle.representation.bank
      (state.words observation) observation.symbols :=
  (state.frameCosted observation).val

theorem Agent.frame_def (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    state.frame observation =
      state.control.runtime.encodeCurrent (state.words observation) observation.symbols := rfl

theorem Agent.words_length (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.words observation).length ≤ interface.words + interface.layout.length := by
  have feedback := feedbackWords_length interface.feedback interface.layout
    state.control.runtime.references.demonPredictions.words 0
  have world := observation.bounded
  simp only [Agent.words_def, List.length_append]
  omega

theorem Agent.frame_length (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.frame observation).active.indices.length ≤
      config.tilings.toNat * (interface.words + interface.layout.length) + config.units.count := by
  have words := Nat.mul_le_mul_left config.tilings.toNat (state.words_length observation)
  rw [(state.frame observation).fresh]
  exact Nat.le_trans (encode_length dimension _ (state.words observation) observation.symbols)
    (Nat.add_le_add_right words _)

theorem Ensemble.releaseAll_admitted (units : List (Fin config.units.count)) :
    ∀ (ensemble : Ensemble interface.actions config criterion dimension interface.layout),
      ensemble.Aligned → ensemble.Distinct →
        (ensemble.releaseAll units).Aligned ∧ (ensemble.releaseAll units).Distinct := by
  induction units with
  | nil => intro ensemble aligned distinct; exact ⟨aligned, distinct⟩
  | cons head rest ih =>
    intro ensemble aligned distinct
    exact ih _ (Ensemble.release_aligned _ aligned head) (Ensemble.release_distinct _ head distinct)

theorem TemporalControl.retire_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (active : Vector Bool config.units.count) :
    ({ state with runtime := state.runtime.retire active }).Aligned := by
  have tested := state.runtime.lifecycle.test_preserves state.runtime.references.phase.free active
    (fun ensemble => ensemble.Aligned ∧ ensemble.Distinct)
    (fun ensemble feature held =>
      ⟨ensemble.retire_aligned held.1 feature, Ensemble.retire_distinct _ feature held.2⟩) aligned
  exact Ensemble.releaseAll_admitted
    (state.runtime.lifecycle.test state.runtime.references.phase.free active).2 _ tested.1 tested.2

theorem TemporalControl.retire_episodes (state : TemporalControl interface profile config criterion dimension)
    (valid : state.Episodes) (active : Vector Bool config.units.count) :
    ({ state with runtime := state.runtime.retire active }).Episodes := by
  unfold TemporalControl.Episodes TemporalControl.activeSlot
  rw [state.runtime.retire_references active]
  exact valid

@[noinline] def Agent.retire (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) : Agent interface profile config criterion dimension planning :=
  if profile.mode == .frozen then state else
    ⟨{ state.control with runtime := state.control.runtime.retire active },
      state.control.retire_aligned state.aligned active,
      state.control.retire_episodes state.episodes active⟩

def Agent.act (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    Agent interface profile config criterion dimension planning ×
      TemporalDecision interface.actions :=
  let prepared := state.advanceClock
  let frame := (prepared.frameCosted percept.frame).val
  let result := prepared.control.alignedStep prepared.aligned planning frame.active percept.frame
    percept.reward percept.frame.achieved
  let next : Agent interface profile config criterion dimension planning :=
    ⟨result.1.1, result.2.2, prepared.control.step_episodes result.1.1 prepared.episodes planning
      frame.active percept.frame percept.reward percept.frame.achieved result.1.2 result.2.1⟩
  (next.retire frame.units, result.1.2)

def Agent.recordEnvironment (state : Agent interface profile config criterion dimension planning)
    (family : Fin 4) (reward : Binary32) : Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with lifetime := state.control.lifetime.recordEnvironment state.clock family reward }, state.aligned, state.episodes⟩

def Agent.censorObservations (state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with lifetime := state.control.lifetime.censor }, state.aligned, state.episodes⟩

def Agent.recordAttempt (state : Agent interface profile config criterion dimension planning)
    (family : Fin 4) (cycle steps : UInt64) (achieved : Bool) : Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with
      lifetime := state.control.lifetime.recordAttempt family cycle steps achieved }, state.aligned, state.episodes⟩

def Agent.clear (_state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  Agent.initial interface profile config criterion dimension planning

def Agent.beginSession (state : Agent interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨{ state.control with lifetime := { state.control.lifetime.durable.restore with
      agreementStarted := some state.clock
      agreementLastClock := some state.clock } }, state.aligned, state.episodes⟩

structure AgentImage (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) where
  control : TemporalControl interface profile config criterion dimension
  aligned : control.Aligned
  episodes : control.Episodes

def Agent.image (state : Agent interface profile config criterion dimension planning) :
    AgentImage interface profile config criterion dimension :=
  ⟨state.control, state.aligned, state.episodes⟩

def AgentImage.agent (image : AgentImage interface profile config criterion dimension)
    (planning : PlanningSelection) : Agent interface profile config criterion dimension planning :=
  ⟨image.control, image.aligned, image.episodes⟩

theorem Agent.image_agent (state : Agent interface profile config criterion dimension planning) :
    state.image.agent planning = state := rfl

def Agent.restore (_state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface profile config criterion dimension) :
    Option (Agent interface profile config criterion dimension planning) :=
  if profile.checkpointSupported then some (image.agent planning) else none

theorem Agent.restore_refuses (state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface profile config criterion dimension) (unsupported : profile.checkpointSupported = false) :
    state.restore image = none := by simp [Agent.restore, unsupported]

theorem Agent.restore_exact (state : Agent interface profile config criterion dimension planning)
    (image : AgentImage interface profile config criterion dimension) (supported : profile.checkpointSupported = true) :
    state.restore image = some (image.agent planning) := by
  simp [Agent.restore, supported]

theorem Agent.restore_image (state source : Agent interface profile config criterion dimension planning)
    (supported : profile.checkpointSupported = true) : state.restore source.image = some source :=
  state.restore_exact source.image supported

theorem Agent.act_aligned (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (state.act percept).1.control.Aligned := (state.act percept).1.aligned

end Acorn.Handcrafted
