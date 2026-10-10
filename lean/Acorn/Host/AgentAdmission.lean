/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentPrefix
import Acorn.Timing

/-!
# Immutable full-agent construction

Public construction admits the complete nonzero tiling word and bank-size
domain, every power-of-two feature capacity below the UInt32 limit, all current
profile discriminants, either criterion, either planning selection and every step order. Native
allocation remains a runtime boundary; structural admission is not an allocation
or infinite-run liveness promise.
-/
namespace Acorn.Handcrafted
open Features

/-- Complete immutable construction choices for the current agent. -/
structure AgentConstruction where
  /-- All current mode, credit, rate and subtask alternatives. -/
  profile : FeatureProfile
  /-- Criterion fixes the numeric rules and model arity. -/
  criterion : Criterion
  /-- Explicit planning selection. -/
  planning : PlanningSelection
  /-- Declared order of the two step parts, planning and the world's transition. -/
  order : StepOrder
  /-- Receiver-owned feature salt, tilings and unit capacity. -/
  config : Features.Config
  /-- Compiler-admitted hash and learner dimension. -/
  dimension : Dimension

/-- Full word admission before feature allocation; no truncation or default substitution. -/
def AgentConstruction.admit (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (order : StepOrder) (seed tilings : UInt64)
    (units exponent : Nat) : Option AgentConstruction :=
  if ht : 0 < tilings.toNat then
    if hu : 0 < units ∧ units ≤ 65535 then
      if he : exponent < 32 then
        some ⟨profile, criterion, planning, order,
          ⟨seed, tilings, ht, ⟨units, hu.1, hu.2⟩, declaredTester⟩,
          ⟨2^exponent, Nat.pow_pos (by decide), ⟨exponent, rfl⟩, Nat.pow_lt_pow_right (by decide) he⟩⟩
      else none
    else none
  else none

/-- Construction rejects exactly the absent positive/capacity conditions. -/
theorem AgentConstruction.admit_iff (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (order : StepOrder) (seed tilings : UInt64)
    (units exponent : Nat) :
    (admit profile criterion planning order seed tilings units exponent).isSome = true ↔
      0 < tilings.toNat ∧ 0 < units ∧ units ≤ 65535 ∧ exponent < 32 := by
  by_cases ht : 0 < tilings.toNat <;> by_cases hu : 0 < units ∧ units ≤ 65535 <;>
    by_cases he : exponent < 32 <;> simp [admit, ht, hu, he]

/-- Admission keeps the declared step order. -/
theorem AgentConstruction.admit_order (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (order : StepOrder) (seed tilings : UInt64)
    (units exponent : Nat) (construction : AgentConstruction)
    (admitted : admit profile criterion planning order seed tilings units exponent =
      some construction) : construction.order = order := by
  unfold admit at admitted
  split at admitted
  · split at admitted
    · split at admitted
      · cases admitted
        rfl
      · cases admitted
    · cases admitted
  · cases admitted

/-- Every typed dimension lies in the public exponent domain; no admitted shape is omitted. -/
theorem dimension_exponent_complete (dimension : Dimension) :
    ∃ exponent < 32, dimension.capacity = 2^exponent := by
  obtain ⟨exponent, same⟩ := dimension.powerOfTwo
  refine ⟨exponent, ?_, same⟩
  have bound := dimension.wordBound
  rw [same] at bound
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp bound

/-- The CLI default feature configuration is derived from the shared Lean feature constants. -/
def AgentConstruction.standard (seed : UInt64) (selection : Host.AgentSelection)
    (planning : PlanningSelection) (order : StepOrder) : AgentConstruction :=
  ⟨researchProfile selection.profile, selection.criterion, planning, order,
    ⟨seed, Acorn.FeatureConstants.defaultTilings.toUInt64, by decide,
      ⟨Acorn.FeatureConstants.defaultImprintUnits, by decide, by decide⟩, declaredTester⟩,
    ⟨Acorn.FeatureConstants.defaultWeightSpace, by decide, ⟨14, rfl⟩, by decide⟩⟩

/-- The agent of one construction. The construction, and with it the step order, is an
index of the type, so a state of one order and a state of another do not meet by
accident. The learner state it holds carries no order: that every step of its history,
from cold initialization or from an image admitted for the same construction, was taken
under the construction's step order is a claim about the code that made the value. The
operations below make a state, and each of them keeps the construction. No check stops a
module of this project from making a state of another history: the constructor is
private, which stops the constructor notation and the constructor name outside this
module and does not stop a tactic. A state under another index gives the agent's step of
that index's order on the same learner state (`AgentConstruction.callbacks_act`), and a
save that writes that index's word (`AcornVerif.CurrentCheckpoint.saved_header`). -/
structure AgentConstruction.State (construction : AgentConstruction) where
  private mk ::
  /-- The learner state, with all immutable construction choices in its type. -/
  agent : Agent Grid.interface construction.profile construction.config construction.criterion
    construction.dimension construction.planning

/-- Every native constructor calls the full current cold initialization. -/
def AgentConstruction.initial (construction : AgentConstruction) : construction.State :=
  ⟨Agent.initial _ _ _ _ _ _⟩

/-- Cold initialization is the agent's own initial state. -/
theorem AgentConstruction.initial_agent (construction : AgentConstruction) :
    construction.initial.agent = Agent.initial _ _ _ _ _ _ := rfl

/-- A durable image of one construction. The construction is an index of the type, so an
image of one order and a state of another do not meet by accident. This project makes an
image in two places: the snapshot of a state of the construction
(`Acorn.Checkpoint.snapshotImage`), and the admission of a decoded payload whose header
holds the word of the construction's order (`Acorn.Checkpoint.admitPayload`). The
durable image it holds carries no order, and the constructor is public: every module can
apply it to a durable image, and no check stops that. An image under another index is
the payload of the first construction with the order word replaced, which the loader of
the second construction admits with the same durable data
(`AcornVerif.CurrentCheckpoint.relabeled_loaded`). -/
structure AgentConstruction.Image (construction : AgentConstruction) where
  /-- The durable image. -/
  image : AgentImage Grid.interface construction.config construction.criterion
    construction.dimension

/-- Restoration takes an image of the receiver's own construction. The learner state is
replaced by the agent's own restore; a profile that cannot restore is refused. -/
def AgentConstruction.State.restore {construction : AgentConstruction}
    (state : construction.State) (image : construction.Image) : Option construction.State :=
  (state.agent.restore image.image).map (⟨·⟩)

/-- Restoration is the agent's own restore on the admitted image. -/
theorem AgentConstruction.State.restore_agent {construction : AgentConstruction}
    (state : construction.State) (image : construction.Image) :
    (state.restore image).map (·.agent) = state.agent.restore image.image := by
  unfold AgentConstruction.State.restore
  cases state.agent.restore image.image <;> rfl

/-- Censoring the observations a host keeps changes no step and keeps the construction. -/
def AgentConstruction.State.censorObservations {construction : AgentConstruction}
    (state : construction.State) : construction.State :=
  ⟨state.agent.censorObservations⟩

/-- What the agent of one construction holds between the two parts of a step. The first
part of `AgentConstruction.callbacks` makes it. -/
structure AgentConstruction.Chosen (construction : AgentConstruction) where
  private mk ::
  /-- The chosen value of the agent, made under the construction's order. -/
  chosen : Handcrafted.Chosen Grid.interface construction.profile construction.config
    construction.criterion construction.dimension construction.planning

/-- The host callbacks of one construction: the two parts of the construction's own step
order, over the construction's own state type, with that order as the index a host loop
reads. The step, the loop, the state that a checkpoint stamps and the image it admits
all come from the one construction. A campaign does not take this record from a caller:
`AgentConstruction.runCampaign` derives it. The constructor of the record is public, and
no check stops a module of this project from making a record of this type. -/
def AgentConstruction.callbacks (construction : AgentConstruction) :
    Host.AgentCallbacks construction.order construction.State
      (AgentObservation construction.config construction.dimension) :=
  let raw := Agent.callbacks (profile := construction.profile) (config := construction.config)
    (criterion := construction.criterion) (dimension := construction.dimension)
    (planning := construction.planning) construction.order
  { Chosen := construction.Chosen
    choose := fun state observation result =>
      let chosen := raw.choose state.agent observation result
      (chosen.1, ⟨chosen.2⟩)
    learn := fun chosen => ⟨raw.learn chosen.chosen⟩
    recordEnvironment := fun state family reward =>
      ⟨raw.recordEnvironment state.agent family reward⟩
    recordAttempt := fun state family cycle steps achieved =>
      ⟨raw.recordAttempt state.agent family cycle steps achieved⟩
    capture := fun state => raw.capture state.agent
    metrics := fun state => raw.metrics state.agent }

/-- **The whole step of a construction is the agent's step of its order.** For every
construction, state, observation and carried result, the action and the learner state
of the construction's whole step are those of `Agent.callbacks` at the construction's
order on the learner state. -/
theorem AgentConstruction.callbacks_act (construction : AgentConstruction)
    (state : construction.State) (observation : Host.Observation)
    (result : Host.RawStepResult) :
    ((construction.callbacks.act state observation result).1,
        (construction.callbacks.act state observation result).2.agent) =
      (Agent.callbacks construction.order).act state.agent observation result := rfl

/-- The campaign of one construction. A caller gives the construction and no agent
function: the constructor of the agent is the construction's cold initialization, the two
parts of each step are the construction's callbacks, and the index of those callbacks
selects the loop, so the position of the world's transition is that of the construction's
order. The checkpoint hooks are over the construction's state type. The attempt loops take
each transition of the grid world as one call of its step function, which is the discipline
of a world that waits, so the campaign takes the proof that the grid's interface declares
`synchronized` (`Grid.interface_timing`): it runs no world whose interface declares a wall
clock. -/
def AgentConstruction.runCampaign (construction : AgentConstruction)
    (_ : Grid.interface.timing = .synchronized) (config : Host.WorldConfig)
    (seed : UInt64) (selection : Host.AgentSelection) (spec : Host.CampaignSpec)
    (observer : Host.StreamObserver
      (AgentObservation construction.config construction.dimension))
    (checkpoint : Option (Host.CheckpointHooks construction.State)) (readStop : BaseIO Bool) :
    IO (Except Host.RunnerError (Host.CampaignResult config construction.State)) :=
  Host.runCampaign config seed selection spec (fun _ => IO.lazyPure fun _ => construction.initial)
    construction.callbacks observer checkpoint readStop

/-- A construction of the default step order. The finite-prefix transition folds
`Agent.act`, which is the step of that order, so the prefix operations take this type
only. -/
structure DefaultConstruction where
  /-- The construction. -/
  construction : AgentConstruction
  /-- Its step order is the default one. -/
  default : construction.order = .learnThenAct

/-- Fold a finite prefix from a state of a default-order construction. The fold is
`Agent.runPrefix`, whose action edge is `Agent.act`, so its type admits a construction
of the default order and no other. The inputs are the agent's own events; the restore
event holds a durable image with no construction. -/
def DefaultConstruction.runPrefix (admitted : DefaultConstruction)
    (state : admitted.construction.State)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    Except AgentRefusal (admitted.construction.State × Bool) :=
  (state.agent.runPrefix inputs).map fun result => (⟨result.1⟩, result.2)

/-- The prefix of a default-order construction is the agent's own prefix on the learner
state and the same events. -/
theorem DefaultConstruction.runPrefix_agent (admitted : DefaultConstruction)
    (state : admitted.construction.State)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    (admitted.runPrefix state inputs).map (fun result => (result.1.agent, result.2)) =
      state.agent.runPrefix inputs := by
  unfold DefaultConstruction.runPrefix
  cases state.agent.runPrefix inputs <;> rfl

/-- The compiled finite-prefix fold from cold initialization, for a construction of the
default order. It takes the agent's own events. -/
@[noinline] def AgentConstruction.execute (admitted : DefaultConstruction)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    Except AgentRefusal (admitted.construction.State × Bool) :=
  admitted.runPrefix admitted.construction.initial inputs

end Acorn.Handcrafted
