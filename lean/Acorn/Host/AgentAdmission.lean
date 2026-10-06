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
profile discriminants, either criterion, either planning selection and either step order. Native
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

/-- The agent of one construction. Every step of its history, from cold initialization
or from an image admitted for the same construction, was taken under the construction's
step order. The learner state it holds carries no order; that history is the claim of
this type. The constructor is private to this module, so the operations below are the
only ways to make a state, and each of them keeps the construction: a state of one
construction is not a state of a construction of another order. -/
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

/-- An image admitted for one construction: the step order word of its saved bytes is the
word of the construction's order. `AgentConstruction.admitImage` is its one producer. -/
structure AgentConstruction.Image (construction : AgentConstruction) where
  private mk ::
  /-- The admitted durable image. -/
  image : AgentImage Grid.interface construction.config construction.criterion
    construction.dimension

/-- Admit a decoded image under the step order word that was read from its bytes. A
word that is not the word of the receiving order is refused here, where the typed image
is made, and not only where the header is read. -/
def AgentConstruction.admitImage (construction : AgentConstruction) (word : UInt32)
    (image : AgentImage Grid.interface construction.config construction.criterion
      construction.dimension) : Option construction.Image :=
  if word = construction.order.tag then some ⟨image⟩ else none

/-- **A typed image exists exactly for the receiver's order word.** For every
construction, word and decoded image, admission returns an image exactly when the word
is the word of the construction's order, and the admitted image is the decoded one. -/
theorem AgentConstruction.admitImage_iff (construction : AgentConstruction) (word : UInt32)
    (image : AgentImage Grid.interface construction.config construction.criterion
      construction.dimension) (admitted : construction.Image) :
    construction.admitImage word image = some admitted ↔
      word = construction.order.tag ∧ admitted.image = image := by
  unfold AgentConstruction.admitImage
  constructor
  · intro made
    split at made
    · rename_i same
      cases made
      exact ⟨same, rfl⟩
    · cases made
  · rintro ⟨same, rfl⟩
    cases admitted
    simp [same]

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
part of `AgentConstruction.callbacks` is its one producer. -/
structure AgentConstruction.Chosen (construction : AgentConstruction) where
  private mk ::
  /-- The chosen value of the agent, made under the construction's order. -/
  chosen : Handcrafted.Chosen Grid.interface construction.profile construction.config
    construction.criterion construction.dimension construction.planning

/-- The host callbacks of one construction: the two parts of the construction's own step
order, over the construction's own state type, with that order as the index a host loop
reads. The step, the loop, the state that a checkpoint stamps and the image it admits
all come from the one construction. -/
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

/-- A construction of the default step order. The finite-prefix transition folds
`Agent.act`, which is the step of that order, so the prefix operations take this type
only. -/
structure DefaultConstruction where
  /-- The construction. -/
  construction : AgentConstruction
  /-- Its step order is the default one. -/
  default : construction.order = .learnThenAct

/-- The prefix inputs of one construction. They are the agent's public events, with the
restore event restricted to an image admitted for the same construction. -/
inductive AgentConstruction.Input (construction : AgentConstruction) where
  /-- One decision from the current external observation and previous environment result. -/
  | act (observation : Host.Observation) (result : Host.RawStepResult)
  /-- Account for the environment result after executing the chosen primitive. -/
  | environment (family : Host.GoalFamily) (reward : Binary32)
  /-- Complete an attempt, preserving the continuing stream. -/
  | attempt (family : Host.GoalFamily) (cycle steps : UInt64) (achieved : Bool)
  /-- Explicit fresh construction. -/
  | clear
  /-- Install an image admitted for this construction. -/
  | restore (image : construction.Image)
  /-- Host has reached an admitted stop boundary. -/
  | stop

/-- The agent's event of a construction's input. -/
def AgentConstruction.Input.raw {construction : AgentConstruction} :
    construction.Input →
      AgentInput construction.config construction.criterion construction.dimension
  | .act observation result => .act observation result
  | .environment family reward => .environment family reward
  | .attempt family cycle steps achieved => .attempt family cycle steps achieved
  | .clear => .clear
  | .restore image => .restore image.image
  | .stop => .stop

/-- Fold a finite prefix from a state of a default-order construction. The fold is
`Agent.runPrefix`, whose action edge is `Agent.act`, so its type admits a construction
of the default order and no other. -/
def DefaultConstruction.runPrefix (admitted : DefaultConstruction)
    (state : admitted.construction.State) (inputs : List admitted.construction.Input) :
    Except AgentRefusal (admitted.construction.State × Bool) :=
  (state.agent.runPrefix (inputs.map AgentConstruction.Input.raw)).map fun result =>
    (⟨result.1⟩, result.2)

/-- The prefix of a default-order construction is the agent's own prefix on the learner
state and the agent's events. -/
theorem DefaultConstruction.runPrefix_agent (admitted : DefaultConstruction)
    (state : admitted.construction.State) (inputs : List admitted.construction.Input) :
    (admitted.runPrefix state inputs).map (fun result => (result.1.agent, result.2)) =
      state.agent.runPrefix (inputs.map AgentConstruction.Input.raw) := by
  unfold DefaultConstruction.runPrefix
  cases state.agent.runPrefix (inputs.map AgentConstruction.Input.raw) <;> rfl

/-- The compiled finite-prefix fold from cold initialization, for a construction of the
default order. -/
@[noinline] def AgentConstruction.execute (admitted : DefaultConstruction)
    (inputs : List admitted.construction.Input) :
    Except AgentRefusal (admitted.construction.State × Bool) :=
  admitted.runPrefix admitted.construction.initial inputs

end Acorn.Handcrafted
