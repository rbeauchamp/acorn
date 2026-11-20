/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! # The frame of a learned-state result

A result on learned agent state is about an agent that, from a cold start on one stream, uses
state that it needs. This module fixes the statements such a result has to prove. A term of
`Result` is a *complete result*: seven necessary conditions, and no more than that. The module
does not fix which goal is posed, over which family of worlds, or how the state is built: those
are the submission's.

**What is fixed.** A `Setting` holds everything about the agent: the seeds its construction
admits, the base agent with its cold construction and its step, what a state mechanism may hand
the base agent with each percept (`extend`), and what the base agent's prediction learners and
control learners hold (`predictor`, `controller`, with the operations that overwrite them). A
submission supplies none of it and changes none of it.

**What a submission supplies.** A `Mechanism`: a memory, and what it hands the base agent with
each percept. And a `Task`: a family of worlds and a goal. The agent a result is about is
`assembled`: the base agent, stepping on each percept extended by what the mechanism hands it.
Nothing else about the step is the submission's.

**What a result must prove.** `Result` has seven fields, each a closed statement with no
hypothesis, each at every seed:

* `meets`: from the cold construction, in every world of the family, the goal holds of the
  assembled agent's run.
* `baseFails`: the base agent alone fails the goal in some world of the family.
* `historyNeeded`: every responder with no history, which emits at each step what a rule of the
  time and the current percept gives, fails the goal in some world of the family. This is a
  statement about the task alone.
* `stateNeeded`: the base agent fed, in place of the mechanism, by any rule of the time and the
  current percept fails the goal in some world of the family.
* `predictionNeeded`: the assembled agent whose prediction learners' store is overwritten before
  every step by any schedule over time fails the goal in some world of the family.
* `controlNeeded`: the same for the control learners' store.
* `learningNeeded`: the same with both stores overwritten.

A rule and a schedule are chosen after the seed and before the world. So `historyNeeded` says
that the goal cannot be satisfied across the family without the past, and the last four fields
say that neither a memory that ignores the stream, nor weights fixed in advance, give a run
that satisfies it across the family.

**What a complete result certifies, and what it does not.** `AcornVerif.LearnedStateFrame`
proves that some goal has a complete result exactly when the goal that only recognizes the
assembled agent's own traces has one (`recognized_iff`). So a complete result certifies that
the assembled agent's trace satisfies the goal and that each compared agent's trace, in some
world, does not. It does not certify that the goal is a task anyone would pose, that
the worlds of the family occur where the agent is run, or that the mechanism's memory was
learned and not written by hand. Those are read by a referee.
-/

namespace AcornVerif.LearnedState

/-! ## Worlds, agents and runs -/

/-- A world: a deterministic state machine with its start, which answers each action with a
successor state and delivers one percept at each state. Randomness, the clock and the task
live in the state. -/
structure World (Percept Action : Type) where
  /-- Everything the next percept and the next transition depend on. -/
  State : Type
  /-- The state before the first percept. -/
  start : State
  /-- The transition. -/
  step : State → Action → State
  /-- The percept delivered at a state. -/
  percept : State → Percept

/-- An agent: its cold construction at each seed, and its step, which turns a state and one
percept into what the step emits and the next state. -/
structure Agent (Seed Percept Output : Type) where
  /-- Everything the agent holds between percepts. -/
  State : Type
  /-- The cold construction: the state before the first percept, at a seed. -/
  cold : Seed → State
  /-- One step. -/
  step : State → Percept → Output × State

/-- Everything that is fixed about the agent. -/
structure Setting where
  /-- The seeds the cold construction admits. -/
  Seed : Type
  /-- The construction admits a seed. -/
  seeded : Nonempty Seed
  /-- What a world delivers at each step. -/
  Percept : Type
  /-- What a world receives at each step. -/
  Action : Type
  /-- What a step emits, which a goal may read. -/
  Output : Type
  /-- The action of what a step emits. -/
  action : Output → Action
  /-- The base agent, with its learners. -/
  base : Agent Seed Percept Output
  /-- What a state mechanism may hand the base agent with a percept. -/
  Extra : Type
  /-- The percept the base agent steps on when handed an extra. -/
  extend : Percept → Extra → Percept
  /-- What the base agent's prediction learners hold. -/
  Predictor : Type
  /-- What the base agent's control learners hold. -/
  Controller : Type
  /-- The prediction learners' store of a state. -/
  predictor : base.State → Predictor
  /-- The control learners' store of a state. -/
  controller : base.State → Controller
  /-- A state with its prediction learners' store overwritten. -/
  setPredictor : base.State → Predictor → base.State
  /-- A state with its control learners' store overwritten. -/
  setController : base.State → Controller → base.State
  /-- Overwriting the prediction store with itself changes nothing. -/
  predictor_same : ∀ state, setPredictor state (predictor state) = state
  /-- Overwriting the control store with itself changes nothing. -/
  controller_same : ∀ state, setController state (controller state) = state

/-- The closed loop of an agent from its cold construction at a seed, in a world from its
start: the world state and the agent state before each step. -/
def run (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (seed : S.Seed)
    (world : World S.Percept S.Action) : Nat → world.State × agent.State
  | 0 => (world.start, agent.cold seed)
  | time + 1 =>
    let before := run S agent seed world time
    let stepped := agent.step before.2 (world.percept before.1)
    (world.step before.1 (S.action stepped.1), stepped.2)

/-- What a goal judges at each time: the world state before the step and what the step
emits. -/
def trace (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (seed : S.Seed)
    (world : World S.Percept S.Action) (time : Nat) : world.State × S.Output :=
  ((run S agent seed world time).1,
    (agent.step (run S agent seed world time).2
      (world.percept (run S agent seed world time).1)).1)

/-! ## What a submission supplies -/

/-- A state mechanism: a memory with its start, what it hands the base agent with each percept,
and how it notes what the step emitted. It reads the percept stream and the agent's own
outputs, and nothing inside the base agent. -/
structure Mechanism (S : Setting) where
  /-- What the mechanism holds between percepts. -/
  Memory : Type
  /-- The memory before the first percept, at a seed. -/
  cold : S.Seed → Memory
  /-- With a percept: what the mechanism hands the base agent, and its memory after reading. -/
  read : Memory → S.Percept → S.Extra × Memory
  /-- Its memory after the step's output. -/
  note : Memory → S.Output → Memory

/-- A family of worlds and a goal. The goal reads a world of the family and the trace of a run
in it. It reads no seed and no state of an agent. -/
structure Task (S : Setting) where
  /-- The worlds the goal is posed over. -/
  Family : Type
  /-- The world of a member. -/
  world : Family → World S.Percept S.Action
  /-- The goal, of a member and the trace of a run in its world. -/
  goal : (member : Family) → (Nat → (world member).State × S.Output) → Prop

/-! ## The agents a result compares -/

/-- The base agent with a state mechanism, stepping with the base state rewritten first by
`rewrite` at the time. The mechanism reads the percept, the base agent steps on the percept
extended by what the mechanism hands it, and the mechanism notes the output. -/
abbrev rewritten (S : Setting) (mechanism : Mechanism S)
    (rewrite : Nat → S.base.State → S.base.State) : Agent S.Seed S.Percept S.Output where
  State := (S.base.State × mechanism.Memory) × Nat
  cold seed := ((S.base.cold seed, mechanism.cold seed), 0)
  step state percept :=
    let read := mechanism.read state.1.2 percept
    let stepped := S.base.step (rewrite state.2 state.1.1) (S.extend percept read.1)
    (stepped.1, ((stepped.2, mechanism.note read.2 stepped.1), state.2 + 1))

/-- **The agent a result is about**: the base agent with the mechanism, nothing rewritten. -/
abbrev assembled (S : Setting) (mechanism : Mechanism S) : Agent S.Seed S.Percept S.Output :=
  rewritten S mechanism fun _ state => state

/-- A responder with no history: at each step it emits what a rule of the time and the current
percept gives. It has no learner and no memory but the time. -/
abbrev responding (S : Setting) (reply : Nat → S.Percept → S.Output) :
    Agent S.Seed S.Percept S.Output where
  State := Nat
  cold _ := 0
  step time percept := (reply time percept, time + 1)

/-- The base agent fed, in place of a mechanism, by a rule of the time and the current
percept. -/
abbrev fed (S : Setting) (rule : Nat → S.Percept → S.Extra) : Agent S.Seed S.Percept S.Output where
  State := S.base.State × Nat
  cold seed := (S.base.cold seed, 0)
  step state percept :=
    let stepped := S.base.step state.1 (S.extend percept (rule state.2 percept))
    (stepped.1, (stepped.2, state.2 + 1))

/-- The assembled agent with its prediction learners' store overwritten before every step by a
schedule. -/
abbrev withoutPrediction (S : Setting) (mechanism : Mechanism S) (schedule : Nat → S.Predictor) :
    Agent S.Seed S.Percept S.Output :=
  rewritten S mechanism fun time state => S.setPredictor state (schedule time)

/-- The assembled agent with its control learners' store overwritten before every step by a
schedule. -/
abbrev withoutControl (S : Setting) (mechanism : Mechanism S) (schedule : Nat → S.Controller) :
    Agent S.Seed S.Percept S.Output :=
  rewritten S mechanism fun time state => S.setController state (schedule time)

/-- The assembled agent with both stores overwritten before every step. -/
abbrev withoutLearning (S : Setting) (mechanism : Mechanism S) (predictions : Nat → S.Predictor)
    (controls : Nat → S.Controller) : Agent S.Seed S.Percept S.Output :=
  rewritten S mechanism fun time state =>
    S.setController (S.setPredictor state (predictions time)) (controls time)

/-! ## The obligations -/

/-- An agent meets the goal: at every seed, from its cold construction, in every world of the
family. -/
def Meets (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (task : Task S) : Prop :=
  ∀ seed member, task.goal member (trace S agent seed (task.world member))

/-- An agent fails the goal: from its cold construction at a seed, in some world of the
family. -/
def Fails (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (task : Task S)
    (seed : S.Seed) : Prop :=
  ∃ member, ¬ task.goal member (trace S agent seed (task.world member))

/-- **A complete result**: the seven necessary conditions. A submission that gives no term of
this structure is partial: it is recorded by the fields it proves. -/
structure Result (S : Setting) (mechanism : Mechanism S) (task : Task S) : Prop where
  /-- The assembled agent meets the goal. -/
  meets : Meets S (assembled S mechanism) task
  /-- The base agent fails the goal, at every seed. -/
  baseFails : ∀ seed, Fails S S.base task seed
  /-- Every responder with no history fails the goal: the task itself needs the past. -/
  historyNeeded : ∀ seed reply, Fails S (responding S reply) task seed
  /-- The base agent fed by any rule of the time and the percept fails, at every seed. -/
  stateNeeded : ∀ seed rule, Fails S (fed S rule) task seed
  /-- With the prediction store on any schedule the agent fails, at every seed. -/
  predictionNeeded : ∀ seed schedule, Fails S (withoutPrediction S mechanism schedule) task seed
  /-- With the control store on any schedule the agent fails, at every seed. -/
  controlNeeded : ∀ seed schedule, Fails S (withoutControl S mechanism schedule) task seed
  /-- With both stores on any schedules the agent fails, at every seed. -/
  learningNeeded : ∀ seed predictions controls,
    Fails S (withoutLearning S mechanism predictions controls) task seed

end AcornVerif.LearnedState
