namespace AcornVerif.LearnedState

structure World (Percept Action : Type) where
  State : Type
  start : State
  step : State → Action → State
  percept : State → Percept

structure Agent (Seed Percept Output : Type) where
  State : Type
  cold : Seed → State
  step : State → Percept → Output × State

structure Setting where
  Seed : Type
  seeded : Nonempty Seed
  Percept : Type
  Action : Type
  Output : Type
  action : Output → Action
  base : Agent Seed Percept Output
  Extra : Type
  extend : Percept → Extra → Percept
  Predictor : Type
  Controller : Type
  predictor : base.State → Predictor
  controller : base.State → Controller
  setPredictor : base.State → Predictor → base.State
  setController : base.State → Controller → base.State
  predictor_same : ∀ state, setPredictor state (predictor state) = state
  controller_same : ∀ state, setController state (controller state) = state

def run (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (seed : S.Seed)
    (world : World S.Percept S.Action) : Nat → world.State × agent.State
  | 0 => (world.start, agent.cold seed)
  | time + 1 =>
    let before := run S agent seed world time
    let stepped := agent.step before.2 (world.percept before.1)
    (world.step before.1 (S.action stepped.1), stepped.2)

def trace (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (seed : S.Seed)
    (world : World S.Percept S.Action) (time : Nat) : world.State × S.Output :=
  ((run S agent seed world time).1,
    (agent.step (run S agent seed world time).2
      (world.percept (run S agent seed world time).1)).1)

structure Mechanism (S : Setting) where
  Memory : Type
  cold : S.Seed → Memory
  read : Memory → S.Percept → S.Extra × Memory
  note : Memory → S.Output → Memory

structure Task (S : Setting) where
  Family : Type
  world : Family → World S.Percept S.Action
  goal : (member : Family) → (Nat → (world member).State × S.Output) → Prop
  sameWorld : ∀ (first second : Family) (same : world first = world second)
    (trace : Nat → (world first).State × S.Output), goal first trace → goal second (same ▸ trace)

abbrev rewritten (S : Setting) (mechanism : Mechanism S)
    (rewrite : Nat → S.base.State → S.base.State) : Agent S.Seed S.Percept S.Output where
  State := (S.base.State × mechanism.Memory) × Nat
  cold seed := ((S.base.cold seed, mechanism.cold seed), 0)
  step state percept :=
    let read := mechanism.read state.1.2 percept
    let stepped := S.base.step (rewrite state.2 state.1.1) (S.extend percept read.1)
    (stepped.1, ((stepped.2, mechanism.note read.2 stepped.1), state.2 + 1))

abbrev assembled (S : Setting) (mechanism : Mechanism S) : Agent S.Seed S.Percept S.Output :=
  rewritten S mechanism fun _ state => state

abbrev responding (S : Setting) (reply : Nat → S.Percept → S.Output) :
    Agent S.Seed S.Percept S.Output where
  State := Nat
  cold _ := 0
  step time percept := (reply time percept, time + 1)

abbrev fed (S : Setting) (rule : Nat → S.Percept → S.Extra) : Agent S.Seed S.Percept S.Output where
  State := S.base.State × Nat
  cold seed := (S.base.cold seed, 0)
  step state percept :=
    let stepped := S.base.step state.1 (S.extend percept (rule state.2 percept))
    (stepped.1, (stepped.2, state.2 + 1))

abbrev withoutPrediction (S : Setting) (mechanism : Mechanism S) (schedule : Nat → S.Predictor) :
    Agent S.Seed S.Percept S.Output :=
  rewritten S mechanism fun time state => S.setPredictor state (schedule time)

abbrev withoutControl (S : Setting) (mechanism : Mechanism S) (schedule : Nat → S.Controller) :
    Agent S.Seed S.Percept S.Output :=
  rewritten S mechanism fun time state => S.setController state (schedule time)

abbrev withoutLearning (S : Setting) (mechanism : Mechanism S) (predictions : Nat → S.Predictor)
    (controls : Nat → S.Controller) : Agent S.Seed S.Percept S.Output :=
  rewritten S mechanism fun time state =>
    S.setController (S.setPredictor state (predictions time)) (controls time)

def Meets (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (task : Task S) : Prop :=
  ∀ seed member, task.goal member (trace S agent seed (task.world member))

def Fails (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (task : Task S)
    (seed : S.Seed) : Prop :=
  ∃ member, ¬ task.goal member (trace S agent seed (task.world member))

structure Result (S : Setting) (mechanism : Mechanism S) (task : Task S) : Prop where
  meets : Meets S (assembled S mechanism) task
  baseFails : ∀ seed, Fails S S.base task seed
  historyNeeded : ∀ seed reply, Fails S (responding S reply) task seed
  stateNeeded : ∀ seed rule, Fails S (fed S rule) task seed
  predictionNeeded : ∀ seed schedule, Fails S (withoutPrediction S mechanism schedule) task seed
  controlNeeded : ∀ seed schedule, Fails S (withoutControl S mechanism schedule) task seed
  learningNeeded : ∀ seed predictions controls,
    Fails S (withoutLearning S mechanism predictions controls) task seed

end AcornVerif.LearnedState
