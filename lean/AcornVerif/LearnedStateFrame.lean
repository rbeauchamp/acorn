/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Targets.LearnedState

/-! # What a complete result entails, and all that it certifies

For every setting, mechanism and task.

**Consequences of a complete result** (a term of `Result`).
* `Result.history_free_refused`: a goal that an agent whose output is a function of the current
  percept meets in every world has no result.
* `Result.handout_not_rule`: at every seed, what the mechanism hands the base agent along the
  run is not a rule of the time and the current percept. A mechanism whose hand-out ignores its
  memory has no result (`Result.stateless_refused`).
* `Result.predictor_not_schedule`, `Result.controller_not_schedule`: at every seed, what each
  learner store holds along the run is not a schedule over time that is the same in every world
  of the family.
* `Result.family_varied`, `Result.goal_separates`: the family has two worlds, and the goal holds
  of one trace and fails of another.

**All that a complete result certifies about its goal.** `Result.recognized`: every complete
result is also one for the goal "the trace is the assembled agent's at some seed", which
recognizes the submission and asks nothing else. `recognized_iff`: for a mechanism and a family
of worlds, some goal has a complete result exactly when that goal has one. So the fields cannot
tell a task from that goal.
-/

namespace AcornVerif.LearnedState

variable {S : Setting}

/-- One more step of a run. -/
theorem run_succ (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (seed : S.Seed)
    (world : World S.Percept S.Action) (time : Nat) :
    run S agent seed world (time + 1) =
      (world.step (run S agent seed world time).1
          (S.action (agent.step (run S agent seed world time).2
            (world.percept (run S agent seed world time).1)).1),
        (agent.step (run S agent seed world time).2
          (world.percept (run S agent seed world time).1)).2) := rfl

/-- A rewritten agent's clock is the time. -/
theorem rewritten_clock (mechanism : Mechanism S) (rewrite : Nat → S.base.State → S.base.State)
    (seed : S.Seed) (world : World S.Percept S.Action) (time : Nat) :
    (run S (rewritten S mechanism rewrite) seed world time).2.2 = time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [run_succ]
    exact congrArg (· + 1) ih

/-- Two rewrites that agree at a state give one step there. -/
theorem rewritten_step (mechanism : Mechanism S) (first second : Nat → S.base.State → S.base.State)
    (state : (S.base.State × mechanism.Memory) × Nat) (percept : S.Percept)
    (same : second state.2 state.1.1 = first state.2 state.1.1) :
    (rewritten S mechanism second).step state percept =
      (rewritten S mechanism first).step state percept := by
  simp only [rewritten, same]

/-- Two rewrites that agree along the run of the first give one run. -/
theorem run_rewritten (mechanism : Mechanism S) (first second : Nat → S.base.State → S.base.State)
    (seed : S.Seed) (world : World S.Percept S.Action)
    (same : ∀ time,
      second time (run S (rewritten S mechanism first) seed world time).2.1.1 =
        first time (run S (rewritten S mechanism first) seed world time).2.1.1) (time : Nat) :
    run S (rewritten S mechanism second) seed world time =
      run S (rewritten S mechanism first) seed world time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have here : second (run S (rewritten S mechanism first) seed world time).2.2
          (run S (rewritten S mechanism first) seed world time).2.1.1 =
        first (run S (rewritten S mechanism first) seed world time).2.2
          (run S (rewritten S mechanism first) seed world time).2.1.1 := by
      rw [rewritten_clock mechanism first seed world time]
      exact same time
    rw [run_succ, run_succ, ih, rewritten_step mechanism first second _ _ here]

/-- Two rewrites that agree along the run of the first give one trace. -/
theorem trace_rewritten (mechanism : Mechanism S)
    (first second : Nat → S.base.State → S.base.State) (seed : S.Seed)
    (world : World S.Percept S.Action)
    (same : ∀ time,
      second time (run S (rewritten S mechanism first) seed world time).2.1.1 =
        first time (run S (rewritten S mechanism first) seed world time).2.1.1) :
    trace S (rewritten S mechanism second) seed world =
      trace S (rewritten S mechanism first) seed world := by
  funext time
  have here : second (run S (rewritten S mechanism first) seed world time).2.2
        (run S (rewritten S mechanism first) seed world time).2.1.1 =
      first (run S (rewritten S mechanism first) seed world time).2.2
        (run S (rewritten S mechanism first) seed world time).2.1.1 := by
    rw [rewritten_clock mechanism first seed world time]
    exact same time
  unfold trace
  rw [run_rewritten mechanism first second seed world same time,
    rewritten_step mechanism first second _ _ here]

/-- A rule that hands the base agent what the mechanism hands it along the assembled run gives
the assembled run, without the mechanism's memory. -/
theorem run_fed (mechanism : Mechanism S) (rule : Nat → S.Percept → S.Extra) (seed : S.Seed)
    (world : World S.Percept S.Action)
    (same : ∀ time,
      rule time (world.percept (run S (assembled S mechanism) seed world time).1) =
        (mechanism.read (run S (assembled S mechanism) seed world time).2.1.2
          (world.percept (run S (assembled S mechanism) seed world time).1)).1) (time : Nat) :
    run S (fed S rule) seed world time =
      ((run S (assembled S mechanism) seed world time).1,
        ((run S (assembled S mechanism) seed world time).2.1.1, time)) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have here := same time
    rw [run_succ, ih, run_succ]
    simp only [fed, assembled, rewritten, here]

/-- Under the same hypothesis the fed agent and the assembled agent have one trace. -/
theorem trace_fed (mechanism : Mechanism S) (rule : Nat → S.Percept → S.Extra) (seed : S.Seed)
    (world : World S.Percept S.Action)
    (same : ∀ time,
      rule time (world.percept (run S (assembled S mechanism) seed world time).1) =
        (mechanism.read (run S (assembled S mechanism) seed world time).2.1.2
          (world.percept (run S (assembled S mechanism) seed world time).1)).1) :
    trace S (fed S rule) seed world = trace S (assembled S mechanism) seed world := by
  funext time
  have here := same time
  unfold trace
  rw [run_fed mechanism rule seed world same time]
  simp only [assembled, rewritten, here]

/-- An agent whose output is a function of the current percept moves a world as the responder
with that reply does. -/
theorem world_of_stateless (agent : Agent S.Seed S.Percept S.Output) (reply : S.Percept → S.Output)
    (stateless : ∀ state percept, (agent.step state percept).1 = reply percept) (seed : S.Seed)
    (world : World S.Percept S.Action) (time : Nat) :
    (run S agent seed world time).1 = (run S (responding S fun _ => reply) seed world time).1 := by
  induction time with
  | zero => rfl
  | succ time ih =>
    show world.step (run S agent seed world time).1 (S.action (agent.step _ _).1) =
      world.step (run S (responding S fun _ => reply) seed world time).1
        (S.action (reply (world.percept (run S (responding S fun _ => reply) seed world time).1)))
    rw [stateless, ih]

/-- An agent whose output is a function of the current percept has the trace of the responder
with that reply. -/
theorem trace_of_stateless (agent : Agent S.Seed S.Percept S.Output) (reply : S.Percept → S.Output)
    (stateless : ∀ state percept, (agent.step state percept).1 = reply percept) (seed : S.Seed)
    (world : World S.Percept S.Action) :
    trace S agent seed world = trace S (responding S fun _ => reply) seed world := by
  funext time
  show ((run S agent seed world time).1, (agent.step _ _).1) =
    ((run S (responding S fun _ => reply) seed world time).1,
      reply (world.percept (run S (responding S fun _ => reply) seed world time).1))
  rw [stateless, world_of_stateless agent reply stateless seed world time]

variable {mechanism : Mechanism S} {task : Task S}

/-- **The task needs the past.** If an agent whose output is a function of the current percept
meets the goal in every world of the family, at some seed, there is no result. A constant
emitter and a responder that copies part of the current percept are such agents. -/
theorem Result.history_free_refused (result : Result S mechanism task)
    (agent : Agent S.Seed S.Percept S.Output) (reply : S.Percept → S.Output)
    (stateless : ∀ state percept, (agent.step state percept).1 = reply percept) (seed : S.Seed)
    (met : ∀ member, task.goal member (trace S agent seed (task.world member))) : False := by
  obtain ⟨member, fails⟩ := result.historyNeeded seed fun _ => reply
  apply fails
  rw [← trace_of_stateless agent reply stateless seed (task.world member)]
  exact met member

/-- **The mechanism's hand-out is not a rule.** In a result, at every seed, no rule of
the time and the current percept hands the base agent what the mechanism hands it along the
runs in every world of the family. -/
theorem Result.handout_not_rule (result : Result S mechanism task) (seed : S.Seed) :
    ¬ ∃ rule : Nat → S.Percept → S.Extra, ∀ member time,
      rule time ((task.world member).percept
          (run S (assembled S mechanism) seed (task.world member) time).1) =
        (mechanism.read (run S (assembled S mechanism) seed (task.world member) time).2.1.2
          ((task.world member).percept
            (run S (assembled S mechanism) seed (task.world member) time).1)).1 := by
  rintro ⟨rule, agrees⟩
  obtain ⟨member, fails⟩ := result.stateNeeded seed rule
  apply fails
  rw [trace_fed mechanism rule seed (task.world member) (agrees member)]
  exact result.meets seed member

/-- A mechanism whose hand-out ignores its memory has no result. -/
theorem Result.stateless_refused (result : Result S mechanism task)
    (recode : S.Percept → S.Extra)
    (stateless : ∀ memory percept, (mechanism.read memory percept).1 = recode percept) :
    False := by
  obtain ⟨seed⟩ := S.seeded
  exact result.handout_not_rule seed ⟨fun _ => recode, fun _ _ => (stateless _ _).symm⟩

/-- **The prediction learners' store is not a schedule.** In a result, at every seed, what
the prediction learners hold along the runs is not one schedule over time in every world of
the family. -/
theorem Result.predictor_not_schedule (result : Result S mechanism task) (seed : S.Seed) :
    ¬ ∃ schedule : Nat → S.Predictor, ∀ member time,
      S.predictor (run S (assembled S mechanism) seed (task.world member) time).2.1.1 =
        schedule time := by
  rintro ⟨schedule, follows⟩
  obtain ⟨member, fails⟩ := result.predictionNeeded seed schedule
  apply fails
  have same := trace_rewritten mechanism (fun _ state => state)
    (fun time state => S.setPredictor state (schedule time)) seed (task.world member)
    (fun time => by
      show S.setPredictor _ (schedule time) = _
      rw [← follows member time]
      exact S.predictor_same _)
  exact same ▸ result.meets seed member

/-- **The control learners' store is not a schedule.** In a result, at every seed, what the
control learners hold along the runs is not one schedule over time in every world of the
family. -/
theorem Result.controller_not_schedule (result : Result S mechanism task) (seed : S.Seed) :
    ¬ ∃ schedule : Nat → S.Controller, ∀ member time,
      S.controller (run S (assembled S mechanism) seed (task.world member) time).2.1.1 =
        schedule time := by
  rintro ⟨schedule, follows⟩
  obtain ⟨member, fails⟩ := result.controlNeeded seed schedule
  apply fails
  have same := trace_rewritten mechanism (fun _ state => state)
    (fun time state => S.setController state (schedule time)) seed (task.world member)
    (fun time => by
      show S.setController _ (schedule time) = _
      rw [← follows member time]
      exact S.controller_same _)
  exact same ▸ result.meets seed member

/-- A family whose members all have one world has no result: what the prediction learners hold
in that world, at each time, is a schedule. So the family of a result has two worlds. -/
theorem Result.family_varied (result : Result S mechanism task)
    (single : ∀ first second : task.Family, task.world first = task.world second) : False := by
  obtain ⟨seed⟩ := S.seeded
  obtain ⟨only, _⟩ := result.baseFails seed
  refine result.predictor_not_schedule seed ⟨fun time =>
    S.predictor (run S (assembled S mechanism) seed (task.world only) time).2.1.1, ?_⟩
  intro member time
  exact congrArg
    (fun world => S.predictor (run S (assembled S mechanism) seed world time).2.1.1)
    (single member only)

/-- The goal of a result holds of one trace and fails of another, in one world. -/
theorem Result.goal_separates (result : Result S mechanism task) :
    ∃ member, ∃ met failed : Nat → (task.world member).State × S.Output,
      task.goal member met ∧ ¬ task.goal member failed := by
  obtain ⟨seed⟩ := S.seeded
  obtain ⟨member, fails⟩ := result.baseFails seed
  exact ⟨member, _, _, result.meets seed member, fails⟩

/-! ## All that a complete result certifies -/

/-- A goal over a family whose members are determined by their worlds reads a member only
through its world. -/
theorem sameWorld_of_injective {S : Setting} {Family : Type}
    (world : Family → World S.Percept S.Action)
    (goal : (member : Family) → (Nat → (world member).State × S.Output) → Prop)
    (injective : ∀ first second, world first = world second → first = second)
    (first second : Family) (same : world first = world second)
    (trace : Nat → (world first).State × S.Output) (holds : goal first trace) :
    goal second (same ▸ trace) := by
  obtain rfl := injective first second same
  exact holds

/-- The trace is the assembled agent's, in a world, at some seed. -/
def Recognized (S : Setting) (mechanism : Mechanism S) (world : World S.Percept S.Action)
    (trace : Nat → world.State × S.Output) : Prop :=
  ∃ other, AcornVerif.LearnedState.trace S (assembled S mechanism) other world = trace

/-- Being the assembled agent's trace is read off the world alone. -/
theorem Recognized.cast {S : Setting} {mechanism : Mechanism S}
    {first second : World S.Percept S.Action} (same : first = second)
    (trace : Nat → first.State × S.Output) (holds : Recognized S mechanism first trace) :
    Recognized S mechanism second (same ▸ trace) := by
  subst same
  exact holds

/-- The task that only recognizes the submission: over a family of worlds, the goal "the trace
is the assembled agent's, in that world, at some seed". -/
def recognizer (S : Setting) (mechanism : Mechanism S) {Family : Type}
    (world : Family → World S.Percept S.Action) : Task S where
  Family := Family
  world := world
  goal member := Recognized S mechanism (world member)
  sameWorld _ _ same trace holds := holds.cast same trace

/-- **Every complete result is also one for the task that only recognizes the submission**,
over the same worlds: an agent that fails the goal has, in that world, a trace that is the
assembled agent's at no seed. So no field depends on the goal being a task. -/
theorem Result.recognized {S : Setting} {mechanism : Mechanism S} {task : Task S}
    (result : Result S mechanism task) :
    Result S mechanism (recognizer S mechanism task.world) := by
  have fails : ∀ agent seed, Fails S agent task seed →
      Fails S agent (recognizer S mechanism task.world) seed := by
    rintro agent seed ⟨member, failed⟩
    refine ⟨member, ?_⟩
    rintro ⟨other, same⟩
    exact failed (same ▸ result.meets other member)
  exact ⟨fun seed _ => ⟨seed, rfl⟩,
    fun seed => fails _ seed (result.baseFails seed),
    fun seed reply => fails _ seed (result.historyNeeded seed reply),
    fun seed rule => fails _ seed (result.stateNeeded seed rule),
    fun seed schedule => fails _ seed (result.predictionNeeded seed schedule),
    fun seed schedule => fails _ seed (result.controlNeeded seed schedule),
    fun seed predictions controls =>
      fails _ seed (result.learningNeeded seed predictions controls)⟩

/-- **All that a complete result certifies about its goal.** For a mechanism and a family of
worlds, some task over those worlds has a complete result exactly when the task that only
recognizes the submission has one. -/
theorem recognized_iff (S : Setting) (mechanism : Mechanism S) {Family : Type}
    (world : Family → World S.Percept S.Action) :
    (∃ goal sameWorld, Result S mechanism ⟨Family, world, goal, sameWorld⟩) ↔
      Result S mechanism (recognizer S mechanism world) :=
  ⟨fun ⟨_, _, result⟩ => result.recognized, fun result => ⟨_, _, result⟩⟩

end AcornVerif.LearnedState
