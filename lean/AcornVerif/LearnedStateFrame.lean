/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Targets.LearnedState

namespace AcornVerif.LearnedState

variable {S : Setting}

/-- One more step of a run. -/
theorem run_succ (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (seed : S.Seed)
    (world : World S.Percept S.Action) (time : Nat) :
    run S agent seed world (time + 1) =
      (world.step (run S agent seed world time).1
          (S.action (agent.step (run S agent seed world time).2
            (world.percept (run S agent seed world time).1)).1.shown),
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
theorem world_of_stateless (agent : Agent S.Seed S.Percept S.Output) (reply : S.Percept → S.Shown)
    (stateless : ∀ state percept, (agent.step state percept).1.shown = reply percept)
    (seed : S.Seed) (world : World S.Percept S.Action) (time : Nat) :
    (run S agent seed world time).1 = (run S (responding S fun _ => reply) seed world time).1 := by
  induction time with
  | zero => rfl
  | succ time ih =>
    show world.step (run S agent seed world time).1 (S.action (agent.step _ _).1.shown) =
      world.step (run S (responding S fun _ => reply) seed world time).1
        (S.action (reply (world.percept (run S (responding S fun _ => reply) seed world time).1)))
    rw [stateless, ih]

theorem trace_of_stateless (agent : Agent S.Seed S.Percept S.Output) (reply : S.Percept → S.Shown)
    (stateless : ∀ state percept, (agent.step state percept).1 = ⟨reply percept, false⟩)
    (seed : S.Seed) (world : World S.Percept S.Action) :
    trace S agent seed world = trace S (responding S fun _ => reply) seed world := by
  funext time
  show ((run S agent seed world time).1, (agent.step _ _).1) =
    ((run S (responding S fun _ => reply) seed world time).1,
      ⟨reply (world.percept (run S (responding S fun _ => reply) seed world time).1), false⟩)
  rw [stateless, world_of_stateless agent reply (fun state percept => by rw [stateless]) seed
    world time]

variable {mechanism : Mechanism S} {task : Task S}

theorem Result.history_free_refused (result : Result S mechanism task)
    (agent : Agent S.Seed S.Percept S.Output) (reply : S.Percept → S.Shown)
    (stateless : ∀ state percept, (agent.step state percept).1 = ⟨reply percept, false⟩)
    (seed : S.Seed)
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

/-- A goal over a family whose members are determined by their worlds reads a member only
through its world. -/
theorem sameWorld_of_injective {S : Setting} {Family : Type}
    (world : Family → World S.Percept S.Action)
    (condition : (member : Family) → (Nat → (world member).State × S.Shown) → Prop)
    (scored : (member : Family) → (Nat → (world member).State × S.Shown) → Nat → Prop)
    (injective : ∀ first second, world first = world second → first = second)
    (first second : Family) (same : world first = world second)
    (trace : Nat → (world first).State × S.Output)
    (holds : Verdict (condition first) (scored first) trace) :
    Verdict (condition second) (scored second) (same ▸ trace) := by
  obtain rfl := injective first second same
  exact holds

theorem responding_unflagged (reply : Nat → S.Percept → S.Shown) (seed : S.Seed)
    (world : World S.Percept S.Action) (time : Nat) :
    (trace S (responding S reply) seed world time).2.explored = false := rfl

theorem Verdict.explores_more {State Shown : Type} {condition : (Nat → State × Shown) → Prop}
    {scored : (Nat → State × Shown) → Nat → Prop} {first second : Nat → State × Emitted Shown}
    (same : flagFree first = flagFree second)
    (more : ∃ start, ∀ time, start ≤ time → (second time).2.explored = false →
      (first time).2.explored = false)
    (holds : Verdict condition scored first) : Verdict condition scored second := by
  obtain ⟨met, start, scoredFrom⟩ := holds
  obtain ⟨later, calm⟩ := more
  refine ⟨by rw [← same]; exact met, max start later, fun time after unflagged => ?_⟩
  rw [← same]
  exact scoredFrom time (Nat.le_trans (Nat.le_max_left _ _) after)
    (calm time (Nat.le_trans (Nat.le_max_right _ _) after) unflagged)

theorem Verdict.of_flags {State Shown : Type} {condition : (Nat → State × Shown) → Prop}
    {scored : (Nat → State × Shown) → Nat → Prop} {first second : Nat → State × Emitted Shown}
    (same : flagFree first = flagFree second)
    (exempt : ∃ start, ∀ time, start ≤ time →
      (first time).2.explored ≠ (second time).2.explored → scored (flagFree first) time)
    (holds : Verdict condition scored first) : Verdict condition scored second := by
  obtain ⟨met, start, scoredFrom⟩ := holds
  obtain ⟨later, differ⟩ := exempt
  refine ⟨by rw [← same]; exact met, max start later, fun time after unflagged => ?_⟩
  rw [← same]
  by_cases agree : (first time).2.explored = (second time).2.explored
  · exact scoredFrom time (Nat.le_trans (Nat.le_max_left _ _) after) (agree.trans unflagged)
  · exact differ time (Nat.le_trans (Nat.le_max_right _ _) after) agree

theorem Verdict.flags {State Shown : Type} {condition : (Nat → State × Shown) → Prop}
    {scored : (Nat → State × Shown) → Nat → Prop} {first second : Nat → State × Emitted Shown}
    (same : flagFree first = flagFree second)
    (exempt : ∃ start, ∀ time, start ≤ time →
      (first time).2.explored ≠ (second time).2.explored → scored (flagFree first) time) :
    Verdict condition scored first ↔ Verdict condition scored second := by
  refine ⟨Verdict.of_flags same exempt, Verdict.of_flags same.symm ?_⟩
  obtain ⟨start, differ⟩ := exempt
  exact ⟨start, fun time after other => by
    rw [← same]
    exact differ time after (Ne.symm other)⟩

theorem Task.goal_flags (task : Task S) (member : task.Family)
    (first second : Nat → (task.world member).State × S.Output)
    (same : flagFree first = flagFree second)
    (exempt : ∃ start, ∀ time, start ≤ time →
      (first time).2.explored ≠ (second time).2.explored →
        task.scored member (flagFree first) time) :
    task.goal member first ↔ task.goal member second :=
  Verdict.flags same exempt

theorem Task.goal_explores_more (task : Task S) (member : task.Family)
    (first second : Nat → (task.world member).State × S.Output)
    (same : flagFree first = flagFree second)
    (more : ∃ start, ∀ time, start ≤ time → (second time).2.explored = false →
      (first time).2.explored = false)
    (holds : task.goal member first) : task.goal member second :=
  Verdict.explores_more same more holds

/-- The trace is the assembled agent's, in a world, at some seed. -/
def Recognized (S : Setting) (mechanism : Mechanism S) (world : World S.Percept S.Action)
    (trace : Nat → world.State × S.Output) : Prop :=
  ∃ other, AcornVerif.LearnedState.trace S (assembled S mechanism) other world = trace

def Unrecognized (S : Setting) (mechanism : Mechanism S) {Family : Type}
    (world : Family → World S.Percept S.Action) (agent : Agent S.Seed S.Percept S.Output)
    (seed : S.Seed) : Prop :=
  ∃ member, ¬ Recognized S mechanism (world member) (trace S agent seed (world member))

structure Separated (S : Setting) (mechanism : Mechanism S) {Family : Type}
    (world : Family → World S.Percept S.Action) : Prop where
  baseSeparated : ∀ seed, Unrecognized S mechanism world S.base seed
  historySeparated : ∀ seed reply, Unrecognized S mechanism world (responding S reply) seed
  stateSeparated : ∀ seed rule, Unrecognized S mechanism world (fed S rule) seed
  predictionSeparated : ∀ seed schedule,
    Unrecognized S mechanism world (withoutPrediction S mechanism schedule) seed
  controlSeparated : ∀ seed schedule,
    Unrecognized S mechanism world (withoutControl S mechanism schedule) seed
  learningSeparated : ∀ seed predictions controls,
    Unrecognized S mechanism world (withoutLearning S mechanism predictions controls) seed

theorem Result.unrecognized (result : Result S mechanism task)
    {agent : Agent S.Seed S.Percept S.Output} {seed : S.Seed} (fails : Fails S agent task seed) :
    Unrecognized S mechanism task.world agent seed := by
  obtain ⟨member, failed⟩ := fails
  refine ⟨member, ?_⟩
  rintro ⟨other, same⟩
  exact failed (same ▸ result.meets other member)

theorem Result.separated (result : Result S mechanism task) :
    Separated S mechanism task.world :=
  ⟨fun seed => result.unrecognized (result.baseFails seed),
    fun seed reply => result.unrecognized (result.historyNeeded seed reply),
    fun seed rule => result.unrecognized (result.stateNeeded seed rule),
    fun seed schedule => result.unrecognized (result.predictionNeeded seed schedule),
    fun seed schedule => result.unrecognized (result.controlNeeded seed schedule),
    fun seed predictions controls =>
      result.unrecognized (result.learningNeeded seed predictions controls)⟩

theorem trace_eq_of_flagFree {State Shown : Type} {first second : Nat → State × Emitted Shown}
    (same : flagFree first = flagFree second)
    (flags : ∀ time, (first time).2.explored = (second time).2.explored) : first = second := by
  funext time
  have parts := congrFun same time
  have flag := flags time
  unfold flagFree at parts
  generalize first time = one at parts flag ⊢
  generalize second time = other at parts flag ⊢
  obtain ⟨state, shown, explored⟩ := one
  obtain ⟨state', shown', explored'⟩ := other
  simp only [Prod.mk.injEq] at parts
  obtain ⟨rfl, rfl⟩ := parts
  cases flag
  rfl

def ShownRecognized (S : Setting) (mechanism : Mechanism S) (world : World S.Percept S.Action)
    (shown : Nat → world.State × S.Shown) : Prop :=
  ∃ other, flagFree (trace S (assembled S mechanism) other world) = shown

theorem sameWorld_of_world {S : Setting} {Family : Type}
    (world : Family → World S.Percept S.Action)
    (condition : (one : World S.Percept S.Action) → (Nat → one.State × S.Shown) → Prop)
    (scored : (one : World S.Percept S.Action) → (Nat → one.State × S.Shown) → Nat → Prop)
    (first second : Family) (same : world first = world second)
    (trace : Nat → (world first).State × S.Output)
    (holds : Verdict (condition (world first)) (scored (world first)) trace) :
    Verdict (condition (world second)) (scored (world second)) (same ▸ trace) := by
  have key : ∀ (one other : World S.Percept S.Action) (equal : one = other)
      (trace : Nat → one.State × S.Output),
      Verdict (condition one) (scored one) trace →
        Verdict (condition other) (scored other) (equal ▸ trace) := by
    rintro one other rfl trace holds
    exact holds
  exact key _ _ same trace holds

def recognizer (S : Setting) (mechanism : Mechanism S) {Family : Type}
    (world : Family → World S.Percept S.Action) : Task S where
  Family := Family
  world := world
  condition member := ShownRecognized S mechanism (world member)
  scored _ _ _ := True
  sameWorld := sameWorld_of_world world (ShownRecognized S mechanism) (fun _ _ _ => True)

end AcornVerif.LearnedState
