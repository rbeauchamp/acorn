import AcornVerif.Targets.LearnedState

namespace AcornVerif.LearnedState

variable {S : Setting}

theorem run_succ (S : Setting) (agent : Agent S.Seed S.Percept S.Output) (seed : S.Seed)
    (world : World S.Percept S.Action) (time : Nat) :
    run S agent seed world (time + 1) =
      (world.step (run S agent seed world time).1
          (S.action (agent.step (run S agent seed world time).2
            (world.percept (run S agent seed world time).1)).1),
        (agent.step (run S agent seed world time).2
          (world.percept (run S agent seed world time).1)).2) := rfl

theorem rewritten_clock (mechanism : Mechanism S) (rewrite : Nat → S.base.State → S.base.State)
    (seed : S.Seed) (world : World S.Percept S.Action) (time : Nat) :
    (run S (rewritten S mechanism rewrite) seed world time).2.2 = time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [run_succ]
    exact congrArg (· + 1) ih

theorem rewritten_step (mechanism : Mechanism S) (first second : Nat → S.base.State → S.base.State)
    (state : (S.base.State × mechanism.Memory) × Nat) (percept : S.Percept)
    (same : second state.2 state.1.1 = first state.2 state.1.1) :
    (rewritten S mechanism second).step state percept =
      (rewritten S mechanism first).step state percept := by
  simp only [rewritten, same]

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

theorem Result.history_free_refused (result : Result S mechanism task)
    (agent : Agent S.Seed S.Percept S.Output) (reply : S.Percept → S.Output)
    (stateless : ∀ state percept, (agent.step state percept).1 = reply percept) (seed : S.Seed)
    (met : ∀ member, task.goal member (trace S agent seed (task.world member))) : False := by
  obtain ⟨member, fails⟩ := result.historyNeeded seed fun _ => reply
  apply fails
  rw [← trace_of_stateless agent reply stateless seed (task.world member)]
  exact met member

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

theorem Result.stateless_refused (result : Result S mechanism task)
    (recode : S.Percept → S.Extra)
    (stateless : ∀ memory percept, (mechanism.read memory percept).1 = recode percept) :
    False := by
  obtain ⟨seed⟩ := S.seeded
  exact result.handout_not_rule seed ⟨fun _ => recode, fun _ _ => (stateless _ _).symm⟩

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

theorem Result.goal_separates (result : Result S mechanism task) :
    ∃ member, ∃ met failed : Nat → (task.world member).State × S.Output,
      task.goal member met ∧ ¬ task.goal member failed := by
  obtain ⟨seed⟩ := S.seeded
  obtain ⟨member, fails⟩ := result.baseFails seed
  exact ⟨member, _, _, result.meets seed member, fails⟩

theorem sameWorld_of_injective {S : Setting} {Family : Type}
    (world : Family → World S.Percept S.Action)
    (goal : (member : Family) → (Nat → (world member).State × S.Output) → Prop)
    (injective : ∀ first second, world first = world second → first = second)
    (first second : Family) (same : world first = world second)
    (trace : Nat → (world first).State × S.Output) (holds : goal first trace) :
    goal second (same ▸ trace) := by
  obtain rfl := injective first second same
  exact holds

def Recognized (S : Setting) (mechanism : Mechanism S) (world : World S.Percept S.Action)
    (trace : Nat → world.State × S.Output) : Prop :=
  ∃ other, AcornVerif.LearnedState.trace S (assembled S mechanism) other world = trace

theorem Recognized.cast {S : Setting} {mechanism : Mechanism S}
    {first second : World S.Percept S.Action} (same : first = second)
    (trace : Nat → first.State × S.Output) (holds : Recognized S mechanism first trace) :
    Recognized S mechanism second (same ▸ trace) := by
  subst same
  exact holds

def recognizer (S : Setting) (mechanism : Mechanism S) {Family : Type}
    (world : Family → World S.Percept S.Action) : Task S where
  Family := Family
  world := world
  goal member := Recognized S mechanism (world member)
  sameWorld _ _ same trace holds := holds.cast same trace

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

theorem recognized_iff (S : Setting) (mechanism : Mechanism S) {Family : Type}
    (world : Family → World S.Percept S.Action) :
    (∃ goal sameWorld, Result S mechanism ⟨Family, world, goal, sameWorld⟩) ↔
      Result S mechanism (recognizer S mechanism world) :=
  ⟨fun ⟨_, _, result⟩ => result.recognized, fun result => ⟨_, _, result⟩⟩

end AcornVerif.LearnedState
