import AcornVerif.Separation

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {Φ : Type}

def driven (agent : Agent interface) (percepts : ℕ → Percept interface) : ℕ → agent.Memory
  | 0 => agent.initial
  | time + 1 => (agent.act (driven agent percepts time) (percepts time)).2

def response (agent : Agent interface) (percepts : ℕ → Percept interface) (time : ℕ) :
    Act interface :=
  (agent.act (driven agent percepts time) (percepts time)).1

theorem memoryAt_driven (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) :
    memoryAt world agent start time = driven agent (perceptAt world agent start) time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    change (agent.act (memoryAt world agent start time) (perceptAt world agent start time)).2 =
      (agent.act (driven agent (perceptAt world agent start) time)
        (perceptAt world agent start time)).2
    rw [ih]

theorem actionAt_response (world : World interface) (agent : Agent interface)
    (start : world.State) (time : ℕ) :
    actionAt world agent start time = response agent (perceptAt world agent start) time := by
  change (agent.act (memoryAt world agent start time) (perceptAt world agent start time)).1 = _
  rw [memoryAt_driven]
  rfl

theorem driven_congr (agent : Agent interface) (first second : ℕ → Percept interface)
    (time : ℕ)
    (same : ∀ earlier, earlier < time → first earlier = second earlier) :
    driven agent first time = driven agent second time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    change (agent.act (driven agent first time) (first time)).2 =
      (agent.act (driven agent second time) (second time)).2
    rw [ih (fun earlier before => same earlier (Nat.lt_succ_of_lt before)),
      same time (Nat.lt_succ_self time)]

def FeedbackDriven (feedback : Percept interface → Φ) (agent : Agent interface) : Prop :=
  ∀ (first second : ℕ → Percept interface) (time : ℕ),
    (∀ earlier, earlier ≤ time → feedback (first earlier) = feedback (second earlier)) →
      response agent first time = response agent second time

def Stepped (feedback : Percept interface → Φ) (agent : Agent interface) : Prop :=
  ∃ step : agent.Memory → Φ → Act interface × agent.Memory,
    ∀ memory percept, agent.act memory percept = step memory (feedback percept)

theorem Stepped.feedbackDriven {feedback : Percept interface → Φ} {agent : Agent interface}
    (stepped : Stepped feedback agent) : FeedbackDriven feedback agent := by
  obtain ⟨step, law⟩ := stepped
  intro first second time same
  have memory : ∀ count, count ≤ time →
      driven agent first count = driven agent second count := by
    intro count
    induction count with
    | zero => exact fun _ => rfl
    | succ count ih =>
      intro within
      have earlier := ih (Nat.le_of_succ_le within)
      change (agent.act (driven agent first count) (first count)).2 =
        (agent.act (driven agent second count) (second count)).2
      rw [law, law, earlier, same count (Nat.le_of_succ_le within)]
  change (agent.act (driven agent first time) (first time)).1 =
    (agent.act (driven agent second time) (second time)).1
  rw [law, law, memory time (Nat.le_refl time), same time (Nat.le_refl time)]

def spliced (before : ℕ → Percept interface) (time : ℕ) (after : ℕ → Percept interface) :
    ℕ → Percept interface :=
  fun index => if index < time then before index else after (index - time)

theorem driven_spliced (agent : Agent interface) (before : ℕ → Percept interface) (time : ℕ)
    (after : ℕ → Percept interface) (later : ℕ) :
    driven agent (spliced before time after) (time + later) =
      driven (agent.resume (driven agent before time)) after later := by
  induction later with
  | zero =>
    exact driven_congr agent _ _ time (fun earlier early => by
      simp only [spliced, ite_eq_left early])
  | succ later ih =>
    change (agent.act (driven agent (spliced before time after) (time + later))
        (spliced before time after (time + later))).2 =
      (agent.act (driven (agent.resume (driven agent before time)) after later) (after later)).2
    rw [ih]
    simp only [spliced, ite_eq_right (Nat.not_lt.mpr (Nat.le_add_right time later)),
      Nat.add_sub_cancel_left]

theorem FeedbackDriven.resume {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (before : ℕ → Percept interface) (time : ℕ) :
    FeedbackDriven feedback (agent.resume (driven agent before time)) := by
  intro first second later same
  have joined := blind (spliced before time first) (spliced before time second) (time + later)
    (fun earlier within => by
      by_cases early : earlier < time
      · simp only [spliced, ite_eq_left early]
      · simp only [spliced, ite_eq_right early]
        exact same (earlier - time) (by omega))
  have unfold : ∀ after : ℕ → Percept interface,
      response agent (spliced before time after) (time + later) =
        response (agent.resume (driven agent before time)) after later := by
    intro after
    change (agent.act (driven agent (spliced before time after) (time + later))
        (spliced before time after (time + later))).1 =
      (agent.act (driven (agent.resume (driven agent before time)) after later) (after later)).1
    rw [driven_spliced]
    simp only [spliced, ite_eq_right (Nat.not_lt.mpr (Nat.le_add_right time later)),
      Nat.add_sub_cancel_left]
  rw [← unfold first, ← unfold second]
  exact joined

theorem exists_first {holds : ℕ → Prop} (once : ∃ time, holds time) :
    ∃ time, holds time ∧ ∀ earlier, earlier < time → ¬ holds earlier := by
  obtain ⟨time, held⟩ := once
  induction time using Nat.strongRecOn with
  | _ time ih =>
    by_cases sooner : ∃ earlier, earlier < time ∧ holds earlier
    · obtain ⟨earlier, before, heldEarlier⟩ := sooner
      exact ih earlier before heldEarlier
    · exact ⟨time, held, fun earlier before heldEarlier =>
        sooner ⟨earlier, before, heldEarlier⟩⟩

theorem FeedbackDriven.agree {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) {first second : World interface}
    (origin : first.State) (start : second.State)
    (metFirst : first.State → Prop) (metSecond : second.State → Prop)
    (twins : ∀ (actions : ℕ → Act interface) (time : ℕ),
      (∀ earlier, 1 ≤ earlier → earlier ≤ time →
        ¬ metFirst (path first origin actions earlier)) →
      (∀ earlier, 1 ≤ earlier → earlier ≤ time →
        ¬ metSecond (path second start actions earlier)) →
      feedback (first.percept (path first origin actions time)) =
        feedback (second.percept (path second start actions time)))
    (time : ℕ)
    (unmetFirst : ∀ earlier, 1 ≤ earlier → earlier ≤ time →
      ¬ metFirst (stateAt first agent origin earlier))
    (unmetSecond : ∀ earlier, 1 ≤ earlier → earlier ≤ time →
      ¬ metSecond (stateAt second agent start earlier)) :
    ∀ step, step ≤ time →
      actionAt first agent origin step = actionAt second agent start step := by
  intro step
  induction step using Nat.strongRecOn with
  | _ step ih =>
    intro within
    have track : ∀ count, count ≤ step → stateAt second agent start count =
        path second start (actionAt first agent origin) count := by
      intro count le
      rw [stateAt_eq_path]
      exact path_congr second start _ _ count (fun index before =>
        (ih index (Nat.lt_of_lt_of_le before le)
          (Nat.le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le before le)) within)).symm)
    rw [actionAt_response, actionAt_response]
    refine blind _ _ step (fun earlier le => ?_)
    have shown := twins (actionAt first agent origin) earlier
      (fun moment low high => by
        rw [← stateAt_eq_path]
        exact unmetFirst moment low (Nat.le_trans high (Nat.le_trans le within)))
      (fun moment low high => by
        rw [← track moment (Nat.le_trans high le)]
        exact unmetSecond moment low (Nat.le_trans high (Nat.le_trans le within)))
    change feedback (first.percept (stateAt first agent origin earlier)) =
      feedback (second.percept (stateAt second agent start earlier))
    rw [stateAt_eq_path first agent origin earlier, track earlier le]
    exact shown

theorem FeedbackDriven.fork {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) {first second : World interface}
    (origin : first.State) (start : second.State)
    (goalFirst : AttemptGoal first) (goalSecond : AttemptGoal second)
    (twins : ∀ (actions : ℕ → Act interface) (time : ℕ),
      (∀ earlier, 1 ≤ earlier → earlier ≤ time →
        ¬ goalFirst.satisfied (path first origin actions earlier)) →
      (∀ earlier, 1 ≤ earlier → earlier ≤ time →
        ¬ goalSecond.satisfied (path second start actions earlier)) →
      feedback (first.percept (path first origin actions time)) =
        feedback (second.percept (path second start actions time)))
    (apart : ∀ actions : ℕ → Act interface,
      ¬ (goalFirst.MetBy origin actions ∧ goalSecond.MetBy start actions)) :
    ¬ (Achieves agent goalFirst origin ∧ Achieves agent goalSecond start) := by
  rintro ⟨⟨timeFirst, lowFirst, highFirst, metFirst⟩,
    ⟨timeSecond, lowSecond, highSecond, metSecond⟩⟩
  obtain ⟨soonFirst, ⟨positiveFirst, reachedFirst⟩, noneFirst⟩ := exists_first
    (holds := fun time => 1 ≤ time ∧ goalFirst.satisfied (stateAt first agent origin time))
    ⟨timeFirst, lowFirst, metFirst⟩
  obtain ⟨soonSecond, ⟨positiveSecond, reachedSecond⟩, noneSecond⟩ := exists_first
    (holds := fun time => 1 ≤ time ∧ goalSecond.satisfied (stateAt second agent start time))
    ⟨timeSecond, lowSecond, metSecond⟩
  have capFirst : soonFirst ≤ goalFirst.cap := by
    refine Nat.le_trans (Nat.le_of_not_lt (fun late => ?_)) highFirst
    exact noneFirst timeFirst late ⟨lowFirst, metFirst⟩
  have capSecond : soonSecond ≤ goalSecond.cap := by
    refine Nat.le_trans (Nat.le_of_not_lt (fun late => ?_)) highSecond
    exact noneSecond timeSecond late ⟨lowSecond, metSecond⟩
  rcases Nat.le_total soonFirst soonSecond with order | order
  · have same := blind.agree origin start goalFirst.satisfied goalSecond.satisfied twins
      (soonFirst - 1)
      (fun earlier low high reached => noneFirst earlier (by omega) ⟨low, reached⟩)
      (fun earlier low high reached => noneSecond earlier (by omega) ⟨low, reached⟩)
    refine apart (actionAt second agent start) ⟨⟨soonFirst, positiveFirst, capFirst, ?_⟩,
      (achieves_iff_metBy agent goalSecond start).mp
        ⟨timeSecond, lowSecond, highSecond, metSecond⟩⟩
    rw [stateAt_eq_path] at reachedFirst
    rwa [path_congr first origin (actionAt second agent start) (actionAt first agent origin)
      soonFirst (fun index before => (same index (by omega)).symm)]
  · have same := blind.agree origin start goalFirst.satisfied goalSecond.satisfied twins
      (soonSecond - 1)
      (fun earlier low high reached => noneFirst earlier (by omega) ⟨low, reached⟩)
      (fun earlier low high reached => noneSecond earlier (by omega) ⟨low, reached⟩)
    refine apart (actionAt first agent origin) ⟨(achieves_iff_metBy agent goalFirst origin).mp
      ⟨timeFirst, lowFirst, highFirst, metFirst⟩, ⟨soonSecond, positiveSecond, capSecond, ?_⟩⟩
    rw [stateAt_eq_path] at reachedSecond
    rwa [path_congr second start (actionAt first agent origin) (actionAt second agent start)
      soonSecond (fun index before => same index (by omega))]

variable {E Core V : Type}

def chooser (select : E → V → Act interface × E) (core : Core) (seed : E)
    (prefer : Core → Percept interface → V)
    (advance : Core → Percept interface → Act interface → Core) : Agent interface where
  Memory := Core × E
  initial := (core, seed)
  act := fun memory percept =>
    ((select memory.2 (prefer memory.1 percept)).1,
      (advance memory.1 percept (select memory.2 (prefer memory.1 percept)).1,
        (select memory.2 (prefer memory.1 percept)).2))

theorem chooser_stepped (feedback : Percept interface → Φ)
    (select : E → V → Act interface × E) (core : Core) (seed : E) (prefer : Core → Φ → V)
    (advance : Core → Φ → Act interface → Core) :
    Stepped feedback (chooser select core seed
      (fun inner percept => prefer inner (feedback percept))
      (fun inner percept action => advance inner (feedback percept) action)) :=
  ⟨fun memory shown =>
    ((select memory.2 (prefer memory.1 shown)).1,
      (advance memory.1 shown (select memory.2 (prefer memory.1 shown)).1,
        (select memory.2 (prefer memory.1 shown)).2)),
    fun _ _ => rfl⟩

def aloof (alien : Percept interface → Prop) [DecidablePred alien] (rest : V)
    (prefer : Core → Percept interface → V) : Core → Percept interface → V :=
  fun inner percept => if alien percept then rest else prefer inner percept

theorem aloof_loop (select : E → V → Act interface × E) (core : Core) (seed : E)
    (prefer : Core → Percept interface → V)
    (advance : Core → Percept interface → Act interface → Core)
    (alien : Percept interface → Prop) [DecidablePred alien] (rest : V)
    (world : World interface) (start : world.State)
    (never : ∀ state, ¬ alien (world.percept state)) (time : ℕ) :
    loop world (chooser select core seed (aloof alien rest prefer) advance) start time =
      loop world (chooser select core seed prefer advance) start time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    change interact world (chooser select core seed (aloof alien rest prefer) advance)
        (loop world (chooser select core seed (aloof alien rest prefer) advance) start time) =
      interact world (chooser select core seed prefer advance)
        (loop world (chooser select core seed prefer advance) start time)
    rw [ih]
    generalize loop world (chooser select core seed prefer advance) start time = pair
    have plain : aloof alien rest prefer pair.2.1 (world.percept pair.1) =
        prefer pair.2.1 (world.percept pair.1) := by
      simp only [aloof, never pair.1, ↓reduceIte]
    change (world.step pair.1
        (select pair.2.2 (aloof alien rest prefer pair.2.1 (world.percept pair.1))).1,
      (advance pair.2.1 (world.percept pair.1)
          (select pair.2.2 (aloof alien rest prefer pair.2.1 (world.percept pair.1))).1,
        (select pair.2.2 (aloof alien rest prefer pair.2.1 (world.percept pair.1))).2)) = _
    rw [plain]
    rfl

end AcornVerif.Kernel
