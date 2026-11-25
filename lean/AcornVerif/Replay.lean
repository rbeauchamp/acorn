import AcornVerif.Visits

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

structure ReplayMemory (interface : Interface) where
  step : ℕ
  taken : List (Act interface)
  count : ℕ
  stored : Option (List (Act interface))

def ReplayMemory.record (memory : ReplayMemory interface) (shown : Bool) :
    Option (List (Act interface)) :=
  match memory.stored with
  | some actions => some actions
  | none => if 1 ≤ memory.step ∧ shown = true then some memory.taken.reverse else none

def ReplayMemory.choose (memory : ReplayMemory interface)
    (stored : Option (List (Act interface))) (explore : ℕ → ℕ → Act interface) :
    Act interface :=
  (stored.getD []).getD memory.step (explore memory.count memory.step)

def replay (interface : Interface) (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) : Agent interface where
  Memory := ReplayMemory interface
  initial := ⟨0, [], 0, none⟩
  act := fun memory percept =>
    (memory.choose (memory.record (signal percept)) explore,
      if memory.step < length then
        ⟨memory.step + 1, memory.choose (memory.record (signal percept)) explore :: memory.taken,
          memory.count, memory.record (signal percept)⟩
      else ⟨0, [], memory.count + 1, memory.record (signal percept)⟩)

theorem ReplayMemory.record_kept (memory : ReplayMemory interface) (shown : Bool)
    (actions : List (Act interface)) (kept : memory.stored = some actions) :
    memory.record shown = some actions := by
  unfold ReplayMemory.record
  rw [kept]

theorem ReplayMemory.record_shown (memory : ReplayMemory interface) (positive : 1 ≤ memory.step) :
    ∃ actions, memory.record true = some actions := by
  obtain ⟨step, taken, count, stored⟩ := memory
  cases stored with
  | some kept => exact ⟨kept, rfl⟩
  | none =>
    refine ⟨taken.reverse, ?_⟩
    change (if 1 ≤ step ∧ true = true then some taken.reverse else none) = some taken.reverse
    rw [ite_eq_left ⟨positive, rfl⟩]

theorem replay_action (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (memory : ReplayMemory interface)
    (percept : Percept interface) :
    ((replay interface length signal explore).act memory percept).1 =
      memory.choose (memory.record (signal percept)) explore := rfl

theorem replay_stored (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (memory : ReplayMemory interface)
    (percept : Percept interface) :
    ((replay interface length signal explore).act memory percept).2.stored =
      memory.record (signal percept) := by
  dsimp only [replay]
  split <;> rfl

theorem replay_taken (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (memory : ReplayMemory interface)
    (percept : Percept interface) (short : memory.step < length) :
    ((replay interface length signal explore).act memory percept).2.taken =
      memory.choose (memory.record (signal percept)) explore :: memory.taken := by
  dsimp only [replay]
  rw [ite_eq_left short]

theorem replay_count_within (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (memory : ReplayMemory interface)
    (percept : Percept interface) (short : memory.step < length) :
    ((replay interface length signal explore).act memory percept).2.count = memory.count := by
  dsimp only [replay]
  rw [ite_eq_left short]

theorem replay_count_last (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (memory : ReplayMemory interface)
    (percept : Percept interface) (last : ¬ memory.step < length) :
    ((replay interface length signal explore).act memory percept).2.count = memory.count + 1 := by
  dsimp only [replay]
  rw [ite_eq_right last]

theorem replay_not_experienceFree (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (shown hidden : Percept interface)
    (shows : signal shown = true) (hides : signal hidden = false) :
    ¬ ExperienceFree (replay interface length signal explore) := by
  rintro ⟨advance, law⟩
  have same := (law (⟨1, [], 0, none⟩ : ReplayMemory interface) shown).trans
    (law (⟨1, [], 0, none⟩ : ReplayMemory interface) hidden).symm
  have stored := (replay_stored length signal explore _ shown).symm.trans
    ((congrArg ReplayMemory.stored same).trans (replay_stored length signal explore _ hidden))
  rw [shows, hides] at stored
  simp [ReplayMemory.record] at stored

def ReplayInvariant (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (state : (visits world start length).State)
    (memory : ReplayMemory interface) : Prop :=
  memory.step = state.2.val ∧ memory.taken.length = memory.step ∧
    state.1 = memory.taken.reverse.foldl world.step start ∧
    ∀ actions, memory.stored = some actions →
      1 ≤ actions.length ∧ actions.length ≤ length ∧
        satisfied (actions.foldl world.step start)

theorem replay_invariant_step (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (sound : ∀ state action, signal (world.percept (world.step state action)) = true →
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (inner : world.State) (counter : Fin (length + 1))
    (memory : ReplayMemory interface)
    (holds : ReplayInvariant world start length satisfied (inner, counter) memory) :
    ReplayInvariant world start length satisfied
      ((visits world start length).step (inner, counter)
        ((replay interface length signal explore).act memory (world.percept inner)).1)
      ((replay interface length signal explore).act memory (world.percept inner)).2 := by
  obtain ⟨stepEq, takenLength, innerEq, storedOk⟩ := holds
  change memory.step = counter.val at stepEq
  change inner = memory.taken.reverse.foldl world.step start at innerEq
  have stepped : 1 ≤ memory.step → ∃ before last, inner = world.step before last := by
    intro positive
    cases taken : memory.taken with
    | nil =>
      rw [taken, List.length_nil] at takenLength
      omega
    | cons last rest =>
      refine ⟨rest.reverse.foldl world.step start, last, ?_⟩
      rw [innerEq, taken, List.reverse_cons, List.foldl_append]
      rfl
  have recordOk : ∀ actions, memory.record (signal (world.percept inner)) = some actions →
      1 ≤ actions.length ∧ actions.length ≤ length ∧
        satisfied (actions.foldl world.step start) := by
    intro actions recorded
    cases stored : memory.stored with
    | some kept =>
      rw [memory.record_kept _ kept stored] at recorded
      rw [← Option.some.inj recorded]
      exact storedOk kept stored
    | none =>
      have unfolded : memory.record (signal (world.percept inner)) =
          if 1 ≤ memory.step ∧ signal (world.percept inner) = true then
            some memory.taken.reverse else none := by
        unfold ReplayMemory.record
        rw [stored]
      rw [unfolded] at recorded
      split at recorded
      · rename_i shows
        cases recorded
        refine ⟨?_, ?_, ?_⟩
        · rw [List.length_reverse, takenLength]
          exact shows.1
        · rw [List.length_reverse, takenLength, stepEq]
          exact Nat.le_of_lt_succ counter.isLt
        · rw [← innerEq]
          obtain ⟨before, last, landed⟩ := stepped shows.1
          have shown := shows.2
          rw [landed] at shown ⊢
          exact sound before last shown
      · cases recorded
  by_cases short : counter.val < length
  · have memoryShort : memory.step < length := stepEq ▸ short
    simp only [visits, replay, dite_eq_left short, ite_eq_left memoryShort]
    refine ⟨by rw [stepEq], by rw [List.length_cons, takenLength], ?_, recordOk⟩
    rw [List.reverse_cons, List.foldl_append, ← innerEq]
    rfl
  · have memoryLong : ¬ memory.step < length := stepEq ▸ short
    simp only [visits, replay, dite_eq_right short, ite_eq_right memoryLong]
    exact ⟨rfl, rfl, rfl, recordOk⟩

theorem replay_invariant (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (sound : ∀ state action, signal (world.percept (world.step state action)) = true →
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (time : ℕ) :
    ReplayInvariant world start length satisfied
      (stateAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) time)
      (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) time) := by
  induction time with
  | zero => exact ⟨rfl, rfl, rfl, fun _ stored => by cases stored⟩
  | succ time ih =>
    exact replay_invariant_step world start length satisfied signal sound explore
      (stateAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) time).1
      (stateAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) time).2
      (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) time) ih

theorem replay_stored_keeps (world : World interface) (start : world.State) (length : ℕ)
    (signal : Percept interface → Bool) (explore : ℕ → ℕ → Act interface)
    (time later : ℕ)
    (actions : List (Act interface))
    (kept : (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) time).stored = some actions) :
    (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) (time + later)).stored = some actions := by
  induction later with
  | zero => exact kept
  | succ later ih =>
    change ((replay interface length signal explore).act
      (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (time + later))
      (perceptAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (time + later))).2.stored = some actions
    exact (replay_stored length signal explore _ _).trans
      (ReplayMemory.record_kept _ _ actions ih)

theorem replay_records (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (sound : ∀ state action, signal (world.percept (world.step state action)) = true →
      satisfied (world.step state action))
    (complete : ∀ state action, satisfied (world.step state action) →
      signal (world.percept (world.step state action)) = true)
    (explore : ℕ → ℕ → Act interface) (time : ℕ)
    (positive : 1 ≤ (stateAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) time).2.val)
    (met : satisfied (stateAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) time).1) :
    ∃ actions, (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) (time + 1)).stored = some actions := by
  obtain ⟨stepEq, takenLength, innerEq, -⟩ :=
    replay_invariant world start length satisfied signal sound explore time
  have memoryPositive : 1 ≤ (memoryAt (visits world start length)
      (replay interface length signal explore) (visitStart world start length) time).step := by
    rw [stepEq]
    exact positive
  have shown : signal (perceptAt (visits world start length)
      (replay interface length signal explore)
      (visitStart world start length) time) = true := by
    change signal (world.percept (stateAt (visits world start length)
      (replay interface length signal explore) (visitStart world start length) time).1) = true
    cases taken : (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) time).taken with
    | nil =>
      rw [taken, List.length_nil] at takenLength
      omega
    | cons last rest =>
      have landed : (stateAt (visits world start length) (replay interface length signal explore)
          (visitStart world start length) time).1 =
            world.step (rest.reverse.foldl world.step start) last := by
        rw [innerEq, taken, List.reverse_cons, List.foldl_append]
        rfl
      rw [landed] at met ⊢
      exact complete _ _ met
  change ∃ actions, ((replay interface length signal explore).act
    (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) time)
    (perceptAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) time)).2.stored = some actions
  obtain ⟨found, recorded⟩ := ReplayMemory.record_shown _ memoryPositive
  refine ⟨found, (replay_stored length signal explore _ _).trans ?_⟩
  rw [shown]
  exact recorded

theorem replay_follows (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (sound : ∀ state action, signal (world.percept (world.step state action)) = true →
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (count : ℕ) (actions : List (Act interface))
    (kept : (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) (count * (length + 1))).stored = some actions)
    (short : actions.length ≤ length) (step : ℕ) (within : step ≤ actions.length) :
    (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) (count * (length + 1) + step)).taken.reverse =
        actions.take step := by
  induction step with
  | zero =>
    obtain ⟨stepEq, takenLength, -, -⟩ :=
      replay_invariant world start length satisfied signal sound explore (count * (length + 1))
    rw [visits_period] at stepEq
    have empty := List.eq_nil_of_length_eq_zero (takenLength.trans stepEq)
    rw [Nat.add_zero, empty, List.take_zero]
    rfl
  | succ step ih =>
    have before := ih (Nat.le_of_succ_le within)
    have stillKept := replay_stored_keeps world start length signal explore
      (count * (length + 1)) step actions kept
    obtain ⟨stepEq, -, -, -⟩ :=
      replay_invariant world start length satisfied signal sound explore
        (count * (length + 1) + step)
    have atStep : (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (count * (length + 1) + step)).step = step :=
      stepEq.trans (visits_counter world start length _ count step (by omega))
    have below : step < actions.length := Nat.lt_of_succ_le within
    change ((replay interface length signal explore).act
      (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (count * (length + 1) + step))
      (perceptAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (count * (length + 1) + step))).2.taken.reverse =
      actions.take (step + 1)
    refine (congrArg List.reverse (replay_taken length signal explore _ _
      (by rw [atStep]; omega))).trans ?_
    rw [List.reverse_cons, before]
    unfold ReplayMemory.choose
    rw [ReplayMemory.record_kept _ _ actions stillKept, Option.getD_some, atStep,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem below, Option.getD_some,
      ← List.take_concat_get below, List.concat_eq_append]

theorem replay_stored_solves (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (sound : ∀ state action, signal (world.percept (world.step state action)) = true →
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (visit : ℕ) (actions : List (Act interface))
    (kept : (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) (visit * (length + 1))).stored = some actions) :
    ∃ step, 1 ≤ step ∧ step ≤ length ∧ satisfied
      (stateAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (visit * (length + 1) + step)).1 := by
  obtain ⟨-, -, -, storedOk⟩ :=
    replay_invariant world start length satisfied signal sound explore (visit * (length + 1))
  obtain ⟨nonempty, fits, lands⟩ := storedOk actions kept
  refine ⟨actions.length, nonempty, fits, ?_⟩
  obtain ⟨-, -, innerEq, -⟩ :=
    replay_invariant world start length satisfied signal sound explore
      (visit * (length + 1) + actions.length)
  rw [innerEq, replay_follows world start length satisfied signal sound explore visit actions kept
    fits actions.length (Nat.le_refl _), List.take_length]
  exact lands

theorem replay_step_visit (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (sound : ∀ state action, signal (world.percept (world.step state action)) = true →
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (count step : ℕ) (within : step ≤ length) :
    (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) (count * (length + 1) + step)).step = step :=
  (replay_invariant world start length satisfied signal sound explore _).1.trans
    (visits_counter world start length _ count step within)

theorem replay_count_visit (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (sound : ∀ state action, signal (world.percept (world.step state action)) = true →
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (count : ℕ) :
    ∀ step, step ≤ length →
      (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (count * (length + 1) + step)).count = count := by
  have within : ∀ visit step, step < length →
      (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (visit * (length + 1) + step)).count = visit →
      (memoryAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (visit * (length + 1) + (step + 1))).count = visit := by
    intro visit step short counted
    exact (replay_count_within length signal explore _ _ (lt_of_eq_of_lt
      (replay_step_visit world start length satisfied signal sound explore visit step
        (Nat.le_of_lt short)) short)).trans counted
  induction count with
  | zero =>
    intro step bounded
    induction step with
    | zero =>
      rw [Nat.zero_mul]
      rfl
    | succ step ih => exact within 0 step bounded (ih (Nat.le_of_succ_le bounded))
  | succ count ih =>
    intro step bounded
    induction step with
    | zero =>
      have last := ih length (Nat.le_refl length)
      have boundary : (count + 1) * (length + 1) + 0 = count * (length + 1) + length + 1 := by
        rw [Nat.add_zero, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      rw [boundary]
      have atLast := replay_step_visit world start length satisfied signal sound explore count
        length (Nat.le_refl length)
      exact (replay_count_last length signal explore _ _
        (fun short => Nat.lt_irrefl length (lt_of_eq_of_lt atLast.symm short))).trans
        (congrArg (· + 1) last)
    | succ step ihStep => exact within (count + 1) step bounded (ihStep (Nat.le_of_succ_le bounded))

theorem replay_explored (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (sound : ∀ state action, signal (world.percept (world.step state action)) = true →
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (visit : ℕ)
    (meets : ∃ step, 1 ≤ step ∧ step ≤ length ∧
      satisfied (path world start (explore visit) step)) :
    ∃ step, 1 ≤ step ∧ step ≤ length ∧ satisfied
      (stateAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (visit * (length + 1) + step)).1 := by
  obtain ⟨target, low, high, met⟩ := meets
  cases kept : (memoryAt (visits world start length) (replay interface length signal explore)
      (visitStart world start length) (visit * (length + 1))).stored with
  | some actions =>
    exact replay_stored_solves world start length satisfied signal sound explore visit actions kept
  | none =>
    have claim : ∀ step, step ≤ target →
        (∃ earlier, 1 ≤ earlier ∧ earlier ≤ length ∧ satisfied
          (stateAt (visits world start length) (replay interface length signal explore)
            (visitStart world start length) (visit * (length + 1) + earlier)).1) ∨
        ((memoryAt (visits world start length) (replay interface length signal explore)
            (visitStart world start length) (visit * (length + 1) + step)).stored = none ∧
          (memoryAt (visits world start length) (replay interface length signal explore)
            (visitStart world start length) (visit * (length + 1) + step)).taken.reverse =
            (List.range step).map (explore visit)) := by
      intro step
      induction step with
      | zero =>
        intro _
        obtain ⟨-, takenLength, -, -⟩ :=
          replay_invariant world start length satisfied signal sound explore
            (visit * (length + 1) + 0)
        rw [replay_step_visit world start length satisfied signal sound explore visit 0
          (Nat.zero_le _)] at takenLength
        refine Or.inr ⟨kept, ?_⟩
        rw [List.eq_nil_of_length_eq_zero takenLength]
        rfl
      | succ step ih =>
        intro bounded
        rcases ih (Nat.le_of_succ_le bounded) with solved | ⟨unstored, taken⟩
        · exact Or.inl solved
        have atStep := replay_step_visit world start length satisfied signal sound explore visit
          step (by omega)
        have atCount := replay_count_visit world start length satisfied signal sound explore visit
          step (by omega)
        obtain ⟨-, takenLength, innerEq, -⟩ :=
          replay_invariant world start length satisfied signal sound explore
            (visit * (length + 1) + step)
        by_cases shows : 1 ≤ step ∧ signal (perceptAt (visits world start length)
            (replay interface length signal explore) (visitStart world start length)
            (visit * (length + 1) + step)) = true
        · refine Or.inl ⟨step, shows.1, by omega, ?_⟩
          cases visitTaken : (memoryAt (visits world start length)
              (replay interface length signal explore) (visitStart world start length)
              (visit * (length + 1) + step)).taken with
          | nil =>
            rw [visitTaken, List.length_nil, atStep] at takenLength
            omega
          | cons last rest =>
            have landed : (stateAt (visits world start length)
                (replay interface length signal explore) (visitStart world start length)
                (visit * (length + 1) + step)).1 =
                  world.step (rest.reverse.foldl world.step start) last := by
              rw [innerEq, visitTaken, List.reverse_cons, List.foldl_append]
              rfl
            have shown := shows.2
            change signal (world.percept (stateAt (visits world start length)
              (replay interface length signal explore) (visitStart world start length)
              (visit * (length + 1) + step)).1) = true at shown
            rw [landed] at shown ⊢
            exact sound _ _ shown
        · have quiet : (memoryAt (visits world start length)
              (replay interface length signal explore) (visitStart world start length)
              (visit * (length + 1) + step)).record (signal (perceptAt (visits world start length)
                (replay interface length signal explore) (visitStart world start length)
                (visit * (length + 1) + step))) = none := by
            unfold ReplayMemory.record
            rw [unstored, atStep]
            exact ite_eq_right shows
          right
          refine ⟨(replay_stored length signal explore _ _).trans quiet, ?_⟩
          refine (congrArg List.reverse (replay_taken length signal explore
            (memoryAt (visits world start length) (replay interface length signal explore)
              (visitStart world start length) (visit * (length + 1) + step))
            (perceptAt (visits world start length) (replay interface length signal explore)
              (visitStart world start length) (visit * (length + 1) + step))
            (lt_of_eq_of_lt atStep (by omega)))).trans ?_
          rw [List.reverse_cons, taken, List.range_succ, List.map_append]
          unfold ReplayMemory.choose
          rw [quiet, atStep, atCount]
          rfl
    rcases claim target (Nat.le_refl target) with solved | ⟨-, taken⟩
    · exact solved
    · refine ⟨target, low, high, ?_⟩
      obtain ⟨-, -, innerEq, -⟩ :=
        replay_invariant world start length satisfied signal sound explore
          (visit * (length + 1) + target)
      rw [innerEq, taken, ← path_eq_foldl]
      exact met

theorem replay_keeps (world : World interface) (start : world.State) (length : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (decodes : ∀ state action, signal (world.percept (world.step state action)) = true ↔
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (count later : ℕ) (after : count < later)
    (met : ∃ step, 1 ≤ step ∧ step ≤ length ∧ satisfied
      (stateAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (count * (length + 1) + step)).1) :
    ∃ step, 1 ≤ step ∧ step ≤ length ∧ satisfied
      (stateAt (visits world start length) (replay interface length signal explore)
        (visitStart world start length) (later * (length + 1) + step)).1 := by
  have sound := fun state action => (decodes state action).mp
  have complete := fun state action => (decodes state action).mpr
  obtain ⟨step, low, high, solved⟩ := met
  obtain ⟨actions, recorded⟩ :=
    replay_records world start length satisfied signal sound complete
      explore (count * (length + 1) + step)
      (by rw [visits_counter world start length _ count step high]; exact low) solved
  have whole : (count + 1) * (length + 1) ≤ later * (length + 1) :=
    Nat.mul_le_mul_right (length + 1) after
  rw [Nat.add_mul, Nat.one_mul] at whole
  obtain ⟨gap, split⟩ := Nat.exists_eq_add_of_le
    (show count * (length + 1) + step + 1 ≤ later * (length + 1) by omega)
  have kept := replay_stored_keeps world start length signal explore
    (count * (length + 1) + step + 1) gap actions recorded
  rw [← split] at kept
  exact replay_stored_solves world start length satisfied signal sound explore later actions kept

theorem replay_solves (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (signal : Percept interface → Bool) (explore : ℕ → ℕ → Act interface)
    (index : family.Index)
    (decodes : ∀ state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (count later : ℕ) (after : count < later)
    (solved : SolvesOnVisit family goals length (replay interface length signal explore)
      count index) :
    SolvesOnVisit family goals length (replay interface length signal explore) later index :=
  replay_keeps (family.world index) (family.start index) length (goals index).satisfied signal
    decodes explore count later after solved

theorem replay_solves_explored (family : WorldClass interface) (goals : family.Goals)
    (length : ℕ) (signal : Percept interface → Bool) (explore : ℕ → ℕ → Act interface)
    (index : family.Index)
    (decodes : ∀ state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (visit later : ℕ) (after : visit ≤ later)
    (meets : ∃ step, 1 ≤ step ∧ step ≤ length ∧
      (goals index).satisfied
        (path (family.world index) (family.start index) (explore visit) step)) :
    SolvesOnVisit family goals length (replay interface length signal explore) later index := by
  have first := replay_explored (family.world index) (family.start index) length
    (goals index).satisfied signal (fun state action => (decodes state action).mp) explore visit
    meets
  rcases Nat.lt_or_eq_of_le after with sooner | same
  · exact replay_solves family goals length signal explore index decodes visit later sooner first
  · rw [← same]
    exact first

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

theorem replay_separates (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound)
    (signal : Percept interface → Bool) (explore : ℕ → ℕ → Act interface)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (members : Finset family.Index) (last : ℕ)
    (explored : ∀ index ∈ members, ∃ visit, visit ≤ last ∧
      ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
        (path (family.world index) (family.start index) (explore visit) step))
    (many : bound < members.card) :
    (∀ index ∈ members,
      SolvesOnVisit family goals length (replay interface length signal explore) last index) ∧
    ∀ agent : Agent interface, ExperienceFree agent →
      ∀ (count : ℕ) (solved : Finset family.Index),
        (∀ index ∈ solved, SolvesOnVisit family goals length agent count index) →
          solved.card < members.card := by
  refine ⟨fun index member => ?_, fun agent free count solved each => ?_⟩
  · obtain ⟨visit, before, meets⟩ := explored index member
    exact replay_solves_explored family goals length signal explore index (decodes index) visit
      last before meets
  · exact Nat.lt_of_le_of_lt (visits_need hidden covered free count solved each) many

end AcornVerif.Kernel
