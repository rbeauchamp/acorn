import AcornVerif.Visits

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

theorem visits_path_within (world : World interface) (start : world.State) (length : ℕ)
    (actions : ℕ → Act interface) (base : ℕ)
    (begun : path (visits world start length) (visitStart world start length) actions base =
      visitStart world start length)
    (step : ℕ) (within : step ≤ length) :
    path (visits world start length) (visitStart world start length) actions (base + step) =
      (path world start (fun index => actions (base + index)) step,
        ⟨step, Nat.lt_succ_of_le within⟩) := by
  induction step with
  | zero => exact begun
  | succ step ih =>
    have earlier := ih (Nat.le_of_succ_le within)
    have short : step < length := Nat.lt_of_succ_le within
    change (visits world start length).step
        (path (visits world start length) (visitStart world start length) actions (base + step))
        (actions (base + step)) = _
    rw [earlier]
    simp only [visits, dite_eq_left short]
    rfl

theorem visits_path_period (world : World interface) (start : world.State) (length : ℕ)
    (actions : ℕ → Act interface) (count : ℕ) :
    path (visits world start length) (visitStart world start length) actions
        (count * (length + 1)) =
      visitStart world start length := by
  induction count with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ count ih =>
    have last := visits_path_within world start length actions (count * (length + 1)) ih length
      (Nat.le_refl length)
    rw [Nat.add_mul, Nat.one_mul]
    change (visits world start length).step
        (path (visits world start length) (visitStart world start length) actions
          (count * (length + 1) + length))
        (actions (count * (length + 1) + length)) = _
    rw [last]
    simp only [visits, dite_eq_right (Nat.lt_irrefl length)]
    rfl

theorem visits_path (world : World interface) (start : world.State) (length : ℕ)
    (actions : ℕ → Act interface) (count step : ℕ) (within : step ≤ length) :
    path (visits world start length) (visitStart world start length) actions
        (count * (length + 1) + step) =
      (path world start (fun index => actions (count * (length + 1) + index)) step,
        ⟨step, Nat.lt_succ_of_le within⟩) :=
  visits_path_within world start length actions (count * (length + 1))
    (visits_path_period world start length actions count) step within

theorem visits_foldl (world : World interface) (start : world.State) (length : ℕ)
    (actions : List (Act interface)) (state : world.State) (count : Fin (length + 1))
    (room : count.val + actions.length ≤ length) :
    actions.foldl (visits world start length).step (state, count) =
      (actions.foldl world.step state,
        ⟨count.val + actions.length, Nat.lt_succ_of_le room⟩) := by
  induction actions generalizing state count with
  | nil => rfl
  | cons head rest ih =>
    have short : count.val < length := by
      rw [List.length_cons] at room
      omega
    have stepped : (visits world start length).step (state, count) head =
        (world.step state head, ⟨count.val + 1, Nat.succ_lt_succ short⟩) := by
      simp only [visits, dite_eq_left short]
    change rest.foldl (visits world start length).step
        ((visits world start length).step (state, count) head) = _
    rw [stepped, ih (world.step state head) ⟨count.val + 1, Nat.succ_lt_succ short⟩
      (by
        rw [List.length_cons] at room
        change count.val + 1 + rest.length ≤ length
        omega)]
    refine Prod.ext rfl (Fin.ext ?_)
    change count.val + 1 + rest.length = count.val + (rest.length + 1)
    omega

theorem visits_step_shape (world : World interface) (start : world.State) (length : ℕ)
    (state : (visits world start length).State) (action : Act interface) :
    (((visits world start length).step state action).2.val = 0 ∧
        ((visits world start length).step state action).1 = start) ∨
      (1 ≤ ((visits world start length).step state action).2.val ∧
        ((visits world start length).step state action).1 = world.step state.1 action) := by
  by_cases within : state.2.val < length
  · have stepped : (visits world start length).step state action =
        (world.step state.1 action, ⟨state.2.val + 1, Nat.succ_lt_succ within⟩) := by
      simp only [visits, dite_eq_left within]
    rw [stepped]
    exact .inr ⟨Nat.succ_pos _, rfl⟩
  · have stepped : (visits world start length).step state action =
        (start, ⟨0, Nat.succ_pos length⟩) := by
      simp only [visits, dite_eq_right within]
    rw [stepped]
    exact .inl ⟨rfl, rfl⟩

theorem visits_shape (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (time : ℕ) :
    ((stateAt (visits world start length) agent (visitStart world start length) time).2.val = 0 ∧
        (stateAt (visits world start length) agent (visitStart world start length) time).1 =
          start) ∨
      (1 ≤ (stateAt (visits world start length) agent (visitStart world start length) time).2.val ∧
        ∃ before action,
          (stateAt (visits world start length) agent (visitStart world start length) time).1 =
            world.step before action) := by
  cases time with
  | zero => exact .inl ⟨rfl, rfl⟩
  | succ time =>
    rcases visits_step_shape world start length
        (stateAt (visits world start length) agent (visitStart world start length) time)
        (actionAt (visits world start length) agent (visitStart world start length) time) with
      begun | ⟨counted, stepped⟩
    · exact .inl begun
    · exact .inr ⟨counted, _, _, stepped⟩

def WorldClass.inVisits (family : WorldClass interface) (length : ℕ) : WorldClass interface where
  Index := family.Index
  world := fun index => visits (family.world index) (family.start index) length
  start := fun index => visitStart (family.world index) (family.start index) length

def visitsGoals {family : WorldClass interface} (goals : family.Goals) (length : ℕ) :
    (family.inVisits length).Goals :=
  fun index =>
    ⟨fun (state : (family.world index).State × Fin (length + 1)) =>
      1 ≤ state.2.val ∧ (goals index).satisfied state.1, (goals index).cap⟩

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

theorem Conceals.inVisits (hidden : Conceals family goals reference origin) (length : ℕ) :
    Conceals (family.inVisits length) (visitsGoals goals length) (visits reference origin length)
      (visitStart reference origin length) := by
  intro index actions time unmet
  obtain ⟨count, step, within, rfl⟩ :
      ∃ count step, step ≤ length ∧ time = count * (length + 1) + step :=
    ⟨time / (length + 1), time % (length + 1),
      Nat.le_of_lt_succ (Nat.mod_lt time (Nat.succ_pos length)),
      by rw [Nat.mul_comm]; exact (Nat.div_add_mod time (length + 1)).symm⟩
  change (family.world index).percept
      (path (visits (family.world index) (family.start index) length)
        (visitStart (family.world index) (family.start index) length) actions
        (count * (length + 1) + step)).1 =
    reference.percept
      (path (visits reference origin length) (visitStart reference origin length) actions
        (count * (length + 1) + step)).1
  rw [visits_path _ _ _ _ _ _ within, visits_path _ _ _ _ _ _ within]
  refine hidden index (fun later => actions (count * (length + 1) + later)) step
    (fun earlier low high reached => ?_)
  refine unmet (count * (length + 1) + earlier) (by omega) (by omega) ?_
  change 1 ≤ (path (visits (family.world index) (family.start index) length)
      (visitStart (family.world index) (family.start index) length) actions
      (count * (length + 1) + earlier)).2.val ∧
    (goals index).satisfied
      (path (visits (family.world index) (family.start index) length)
        (visitStart (family.world index) (family.start index) length) actions
        (count * (length + 1) + earlier)).1
  rw [visits_path _ _ _ _ _ _ (Nat.le_trans high within)]
  exact ⟨low, reached⟩

end AcornVerif.Kernel
