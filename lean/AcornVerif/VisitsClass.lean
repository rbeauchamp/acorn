/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Visits

/-!
# A class of worlds, each run in visits

`AcornVerif.Kernel.visits` runs one world in visits. `WorldClass.inVisits` is a whole class run
that way: each member's world in visits of one length, from the start of a visit. `visitsGoals`
counts a member's goal met at a state of such a world that at least one step of a visit has
reached, as `AcornVerif.Kernel.SolvesOnVisit` does.

`visits_path` gives the states of a world in visits under any action sequence: at step `step` of
visit `count`, the state the world itself reaches after `step` of that visit's actions, with the
step count. So a class that conceals its goals still conceals them when it is run in visits, behind
its reference world run in visits (`Conceals.inVisits`): the theorems of
`AcornVerif.Concealment` then say, of every agent's whole run across visits, that it perceives in a
member what it perceives in the reference until that member's goal is first met.

`visits_foldl` folds a list of actions that fits in the rest of a visit, and `visits_step_shape`
says what a step of a world in visits does: it begins a visit in the start state, or it is a step of
the world itself.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-! ## Paths -/

/-- From a time at which a world in visits is at the start of a visit, under any action sequence,
after at most `length` more steps it is in the state the world itself reaches under those steps'
actions, with the step count. -/
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

/-- Under any action sequence, a world in visits is at the start of a visit after each multiple of
`length + 1` steps. -/
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

/-- The states of a world in visits under any action sequence: at step `step` of visit `count`,
the state the world itself reaches from its start after `step` of that visit's actions, with the
step count. -/
theorem visits_path (world : World interface) (start : world.State) (length : ℕ)
    (actions : ℕ → Act interface) (count step : ℕ) (within : step ≤ length) :
    path (visits world start length) (visitStart world start length) actions
        (count * (length + 1) + step) =
      (path world start (fun index => actions (count * (length + 1) + index)) step,
        ⟨step, Nat.lt_succ_of_le within⟩) :=
  visits_path_within world start length actions (count * (length + 1))
    (visits_path_period world start length actions count) step within

/-- A list of actions that fits in the rest of a visit moves a world in visits as it moves the
world itself, and counts its steps. -/
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

/-- A step of a world in visits begins a visit in the start state, or is a step of the world
itself within a visit. -/
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

/-- Every state of an agent's closed loop in a world in visits, from the start of a visit, is the
start state with no step counted, or a state a step of the world itself reached, with at least one
step counted. -/
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

/-! ## A class in visits -/

/-- A class of worlds, each run in visits of one length from the start of a visit. -/
def WorldClass.inVisits (family : WorldClass interface) (length : ℕ) : WorldClass interface where
  Index := family.Index
  world := fun index => visits (family.world index) (family.start index) length
  start := fun index => visitStart (family.world index) (family.start index) length

/-- The goals of a class run in visits: a member's goal is met at a state that at least one step
of a visit has reached and that satisfies the member's goal. -/
def visitsGoals {family : WorldClass interface} (goals : family.Goals) (length : ℕ) :
    (family.inVisits length).Goals :=
  fun index =>
    ⟨fun (state : (family.world index).State × Fin (length + 1)) =>
      1 ≤ state.2.val ∧ (goals index).satisfied state.1, (goals index).cap⟩

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

/-- A class that conceals its goals conceals them when it is run in visits, behind its reference
world run in visits: along every action sequence, each member in visits delivers the percept of the
reference in visits at every time before that member's goal is first met on any visit. -/
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
