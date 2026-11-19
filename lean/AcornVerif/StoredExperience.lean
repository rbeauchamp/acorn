/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Perceiving

/-!
# Storing and replaying experience, at the kernel's level

* `historian`: for every agent, an agent that keeps every percept it has received and, at every
  step, replays the whole record through the agent's step to decide. It takes the agent's action
  at every time in every world (`historian_actions`), so every statement about which members are
  solved on which visits holds of one exactly when it holds of the other (`historian_clauses`).
  No definition that reads an agent through its actions can tell an agent that stores and replays
  its experience from one that does not.
* What does tell them apart is a bound on the memories a run holds: the historian's record grows
  by one percept a step (`historian_unbounded`), and the replaying agent of `AcornVerif.Replay`
  counts its visits without bound (`replay_unbounded`), so neither holds one of finitely many
  memories along a run (`HoldsFinitely`).
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-! ## Agents with one response to every stream act alike in every world -/

/-- Every agent is driven by its whole percept. -/
theorem drivenByPercept (agent : Agent interface) :
    FeedbackDriven (fun percept : Percept interface => percept) agent :=
  Stepped.feedbackDriven (⟨agent.act, fun _ _ => rfl⟩ :
    Stepped (fun percept : Percept interface => percept) agent)

/-- Two agents with one response to every sequence of percepts pass through the same states in
every world. -/
theorem stateAt_of_response {first second : Agent interface}
    (same : ∀ percepts time, response first percepts time = response second percepts time)
    (world : World interface) (start : world.State) (time : ℕ) :
    stateAt world first start time = stateAt world second start time := by
  induction time using Nat.strong_induction_on with
  | _ time ih =>
    cases time with
    | zero => rfl
    | succ time =>
      have act : actionAt world first start time = actionAt world second start time :=
        (actionAt_response world first start time).trans ((same _ time).trans
          ((drivenByPercept second _ _ time (fun earlier within =>
            congrArg world.percept (ih earlier (Nat.lt_succ_of_le within)))).trans
            (actionAt_response world second start time).symm))
      change world.step (stateAt world first start time) (actionAt world first start time) =
        world.step (stateAt world second start time) (actionAt world second start time)
      rw [act, ih time (Nat.lt_succ_self time)]

/-- Two agents with one response to every sequence of percepts take the same action at every time
in every world. -/
theorem actionAt_of_response {first second : Agent interface}
    (same : ∀ percepts time, response first percepts time = response second percepts time)
    (world : World interface) (start : world.State) (time : ℕ) :
    actionAt world first start time = actionAt world second start time :=
  (actionAt_response world first start time).trans ((same _ time).trans
    ((drivenByPercept second _ _ time (fun earlier _ =>
      congrArg world.percept (stateAt_of_response same world start earlier))).trans
      (actionAt_response world second start time).symm))

/-! ## The historian -/

/-- The memory an agent holds after the percepts of a record, the latest first. -/
def recollect (agent : Agent interface) : List (Percept interface) → agent.Memory
  | [] => agent.initial
  | percept :: earlier => (agent.act (recollect agent earlier) percept).2

/-- The historian of an agent: it keeps every percept it has received, the latest first, and at
each step replays the whole record through the agent's step to find the memory the agent would
hold, then takes the agent's action on the new percept. -/
def historian (agent : Agent interface) : Agent interface where
  Memory := List (Percept interface)
  initial := []
  act := fun record percept => ((agent.act (recollect agent record) percept).1, percept :: record)

/-- Replaying the historian's record gives the agent's memory. -/
theorem historian_driven (agent : Agent interface) (percepts : ℕ → Percept interface) (time : ℕ) :
    recollect agent (driven (historian agent) percepts time) = driven agent percepts time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    change (agent.act (recollect agent (driven (historian agent) percepts time))
      (percepts time)).2 = (agent.act (driven agent percepts time) (percepts time)).2
    rw [ih]

/-- The historian's record is the whole stream so far: it holds every percept received. -/
theorem historian_keeps (agent : Agent interface) (percepts : ℕ → Percept interface) (time : ℕ) :
    driven (historian agent) percepts time = ((List.range time).map percepts).reverse := by
  induction time with
  | zero => rfl
  | succ time ih =>
    change percepts time :: driven (historian agent) percepts time = _
    rw [ih, List.range_succ, List.map_append, List.reverse_append]
    rfl

/-- The historian responds to every sequence of percepts as the agent does. -/
theorem historian_response (agent : Agent interface) (percepts : ℕ → Percept interface)
    (time : ℕ) : response (historian agent) percepts time = response agent percepts time := by
  change (agent.act (recollect agent (driven (historian agent) percepts time))
    (percepts time)).1 = (agent.act (driven agent percepts time) (percepts time)).1
  rw [historian_driven]

/-- **The historian takes the agent's action at every time in every world.** -/
theorem historian_actions (agent : Agent interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    actionAt world (historian agent) start time = actionAt world agent start time :=
  actionAt_of_response (historian_response agent) world start time

/-- **Both promises about solving hold of the historian exactly when they hold of the agent.** -/
theorem historian_clauses (agent : Agent interface) (family : WorldClass interface)
    (goals : family.Goals) (length bound limit horizon lapses : ℕ)
    (counted : List family.Index) :
    (SeparatesBy family goals length bound counted limit (historian agent) ↔
      SeparatesBy family goals length bound counted limit agent) ∧
    (RetainsBut family goals length horizon lapses (historian agent) ↔
      RetainsBut family goals length horizon lapses agent) := by
  have each := fun visit index => solvesOnVisit_of_actions (family := family) (goals := goals)
    (length := length) (historian_actions agent) visit index
  unfold SeparatesBy RetainsBut
  simp only [each]
  exact ⟨trivial, trivial⟩

/-! ## A bound on the memories of a run tells them apart -/

/-- One finite list holds every memory the agent holds at any time of its run in a world. Its
failing examples are `historian_unbounded` and `replay_unbounded`; no witness is stated here. -/
def HoldsFinitely (world : World interface) (agent : Agent interface) (start : world.State) :
    Prop :=
  ∃ held : List agent.Memory, ∀ time, memoryAt world agent start time ∈ held

/-- A measure of the items of a list is bounded. -/
theorem bounded_on_list {α : Type} (measure : α → ℕ) (held : List α) :
    ∃ top, ∀ item ∈ held, measure item ≤ top := by
  induction held with
  | nil => exact ⟨0, fun _ member => absurd member List.not_mem_nil⟩
  | cons head rest ih =>
    obtain ⟨top, below⟩ := ih
    refine ⟨max (measure head) top, fun item member => ?_⟩
    rcases List.mem_cons.mp member with here | there
    · rw [here]
      exact Nat.le_max_left _ _
    · exact (below item there).trans (Nat.le_max_right _ _)

/-- The historian's record after a number of steps has that many percepts. -/
theorem historian_length (agent : Agent interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    (memoryAt world (historian agent) start time).length = time := by
  induction time with
  | zero => rfl
  | succ time ih => exact congrArg Nat.succ ih

/-- **No finite list holds the historian's memories**, in any world: its record grows by one
percept at every step. -/
theorem historian_unbounded (agent : Agent interface) (world : World interface)
    (start : world.State) : ¬ HoldsFinitely world (historian agent) start := by
  rintro ⟨held, all⟩
  obtain ⟨top, below⟩ := bounded_on_list List.length held
  have short := below _ (all (top + 1))
  rw [historian_length] at short
  exact Nat.lt_irrefl _ short

/-- **No finite list holds the replaying agent's memories** in a world in visits: it counts its
visits. -/
theorem replay_unbounded (world : World interface) (start : world.State) (length : ℕ)
    (signal : Percept interface → Bool) (explore : ℕ → ℕ → Act interface) :
    ¬ HoldsFinitely (visits world start length) (replay interface length signal explore)
      (visitStart world start length) := by
  rintro ⟨held, all⟩
  obtain ⟨top, below⟩ := bounded_on_list ReplayMemory.count held
  have short := below _ (all ((top + 1) * (length + 1) + 0))
  rw [replay_count_visit world start length (fun _ => True) signal (fun _ _ _ => trivial)
    explore _ 0 (Nat.zero_le length)] at short
  exact Nat.lt_irrefl _ short

end AcornVerif.Kernel
