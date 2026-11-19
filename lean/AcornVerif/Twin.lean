/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Blindness

/-!
# The twin of an agent

A *feedback* is any projection of a percept, such as its reward word (`AcornVerif.Blindness`).

`twin`, `twin_stepped`, `twin_loop`, `twin_clauses`: where a member's percept is a function of a
reference world's state along the same actions and of the percept's own feedback, every agent
has a twin, stepped by the feedback alone, that takes the same action at every time, solves each
member on the same visits, and separates and retains exactly when the agent does.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {Φ : Type}

/-! ## The twin of an agent -/

/-- The twin of an agent over a reference world: it carries the agent's memory and a state of the
reference, rebuilds a percept from that state and from the feedback of the percept it receives,
and gives the agent the rebuilt percept. -/
def twin (feedback : Percept interface → Φ) (agent : Agent interface) (reference : World interface)
    (origin : reference.State) (rebuild : reference.State → Φ → Percept interface) :
    Agent interface where
  Memory := agent.Memory × reference.State
  initial := (agent.initial, origin)
  act := fun memory percept =>
    ((agent.act memory.1 (rebuild memory.2 (feedback percept))).1,
      ((agent.act memory.1 (rebuild memory.2 (feedback percept))).2,
        reference.step memory.2 (agent.act memory.1 (rebuild memory.2 (feedback percept))).1))

/-- The twin is stepped by the feedback. -/
theorem twin_stepped (feedback : Percept interface → Φ) (agent : Agent interface)
    (reference : World interface) (origin : reference.State)
    (rebuild : reference.State → Φ → Percept interface) :
    Stepped feedback (twin feedback agent reference origin rebuild) :=
  ⟨fun memory shown =>
    ((agent.act memory.1 (rebuild memory.2 shown)).1,
      ((agent.act memory.1 (rebuild memory.2 shown)).2,
        reference.step memory.2 (agent.act memory.1 (rebuild memory.2 shown)).1)),
    fun _ _ => rfl⟩

/-- **The twin takes the agent's actions.** In a world related to the reference by a relation the
two transitions keep, where every related state delivers the percept rebuilt from the reference's
state and from its own feedback, the twin's closed loop holds the agent's memory and a related
state of the reference, and the twin takes the agent's action, at every time. -/
theorem twin_loop (feedback : Percept interface → Φ) (agent : Agent interface)
    (reference : World interface) (origin : reference.State)
    (rebuild : reference.State → Φ → Percept interface)
    (world : World interface) (start : world.State)
    (related : world.State → reference.State → Prop) (first : related start origin)
    (kept : ∀ state shadow action, related state shadow →
      related (world.step state action) (reference.step shadow action))
    (shown : ∀ state shadow, related state shadow →
      world.percept state = rebuild shadow (feedback (world.percept state)))
    (time : ℕ) :
    stateAt world (twin feedback agent reference origin rebuild) start time =
        stateAt world agent start time ∧
      (memoryAt world (twin feedback agent reference origin rebuild) start time).1 =
        memoryAt world agent start time ∧
      related (stateAt world agent start time)
        (memoryAt world (twin feedback agent reference origin rebuild) start time).2 ∧
      actionAt world (twin feedback agent reference origin rebuild) start time =
        actionAt world agent start time := by
  have reached : stateAt world (twin feedback agent reference origin rebuild) start time =
        stateAt world agent start time ∧
      (memoryAt world (twin feedback agent reference origin rebuild) start time).1 =
        memoryAt world agent start time ∧
      related (stateAt world agent start time)
        (memoryAt world (twin feedback agent reference origin rebuild) start time).2 := by
    induction time with
    | zero => exact ⟨rfl, rfl, first⟩
    | succ time ih =>
      obtain ⟨state, memory, shadow⟩ := ih
      have percept : rebuild
          (memoryAt world (twin feedback agent reference origin rebuild) start time).2
          (feedback (world.percept
            (stateAt world (twin feedback agent reference origin rebuild) start time))) =
          perceptAt world agent start time := by
        rw [state]
        exact (shown _ _ shadow).symm
      have action : actionAt world (twin feedback agent reference origin rebuild) start time =
          actionAt world agent start time := by
        change (agent.act
          (memoryAt world (twin feedback agent reference origin rebuild) start time).1
          (rebuild (memoryAt world (twin feedback agent reference origin rebuild) start time).2
            (feedback (world.percept
              (stateAt world (twin feedback agent reference origin rebuild) start time))))).1 = _
        rw [percept, memory]
        rfl
      refine ⟨?_, ?_, ?_⟩
      · change world.step (stateAt world (twin feedback agent reference origin rebuild) start time)
          (actionAt world (twin feedback agent reference origin rebuild) start time) =
          world.step (stateAt world agent start time) (actionAt world agent start time)
        rw [state, action]
      · change (agent.act
          (memoryAt world (twin feedback agent reference origin rebuild) start time).1
          (rebuild (memoryAt world (twin feedback agent reference origin rebuild) start time).2
            (feedback (world.percept
              (stateAt world (twin feedback agent reference origin rebuild) start time))))).2 = _
        rw [percept, memory]
        rfl
      · change related (world.step (stateAt world agent start time)
            (actionAt world agent start time))
          (reference.step
            (memoryAt world (twin feedback agent reference origin rebuild) start time).2
            (agent.act
              (memoryAt world (twin feedback agent reference origin rebuild) start time).1
              (rebuild (memoryAt world (twin feedback agent reference origin rebuild) start time).2
                (feedback (world.percept
                  (stateAt world (twin feedback agent reference origin rebuild) start
                    time))))).1)
        rw [percept, memory]
        exact kept _ _ _ shadow
  obtain ⟨state, memory, shadow⟩ := reached
  refine ⟨state, memory, shadow, ?_⟩
  change (agent.act (memoryAt world (twin feedback agent reference origin rebuild) start time).1
    (rebuild (memoryAt world (twin feedback agent reference origin rebuild) start time).2
      (feedback (world.percept
        (stateAt world (twin feedback agent reference origin rebuild) start time))))).1 = _
  rw [state, ← shown _ _ shadow, memory]
  rfl

/-! ## The twin over a class in visits -/

/-- **In a class in visits the twin solves what the agent solves.** Take a class and a reference
world, and for each member a relation between its states and the reference's that holds of the
two starts, that the two transitions keep, and under which the member's percept is rebuilt from
the reference's state and the percept's own feedback. Then one agent stepped by the feedback, the
twin over the reference in visits, solves each member on exactly the visits on which the agent
solves it. -/
theorem twin_solvesOnVisit (feedback : Percept interface → Φ) (agent : Agent interface)
    (reference : World interface) (origin : reference.State)
    (rebuild : reference.State → Φ → Percept interface)
    (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (related : (index : family.Index) → (family.world index).State → reference.State → Prop)
    (first : ∀ index, related index (family.start index) origin)
    (kept : ∀ index state shadow action, related index state shadow →
      related index ((family.world index).step state action) (reference.step shadow action))
    (shown : ∀ index state shadow, related index state shadow →
      (family.world index).percept state =
        rebuild shadow (feedback ((family.world index).percept state)))
    (count : ℕ) (index : family.Index) :
    SolvesOnVisit family goals length
        (twin feedback agent (visits reference origin length) (visitStart reference origin length)
          (fun shadow => rebuild shadow.1)) count index ↔
      SolvesOnVisit family goals length agent count index := by
  have same : ∀ time,
      stateAt (visits (family.world index) (family.start index) length)
          (twin feedback agent (visits reference origin length)
            (visitStart reference origin length) (fun shadow => rebuild shadow.1))
          (visitStart (family.world index) (family.start index) length) time =
        stateAt (visits (family.world index) (family.start index) length) agent
          (visitStart (family.world index) (family.start index) length) time := by
    intro time
    refine (twin_loop feedback agent (visits reference origin length)
      (visitStart reference origin length) (fun shadow => rebuild shadow.1)
      (visits (family.world index) (family.start index) length)
      (visitStart (family.world index) (family.start index) length)
      (fun state shadow => related index state.1 shadow.1 ∧ state.2.val = shadow.2.val)
      ⟨first index, rfl⟩ ?_ ?_ time).1
    · rintro ⟨state, clock⟩ ⟨shadow, tick⟩ action ⟨held, equal⟩
      have ticks : clock.val = tick.val := equal
      by_cases within : clock.val < length
      · have withinShadow : tick.val < length := ticks ▸ within
        simp only [visits, dite_eq_left within, dite_eq_left withinShadow]
        exact ⟨kept index state shadow action held, by simp only [ticks]⟩
      · have withinShadow : ¬ tick.val < length := ticks ▸ within
        simp only [visits, dite_eq_right within, dite_eq_right withinShadow]
        exact ⟨first index, trivial⟩
    · rintro ⟨state, clock⟩ ⟨shadow, tick⟩ ⟨held, -⟩
      exact shown index state shadow held
  unfold SolvesOnVisit
  simp only [same]

/-- The twin of `twin_solvesOnVisit` separates exactly when the agent does, and retains exactly
when the agent does. -/
theorem twin_clauses (feedback : Percept interface → Φ) (agent : Agent interface)
    (reference : World interface) (origin : reference.State)
    (rebuild : reference.State → Φ → Percept interface)
    (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (related : (index : family.Index) → (family.world index).State → reference.State → Prop)
    (first : ∀ index, related index (family.start index) origin)
    (kept : ∀ index state shadow action, related index state shadow →
      related index ((family.world index).step state action) (reference.step shadow action))
    (shown : ∀ index state shadow, related index state shadow →
      (family.world index).percept state =
        rebuild shadow (feedback ((family.world index).percept state)))
    (bound limit horizon lapses : ℕ) (counted : List family.Index) :
    (SeparatesBy family goals length bound counted limit
        (twin feedback agent (visits reference origin length) (visitStart reference origin length)
          (fun shadow => rebuild shadow.1)) ↔
      SeparatesBy family goals length bound counted limit agent) ∧
    (RetainsBut family goals length horizon lapses
        (twin feedback agent (visits reference origin length) (visitStart reference origin length)
          (fun shadow => rebuild shadow.1)) ↔
      RetainsBut family goals length horizon lapses agent) := by
  have each := twin_solvesOnVisit feedback agent reference origin rebuild family goals length
    related first kept shown
  unfold SeparatesBy RetainsBut
  simp only [each]
  exact ⟨trivial, trivial⟩

end AcornVerif.Kernel
