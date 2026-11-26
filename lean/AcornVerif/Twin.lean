import AcornVerif.Blindness

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {Φ : Type}

def twin (feedback : Percept interface → Φ) (agent : Agent interface) (reference : World interface)
    (origin : reference.State) (rebuild : reference.State → Φ → Percept interface) :
    Agent interface where
  Memory := agent.Memory × reference.State
  initial := (agent.initial, origin)
  act := fun memory percept =>
    ((agent.act memory.1 (rebuild memory.2 (feedback percept))).1,
      ((agent.act memory.1 (rebuild memory.2 (feedback percept))).2,
        reference.step memory.2 (agent.act memory.1 (rebuild memory.2 (feedback percept))).1))

theorem twin_stepped (feedback : Percept interface → Φ) (agent : Agent interface)
    (reference : World interface) (origin : reference.State)
    (rebuild : reference.State → Φ → Percept interface) :
    Stepped feedback (twin feedback agent reference origin rebuild) :=
  ⟨fun memory shown =>
    ((agent.act memory.1 (rebuild memory.2 shown)).1,
      ((agent.act memory.1 (rebuild memory.2 shown)).2,
        reference.step memory.2 (agent.act memory.1 (rebuild memory.2 shown)).1)),
    fun _ _ => rfl⟩

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
