/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Blindness

/-!
# The twin of an agent, and a law that shuts out every feedback-driven agent

A *feedback* is any projection of a percept, such as its reward word (`AcornVerif.Blindness`).

- `twin`, `twin_stepped`, `twin_loop`, `twin_clauses`: where a member's percept is a function of a
  reference world's state along the same actions and of the percept's own feedback, every agent
  has a twin, stepped by the feedback alone, that takes the same action at every time, solves each
  member on the same visits, and separates and retains exactly when the agent does.
- `FeedbackDriven.cold`, `feedbackDriven_needs`: a feedback-driven agent that acts as at a cold
  start on every percept it holds nothing about takes one fixed action sequence everywhere, and
  so separates in no concealing class above the covering bound. `aloof_cold` shows that an agent
  which differs from a feedback-driven one only on percepts a class never shows meets that law.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {Φ : Type}

/-! ## An agent on an arbitrary sequence of percepts -/

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

/-! ## A fork: one feedback, two goals no one action sequence meets -/

/-! ## A law that shuts out every feedback-driven agent -/

variable {E : Type}

/-- The state a cold decision leaves after a number of decisions. -/
def coldState (cold : E → Act interface × E) (first : E) : ℕ → E
  | 0 => first
  | time + 1 => (cold (coldState cold first time)).2

/-- The memories an agent passes through when every percept it is given is one it holds nothing
about, chosen with the feedback of a given sequence. -/
noncomputable def novelMemory (feedback : Percept interface → Φ) (agent : Agent interface)
    (novel : agent.Memory → Percept interface → Prop)
    (rich : ∀ memory shown, ∃ percept, feedback percept = shown ∧ novel memory percept)
    (percepts : ℕ → Percept interface) : ℕ → agent.Memory
  | 0 => agent.initial
  | time + 1 => (agent.act (novelMemory feedback agent novel rich percepts time)
      (Classical.choose (rich (novelMemory feedback agent novel rich percepts time)
        (feedback (percepts time))))).2

/-- **Cold at what it has not met, and driven by feedback: one fixed action sequence.** Suppose
that on every percept an agent's memory holds nothing about (`novel`), the agent decides as a cold
decision does: its action and what the decision leaves are those of `cold` on a part of its
memory. Suppose every memory has such a percept with every feedback. Then a feedback-driven
agent takes, on every sequence of percepts, the cold decisions' actions: what it has learned
never reaches an action. -/
theorem FeedbackDriven.cold {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (read : agent.Memory → E)
    (cold : E → Act interface × E) (novel : agent.Memory → Percept interface → Prop)
    (acts : ∀ memory percept, novel memory percept →
      (agent.act memory percept).1 = (cold (read memory)).1 ∧
        read (agent.act memory percept).2 = (cold (read memory)).2)
    (rich : ∀ memory shown, ∃ percept, feedback percept = shown ∧ novel memory percept)
    (percepts : ℕ → Percept interface) (time : ℕ) :
    response agent percepts time = (cold (coldState cold (read agent.initial) time)).1 := by
  let fresh : ℕ → Percept interface := fun count =>
    Classical.choose (rich (novelMemory feedback agent novel rich percepts count)
      (feedback (percepts count)))
  have chosen : ∀ count, feedback (fresh count) = feedback (percepts count) ∧
      novel (novelMemory feedback agent novel rich percepts count) (fresh count) :=
    fun count => Classical.choose_spec (rich (novelMemory feedback agent novel rich percepts count)
      (feedback (percepts count)))
  have memory : ∀ count, driven agent fresh count =
      novelMemory feedback agent novel rich percepts count := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih =>
      change (agent.act (driven agent fresh count) (fresh count)).2 =
        (agent.act (novelMemory feedback agent novel rich percepts count) (fresh count)).2
      rw [ih]
  have state : ∀ count, read (novelMemory feedback agent novel rich percepts count) =
      coldState cold (read agent.initial) count := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih =>
      change read (agent.act (novelMemory feedback agent novel rich percepts count)
        (fresh count)).2 = (cold (coldState cold (read agent.initial) count)).2
      rw [(acts _ _ (chosen count).2).2, ih]
  rw [blind percepts fresh time (fun earlier _ => (chosen earlier).1.symm)]
  change (agent.act (driven agent fresh time) (fresh time)).1 = _
  rw [memory, (acts _ _ (chosen time).2).1, state]

/-- The agent that recites one action sequence. -/
def recite (interface : Interface) (actions : ℕ → Act interface) : Agent interface where
  Memory := ℕ
  initial := 0
  act := fun time _ => (actions time, time + 1)

/-- A reciting agent keeps nothing of its experience. -/
theorem recite_free (actions : ℕ → Act interface) : ExperienceFree (recite interface actions) :=
  ⟨Nat.succ, fun _ _ => rfl⟩

/-- A reciting agent takes its sequence's action at every time, in every world. -/
theorem recite_actions (actions : ℕ → Act interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    actionAt world (recite interface actions) start time = actions time := by
  have clock : ∀ count,
      memoryAt world (recite interface actions) start count = (count : ℕ) := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih => exact congrArg (fun value : ℕ => value + 1) ih
  exact congrArg actions (clock time)

/-- **No feedback-driven agent that is cold at what it has not met separates.** In a class that
conceals its goals, with a covering bound for one visit, a feedback-driven agent under the law of
`FeedbackDriven.cold` solves more members than the bound on no visit, whatever the list and the
limit. -/
theorem feedbackDriven_needs {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (read : agent.Memory → E)
    (cold : E → Act interface × E) (novel : agent.Memory → Percept interface → Prop)
    (acts : ∀ memory percept, novel memory percept →
      (agent.act memory percept).1 = (cold (read memory)).1 ∧
        read (agent.act memory percept).2 = (cold (read memory)).2)
    (rich : ∀ memory shown, ∃ percept, feedback percept = shown ∧ novel memory percept)
    {family : WorldClass interface} {goals : family.Goals} {reference : World interface}
    {origin : reference.State} (hidden : Conceals family goals reference origin)
    {length bound : ℕ} (covered : Covered family (visitGoals goals length) bound)
    (counted : List family.Index) (limit : ℕ) :
    ¬ SeparatesBy family goals length bound counted limit agent := by
  rintro ⟨visit, solved, -, many, each⟩
  have same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world agent start time =
        actionAt world (recite interface
          (fun count => (cold (coldState cold (read agent.initial) count)).1)) start time := by
    intro world start time
    rw [actionAt_response, blind.cold read cold novel acts rich, recite_actions]
  exact absurd (visits_need hidden covered (recite_free _) visit solved
    (fun index member => (solvesOnVisit_of_actions same visit index).mp (each index member).2))
    (Nat.not_le_of_lt many)

/-! ## Agents that choose by a selection over preferences, and the hybrid that evades the law -/

variable {Core V : Type}

/-- **The hybrid meets the law.** A chooser made aloof on a set of percepts decides, on every
percept of the set, as the cold decision does. Where the set holds a percept with every feedback,
this is the law of `FeedbackDriven.cold`, with the set's percepts as those the agent holds
nothing about. -/
theorem aloof_cold (select : E → V → Act interface × E) (core : Core) (seed : E)
    (prefer : Core → Percept interface → V)
    (advance : Core → Percept interface → Act interface → Core)
    (alien : Percept interface → Prop) [DecidablePred alien] (rest : V)
    (memory : (chooser select core seed (aloof alien rest prefer) advance).Memory)
    (percept : Percept interface) (strange : alien percept) :
    ((chooser select core seed (aloof alien rest prefer) advance).act memory percept).1 =
        (select memory.2 rest).1 ∧
      ((chooser select core seed (aloof alien rest prefer) advance).act memory percept).2.2 =
        (select memory.2 rest).2 := by
  change (select memory.2 (aloof alien rest prefer memory.1 percept)).1 = _ ∧
    (select memory.2 (aloof alien rest prefer memory.1 percept)).2 = _
  simp only [aloof, strange, ↓reduceIte]
  exact ⟨trivial, trivial⟩

end AcornVerif.Kernel
