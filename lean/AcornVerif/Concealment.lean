/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.WorldClass

/-!
# Concealed goals

A class of worlds conceals its goals behind a reference world when every member, along
every action sequence, delivers the reference's percepts until that member's goal is first
satisfied (`Conceals`). Before success nothing an agent perceives tells the members apart,
so every agent, learning or not, keeps in each member the memory it keeps in the reference
and takes the reference's actions until that member's goal is met (`Conceals.agree`). Every
agent is therefore blind on the class (`Conceals.blind`), and a covering bound is a need
bound for every agent (`Conceals.need`): one agent, the same in every member, solves at most
as many members as one action sequence meets. This is the first-visit bound. It covers an
agent that learns, provided its memory at the attempt's start is the same in every member:
it has had no experience of the member yet.

The bound says nothing about a later attempt in a world that persists, because the world
can carry what an agent learned nothing about. `park` follows a step counter until its
percept shows the goal met and from then on takes an action that keeps the goal met. It is
experience-free (`park_experienceFree`), and once it has met a goal that the action keeps,
it meets the goal at every later time (`park_keeps`): the world's state holds what its
memory does not. In `AcornVerif.Kernel.visits` each member returns between attempts to its
own fixed start state, which does not depend on earlier attempts; there an experience-free
agent's later attempts are bounded as its first is.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-! ## Concealment -/

/-- A class conceals its goals behind a reference world and a state of it when, along every
action sequence, each member delivers the reference's percept at every time before that
member's goal is first satisfied. -/
def Conceals (family : WorldClass interface) (goals : family.Goals)
    (reference : World interface) (origin : reference.State) : Prop :=
  ∀ (index : family.Index) (actions : ℕ → Act interface) (time : ℕ),
    (∀ earlier, 1 ≤ earlier → earlier ≤ time →
      ¬ (goals index).satisfied
        (path (family.world index) (family.start index) actions earlier)) →
    (family.world index).percept (path (family.world index) (family.start index) actions time) =
      reference.percept (path reference origin actions time)

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

/-- Where an agent's closed loop in a member has so far taken the actions of its closed loop
in the reference, and the member's goal has not been satisfied, the member delivers the
percept the reference delivers. -/
theorem Conceals.perceptAt_eq (hidden : Conceals family goals reference origin)
    (agent : Agent interface) (index : family.Index) (time : ℕ)
    (unmet : ∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) earlier))
    (same : ∀ step, step < time →
      actionAt (family.world index) agent (family.start index) step =
        actionAt reference agent origin step) :
    perceptAt (family.world index) agent (family.start index) time =
      perceptAt reference agent origin time := by
  have track : ∀ earlier, earlier ≤ time →
      stateAt (family.world index) agent (family.start index) earlier =
        path (family.world index) (family.start index) (actionAt reference agent origin)
          earlier :=
    fun earlier within => (stateAt_eq_path _ _ _ earlier).trans
      (path_congr _ _ _ _ earlier (fun step before =>
        same step (Nat.lt_of_lt_of_le before within)))
  have shown := hidden index (actionAt reference agent origin) time (fun earlier low high => by
    rw [← track earlier high]
    exact unmet earlier low high)
  change (family.world index).percept
      (stateAt (family.world index) agent (family.start index) time) =
    reference.percept (stateAt reference agent origin time)
  rw [track time (Nat.le_refl time), stateAt_eq_path reference agent origin time]
  exact shown

/-- Before a time at which a member's goal has not yet been satisfied, every agent keeps in
that member the memory it keeps in the reference, and has taken the reference's actions. -/
theorem Conceals.agree_before (hidden : Conceals family goals reference origin)
    (agent : Agent interface) (index : family.Index) (time : ℕ) :
    (∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) earlier)) →
    memoryAt (family.world index) agent (family.start index) time =
        memoryAt reference agent origin time ∧
      ∀ step, step < time → actionAt (family.world index) agent (family.start index) step =
        actionAt reference agent origin step := by
  induction time with
  | zero => exact fun _ => ⟨rfl, fun step early => absurd early (Nat.not_lt_zero step)⟩
  | succ time ih =>
    intro unmet
    have unmetEarlier : ∀ earlier, 1 ≤ earlier → earlier ≤ time →
        ¬ (goals index).satisfied
        (stateAt (family.world index) agent (family.start index) earlier) :=
      fun earlier low high => unmet earlier low (Nat.le_succ_of_le high)
    obtain ⟨memory, actions⟩ := ih unmetEarlier
    have percept := hidden.perceptAt_eq agent index time unmetEarlier actions
    have decided : agent.act (memoryAt (family.world index) agent (family.start index) time)
          (perceptAt (family.world index) agent (family.start index) time) =
        agent.act (memoryAt reference agent origin time)
          (perceptAt reference agent origin time) := by
      rw [memory, percept]
    refine ⟨congrArg Prod.snd decided, fun step early => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ early) with earlier | equal
    · exact actions step earlier
    · rw [equal]
      exact congrArg Prod.fst decided

/-- Until a member's goal is first satisfied, every agent keeps in that member the memory it
keeps in the reference and takes the reference's actions. -/
theorem Conceals.agree (hidden : Conceals family goals reference origin)
    (agent : Agent interface) (index : family.Index) (time : ℕ)
    (unmet : ∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) earlier)) :
    memoryAt (family.world index) agent (family.start index) time =
        memoryAt reference agent origin time ∧
      ∀ step, step ≤ time → actionAt (family.world index) agent (family.start index) step =
        actionAt reference agent origin step := by
  obtain ⟨memory, actions⟩ := hidden.agree_before agent index time unmet
  have percept := hidden.perceptAt_eq agent index time unmet actions
  refine ⟨memory, fun step within => ?_⟩
  rcases Nat.lt_or_eq_of_le within with earlier | equal
  · exact actions step earlier
  · rw [equal]
    change (agent.act (memoryAt (family.world index) agent (family.start index) time)
        (perceptAt (family.world index) agent (family.start index) time)).1 =
      (agent.act (memoryAt reference agent origin time) (perceptAt reference agent origin time)).1
    rw [memory, percept]

/-- Every agent is blind on a class that conceals its goals: in each member, before that
member's goal is first satisfied, it takes the actions it takes in the reference. -/
theorem Conceals.blind (hidden : Conceals family goals reference origin)
    (agent : Agent interface) : Blind family goals agent :=
  ⟨actionAt reference agent origin, fun index time unmet =>
    (hidden.agree agent index time unmet).2 time (Nat.le_refl time)⟩

/-- The first-visit bound. In a class that conceals its goals, a covering bound is a need bound
for every agent: whatever an agent has learned before, if one action sequence meets the goal
of at most `bound` members, the agent solves at most `bound` members. -/
theorem Conceals.need (hidden : Conceals family goals reference origin) {bound : ℕ}
    (covered : Covered family goals bound) : Need family goals (fun _ => True) bound :=
  fun agent _ => need_of_covered covered agent (hidden.blind agent)

/-! ## Parking -/

/-- The parking agent: its memory is a step counter. It takes the staying action whenever its
percept shows the signal, and otherwise the sequence's action at its count. -/
def park (interface : Interface) (signal : Percept interface → Bool) (stay : Act interface)
    (actions : ℕ → Act interface) : Agent interface where
  Memory := ℕ
  initial := 0
  act := fun count percept => (if signal percept = true then stay else actions count, count + 1)

/-- The parking agent's memory advances without reading percepts. -/
theorem park_experienceFree (signal : Percept interface → Bool) (stay : Act interface)
    (actions : ℕ → Act interface) : ExperienceFree (park interface signal stay actions) :=
  ⟨fun (count : ℕ) => count + 1, fun _ _ => rfl⟩

/-- In a world whose percept after a step shows the signal wherever that step satisfies a goal,
and whose staying action keeps the goal satisfied, the parking agent keeps every goal it has
satisfied after a step: it satisfies the goal at every later time. -/
theorem park_keeps (world : World interface) (start : world.State)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (shows : ∀ state action, satisfied (world.step state action) →
      signal (world.percept (world.step state action)) = true)
    (stay : Act interface)
    (keeps : ∀ state, satisfied state → satisfied (world.step state stay))
    (actions : ℕ → Act interface) (time later : ℕ)
    (met : satisfied (stateAt world (park interface signal stay actions) start (time + 1))) :
    satisfied (stateAt world (park interface signal stay actions) start (time + 1 + later)) := by
  induction later with
  | zero => exact met
  | succ later ih =>
    have shown : signal (world.percept
        (stateAt world (park interface signal stay actions) start (time + 1 + later))) = true := by
      have stepped : stateAt world (park interface signal stay actions) start (time + 1 + later) =
          world.step (stateAt world (park interface signal stay actions) start (time + later))
            (actionAt world (park interface signal stay actions) start (time + later)) := by
        rw [Nat.add_right_comm]
        rfl
      rw [stepped] at ih ⊢
      exact shows _ _ ih
    change satisfied (world.step
      (stateAt world (park interface signal stay actions) start (time + 1 + later))
      (if signal (world.percept
          (stateAt world (park interface signal stay actions) start (time + 1 + later))) = true
        then stay
        else actions
          (memoryAt world (park interface signal stay actions) start (time + 1 + later))))
    rw [ite_eq_left shown]
    exact keeps _ ih

end AcornVerif.Kernel
