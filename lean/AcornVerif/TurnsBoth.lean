/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.TurnsKeeping

/-!
# Mastery of a grid of members

`AcornVerif.Kernel.MastersBy` counts the members an agent solves in both situations of one visit
by one key, a member's part in the first situation. Where a member is a pair of problems, one for
each situation, that count lets the solved set be chosen so that what the agent meets in one
situation tells it the other's answer: a set in which each second problem goes with one region
of first problems is solved from experience of the second situation alone.

`MastersGridBy` closes that. A member has two keys, its part in each situation. The agent
masters a *grid*: a set of more than `bound` first keys and a set of more than `bound` second
keys such that, for every first key and every second key of the two sets, the class has a member
with those keys and the agent solves it on one common visit in both situations. Under one second
key the first keys of the grid are then more than the bound, and nothing met in the second
situation tells them apart; so what the agent does in the first situation has to come from the
first situation. `AcornVerif.CurrentForkedTargetBoth` proves that consequence for concealed
targets. The definition also carries the count of `MastersCalmBy`: in each of the two runs of
each member of the grid, a predicate admits every visit before the horizon but for at most
`lapses`.

What mastery of a grid gives, for every class in turns:

- some member is solved on one visit in both situations (`MastersGridBy.solves`), so no agent
  driven by a feedback for which the class is mute and apart masters a grid
  (`FeedbackDriven.mastersGrid`), nor does an agent in the states of one
  (`MastersGridBy.of_states`, `aloof_mastersGrid`);
- no agent that keeps nothing masters a grid above a covering bound of the first situation
  (`turns_need_grid`);
- with keeping on the admitted visits, each member of the grid is solved again, in each of its
  two runs, on every later visit before the horizon that brings the same situation, but for at
  most `lapses` visits (`MastersGridBy.kept`).
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {family : TurnClass interface} {goals : family.Goals}
  {length : ℕ}

/-- **Mastery of a grid, with room.** Under one order, on one visit before the visit `limit`,
there are a set of more than `bound` first keys and a set of more than `bound` second keys such
that for every first key and every second key of the two sets the class has a member with those
keys which the agent solves on that visit in both situations, and in each of those two runs the
predicate admits every visit before the visit `horizon` but for at most `lapses`. -/
def MastersGridBy (family : TurnClass interface) (goals : family.Goals) (length bound : ℕ)
    {κ μ : Type} (first : family.Index → κ) (second : family.Index → μ)
    (limit horizon lapses : ℕ) (admits : family.Index → (ℕ → Bool) → ℕ → Prop)
    (agent : Agent interface) : Prop :=
  ∃ (order : ℕ → Bool) (visit : ℕ) (firsts : Finset κ) (seconds : Finset μ),
    visit < limit ∧ bound < firsts.card ∧ bound < seconds.card ∧
    ∀ one ∈ firsts, ∀ two ∈ seconds, ∃ index, first index = one ∧ second index = two ∧
      ∀ situation : Bool,
        SolvesTurn family goals length (Function.update order visit situation) agent visit
          index ∧
        ∃ restless : Finset ℕ, restless.card ≤ lapses ∧
          ∀ other, other < horizon → other ∉ restless →
            admits index (Function.update order visit situation) other

variable {κ μ : Type} {first : family.Index → κ} {second : family.Index → μ}
  {bound limit horizon lapses : ℕ} {admits : family.Index → (ℕ → Bool) → ℕ → Prop}
  {agent : Agent interface}

/-- An agent that masters a grid before a visit masters it before every later one. -/
theorem MastersGridBy.mono {later : ℕ} (within : limit ≤ later)
    (masters : MastersGridBy family goals length bound first second limit horizon lapses admits
      agent) :
    MastersGridBy family goals length bound first second later horizon lapses admits agent := by
  obtain ⟨order, visit, firsts, seconds, before, rest⟩ := masters
  exact ⟨order, visit, firsts, seconds, Nat.lt_of_lt_of_le before within, rest⟩

/-- An agent that masters a grid solves some member on one visit in both situations. -/
theorem MastersGridBy.solves
    (masters : MastersGridBy family goals length bound first second limit horizon lapses admits
      agent) :
    ∃ (order : ℕ → Bool) (visit : ℕ) (index : family.Index), visit < limit ∧
      ∀ situation : Bool, SolvesTurn family goals length (Function.update order visit situation)
        agent visit index := by
  obtain ⟨order, visit, firsts, seconds, before, manyFirst, manySecond, each⟩ := masters
  obtain ⟨one, inFirsts⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manyFirst)
  obtain ⟨two, inSeconds⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manySecond)
  obtain ⟨index, -, -, solved⟩ := each one inFirsts two inSeconds
  exact ⟨order, visit, index, before, fun situation => (solved situation).1⟩

/-- **No feedback-driven agent masters a grid**, at any bound, keys, limit, horizon, lapses and
predicate, in a class whose members are forks and whose situations give one feedback until the
goal is met. -/
theorem FeedbackDriven.mastersGrid {Φ : Type} {feedback : Percept interface → Φ}
    (blind : FeedbackDriven feedback agent) (mute : Mute feedback family goals)
    (apart : Apart family goals length) :
    ¬ MastersGridBy family goals length bound first second limit horizon lapses admits
      agent := by
  intro masters
  obtain ⟨order, visit, index, -, solved⟩ := masters.solves
  exact blind.turn mute apart order visit index solved

/-- An agent in the states of an agent that masters a grid, masters it. -/
theorem MastersGridBy.of_states {other : Agent interface}
    (same : ∀ (index : family.Index) (order : ℕ → Bool) (time : ℕ),
      stateAt (turns (family.world index) (family.start index) order length) agent
          (turnStart (family.world index) (family.start index) order length 0) time =
        stateAt (turns (family.world index) (family.start index) order length) other
          (turnStart (family.world index) (family.start index) order length 0) time)
    (masters : MastersGridBy family goals length bound first second limit horizon lapses admits
      agent) :
    MastersGridBy family goals length bound first second limit horizon lapses admits other := by
  obtain ⟨order, visit, firsts, seconds, before, manyFirst, manySecond, each⟩ := masters
  refine ⟨order, visit, firsts, seconds, before, manyFirst, manySecond,
    fun one inFirsts two inSeconds => ?_⟩
  obtain ⟨index, isOne, isTwo, solved⟩ := each one inFirsts two inSeconds
  exact ⟨index, isOne, isTwo, fun situation =>
    ⟨(solvesTurn_of_states same _ visit index).mp (solved situation).1, (solved situation).2⟩⟩

/-- **An agent that is feedback-driven on everything a class shows it masters no grid.** The
chooser of `aloof_masters`, made aloof on a set of percepts no member of the class delivers,
masters no grid: in every member's world in turns its closed loop is the plain chooser's. -/
theorem aloof_mastersGrid {Φ E Core V : Type} {feedback : Percept interface → Φ}
    (select : E → V → Act interface × E) (core : Core) (seed : E) (prefer : Core → Φ → V)
    (advance : Core → Φ → Act interface → Core)
    (alien : Percept interface → Prop) [DecidablePred alien] (rest : V)
    (never : ∀ (index : family.Index) (state : (family.world index).State),
      ¬ alien ((family.world index).percept state))
    (mute : Mute feedback family goals) (apart : Apart family goals length) :
    ¬ MastersGridBy family goals length bound first second limit horizon lapses admits
      (chooser select core seed
        (aloof alien rest (fun inner percept => prefer inner (feedback percept)))
        (fun inner percept action => advance inner (feedback percept) action)) := by
  intro masters
  refine (chooser_stepped feedback select core seed prefer advance).feedbackDriven.mastersGrid
    mute apart (masters.of_states (fun index order time => ?_))
  exact congrArg Prod.fst (aloof_loop select core seed _ _ alien rest
    (turns (family.world index) (family.start index) order length) _
    (fun state => never index state.1) time)

/-- **No agent that keeps nothing masters a grid above a covering bound.** Take a class in turns
whose first situation's class conceals its goals behind a reference, and a bound such that one
action sequence meets, from their first starts within a visit, the goals of at most `bound`
members no two of which have one first key. Then no experience-free agent masters a grid at that
bound. -/
theorem turns_need_grid {reference : World interface} {origin : reference.State}
    (hidden : Conceals (family.side false) goals reference origin)
    (covered : ∀ (actions : ℕ → Act interface) (solved : Finset family.Index),
      (∀ one ∈ solved, ∀ two ∈ solved, first one = first two → one = two) →
      (∀ index ∈ solved,
        (turnGoal goals length index).MetBy (family.start index false) actions) →
      solved.card ≤ bound)
    (free : ExperienceFree agent) :
    ¬ MastersGridBy family goals length bound first second limit horizon lapses admits
      agent := by
  classical
  rintro ⟨order, visit, firsts, seconds, -, manyFirst, manySecond, each⟩
  obtain ⟨two, inSeconds⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manySecond)
  obtain ⟨advance, law⟩ := free
  choose pick isOne _ solved using fun (one : κ) (inFirsts : one ∈ firsts) =>
    each one inFirsts two inSeconds
  have image : (firsts.attach.image fun one => pick one.1 one.2).card = firsts.card := by
    rw [Finset.card_image_of_injective _ (fun one other same => Subtype.ext (by
      rw [← isOne one.1 one.2, ← isOne other.1 other.2, same])), Finset.card_attach]
  refine absurd (covered (actionAt reference
    (agent.resume (advanced advance agent.initial (visit * (length + 1)))) origin)
    (firsts.attach.image fun one => pick one.1 one.2) (fun left inLeft right inRight same => ?_)
    (fun index member => ?_)) (by rw [image]; exact Nat.not_le_of_lt manyFirst)
  · obtain ⟨one, -, rfl⟩ := Finset.mem_image.mp inLeft
    obtain ⟨other, -, rfl⟩ := Finset.mem_image.mp inRight
    rw [isOne one.1 one.2, isOne other.1 other.2] at same
    rw [Subtype.ext same]
  · obtain ⟨one, -, rfl⟩ := Finset.mem_image.mp member
    have solves := (solvesTurn_side family goals length order agent visit _ false).mp
      (solved one.1 one.2 false).1
    unfold turnMemory at solves
    rw [experienceFree_memoryAt law] at solves
    exact ((hidden.withLength length).solves_iff _ _).mp solves

/-- **The grid is kept, but for the lapses.** An agent that masters a grid with room and keeps
on the admitted visits solves each member of the grid again, in each of the two runs of the
visit of mastery, on every later visit before the horizon that brings that run's situation of
that visit, but for at most `lapses` visits. -/
theorem MastersGridBy.kept
    (masters : MastersGridBy family goals length bound first second limit horizon lapses admits
      agent)
    (keeps : KeepsOn family goals length horizon admits agent) :
    ∃ (order : ℕ → Bool) (visit : ℕ) (firsts : Finset κ) (seconds : Finset μ),
      visit < limit ∧ bound < firsts.card ∧ bound < seconds.card ∧
      ∀ one ∈ firsts, ∀ two ∈ seconds, ∃ index, first index = one ∧ second index = two ∧
        ∀ situation : Bool, ∃ lapsed : Finset ℕ, lapsed.card ≤ lapses ∧
          ∀ later, visit < later → later < horizon →
            Function.update order visit situation later = situation → later ∉ lapsed →
              SolvesTurn family goals length (Function.update order visit situation) agent
                later index := by
  obtain ⟨order, visit, firsts, seconds, before, manyFirst, manySecond, each⟩ := masters
  refine ⟨order, visit, firsts, seconds, before, manyFirst, manySecond,
    fun one inFirsts two inSeconds => ?_⟩
  obtain ⟨index, isOne, isTwo, solved⟩ := each one inFirsts two inSeconds
  refine ⟨index, isOne, isTwo, fun situation => ?_⟩
  obtain ⟨once, restless, count, admitted⟩ := solved situation
  refine ⟨restless, count, fun later after within same out => ?_⟩
  exact keeps index (Function.update order visit situation) visit later after within
    (same.trans (Function.update_self visit situation order).symm) once
    (admitted later within out)

end AcornVerif.Kernel
