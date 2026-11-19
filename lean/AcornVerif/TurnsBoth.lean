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
targets.

The definition asks two more things of each of the two runs of each member of the grid, through
a predicate `admits` on a member, an order and a visit, to be read as "the agent takes no
exploratory action on that visit":

- the predicate admits the visit of mastery itself, so the member is solved there by what the
  agent does when it is not exploring;
- at least `returns` later visits before the visit `horizon` bring that run's situation of the
  visit of mastery and are admitted, so there are that many later occasions on which keeping is
  put to the proof.

What mastery of a grid gives, for every class in turns:

- some member is solved on one visit in both situations (`MastersGridBy.solves`), so no agent
  driven by a feedback for which the class is mute and apart masters a grid
  (`FeedbackDriven.mastersGrid`), nor does an agent in the states of one
  (`MastersGridBy.of_states`, `aloof_mastersGrid`);
- no agent that keeps nothing masters a grid above a covering bound of the first situation
  (`turns_need_grid`);
- with keeping on the admitted visits, each member of the grid is solved again, in each of its
  two runs, on at least `returns` later visits before the horizon that bring the same situation
  (`MastersGridBy.kept`).

Degenerate instances, read for what they say. With `returns = 0` the last conjunct asks nothing,
and with the predicate that admits every visit the definition asks only for the solved grid;
`MastersGridBy.kept` then gives nothing beyond it. With the predicate that admits no visit no
agent masters a grid (`mastersGrid_of_never`).
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {family : TurnClass interface} {goals : family.Goals}
  {length : ℕ}

/-- **Mastery of a grid, on a visit the predicate admits, with later occasions.** Under one
order, on one visit before the visit `limit`, there are a set of more than `bound` first keys and
a set of more than `bound` second keys such that for every first key and every second key of the
two sets the class has a member with those keys for which, in both situations of that visit: the
agent solves the member on that visit; the predicate admits that visit; and at least `returns`
later visits before the visit `horizon` bring that situation again and are admitted. -/
def MastersGridBy (family : TurnClass interface) (goals : family.Goals) (length bound : ℕ)
    {κ μ : Type} (first : family.Index → κ) (second : family.Index → μ)
    (limit horizon returns : ℕ) (admits : family.Index → (ℕ → Bool) → ℕ → Prop)
    (agent : Agent interface) : Prop :=
  ∃ (order : ℕ → Bool) (visit : ℕ) (firsts : Finset κ) (seconds : Finset μ),
    visit < limit ∧ bound < firsts.card ∧ bound < seconds.card ∧
    ∀ one ∈ firsts, ∀ two ∈ seconds, ∃ index, first index = one ∧ second index = two ∧
      ∀ situation : Bool,
        SolvesTurn family goals length (Function.update order visit situation) agent visit
          index ∧
        admits index (Function.update order visit situation) visit ∧
        ∃ later : Finset ℕ, returns ≤ later.card ∧
          ∀ other ∈ later, visit < other ∧ other < horizon ∧
            Function.update order visit situation other = situation ∧
            admits index (Function.update order visit situation) other

variable {κ μ : Type} {first : family.Index → κ} {second : family.Index → μ}
  {bound limit horizon returns : ℕ} {admits : family.Index → (ℕ → Bool) → ℕ → Prop}
  {agent : Agent interface}

/-- An agent that masters a grid before a visit masters it before every later one. -/
theorem MastersGridBy.mono {later : ℕ} (within : limit ≤ later)
    (masters : MastersGridBy family goals length bound first second limit horizon returns admits
      agent) :
    MastersGridBy family goals length bound first second later horizon returns admits agent := by
  obtain ⟨order, visit, firsts, seconds, before, rest⟩ := masters
  exact ⟨order, visit, firsts, seconds, Nat.lt_of_lt_of_le before within, rest⟩

/-- An agent that masters a grid solves some member on one visit in both situations. -/
theorem MastersGridBy.solves
    (masters : MastersGridBy family goals length bound first second limit horizon returns admits
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

/-- **No feedback-driven agent masters a grid**, at any bound, keys, limit, horizon, returns and
predicate, in a class whose members are forks and whose situations give one feedback until the
goal is met. -/
theorem FeedbackDriven.mastersGrid {Φ : Type} {feedback : Percept interface → Φ}
    (blind : FeedbackDriven feedback agent) (mute : Mute feedback family goals)
    (apart : Apart family goals length) :
    ¬ MastersGridBy family goals length bound first second limit horizon returns admits
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
    (masters : MastersGridBy family goals length bound first second limit horizon returns admits
      agent) :
    MastersGridBy family goals length bound first second limit horizon returns admits other := by
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
    ¬ MastersGridBy family goals length bound first second limit horizon returns admits
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
    ¬ MastersGridBy family goals length bound first second limit horizon returns admits
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

/-- **The grid is kept on the later occasions.** An agent that masters a grid and keeps on the
admitted visits solves each member of the grid again, in each of the two runs of the visit of
mastery, on at least `returns` later visits before the horizon that bring that run's situation
of that visit. -/
theorem MastersGridBy.kept
    (masters : MastersGridBy family goals length bound first second limit horizon returns admits
      agent)
    (keeps : KeepsOn family goals length horizon admits agent) :
    ∃ (order : ℕ → Bool) (visit : ℕ) (firsts : Finset κ) (seconds : Finset μ),
      visit < limit ∧ bound < firsts.card ∧ bound < seconds.card ∧
      ∀ one ∈ firsts, ∀ two ∈ seconds, ∃ index, first index = one ∧ second index = two ∧
        ∀ situation : Bool, ∃ later : Finset ℕ, returns ≤ later.card ∧
          ∀ other ∈ later, visit < other ∧ other < horizon ∧
            Function.update order visit situation other = situation ∧
            SolvesTurn family goals length (Function.update order visit situation) agent
              other index := by
  obtain ⟨order, visit, firsts, seconds, before, manyFirst, manySecond, each⟩ := masters
  refine ⟨order, visit, firsts, seconds, before, manyFirst, manySecond,
    fun one inFirsts two inSeconds => ?_⟩
  obtain ⟨index, isOne, isTwo, solved⟩ := each one inFirsts two inSeconds
  refine ⟨index, isOne, isTwo, fun situation => ?_⟩
  obtain ⟨once, -, later, count, occasions⟩ := solved situation
  refine ⟨later, count, fun other member => ?_⟩
  obtain ⟨after, within, same, admitted⟩ := occasions other member
  exact ⟨after, within, same,
    keeps index (Function.update order visit situation) visit other after within
      (same.trans (Function.update_self visit situation order).symm) once admitted⟩

/-- Where a predicate admits no visit, no agent masters a grid: mastery asks that the visit of
mastery is admitted. -/
theorem mastersGrid_of_never (family : TurnClass interface) (goals : family.Goals)
    (length bound : ℕ) {κ μ : Type} (first : family.Index → κ) (second : family.Index → μ)
    (limit horizon returns : ℕ) (agent : Agent interface) :
    ¬ MastersGridBy family goals length bound first second limit horizon returns
      (fun _ _ _ => False) agent := by
  rintro ⟨order, visit, firsts, seconds, -, manyFirst, manySecond, each⟩
  obtain ⟨one, inFirsts⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manyFirst)
  obtain ⟨two, inSeconds⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manySecond)
  obtain ⟨index, -, -, solved⟩ := each one inFirsts two inSeconds
  exact (solved false).2.1

end AcornVerif.Kernel
