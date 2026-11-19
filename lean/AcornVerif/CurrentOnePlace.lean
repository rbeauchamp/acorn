/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetRungFirstVisit

/-!
# One place: the visit after a first rewarded visit

A *place* here is a world that returns to one start state after a fixed number of steps, with a
target that some action sequence from that start meets. This module asks one question of the
executed agent at such a place: after its first rewarded visit, does its next visit, at a
decision outside any exploratory run, do again what was rewarded? Two places answer it, one each
way, and both answers come from `AcornVerif.CurrentTraceCounts.first_choice_last`.

**The door: yes, where the visit is one decision.** `door key shown paid` is a place of one step:
the start shows `shown`, and the step leads to a state that shows `paid` when the action was `key`
and `shown` otherwise; the next step returns to the start. Take an agent state whose learners are
at rest and whose primitive controller holds no trace, under a profile with no hierarchy,
per-step credit, the declared rate and the discounted criterion, before a unit of its feature
bank matures. If its first action is the key, `shown` carries a zero reward word and `paid` a
reward word of one, every frame it lays holds at most 1999 slots, the frames laid at the times
zero and two share a slot, and the explorer of its state, after two decisions, holds no committed
run with a step left and begins none, then the agent's action at the time two is the key again,
and the percept at the time three is `paid` (`door_again`).

**The lock: no, where the visit is two decisions and the second frame holds the first.**
`lock first second shown later paid` is a place of two steps: the start shows `shown`, every
state after one step shows `later`, and the state after two steps shows `paid` when the two
actions were `first` and then `second`, and `later` otherwise; the next step returns to the
start. Take an agent state as above whose first two actions are `first` and `second`, two
different actions. If `shown` and `later` carry zero reward words and `paid` a reward word of
one, every frame it lays holds at most 1999 slots, the frames laid at the times one and three
share a slot, every slot that the frame laid at the time three holds of the frame laid at the
time zero is a slot of the frame laid at the time one, and the explorer of its state, after three
decisions, holds no committed run with a step left and begins none, then the agent's action at
the time three, the first decision of its second visit, is `second`, and the percept at the time
five is `later` (`lock_departs`): the second visit is not paid, whatever the agent does at the
time four.

Why the lock fails. After the step that learns a first reward of one, the value of each action
at a frame is its row's trace total there (`AcornVerif.CurrentFirstChoice.reward_values`). Under
the conditions above, a row whose action was taken once before the reward is fresh: each slot of
the frame it was taken on holds one word, the stored step size decayed once for each later step
(`AcornVerif.CurrentTraceCounts.loop_fresh`). At a frame that holds a slot of the last frame laid
before the reward, and at least as many slots of it as of each earlier frame, the last action
taken is the one candidate (`AcornVerif.CurrentTraceCounts.last_candidate`). The frame laid at
the start of the next visit is such a frame when every slot it holds of the first visit's first
frame is a slot of that visit's second frame. So the action that ended the rewarded visit is the
candidate at the start, and outside an exploratory run the agent takes it
(`first_choice_last`).

**Both places exist for the agent on `main`.** For the first rung's cold agent
(`AcornVerif.CurrentConcealedTargetRung.rungConstruction`), whose explorer's first two actions
are to craft an axe and to step south:

- at the door whose key is that first action, the agent is paid on its first visit and on its
  second (`rung_door`), for every pair of percepts of at most 174 words of which `shown` carries a
  word and a zero reward word and `paid` a reward word of one;
- at the lock of those two actions, the agent is paid on its first visit, begins its second
  visit with its explorer's second action, and is not paid on it (`rung_lock`;
  `AcornVerif.CurrentConcealedTargetRungFirstVisit.first_actions` names the two actions), for
  every three percepts of at
  most 174 words of which `later` carries every word of `shown` and the same symbols, `shown`
  carries a word, `shown` and `later` carry zero reward words and `paid` a reward word of one.
  After two decisions, and after three, the explorer of the rung's seed holds no committed run
  with a step left and begins none (`door_calm`,
  `AcornVerif.CurrentConcealedTargetRungChoice.rung_calm`); those are the terms in which
  `first_choice_last` reads a decision outside an exploratory run.
- Such percepts exist over the grid interface (`places_exist`). In the lock built from them the
  percept after one step carries one word more than the start's, so the two steps of a visit
  show different percepts.

What this does not say.

- Nothing of an agent state that is not at rest: a state that has been rewarded before, holds a
  trace, or holds weights. So nothing of a second place met after a first, and nothing of a
  place met again after another. The two theorems for the agent on `main` are at its cold state.
- Nothing of a decision after the first one that follows the reward. At the door that decision is
  the whole next visit; at the lock it is enough to lose it. Of a place of two or more steps
  whose frames are not nested, this module says nothing: there the first choice is a comparison
  of counted traces, which `AcornVerif.CurrentTraceCounts.loop_totals` states and no theorem
  here decides.
- Nothing of a visit on which the explorer serves or begins an exploratory run.
- The lock's percepts are not shown to be percepts of the host's world: `places_exist` builds
  them by replacing a frame's words. The places are worlds of the agent's interface, which is
  what `first_choice_last` is stated for, and no theorem here says that the host's world shows
  two percepts of which one carries every word of the other.
- That a change to the feature bank would alter either answer. Before a unit matures the bank
  does not change (`AcornVerif.CurrentFirstCredit.young_bank`), and the lock's hypothesis is
  about the slots of the frames, whatever lays them: a bank whose units fire at the start and
  not one step later would break the nesting, and then this module is silent.

Degenerate instances, read for what they say. A door whose key the agent's first action is not
gives `door_again` nothing to say. A lock with `first = second` is excluded by hypothesis: there
the two actions before the reward are one action, a row laid twice, of which `first_choice_last`
says nothing. With `later = shown` the two steps of a visit show one percept, so that instance
says nothing about a rule that reads its percept; `places_exist` gives percepts that differ.
-/

namespace AcornVerif.CurrentOnePlace
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentConcealedTargetRungChoice
open AcornVerif.CurrentCreditHorizon AcornVerif.CurrentExplorer AcornVerif.CurrentFirstChoice
open AcornVerif.CurrentFirstCredit AcornVerif.CurrentFrameSize AcornVerif.CurrentFrameSlots
open AcornVerif.CurrentPreReward AcornVerif.CurrentTraceCounts

/-! ## Frames of nested percepts -/

section Frames

variable {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- **A percept that carries every word of another lays every slot of the other's frame.** Two
steps, at agent states that hold the same bank and the same stored predictions, on percepts with
the same symbols of which the second carries every word of the first: every slot the first step
lays, the second lays, whatever the step orders. -/
theorem choose_nested
    (first second : Agent interface profile features criterion dimension planning)
    (order other : StepOrder) (one two : Percept interface)
    (words : ∀ word ∈ one.frame.words, word ∈ two.frame.words)
    (symbols : one.frame.symbols = two.frame.symbols)
    (bank : first.control.runtime.lifecycle.representation.bank =
      second.control.runtime.lifecycle.representation.bank)
    (stored : first.control.runtime.references.demonPredictions =
      second.control.runtime.references.demonPredictions)
    (slot : FeatIdx dimension) (held : slot ∈ (first.choose order one).features.indices) :
    slot ∈ (second.choose other two).features.indices := by
  rw [choose_frame, (first.advanceClock.frame one.frame).fresh, Agent.words_def] at held
  rw [choose_frame, (second.advanceClock.frame two.frame).fresh, Agent.words_def]
  change slot ∈ (encode dimension first.control.runtime.lifecycle.representation.bank
    (one.frame.words ++ feedbackWords interface.feedback interface.layout
      first.control.runtime.references.demonPredictions.words 0) one.frame.symbols).indices
    at held
  change slot ∈ (encode dimension second.control.runtime.lifecycle.representation.bank
    (two.frame.words ++ feedbackWords interface.feedback interface.layout
      second.control.runtime.references.demonPredictions.words 0) two.frame.symbols).indices
  rw [← bank, ← stored, ← symbols, encode_membership]
  rw [encode_membership] at held
  unfold rawEncode at held ⊢
  rw [rawEncodeWith_def, tiledFeatures_def] at held ⊢
  rcases List.mem_append.mp held with tiled | imprinted
  · obtain ⟨tiling, inRange, mapped⟩ := List.mem_flatMap.mp tiled
    obtain ⟨word, inWords, same⟩ := List.mem_map.mp mapped
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨tiling, inRange,
      List.mem_map.mpr ⟨word, ?_, same⟩⟩)
    rcases List.mem_append.mp inWords with own | fed
    · exact List.mem_append_left _ (words word own)
    · exact List.mem_append_right _ fed
  · exact List.mem_append_right _ imprinted

end Frames

/-! ## The two places -/

section Places

variable {interface : Interface}

/-- A kernel run's state one time later is the world's step on the action taken. -/
theorem state_step (world : Kernel.World interface) (agent : Kernel.Agent interface)
    (start : world.State) (time : ℕ) :
    Kernel.stateAt world agent start (time + 1) =
      world.step (Kernel.stateAt world agent start time)
        (Kernel.actionAt world agent start time) := rfl

/-- The states of a door: its start, and the state after its one step, which records whether the
action was the key. -/
inductive Door where
  /-- The start of a visit. -/
  | start
  /-- After the visit's step. -/
  | done (met : Bool)

/-- **A place of one step.** The start shows `shown`; the step leads to a state that shows `paid`
when the action was `key` and `shown` otherwise; the next step returns to the start. -/
def door (key : Kernel.Act interface) (shown paid : Percept interface) :
    Kernel.World interface where
  State := Door
  step := fun state action =>
    match state with
    | .start => .done (decide (action = key))
    | .done _ => .start
  percept := fun state =>
    match state with
    | .start => shown
    | .done met => if met then paid else shown

/-- One visit of a door from its start, for every agent. -/
theorem door_visit (key : Kernel.Act interface) (shown paid : Percept interface)
    (agent : Kernel.Agent interface) (time : ℕ)
    (begun : Kernel.stateAt (door key shown paid) agent Door.start time = Door.start) :
    Kernel.perceptAt (door key shown paid) agent Door.start time = shown ∧
      Kernel.stateAt (door key shown paid) agent Door.start (time + 1) =
        Door.done (decide (Kernel.actionAt (door key shown paid) agent Door.start time = key)) ∧
      Kernel.stateAt (door key shown paid) agent Door.start (time + 1 + 1) = Door.start := by
  have shows : Kernel.perceptAt (door key shown paid) agent Door.start time = shown := by
    change (door key shown paid).percept
      (Kernel.stateAt (door key shown paid) agent Door.start time) = shown
    rw [begun]
    rfl
  have stepped : Kernel.stateAt (door key shown paid) agent Door.start (time + 1) =
      Door.done (decide (Kernel.actionAt (door key shown paid) agent Door.start time = key)) := by
    rw [state_step (door key shown paid) agent Door.start time, begun]
    rfl
  refine ⟨shows, stepped, ?_⟩
  rw [state_step (door key shown paid) agent Door.start (time + 1), stepped]
  rfl

/-- The percepts of a door are `shown` and `paid`. -/
theorem door_percept (key : Kernel.Act interface) (shown paid : Percept interface)
    (state : Door) :
    (door key shown paid).percept state = shown ∨ (door key shown paid).percept state = paid := by
  cases state with
  | start => exact Or.inl rfl
  | done met =>
    cases met with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

/-- The states of a lock: its start, the state after one step, which records whether the action
was the first of the two, and the state after two steps, which records whether both were right. -/
inductive Lock where
  /-- The start of a visit. -/
  | start
  /-- After the visit's first step. -/
  | mid (right : Bool)
  /-- After the visit's second step. -/
  | done (met : Bool)

/-- **A place of two steps.** The start shows `shown`; every state after one step shows `later`;
the state after two steps shows `paid` when the two actions were `first` and then `second`, and
`later` otherwise; the next step returns to the start. -/
def lock (first second : Kernel.Act interface) (shown later paid : Percept interface) :
    Kernel.World interface where
  State := Lock
  step := fun state action =>
    match state with
    | .start => .mid (decide (action = first))
    | .mid right => .done (right && decide (action = second))
    | .done _ => .start
  percept := fun state =>
    match state with
    | .start => shown
    | .mid _ => later
    | .done met => if met then paid else later

/-- One visit of a lock from its start, for every agent. -/
theorem lock_visit (first second : Kernel.Act interface) (shown later paid : Percept interface)
    (agent : Kernel.Agent interface) (time : ℕ)
    (begun : Kernel.stateAt (lock first second shown later paid) agent Lock.start time =
      Lock.start) :
    Kernel.perceptAt (lock first second shown later paid) agent Lock.start time = shown ∧
      Kernel.perceptAt (lock first second shown later paid) agent Lock.start (time + 1) =
        later ∧
      Kernel.stateAt (lock first second shown later paid) agent Lock.start (time + 1 + 1) =
        Lock.done
          (decide (Kernel.actionAt (lock first second shown later paid) agent Lock.start time =
              first) &&
            decide (Kernel.actionAt (lock first second shown later paid) agent Lock.start
              (time + 1) = second)) ∧
      Kernel.stateAt (lock first second shown later paid) agent Lock.start (time + 1 + 1 + 1) =
        Lock.start := by
  have shows : Kernel.perceptAt (lock first second shown later paid) agent Lock.start time =
      shown := by
    change (lock first second shown later paid).percept
      (Kernel.stateAt (lock first second shown later paid) agent Lock.start time) = shown
    rw [begun]
    rfl
  have stepped : Kernel.stateAt (lock first second shown later paid) agent Lock.start
      (time + 1) = Lock.mid (decide
        (Kernel.actionAt (lock first second shown later paid) agent Lock.start time =
          first)) := by
    rw [state_step (lock first second shown later paid) agent Lock.start time, begun]
    rfl
  have next : Kernel.perceptAt (lock first second shown later paid) agent Lock.start
      (time + 1) = later := by
    change (lock first second shown later paid).percept
      (Kernel.stateAt (lock first second shown later paid) agent Lock.start (time + 1)) = later
    rw [stepped]
    rfl
  have ended : Kernel.stateAt (lock first second shown later paid) agent Lock.start
      (time + 1 + 1) = Lock.done
        (decide (Kernel.actionAt (lock first second shown later paid) agent Lock.start time =
            first) &&
          decide (Kernel.actionAt (lock first second shown later paid) agent Lock.start
            (time + 1) = second)) := by
    rw [state_step (lock first second shown later paid) agent Lock.start (time + 1), stepped]
    rfl
  refine ⟨shows, next, ended, ?_⟩
  rw [state_step (lock first second shown later paid) agent Lock.start (time + 1 + 1), ended]
  rfl

/-- The percepts of a lock are `shown`, `later` and `paid`. -/
theorem lock_percept (first second : Kernel.Act interface) (shown later paid : Percept interface)
    (state : Lock) :
    (lock first second shown later paid).percept state = shown ∨
      (lock first second shown later paid).percept state = later ∨
      (lock first second shown later paid).percept state = paid := by
  cases state with
  | start => exact Or.inl rfl
  | mid right => exact Or.inr (Or.inl rfl)
  | done met =>
    cases met with
    | false => exact Or.inr (Or.inl rfl)
    | true => exact Or.inr (Or.inr rfl)

end Places

/-! ## The visit after the first rewarded one, from a state at rest -/

section Rest

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {dimension : Dimension} {planning : PlanningSelection}

/-- **At a door, the visit after the first rewarded one takes the key again.** See the module
documentation for the hypotheses. The action at the time two is the key, and the percept at the
time three is `paid`. -/
theorem door_again (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (key : Kernel.Act interface) (shown paid : Percept interface)
    (opens : Kernel.actionAt (door key shown paid) (executedAgent agent) Door.start 0 = key)
    (young : agent.clock.toNat + (0 + 1) < config.tester.maturity)
    (silent : shown.reward = .zero) (pays : paid.reward = .one)
    (fits : ∀ time,
      (laidAt agent (door key shown paid) Door.start time).features.indices.length ≤ 1999)
    (shares : ∃ slot,
      slot ∈ (laidAt agent (door key shown paid) Door.start (0 + 2)).features.indices ∧
        slot ∈ (laidAt agent (door key shown paid) Door.start 0).features.indices)
    (unserved : ((explorerOf agent.control).after (0 + 2)).run.bind ExploratoryRun.serve = none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (0 + 2)).rng).1 = none) :
    Kernel.actionAt (door key shown paid) (executedAgent agent) Door.start (0 + 2) = key ∧
      Kernel.perceptAt (door key shown paid) (executedAgent agent) Door.start 3 = paid := by
  obtain ⟨shows, stepped, back⟩ := door_visit key shown paid (executedAgent agent) 0 rfl
  have paidAt : Kernel.perceptAt (door key shown paid) (executedAgent agent) Door.start (0 + 1) =
      paid := by
    change (door key shown paid).percept
      (Kernel.stateAt (door key shown paid) (executedAgent agent) Door.start (0 + 1)) = paid
    rw [stepped, opens, decide_eq_true rfl]
    rfl
  obtain ⟨slot, heldNext, heldLast⟩ := shares
  have again := first_choice_last primitive perStep declared agent quiet ctrl
    (door key shown paid) Door.start 0 (by omega) young
    (fun earlier before => by
      obtain rfl : earlier = 0 := by omega
      rw [shows]
      exact silent)
    (by rw [paidAt]; exact pays)
    (fun earlier _ => fits earlier) (fits (0 + 2))
    (fun one two early1 early2 apart => (apart (by omega)).elim)
    (List.countP_pos_iff.mpr ⟨slot, heldNext, decide_eq_true heldLast⟩)
    (fun earlier before => absurd before (Nat.not_lt_zero earlier)) unserved calm
  have key2 : Kernel.actionAt (door key shown paid) (executedAgent agent) Door.start (0 + 2) =
      key := again.trans opens
  refine ⟨key2, ?_⟩
  obtain ⟨-, stepped2, -⟩ := door_visit key shown paid (executedAgent agent) (0 + 1 + 1) back
  change (door key shown paid).percept
    (Kernel.stateAt (door key shown paid) (executedAgent agent) Door.start (0 + 1 + 1 + 1)) = paid
  rw [stepped2]
  change (door key shown paid).percept (Door.done (decide
    (Kernel.actionAt (door key shown paid) (executedAgent agent) Door.start (0 + 2) = key))) =
    paid
  rw [key2, decide_eq_true rfl]
  rfl

/-- **At a lock whose second frame holds the first, the visit after the first rewarded one begins
with the second action.** See the module documentation for the hypotheses. The action at the time
three is `second`, and the percept at the time five is `later`: the second visit is not paid. -/
theorem lock_departs (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (first second : Kernel.Act interface) (shown later paid : Percept interface)
    (apart : first ≠ second)
    (opens : Kernel.actionAt (lock first second shown later paid) (executedAgent agent)
      Lock.start 0 = first)
    (turns : Kernel.actionAt (lock first second shown later paid) (executedAgent agent)
      Lock.start 1 = second)
    (young : agent.clock.toNat + (1 + 1) < config.tester.maturity)
    (silent : shown.reward = .zero) (still : later.reward = .zero) (pays : paid.reward = .one)
    (fits : ∀ time, (laidAt agent (lock first second shown later paid) Lock.start
      time).features.indices.length ≤ 1999)
    (shares : ∃ slot,
      slot ∈ (laidAt agent (lock first second shown later paid) Lock.start
        (1 + 2)).features.indices ∧
      slot ∈ (laidAt agent (lock first second shown later paid) Lock.start 1).features.indices)
    (nested : ∀ slot,
      slot ∈ (laidAt agent (lock first second shown later paid) Lock.start
        (1 + 2)).features.indices →
      slot ∈ (laidAt agent (lock first second shown later paid) Lock.start 0).features.indices →
      slot ∈ (laidAt agent (lock first second shown later paid) Lock.start 1).features.indices)
    (unserved : ((explorerOf agent.control).after (1 + 2)).run.bind ExploratoryRun.serve = none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (1 + 2)).rng).1 = none) :
    Kernel.actionAt (lock first second shown later paid) (executedAgent agent) Lock.start
        (1 + 2) = second ∧
      Kernel.perceptAt (lock first second shown later paid) (executedAgent agent) Lock.start 5 =
        later := by
  obtain ⟨shows, next, ended, back⟩ :=
    lock_visit first second shown later paid (executedAgent agent) 0 rfl
  have paidAt : Kernel.perceptAt (lock first second shown later paid) (executedAgent agent)
      Lock.start (1 + 1) = paid := by
    change (lock first second shown later paid).percept
      (Kernel.stateAt (lock first second shown later paid) (executedAgent agent) Lock.start
        (0 + 1 + 1)) = paid
    rw [ended]
    change (lock first second shown later paid).percept (Lock.done
      (decide (Kernel.actionAt (lock first second shown later paid) (executedAgent agent)
          Lock.start 0 = first) &&
        decide (Kernel.actionAt (lock first second shown later paid) (executedAgent agent)
          Lock.start 1 = second))) = paid
    rw [opens, turns, decide_eq_true rfl, decide_eq_true rfl]
    rfl
  obtain ⟨slot, heldNext, heldLast⟩ := shares
  have again := first_choice_last primitive perStep declared agent quiet ctrl
    (lock first second shown later paid) Lock.start 1 (by omega) young
    (fun earlier before => by
      obtain rfl | rfl : earlier = 0 ∨ earlier = 1 := by omega
      · rw [shows]
        exact silent
      · rw [show (1 : ℕ) = 0 + 1 from rfl, next]
        exact still)
    (by rw [paidAt]; exact pays)
    (fun earlier _ => fits earlier) (fits (1 + 2))
    (fun one two early1 early2 differ same => by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (one = 0 ∧ two = 1) ∨ (one = 1 ∧ two = 0) := by
        omega
      · exact apart (opens.symm.trans (same.trans turns))
      · exact apart (opens.symm.trans (same.symm.trans turns)))
    (List.countP_pos_iff.mpr ⟨slot, heldNext, decide_eq_true heldLast⟩)
    (fun earlier before => by
      obtain rfl : earlier = 0 := by omega
      refine List.countP_mono_left fun slot held inFirst => ?_
      exact decide_eq_true (nested slot held (of_decide_eq_true inFirst)))
    unserved calm
  have taken : Kernel.actionAt (lock first second shown later paid) (executedAgent agent)
      Lock.start (1 + 2) = second := again.trans turns
  refine ⟨taken, ?_⟩
  obtain ⟨-, -, ended2, -⟩ :=
    lock_visit first second shown later paid (executedAgent agent) (0 + 1 + 1 + 1) back
  change (lock first second shown later paid).percept
    (Kernel.stateAt (lock first second shown later paid) (executedAgent agent) Lock.start
      (0 + 1 + 1 + 1 + 1 + 1)) = later
  rw [ended2]
  change (lock first second shown later paid).percept (Lock.done
    (decide (Kernel.actionAt (lock first second shown later paid) (executedAgent agent)
        Lock.start (1 + 2) = first) &&
      decide (Kernel.actionAt (lock first second shown later paid) (executedAgent agent)
        Lock.start (0 + 1 + 1 + 1 + 1) = second))) = later
  rw [taken, decide_eq_false (fun same => apart same.symm), Bool.false_and]
  rfl

end Rest

/-! ## The agent on `main` at the two places -/

section Rung

/-- The first rung's cold agent, at the type the theorems of a state at rest read. -/
abbrev rungCold (planning : PlanningSelection) :
    Agent Grid.interface (rungConstruction planning).profile (rungConstruction planning).config
      .discounted (rungConstruction planning).dimension planning :=
  Agent.initial Grid.interface (rungConstruction planning).profile
    (rungConstruction planning).config .discounted (rungConstruction planning).dimension planning

/-- After two decisions the rung's explorer holds no committed run with a step left, and its
generator begins none at the declared rate. -/
theorem door_calm :
    (rungExplorer.after 2).run.bind ExploratoryRun.serve = none ∧
      (beginExploration Grid.interface.actions declaredRate (rungExplorer.after 2).rng).1 =
        none := by
  decide +kernel

/-- A step of the rung's agent on a percept of at most 174 words lays at most 1999 slots: eight
tilings of those words and the eleven questions, and 512 units. -/
theorem small_fits (planning : PlanningSelection)
    (state : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning)
    (percept : Percept Grid.interface) (small : percept.frame.words.length ≤ 174) :
    (state.choose .learnThenAct percept).features.indices.length ≤ 1999 := by
  refine Nat.le_trans (choose_slots state .learnThenAct percept) ?_
  generalize percept.frame.words.length = count at small ⊢
  change Acorn.FeatureConstants.defaultTilings.toUInt64.toNat *
    (count + Grid.interface.layout.length) + Acorn.FeatureConstants.defaultImprintUnits ≤ 1999
  have eight : Acorn.FeatureConstants.defaultTilings.toUInt64.toNat = 8 := by decide
  have eleven : Grid.interface.layout.length = 11 := by decide
  have units : Acorn.FeatureConstants.defaultImprintUnits = 512 := by decide
  rw [eight, eleven, units]
  omega

/-- The rung's feature configuration has a tiling. -/
theorem rung_tiled (planning : PlanningSelection) :
    0 < (rungConstruction planning).config.tilings.toNat := by
  change 0 < Acorn.FeatureConstants.defaultTilings.toUInt64.toNat
  decide

/-- **The agent on `main` is paid twice running at the door its first action opens.** For the
first rung's cold agent and the door whose key is its explorer's first action, with percepts of
at most 174 words of which `shown` carries a word and a zero reward word and `paid` a reward word
of one: the percept at the time one is `paid`, the action at the time two is the key again, and
the percept at the time three is `paid`. The decision at the time two is outside any exploratory
run (`door_calm`). -/
theorem rung_door (planning : PlanningSelection) (shown paid : Percept Grid.interface)
    (silent : shown.reward = .zero) (pays : paid.reward = .one)
    (small : shown.frame.words.length ≤ 174) (smallPaid : paid.frame.words.length ≤ 174)
    (word : SensorWord) (held : word ∈ shown.frame.words) :
    Kernel.perceptAt (door (rungExplorer.actionAt 0) shown paid) (rungAgent planning)
        Door.start 1 = paid ∧
      Kernel.actionAt (door (rungExplorer.actionAt 0) shown paid) (rungAgent planning)
        Door.start 2 = rungExplorer.actionAt 0 ∧
      Kernel.perceptAt (door (rungExplorer.actionAt 0) shown paid) (rungAgent planning)
        Door.start 3 = paid := by
  have opens : Kernel.actionAt (door (rungExplorer.actionAt 0) shown paid)
      (executedAgent (rungCold planning)) Door.start 0 = rungExplorer.actionAt 0 :=
    cold_actions (profile := (rungConstruction planning).profile)
      (config := (rungConstruction planning).config)
      (dimension := (rungConstruction planning).dimension) rfl rfl planning
      (door (rungExplorer.actionAt 0) shown paid) Door.start 0
      (fun earlier before => absurd before (Nat.not_lt_zero earlier))
  obtain ⟨shows, stepped, back⟩ := door_visit (rungExplorer.actionAt 0) shown paid
    (executedAgent (rungCold planning)) 0 rfl
  obtain ⟨showsNext, -, -⟩ := door_visit (rungExplorer.actionAt 0) shown paid
    (executedAgent (rungCold planning)) (0 + 1 + 1) back
  have fits : ∀ time, (laidAt (rungCold planning) (door (rungExplorer.actionAt 0) shown paid)
      Door.start time).features.indices.length ≤ 1999 := fun time => by
    refine small_fits planning
      (Kernel.memoryAt (door (rungExplorer.actionAt 0) shown paid)
        (executedAgent (rungCold planning)) Door.start time)
      (Kernel.perceptAt (door (rungExplorer.actionAt 0) shown paid)
        (executedAgent (rungCold planning)) Door.start time) ?_
    change ((door (rungExplorer.actionAt 0) shown paid).percept
      (Kernel.stateAt (door (rungExplorer.actionAt 0) shown paid)
        (executedAgent (rungCold planning)) Door.start time)).frame.words.length ≤ 174
    rcases door_percept (rungExplorer.actionAt 0) shown paid
      (Kernel.stateAt (door (rungExplorer.actionAt 0) shown paid)
        (executedAgent (rungCold planning)) Door.start time) with same | same
    · rw [same]
      exact small
    · rw [same]
      exact smallPaid
  have heldNext : word ∈ (Kernel.perceptAt (door (rungExplorer.actionAt 0) shown paid)
      (executedAgent (rungCold planning)) Door.start (0 + 1 + 1)).frame.words := by
    rw [showsNext]
    exact held
  have heldFirst : word ∈ (Kernel.perceptAt (door (rungExplorer.actionAt 0) shown paid)
      (executedAgent (rungCold planning)) Door.start 0).frame.words := by
    rw [shows]
    exact held
  have shares := shared_slot
    (Kernel.memoryAt (door (rungExplorer.actionAt 0) shown paid)
      (executedAgent (rungCold planning)) Door.start (0 + 1 + 1))
    (Kernel.memoryAt (door (rungExplorer.actionAt 0) shown paid)
      (executedAgent (rungCold planning)) Door.start 0) .learnThenAct .learnThenAct _ _ word
    heldNext heldFirst (rung_tiled planning)
  have again := door_again (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl rfl (rungCold planning)
    Quiet.initial ctrlQuiet_initial (rungExplorer.actionAt 0) shown paid opens
    (by change 0 + (0 + 1) < 1000; omega) silent pays fits shares door_calm.1 door_calm.2
  refine ⟨?_, again.1, again.2⟩
  change (door (rungExplorer.actionAt 0) shown paid).percept
    (Kernel.stateAt (door (rungExplorer.actionAt 0) shown paid)
      (executedAgent (rungCold planning)) Door.start (0 + 1)) = paid
  rw [stepped, opens, decide_eq_true rfl]
  rfl

/-- **The agent on `main` opens the lock of its first two actions once and then begins with the
second.** For the first rung's cold agent and the lock of its explorer's first two actions, with
percepts of at most 174 words of which `later` carries every word of `shown` and the same
symbols, `shown` carries a word, `shown` and `later` carry zero reward words and `paid` a reward
word of one: the percept at the time two is `paid`; the action at the time three, the first
decision of the second visit, is the explorer's second action, which is not its first; and the
percept at the time five is `later`, so the second visit is not paid. The decision at the time
three is outside any exploratory run
(`AcornVerif.CurrentConcealedTargetRungChoice.rung_calm`). -/
theorem rung_lock (planning : PlanningSelection) (shown later paid : Percept Grid.interface)
    (silent : shown.reward = .zero) (still : later.reward = .zero) (pays : paid.reward = .one)
    (small : shown.frame.words.length ≤ 174) (smallLater : later.frame.words.length ≤ 174)
    (smallPaid : paid.frame.words.length ≤ 174)
    (nested : ∀ word ∈ shown.frame.words, word ∈ later.frame.words)
    (symbols : shown.frame.symbols = later.frame.symbols)
    (word : SensorWord) (held : word ∈ shown.frame.words) :
    Kernel.perceptAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
        (rungAgent planning) Lock.start 2 = paid ∧
      Kernel.actionAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
        (rungAgent planning) Lock.start 3 = rungExplorer.actionAt 1 ∧
      rungExplorer.actionAt 1 ≠ rungExplorer.actionAt 0 ∧
      Kernel.perceptAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
        (rungAgent planning) Lock.start 5 = later := by
  obtain ⟨shows, next, ended, back⟩ := lock_visit (rungExplorer.actionAt 0)
    (rungExplorer.actionAt 1) shown later paid (executedAgent (rungCold planning)) 0 rfl
  obtain ⟨showsNext, -, -, -⟩ := lock_visit (rungExplorer.actionAt 0)
    (rungExplorer.actionAt 1) shown later paid (executedAgent (rungCold planning))
    (0 + 1 + 1 + 1) back
  have opens : Kernel.actionAt
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start 0 = rungExplorer.actionAt 0 :=
    cold_actions (profile := (rungConstruction planning).profile)
      (config := (rungConstruction planning).config)
      (dimension := (rungConstruction planning).dimension) rfl rfl planning
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid) Lock.start 0
      (fun earlier before => absurd before (Nat.not_lt_zero earlier))
  have turns : Kernel.actionAt
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start 1 = rungExplorer.actionAt 1 :=
    cold_actions (profile := (rungConstruction planning).profile)
      (config := (rungConstruction planning).config)
      (dimension := (rungConstruction planning).dimension) rfl rfl planning
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid) Lock.start 1
      (fun earlier before => by
        obtain rfl : earlier = 0 := by omega
        rw [shows]
        exact (congrArg Binary32.isZero silent).trans (by decide))
  have apart : rungExplorer.actionAt 0 ≠ rungExplorer.actionAt 1 :=
    rung_early_distinct 0 1 (by omega) (by omega) (by omega)
  have fits : ∀ time, (laidAt (rungCold planning)
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid) Lock.start
      time).features.indices.length ≤ 1999 := fun time => by
    refine small_fits planning
      (Kernel.memoryAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later
        paid) (executedAgent (rungCold planning)) Lock.start time)
      (Kernel.perceptAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later
        paid) (executedAgent (rungCold planning)) Lock.start time) ?_
    change ((lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid).percept
      (Kernel.stateAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later
        paid) (executedAgent (rungCold planning)) Lock.start time)).frame.words.length ≤ 174
    rcases lock_percept (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid
      (Kernel.stateAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later
        paid) (executedAgent (rungCold planning)) Lock.start time) with same | same | same
    · rw [same]
      exact small
    · rw [same]
      exact smallLater
    · rw [same]
      exact smallPaid
  have heldNext : word ∈ (Kernel.perceptAt
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start (0 + 1 + 1 + 1)).frame.words := by
    rw [showsNext]
    exact held
  have heldLater : word ∈ (Kernel.perceptAt
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start (0 + 1)).frame.words := by
    rw [next]
    exact nested word held
  have shares := shared_slot
    (Kernel.memoryAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start (0 + 1 + 1 + 1))
    (Kernel.memoryAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start (0 + 1)) .learnThenAct .learnThenAct _ _
    word heldNext heldLater (rung_tiled planning)
  have moved := loop_step (rungCold planning)
    (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid) Lock.start 0
  have bank : (rungCold planning).control.runtime.lifecycle.representation.bank =
      (Kernel.memoryAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later
        paid) (executedAgent (rungCold planning)) Lock.start
        (0 + 1)).control.runtime.lifecycle.representation.bank := by
    rw [moved]
    exact (young_bank rfl _ _ (by change 0 < 1000; decide)).symm
  have stored : (rungCold planning).control.runtime.references.demonPredictions =
      (Kernel.memoryAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later
        paid) (executedAgent (rungCold planning)) Lock.start
        (0 + 1)).control.runtime.references.demonPredictions := by
    rw [moved]
    exact (cold_step_predictions (primitive_learns rfl) .learnThenAct _).symm
  have wordsNested : ∀ word ∈ (Kernel.perceptAt
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start 0).frame.words,
      word ∈ (Kernel.perceptAt
        (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
        (executedAgent (rungCold planning)) Lock.start (0 + 1)).frame.words := by
    rw [shows, next]
    exact nested
  have symbolsSame : (Kernel.perceptAt
      (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start 0).frame.symbols =
      (Kernel.perceptAt
        (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
        (executedAgent (rungCold planning)) Lock.start (0 + 1)).frame.symbols := by
    rw [shows, next]
    exact symbols
  have calm := rung_calm 3 (by omega) (by omega)
  have departs := lock_departs (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl rfl (rungCold planning)
    Quiet.initial ctrlQuiet_initial (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown
    later paid apart opens turns (by change 0 + (1 + 1) < 1000; omega) silent still pays fits
    shares
    (fun slot _ inFirst => choose_nested (rungCold planning)
      (Kernel.memoryAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later
        paid) (executedAgent (rungCold planning)) Lock.start (0 + 1)) .learnThenAct
      .learnThenAct _ _ wordsNested symbolsSame bank stored slot inFirst)
    calm.1 calm.2
  refine ⟨?_, departs.1, fun same => apart same.symm, departs.2⟩
  change (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid).percept
    (Kernel.stateAt (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
      (executedAgent (rungCold planning)) Lock.start (0 + 1 + 1)) = paid
  rw [ended]
  change (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid).percept
    (Lock.done
      (decide (Kernel.actionAt
          (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
          (executedAgent (rungCold planning)) Lock.start 0 = rungExplorer.actionAt 0) &&
        decide (Kernel.actionAt
          (lock (rungExplorer.actionAt 0) (rungExplorer.actionAt 1) shown later paid)
          (executedAgent (rungCold planning)) Lock.start 1 = rungExplorer.actionAt 1))) = paid
  rw [opens, turns, decide_eq_true rfl, decide_eq_true rfl]
  rfl

/-- **Percepts for both places exist over the grid interface.** Three percepts of at most 174
words: `shown` and `later` carry zero reward words and `paid` a reward word of one; `later`
carries every word of `shown`, one word more, and the same symbols; and `shown` carries a word.
They are built from the frame of the rung's world at its refusing state, with the words replaced:
one word for `shown` and `paid`, that word and a second for `later`. -/
theorem places_exist : ∃ shown later paid : Percept Grid.interface,
    shown.reward = .zero ∧ later.reward = .zero ∧ paid.reward = .one ∧
      shown.frame.words.length ≤ 174 ∧ later.frame.words.length ≤ 174 ∧
      paid.frame.words.length ≤ 174 ∧
      (∀ word ∈ shown.frame.words, word ∈ later.frame.words) ∧
      shown.frame.symbols = later.frame.symbols ∧
      (∃ word, word ∈ shown.frame.words) ∧
      later.frame.words.length = shown.frame.words.length + 1 := by
  have clearOne : ∀ word ∈ [(⟨0x43, 1⟩ : SensorWord)],
      Grid.interface.reserved word.channel = false := by
    intro word member
    obtain rfl := List.mem_singleton.mp member
    decide
  have clearTwo : ∀ word ∈ [(⟨0x43, 1⟩ : SensorWord), ⟨0x43, 2⟩],
      Grid.interface.reserved word.channel = false := by
    intro word member
    rcases List.mem_cons.mp member with rfl | rest
    · decide
    · obtain rfl := List.mem_singleton.mp rest
      decide
  refine ⟨⟨{ ((gridWorld witnessConfig (rungConstruction .none).profile.taskMode).percept
        none).frame with
        words := [⟨0x43, 1⟩], bounded := by decide, clear := clearOne }, .zero⟩,
    ⟨{ ((gridWorld witnessConfig (rungConstruction .none).profile.taskMode).percept
        none).frame with
        words := [⟨0x43, 1⟩, ⟨0x43, 2⟩], bounded := by decide, clear := clearTwo },
      .zero⟩,
    ⟨{ ((gridWorld witnessConfig (rungConstruction .none).profile.taskMode).percept
        none).frame with
        words := [⟨0x43, 1⟩], bounded := by decide, clear := clearOne }, .one⟩,
    rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ⟨⟨0x43, 1⟩, ?_⟩, rfl⟩
  · change 1 ≤ 174
    omega
  · change 2 ≤ 174
    omega
  · change 1 ≤ 174
    omega
  · intro word member
    obtain rfl := List.mem_singleton.mp member
    exact List.mem_cons.mpr (Or.inl rfl)
  · exact List.mem_singleton.mpr rfl

end Rung

end AcornVerif.CurrentOnePlace
