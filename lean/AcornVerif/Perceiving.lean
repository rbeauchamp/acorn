/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Replay
import AcornVerif.Turns

/-!
# Where reading the observation is unnecessary, and a condition under which it is necessary

Two results over the kernel's definitions, for every interface.

* `replay_dominates`: in a class that conceals its goals behind one reference world (contract 2
  (b)), run in visits (every visit of a member starts from one state), whose percept after a step
  shows by one signal whether the step met the goal, every agent is dominated by an agent stepped
  by that signal alone: the rival solves, on every visit, every member the agent solves on that
  visit, and retains with no lapse. So no statement that is monotone in which members are solved
  on which visits can require reading the observation, in any class of that shape.
* `PerceptNeeded`: a condition on a class, a feedback, a bound and a visit limit under which no
  agent driven by the feedback alone separates (`PerceptNeeded.need`). It weakens (b) to the
  feedback: behind a projection of percepts that keeps the feedback, the class conceals its goals,
  while the percepts themselves may differ between members.
* `not_perceptNeeded_of_conceals`: the failing example in general form. A class that conceals its
  goals in the full percept, with a success signal, in which some agent separates, does not meet
  `PerceptNeeded` for that signal at that bound and limit.
* `PerceivingDecides`: condition (e) of contract 2. No agent whose effect on every run of the
  class is that of a clock-and-feedback agent meets the promise (`PerceivingNeeded`), and some
  agent meets it. The first half alone holds of every promise that no agent meets
  (`not_decides_of_unmet`). The definitions take any feedback; they compare with agents that read
  at most their reward only where the feedback determines the reward word.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {Φ : Type}

/-! ## The replaying rival of an agent -/

/-- The replaying agent is stepped by its signal. -/
theorem replay_steppedBy (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) :
    Stepped signal (replay interface length signal explore) :=
  ⟨fun memory shown =>
    (memory.choose (memory.record shown) explore,
      if memory.step < length then
        ⟨memory.step + 1, memory.choose (memory.record shown) explore :: memory.taken,
          memory.count, memory.record shown⟩
      else ⟨0, [], memory.count + 1, memory.record shown⟩),
    fun _ _ => rfl⟩

/-- The rival of an agent over a reference world: the replaying agent whose exploring action at a
visit and step is the action the agent takes there in its run in the reference's visits. It reads
its percept through the signal alone. -/
def rival (reference : World interface) (origin : reference.State) (length : ℕ)
    (signal : Percept interface → Bool) (agent : Agent interface) : Agent interface :=
  replay interface length signal
    (fun visit step => visitActions reference origin length agent visit step)

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

/-- **Under one-reference concealment in visits, a signal-stepped replayer dominates every
agent.** In a class that conceals its goals, where each member's percept after a step shows the
signal exactly when that step meets its goal, the rival of an agent is stepped by the signal,
solves on every visit every member the agent solves on that visit, and solves on every later visit
what it has solved once. -/
theorem replay_dominates (hidden : Conceals family goals reference origin) (length : ℕ)
    (signal : Percept interface → Bool)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (agent : Agent interface) :
    Stepped signal (rival reference origin length signal agent) ∧
      (∀ index visit, SolvesOnVisit family goals length agent visit index →
        SolvesOnVisit family goals length (rival reference origin length signal agent) visit
          index) ∧
      Retains family goals length (rival reference origin length signal agent) := by
  refine ⟨replay_steppedBy _ _ _, fun index visit solved => ?_,
    fun index visit later after solved => ?_⟩
  · obtain ⟨found, before, time, low, high, met⟩ :=
      (hidden.found_within length agent index (visit + 1)).mp
        ⟨visit, Nat.lt_succ_self visit, solved⟩
    exact replay_solves_explored family goals length signal _ index (decodes index) found visit
      (Nat.le_of_lt_succ before) ⟨time, low, high, met⟩
  · exact replay_solves family goals length signal _ index (decodes index) visit later after
      solved

/-- **Both promises about solving pass to the rival.** Where an agent separates before a stated
visit, its rival separates before that visit over the same members, and retains before every
horizon with no lapse, whether or not the agent retains. -/
theorem rival_separates (hidden : Conceals family goals reference origin) (length : ℕ)
    (signal : Percept interface → Bool)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    {agent : Agent interface} {bound limit : ℕ} {counted : List family.Index}
    (separates : SeparatesBy family goals length bound counted limit agent) :
    SeparatesBy family goals length bound counted limit
        (rival reference origin length signal agent) ∧
      ∀ horizon, RetainsBut family goals length horizon 0
        (rival reference origin length signal agent) := by
  obtain ⟨-, dominates, retains⟩ := replay_dominates hidden length signal decodes agent
  obtain ⟨visit, solved, before, many, each⟩ := separates
  exact ⟨⟨visit, solved, before, many, fun index member =>
    ⟨(each index member).1, dominates index visit (each index member).2⟩⟩,
    fun horizon => retains.but horizon⟩

/-! ## Masking a world's percepts -/

/-- A world whose percepts pass through a projection: the same states and transitions. -/
abbrev World.masked (world : World interface) (canon : Percept interface → Percept interface) :
    World interface where
  State := world.State
  step := world.step
  percept := fun state => canon (world.percept state)

/-- A class whose members' percepts pass through a projection. -/
abbrev WorldClass.masked (family : WorldClass interface)
    (canon : Percept interface → Percept interface) : WorldClass interface where
  Index := family.Index
  world := fun index => (family.world index).masked canon
  start := fun index => family.start index

/-- The goals of a class, read over the class with masked percepts. -/
def maskedGoals {family : WorldClass interface} (goals : family.Goals)
    (canon : Percept interface → Percept interface) : (family.masked canon).Goals :=
  fun index => ⟨(goals index).satisfied, (goals index).cap⟩

/-- Masking changes no path. -/
theorem path_masked (world : World interface) (canon : Percept interface → Percept interface)
    (start : world.State) (actions : ℕ → Act interface) (time : ℕ) :
    path (world.masked canon) start actions time = path world start actions time := by
  induction time with
  | zero => rfl
  | succ time ih => exact congrArg (fun state => world.step state (actions time)) ih

/-- **A feedback-driven agent cannot tell a world from its mask**, where the mask keeps the
feedback: its closed loop passes through the same states. -/
theorem FeedbackDriven.masked_stateAt {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (canon : Percept interface → Percept interface)
    (keeps : ∀ percept, feedback (canon percept) = feedback percept)
    (world : World interface) (start : world.State) (time : ℕ) :
    stateAt (world.masked canon) agent start time = stateAt world agent start time := by
  induction time using Nat.strong_induction_on with
  | _ time ih =>
    cases time with
    | zero => rfl
    | succ time =>
      have same : actionAt (world.masked canon) agent start time =
          actionAt world agent start time :=
        (actionAt_response (world.masked canon) agent start time).trans
          ((blind _ _ time (fun earlier within =>
            (keeps _).trans (congrArg (fun state => feedback (world.percept state))
              (ih earlier (Nat.lt_succ_of_le within))))).trans
            (actionAt_response world agent start time).symm)
      change world.step (stateAt (world.masked canon) agent start time)
          (actionAt (world.masked canon) agent start time) =
        world.step (stateAt world agent start time) (actionAt world agent start time)
      rw [same, ih time (Nat.lt_succ_self time)]

/-- Masking commutes with running a world in visits. -/
theorem masked_visits (world : World interface) (canon : Percept interface → Percept interface)
    (start : world.State) (length : ℕ) :
    visits (world.masked canon) start length = (visits world start length).masked canon := rfl

/-- A feedback-driven agent solves a member on a visit in the masked class exactly when it does in
the class. -/
theorem FeedbackDriven.masked_solves {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (canon : Percept interface → Percept interface)
    (keeps : ∀ percept, feedback (canon percept) = feedback percept)
    (family : WorldClass interface) (goals : family.Goals) (length visit : ℕ)
    (index : family.Index) :
    SolvesOnVisit (family.masked canon) (maskedGoals goals canon) length agent visit index ↔
      SolvesOnVisit family goals length agent visit index := by
  have same := fun time => blind.masked_stateAt canon keeps
    (visits (family.world index) (family.start index) length)
    (visitStart (family.world index) (family.start index) length) time
  constructor
  · rintro ⟨step, low, high, met⟩
    exact ⟨step, low, high, Eq.mp (congrArg
      (fun state : (family.world index).State × Fin (length + 1) =>
        (goals index).satisfied state.1) (same _)) met⟩
  · rintro ⟨step, low, high, met⟩
    exact ⟨step, low, high, Eq.mpr (congrArg
      (fun state : (family.world index).State × Fin (length + 1) =>
        (goals index).satisfied state.1) (same _)) met⟩

/-- A covering bound of a class is one of the class with masked percepts. -/
theorem covered_masked (canon : Percept interface → Percept interface) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound) :
    Covered (family.masked canon) (visitGoals (maskedGoals goals canon) length) bound := by
  intro actions solved each
  refine covered actions solved (fun index member => ?_)
  obtain ⟨time, low, high, met⟩ := each index member
  exact ⟨time, low, high, Eq.mp (congrArg (fun state => (goals index).satisfied state)
    (path_masked (family.world index) canon (family.start index) actions time)) met⟩

/-! ## A condition under which reading the observation is necessary -/

/-- **Perceiving is needed, at a bound and a visit limit.** Behind a projection of percepts that
keeps the feedback, the class conceals its goals behind one reference world: before a member's goal
is first met, the feedback tells nothing of which member this is. One action sequence meets the
goals of at most `cover` members within a visit. And the bound is at least `limit` times that
cover: more than an agent that cannot tell the members apart finds in the visits before the limit.
The percepts themselves may differ between members; contract 2 (b) is the case in which the
projection is the identity. -/
structure PerceptNeeded (feedback : Percept interface → Φ) (family : WorldClass interface)
    (goals : family.Goals) (length bound limit : ℕ) where
  /-- The projection of percepts. -/
  canon : Percept interface → Percept interface
  /-- The projection keeps the feedback. -/
  keeps : ∀ percept, feedback (canon percept) = feedback percept
  /-- The reference world behind which the projected percepts conceal the goals. -/
  reference : World interface
  /-- The reference world's start state. -/
  origin : reference.State
  /-- Behind the projection the class conceals its goals. -/
  conceals : Conceals (family.masked canon) (maskedGoals goals canon) reference origin
  /-- How many members one action sequence meets within a visit, at most. -/
  cover : ℕ
  /-- The covering bound, over the whole class. -/
  covered : Covered family (visitGoals goals length) cover
  /-- The bound is beyond what the visits before the limit let a percept-blind agent find. -/
  short : limit * cover ≤ bound

/-- **Where perceiving is needed, no agent driven by the feedback separates.** Such an agent runs
in the class as in its mask, where every agent finds at most `cover` new members on each visit, so
it has found at most `limit * cover` members before the limit and solves no more than the bound on
any one of those visits. -/
theorem PerceptNeeded.need {feedback : Percept interface → Φ} {length bound limit : ℕ}
    (needed : PerceptNeeded feedback family goals length bound limit) {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (counted : List family.Index) :
    ¬ SeparatesBy family goals length bound counted limit agent := by
  rintro ⟨visit, solved, before, many, each⟩
  have found := visits_ever needed.conceals (covered_masked needed.canon needed.covered) agent
    (visit + 1) solved (fun index member => ⟨visit, Nat.lt_succ_self visit,
      (blind.masked_solves needed.canon needed.keeps family goals length visit index).mpr
        (each index member).2⟩)
  exact absurd many (Nat.not_lt.mpr (found.trans
    ((Nat.mul_le_mul_right needed.cover (Nat.succ_le_of_lt before)).trans needed.short)))

/-- **The failing example, in general form.** A class that conceals its goals in the full percept
(contract 2 (b)) with a success signal, in which some agent separates at a bound before a limit,
does not meet `PerceptNeeded` for that signal at that bound and limit: the agent's rival is driven
by the signal and separates there. -/
theorem not_perceptNeeded_of_conceals (hidden : Conceals family goals reference origin)
    (length : ℕ) (signal : Percept interface → Bool)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    {agent : Agent interface} {bound limit : ℕ} {counted : List family.Index}
    (separates : SeparatesBy family goals length bound counted limit agent) :
    ¬ Nonempty (PerceptNeeded signal family goals length bound limit) := by
  rintro ⟨needed⟩
  exact needed.need (replay_steppedBy length signal _).feedbackDriven counted
    (rival_separates hidden length signal decodes separates).1

/-! ## Condition (e), by what it means -/

/-- A run of a class: a world and the state it starts in. -/
structure Run (interface : Interface) where
  /-- The world of the run. -/
  world : World interface
  /-- The state the run starts in. -/
  start : world.State

/-- **The agent's effect on every run of the class is that of a clock-and-feedback agent.** Some
agent driven by the feedback takes the world through the agent's states at every time of every run
of the class. The comparison is of the world's states and not of the actions taken, so an agent is
such an agent whatever it does where the world does not listen: at the last decision of a visit,
for instance, the world returns to its start whatever the action. An agent driven by the feedback
is such an agent, and so is one that differs from it only on percepts no run of the class
delivers. -/
def RunsAsDriven {ι : Type} (feedback : Percept interface → Φ) (run : ι → Run interface)
    (agent : Agent interface) : Prop :=
  ∃ shadow : Agent interface, FeedbackDriven feedback shadow ∧ ∀ index time,
    stateAt (run index).world agent (run index).start time =
      stateAt (run index).world shadow (run index).start time

/-- **Perceiving is needed**, for a feedback, the runs of a class and a promise: no agent whose
effect on every run of the class is that of a clock-and-feedback agent meets the promise. An agent
is excluded by its effect on the world, whatever it does where the world does not listen. This is
the negative half of condition (e) of contract 2 and not the condition: it holds of every promise
that no agent meets (`not_decides_of_unmet`). The condition is `PerceivingDecides`. -/
def PerceivingNeeded {ι : Type} (feedback : Percept interface → Φ) (run : ι → Run interface)
    (promise : Agent interface → Prop) : Prop :=
  ∀ agent, RunsAsDriven feedback run agent → ¬ promise agent

/-- **Condition (e) of contract 2: perceiving decides the promise.** Perceiving is needed for the
promise, and some agent meets it; so some agent does what no agent with the effect of an agent
driven by the feedback does. The definition is stated for any feedback and claims no more than
that. It is an advantage over agents that read at most their reward only for a feedback that
determines the reward word: for a feedback that leaves the reward word out, the agent that meets
the promise may be one that reads nothing but its reward. Contract 2 asks the condition for a
feedback that determines the reward. Its witnesses are the cued doors, with the reward word as the
feedback (`cued_perceiving`), and the day-and-night class of the grid world, with the reward word
and the achievement flag (`rung_fork_decides`). A promise no agent meets fails it
(`not_decides_of_unmet`), and so does separation in a class that conceals its goals behind one
reference world with a success signal (`not_decides_of_conceals`). -/
def PerceivingDecides {ι : Type} (feedback : Percept interface → Φ) (run : ι → Run interface)
    (promise : Agent interface → Prop) : Prop :=
  PerceivingNeeded feedback run promise ∧ ∃ agent, promise agent

/-- **A promise no agent meets fails the condition, though perceiving is needed for it.** The
negative half holds of such a promise with nothing to exclude, and no agent shows that reading the
observation does better. -/
theorem not_decides_of_unmet {ι : Type} (feedback : Percept interface → Φ)
    (run : ι → Run interface) {promise : Agent interface → Prop}
    (unmet : ∀ agent, ¬ promise agent) :
    PerceivingNeeded feedback run promise ∧ ¬ PerceivingDecides feedback run promise :=
  ⟨fun agent _ => unmet agent, fun decides => decides.2.elim unmet⟩

/-- An agent driven by the feedback has the effect of one, on every class. -/
theorem FeedbackDriven.runsAsDriven {ι : Type} {feedback : Percept interface → Φ}
    {agent : Agent interface} (blind : FeedbackDriven feedback agent) (run : ι → Run interface) :
    RunsAsDriven feedback run agent :=
  ⟨agent, blind, fun _ _ => rfl⟩

/-- The runs of a class in visits: each member's world in visits, from the start of a visit. -/
def visitRuns (family : WorldClass interface) (length : ℕ) : family.Index → Run interface :=
  fun index => ⟨visits (family.world index) (family.start index) length,
    visitStart (family.world index) (family.start index) length⟩

/-- **The situated condition is sufficient** for the negative half of the condition. In a class
in visits that meets `PerceptNeeded` at a bound and a limit, perceiving is needed for separation
at that bound before that limit. -/
theorem PerceptNeeded.perceivingNeeded {feedback : Percept interface → Φ}
    {length bound limit : ℕ} (needed : PerceptNeeded feedback family goals length bound limit)
    (counted : List family.Index) :
    PerceivingNeeded feedback (visitRuns family length)
      (SeparatesBy family goals length bound counted limit) := by
  rintro agent ⟨shadow, blind, same⟩ ⟨visit, solved, before, many, each⟩
  refine needed.need blind counted ⟨visit, solved, before, many, fun index member =>
    ⟨(each index member).1, ?_⟩⟩
  obtain ⟨step, low, high, met⟩ := (each index member).2
  exact ⟨step, low, high, Eq.mp (congrArg
    (fun state : (family.world index).State × Fin (length + 1) =>
      (goals index).satisfied state.1) (same index _)) met⟩

/-- **A class that conceals its goals behind one reference world, with a success signal, fails
the condition**, in visits, for that signal and for separation at every bound and limit. Where some
agent separates, its rival is driven by the signal and separates too; so either no agent meets the
promise, or one that reads nothing but the signal does. -/
theorem not_decides_of_conceals (hidden : Conceals family goals reference origin) (length : ℕ)
    (signal : Percept interface → Bool)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (bound limit : ℕ) (counted : List family.Index) :
    ¬ PerceivingDecides signal (visitRuns family length)
      (SeparatesBy family goals length bound counted limit) := by
  rintro ⟨needed, agent, separates⟩
  have blind : FeedbackDriven signal (rival reference origin length signal agent) :=
    (replay_steppedBy length signal _).feedbackDriven
  exact needed _ (blind.runsAsDriven _)
    (rival_separates hidden length signal decodes separates).1

/-- **The hybrid has the effect of a clock-and-feedback agent on a class that never shows it the
percepts on which it differs.** A chooser whose preference and memory read the percept through the
feedback alone, made to hold a resting preference on a set of percepts no run of the class
delivers, is in the states of the plain chooser at every time of every run. -/
theorem aloof_runsAsDriven {ι E V Core : Type} (feedback : Percept interface → Φ)
    (select : E → V → Act interface × E) (core : Core) (seed : E) (prefer : Core → Φ → V)
    (advance : Core → Φ → Act interface → Core) (alien : Percept interface → Prop)
    [DecidablePred alien] (rest : V) (run : ι → Run interface)
    (never : ∀ index state, ¬ alien ((run index).world.percept state)) :
    RunsAsDriven feedback run
      (chooser select core seed
        (aloof alien rest (fun inner percept => prefer inner (feedback percept)))
        (fun inner percept action => advance inner (feedback percept) action)) :=
  ⟨chooser select core seed (fun inner percept => prefer inner (feedback percept))
      (fun inner percept action => advance inner (feedback percept) action),
    (chooser_stepped feedback select core seed prefer advance).feedbackDriven,
    fun index time => congrArg Prod.fst
      (aloof_loop select core seed (fun inner percept => prefer inner (feedback percept))
        (fun inner percept action => advance inner (feedback percept) action) alien rest
        (run index).world (run index).start (never index) time)⟩

/-! ## Forks in time are sufficient -/

/-- The runs of a class in turns: each member's world in turns under each order, from the start of
its first visit. -/
def turnRuns (family : TurnClass interface) (length : ℕ) :
    family.Index × (ℕ → Bool) → Run interface :=
  fun pair => ⟨turns (family.world pair.1) (family.start pair.1) pair.2 length,
    turnStart (family.world pair.1) (family.start pair.1) pair.2 length 0⟩

/-- **Forks in time are sufficient** for the negative half of the condition. In a class in turns
whose members are forks and whose situations give one feedback until the goal is met, no agent
whose effect on every run of the class is that of a clock-and-feedback agent masters, at any
bound, key and limit. -/
theorem forks_perceivingNeeded {feedback : Percept interface → Φ} {family : TurnClass interface}
    {goals : family.Goals} {length : ℕ} (mute : Mute feedback family goals)
    (apart : Apart family goals length) (bound limit : ℕ) {κ : Type} (key : family.Index → κ) :
    PerceivingNeeded feedback (turnRuns family length)
      (MastersBy family goals length bound key limit) := by
  rintro agent ⟨shadow, blind, same⟩ masters
  exact blind.masters mute apart bound limit key
    (MastersBy.of_states (fun index order time => same (index, order) time) masters)

/-- **Mastery before visit 0 fails the condition, in every class.** No visit is before visit 0, so
no agent masters before it: perceiving is needed for that promise with nothing to exclude, and no
agent shows that reading the observation does better. -/
theorem not_decides_before_zero {ι : Type} (feedback : Percept interface → Φ)
    (run : ι → Run interface) (family : TurnClass interface) (goals : family.Goals)
    (length bound : ℕ) {κ : Type} (key : family.Index → κ) :
    PerceivingNeeded feedback run (MastersBy family goals length bound key 0) ∧
      ¬ PerceivingDecides feedback run (MastersBy family goals length bound key 0) :=
  not_decides_of_unmet feedback run (fun _ masters => by
    obtain ⟨_, _, _, before, _⟩ := masters
    exact Nat.not_lt_zero _ before)

end AcornVerif.Kernel
