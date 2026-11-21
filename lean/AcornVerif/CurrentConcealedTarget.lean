/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentGridWorld
import AcornVerif.CurrentTerrain
import AcornVerif.Replay

/-!
# A concealed target in the executed grid world

`Host.Goal.find` is a reach goal whose observation conceals its target: the observation is
the one cue of its family and whether the body is in the goal box
(`CurrentGoals.find_observe`). This module builds the class of concealed targets over one
host world from the executed step, observation and percept adapter of
`AcornVerif.CurrentGridWorld`, and proves of it the bounds of `AcornVerif.Concealment`,
`AcornVerif.Visits` and `AcornVerif.Replay`.

`findClass` installs, in one host world with one carried result, each target whose goal box
does not hold the body's position. Its members conceal their goals behind the same world with
the target `nowhere` installed, whose box holds no position of the body's box
(`find_conceals`). Three executed facts give it: the dynamics do not read the goal
(`step_physical`), so a member and the reference step to worlds that differ only in their
goals (`twin_paths`); the observation reads the goal only through the task relation
(`observe_twins`); and the task relation of a concealed target that is not met is the same
for every target (`find_task`). A walk of `cap` steps comes within three tiles of at most
`49 + 7 cap` targets (`find_covered`). So:

- **First visit, every agent.** Every agent, the executed agent included, solves at most
  `49 + 7 cap` members (`find_need`, `executed_find_first`).
- **Every visit, experience-free agents.** In visits of `cap` steps, every experience-free
  agent, the uniform-random comparator included, solves at most `49 + 7 cap` members on each
  visit (`find_visits_need`, `comparator_find_visits`). At a cap of 3000 and a window of
  radius 120 that is at most 21049 of the at least 57551 members in the window: the window's
  57600 tiles less at most 49 within three tiles of the start (`far_window_visits`).
- **First success, every agent.** On each visit every agent solves at most `49 + 7 cap`
  members it has not solved before, and over `n` visits at most `n (49 + 7 cap)`
  (`find_visits_first_success`, `find_visits_ever`).
- **Re-solving and separation.** The percept's achievement flag after a step is the goal's
  completion (`achieved_decodes`), so the replaying agent with that flag as its signal, which
  is not experience-free (`find_replay_learns`), solves on every later visit each member it
  has solved once (`find_replay`). If its explorations of the visits up to one visit meet
  more than `49 + 7 cap` targets, on that visit it solves all of them while every
  experience-free agent solves fewer on every visit (`find_replay_separates`). Whether an
  exploration meets a target depends on the terrain, so the theorem takes it as a hypothesis;
  `witness_separation` discharges it in one world, the standard configuration at seed 1 and
  side 64 with no deer and no food (`witness_standard`): three visits of seven steps east,
  west and south from the box's center meet 147 members, more than the bound 98, so there the
  replaying agent solves 147 on visit 2 and every experience-free agent fewer on every visit.
  The executed step along the three walks (`witness_walk`) reduces structurally to elevation-only
  terrain checks on the 21 entered tiles (`fbm_eq_fastFbm`, discharging moisture via
  `CurrentTerrain.fbm_isOk`); the count is structural.
- **A class with the kernel's form of conditions (a) to (c).** `findClass` holds targets no walk
  can reach within a visit. `feasibleFind` holds the concealed targets a visit can meet, so its
  members are feasible by how it is indexed; it keeps the concealment and the bound
  (`feasibleFind_conceals`, `feasibleFind_covered`). In the same world, with visits of seven
  steps, the 147 members above make it a `Kernel.ConcealedClass` with the bound 98
  (`witness_concealed`). This says nothing about obligation 4 of `docs/mission-contract.md`, the
  goal-information and exploration premises. That structure states condition (c) as fewer than
  all, so the class is not thereby shown to be a concealed class (sentence 5 of contract 2 there).
  Every member's target lies within `3 + length` tiles of the start, for every terrain
  (`feasible_window`), so the class is finite, with at most `(2 (3 + length) + 1)² - 49` members
  (`feasible_count`): at most 392 for visits of seven steps.

Hypotheses and limits. The class is of target positions over one host world: reading a bound
as a fraction of seeds would assume that the seed hash places targets independently of the
agent's walk (assumed). A visit is the kernel's world in visits of the executed grid world;
`AcornVerif.CurrentVisits` relates the host's loop of visits to it. A step the host refuses
leads to the absorbing refused state, where no goal is met, in a member and the reference alike.
-/

namespace AcornVerif.CurrentConcealedTarget
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentCurriculum

variable {config : Host.WorldConfig}

/-! ## The reference target -/

/-- A target whose goal box holds no position of any body's box: four tiles before the box's
first corner on both axes. -/
def nowhere : Host.Position := ⟨⟨-4, by omega⟩, ⟨-4, by omega⟩⟩

/-- No world reports the target `nowhere` met. -/
theorem nowhere_unmet (world : Host.World config)
    (installed : world.goal = some (.find nowhere)) : world.goalSatisfied = false := by
  cases met : world.goalSatisfied with
  | false => rfl
  | true =>
    obtain ⟨horizontal, -⟩ := (find_goal_iff world nowhere installed).mp met
    have nonnegative : (0 : ℤ) ≤ world.body.position.position.x.val :=
      Int.natCast_nonneg world.body.position.x.val
    simp only [nowhere, FeatureConstants.reachRadius] at horizontal
    omega

/-- With a concealed target installed, the world's task relation is the family's cue and
whether the target is met. -/
theorem find_task (world : Host.World config) (target : Host.Position)
    (installed : world.goal = some (.find target)) :
    world.taskObservation = .find (Rng.hash3 5 0 0) world.goalSatisfied := by
  rw [goalSatisfied_eq world _ installed]
  unfold Host.World.taskObservation
  rw [installed]
  exact find_observe _ _ _ _

/-! ## Worlds that differ in their goals -/

/-- Two worlds that differ at most in their installed goals, and deliver one task relation,
deliver one observation. -/
theorem observe_twins (first second : Host.World config)
    (twins : physical first = physical second)
    (task : first.taskObservation = second.taskObservation) :
    first.observe = second.observe := by
  obtain ⟨time, body, goal, goalStart, harvested, deer, food, rng⟩ := first
  obtain ⟨time', body', goal', goalStart', harvested', deer', food', rng'⟩ := second
  have sameTime : time = time' := congrArg Host.World.time twins
  have sameBody : body = body' := congrArg Host.World.body twins
  have sameHarvested : harvested = harvested' := congrArg Host.World.harvested twins
  have sameDeer : deer = deer' := congrArg Host.World.deer twins
  have sameFood : food = food' := congrArg Host.World.food twins
  have sameRng : rng = rng' := congrArg Host.World.rng twins
  subst sameTime sameBody sameHarvested sameDeer sameFood sameRng
  unfold Host.World.observe
  rw [task]
  rfl

/-- Two worlds that differ at most in their installed goals, and deliver one task relation,
deliver one sensed observation. -/
theorem sensed_twins (first second : Host.World config)
    (twins : physical first = physical second)
    (task : first.taskObservation = second.taskObservation) :
    sensed first = sensed second := by
  unfold sensed
  rw [observe_twins first second twins task]

/-- A step result with no completion is unchanged by clearing its completion. -/
theorem clear_done (events : Host.StepResult) (unmet : events.done = false) :
    { events with done := false } = events := by
  cases events
  cases unmet
  rfl

/-- The start of a member: the host world with the concealed target installed. -/
def member (live : Live config) (target : Host.Position) : Option (Live config) :=
  some ⟨live.world.setGoal (.find target), live.carried⟩

/-- Along every action sequence, a member's path and the reference's path are both refused,
or both live with worlds that differ only in their goals, which stay installed. Where the
member's goal has not been met, they carry one result and the member reports its goal
unmet. -/
theorem twin_paths (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (outside : ¬ InGoalBox target live.world.body.position.position) (cap : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface) (time : ℕ)
    (unmet : ∀ earlier, 1 ≤ earlier → earlier ≤ time →
      ¬ (completion config mode cap).satisfied
      (Kernel.path (gridWorld config mode) (member live target) actions earlier)) :
    (Kernel.path (gridWorld config mode) (member live target) actions time = none ∧
      Kernel.path (gridWorld config mode) (member live nowhere) actions time = none) ∨
    ∃ found base, Kernel.path (gridWorld config mode) (member live target) actions time =
        some found ∧
      Kernel.path (gridWorld config mode) (member live nowhere) actions time = some base ∧
      physical found.world = physical base.world ∧ found.world.goal = some (.find target) ∧
      base.world.goal = some (.find nowhere) ∧ found.carried = base.carried ∧
      found.world.goalSatisfied = false := by
  induction time with
  | zero =>
    refine Or.inr ⟨⟨live.world.setGoal (.find target), live.carried⟩,
      ⟨live.world.setGoal (.find nowhere), live.carried⟩, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    cases met : (live.world.setGoal (.find target)).goalSatisfied with
    | false => rfl
    | true => exact absurd ((find_goal_iff _ target rfl).mp met) outside
  | succ time ih =>
    rcases ih (fun earlier low high => unmet earlier low (Nat.le_succ_of_le high)) with
      ⟨gone, goneBase⟩ | ⟨found, base, here, hereBase, twins, goal, goalBase, -, -⟩
    · left
      constructor
      · change (Kernel.path (gridWorld config mode) (member live target) actions time).bind
          (advance · (actions time)) = none
        rw [gone]
        rfl
      · change (Kernel.path (gridWorld config mode) (member live nowhere) actions time).bind
          (advance · (actions time)) = none
        rw [goneBase]
        rfl
    · have next : Kernel.path (gridWorld config mode) (member live target) actions (time + 1) =
          advance found (actions time) := by
        change (Kernel.path (gridWorld config mode) (member live target) actions time).bind
          (advance · (actions time)) = _
        rw [here]
        rfl
      have nextBase : Kernel.path (gridWorld config mode) (member live nowhere) actions
          (time + 1) = advance base (actions time) := by
        change (Kernel.path (gridWorld config mode) (member live nowhere) actions time).bind
          (advance · (actions time)) = _
        rw [hereBase]
        rfl
      have same := (step_physical found.world (Host.Action.fromIndex (actions time).val)).symm.trans
        ((congrArg (fun world => Host.World.step world (Host.Action.fromIndex (actions time).val))
          twins).trans (step_physical base.world (Host.Action.fromIndex (actions time).val)))
      have metNext := unmet (time + 1) (Nat.succ_pos time) (Nat.le_refl _)
      rw [next] at metNext ⊢
      rw [nextBase]
      cases stepped : found.world.step (Host.Action.fromIndex (actions time).val) with
      | error refusal =>
        cases steppedBase : base.world.step (Host.Action.fromIndex (actions time).val) with
        | error refusalBase =>
          left
          exact ⟨by simp only [advance, stepped], by simp only [advance, steppedBase]⟩
        | ok pairBase =>
          simp only [stepped, steppedBase] at same
          cases same
      | ok pair =>
        obtain ⟨world, events⟩ := pair
        cases steppedBase : base.world.step (Host.Action.fromIndex (actions time).val) with
        | error refusalBase =>
          simp only [stepped, steppedBase] at same
          cases same
        | ok pairBase =>
          obtain ⟨worldBase, eventsBase⟩ := pairBase
          simp only [stepped, steppedBase, Except.ok.injEq, Prod.mk.injEq] at same
          obtain ⟨twinsNext, eventsSame⟩ := same
          rw [advance_ok found _ world events stepped] at metNext ⊢
          rw [advance_ok base _ worldBase eventsBase steppedBase]
          have unmetNext : world.goalSatisfied = false := by
            cases met : world.goalSatisfied with
            | false => rfl
            | true => exact (metNext ⟨⟨world, events.raw⟩, rfl, met⟩).elim
          have goalNext : world.goal = some (.find target) :=
            (Host.World.step_goal _ _ _ _ stepped).1.trans goal
          have goalBaseNext : worldBase.goal = some (.find nowhere) :=
            (Host.World.step_goal _ _ _ _ steppedBase).1.trans goalBase
          have done : events.done = false :=
            (Host.World.step_completion _ _ _ _ stepped).trans unmetNext
          have doneBase : eventsBase.done = false :=
            (Host.World.step_completion _ _ _ _ steppedBase).trans
              (nowhere_unmet worldBase goalBaseNext)
          have sameEvents : events = eventsBase :=
            calc events = { events with done := false } := (clear_done events done).symm
              _ = { eventsBase with done := false } := eventsSame
              _ = eventsBase := clear_done eventsBase doneBase
          right
          exact ⟨⟨world, events.raw⟩, ⟨worldBase, eventsBase.raw⟩, rfl, rfl, twinsNext,
            goalNext, goalBaseNext, by rw [sameEvents], unmetNext⟩

/-! ## The class of concealed targets -/

/-- The class of concealed targets over one host world: each member installs a target whose
goal box does not hold the body's position, in the same world with the same carried
result. -/
def findClass (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config) :
    Kernel.WorldClass Grid.interface where
  Index := { target : Host.Position // ¬ InGoalBox target live.world.body.position.position }
  world := fun _ => gridWorld config mode
  start := fun target => member live target.1

/-- The class of concealed targets conceals its goals behind the same world with the target
`nowhere` installed: before a member's target is met, the member delivers the reference's
percept along every action sequence. -/
theorem find_conceals (mode : TaskFeatureMode) (live : Live config) (cap : ℕ) :
    Kernel.Conceals (findClass config mode live) (fun _ => completion config mode cap)
      (gridWorld config mode) (member live nowhere) := by
  intro target actions time unmet
  rcases twin_paths mode live target.1 target.2 cap actions time unmet with
    ⟨gone, goneBase⟩ |
      ⟨found, base, here, hereBase, twins, goal, goalBase, carried, unmetNow⟩
  · change percept mode (Kernel.path (gridWorld config mode) (member live target.1) actions
        time) = percept mode (Kernel.path (gridWorld config mode) (member live nowhere) actions
        time)
    rw [gone, goneBase]
  · change percept mode (Kernel.path (gridWorld config mode) (member live target.1) actions
        time) = percept mode (Kernel.path (gridWorld config mode) (member live nowhere) actions
        time)
    rw [here, hereBase]
    have task : found.world.taskObservation = base.world.taskObservation := by
      rw [find_task found.world target.1 goal, find_task base.world nowhere goalBase, unmetNow,
        nowhere_unmet base.world goalBase]
    change Grid.percept mode (sensed found.world) found.carried.reward found.carried.events.done =
      Grid.percept mode (sensed base.world) base.carried.reward base.carried.events.done
    rw [sensed_twins found.world base.world twins task, carried]

/-- A concealed target that an action sequence meets within `cap` steps lies within three
tiles of the first `cap + 1` points of the body's walk. -/
theorem find_met_swept (mode : TaskFeatureMode) (live : Live config) (cap : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface) (target : Host.Position)
    (met : (completion config mode cap).MetBy (member live target) actions) :
    tile target ∈ swept 3 (walk (physical live.world) actions) cap := by
  obtain ⟨time, -, high, final, reached, done⟩ := met
  have installed : final.world.goal = some (.find target) :=
    path_goal mode ⟨live.world.setGoal (.find target), live.carried⟩ final actions time reached
  have inside : InGoalBox target final.world.body.position.position :=
    (find_goal_iff final.world target installed).mp done
  have track :=
    path_physical mode ⟨live.world.setGoal (.find target), live.carried⟩ actions time
  change (Kernel.path (gridWorld config mode) (member live target) actions time).map
    (fun state => physical state.world) = _ at track
  rw [reached] at track
  have here : walk (physical live.world) actions time =
      tile final.world.body.position.position :=
    walk_live (physical live.world) (physical final.world) actions time track.symm
  have near : tile target ∈ box 3 (walk (physical live.world) actions time) := by
    rw [here]
    exact box_of_goalBox target _ inside
  exact box_subset_swept 3 _ cap time high near

/-- A concealed target within three tiles of the tile the body stands on after a step of an
action sequence is met at that step: the world's dynamics do not read the installed goal. This is
the converse of `find_met_swept` at one step. -/
theorem find_near_met (mode : TaskFeatureMode) (live : Live config) (cap : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface) (step : ℕ) (point : ℤ × ℤ)
    (walked : (physicalPath (physical live.world) actions step).map
      (fun world => tile world.body.position.position) = some point)
    (target : Host.Position) (near : tile target ∈ box 3 point) :
    (completion config mode cap).satisfied
      (Kernel.path (gridWorld config mode) (member live target) actions step) := by
  have track := path_physical mode ⟨live.world.setGoal (.find target), live.carried⟩ actions step
  change (Kernel.path (gridWorld config mode) (member live target) actions step).map
    (fun state => physical state.world) = physicalPath (physical live.world) actions step at track
  cases reached : Kernel.path (gridWorld config mode) (member live target) actions step with
  | none =>
    rw [reached] at track
    rw [← track] at walked
    cases walked
  | some final =>
    rw [reached] at track
    rw [← track] at walked
    have here : tile final.world.body.position.position = point := Option.some.inj walked
    have installed : final.world.goal = some (.find target) :=
      path_goal mode ⟨live.world.setGoal (.find target), live.carried⟩ final actions step reached
    have close : tile target ∈ box 3 (tile final.world.body.position.position) := by
      rw [here]
      exact near
    exact ⟨final, rfl, (find_goal_iff final.world target installed).mpr (mem_box.mp close)⟩

/-- One action sequence meets the concealed targets of at most `49 + 7 cap` members in `cap`
steps, for every terrain. -/
theorem find_covered (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (cap : ℕ) :
    Kernel.Covered (findClass config mode live) (fun _ => completion config mode cap)
      (49 + 7 * cap) := by
  intro actions solved each
  have inside : solved.image (fun target => tile target.1) ⊆
      swept 3 (walk (physical live.world) actions) cap := by
    intro point chosen
    obtain ⟨target, picked, rfl⟩ := Finset.mem_image.mp chosen
    exact find_met_swept mode live cap actions target.1 (each target picked)
  calc solved.card
      = (solved.image (fun target => tile target.1)).card :=
        (Finset.card_image_of_injective solved
          (fun first second same => Subtype.ext (tile_injective same))).symm
    _ ≤ (swept 3 (walk (physical live.world) actions) cap).card := Finset.card_le_card inside
    _ ≤ (2 * 3 + 1) * (2 * 3 + 1) + (2 * 3 + 1) * cap :=
        card_swept 3 _ cap (fun index _ => walk_near _ actions index)
    _ = 49 + 7 * cap := rfl

/-! ## Bounds -/

/-- The first-visit bound. Every agent solves at most `49 + 7 cap` concealed targets in `cap`
steps. -/
theorem find_need (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (cap : ℕ) :
    Kernel.Need (findClass config mode live) (fun _ => completion config mode cap)
      (fun _ => True) (49 + 7 * cap) :=
  (find_conceals mode live cap).need (find_covered config mode live cap)

/-- The executed agent, from every state of it, solves at most `49 + 7 cap` concealed
targets on a first visit. -/
theorem executed_find_first {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
    (state : Agent Grid.interface profile features criterion dimension planning)
    (live : Live config) (cap : ℕ)
    (solved : Finset (findClass config profile.taskMode live).Index)
    (each : ∀ target ∈ solved, Kernel.Solves (findClass config profile.taskMode live)
      (fun _ => completion config profile.taskMode cap) (executedAgent state) target) :
    solved.card ≤ 49 + 7 * cap :=
  find_need config profile.taskMode live cap (executedAgent state) trivial solved each

/-- Need on every visit. In visits of `cap` steps, every experience-free agent solves at most
`49 + 7 cap` concealed targets on each visit. -/
theorem find_visits_need (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (cap : ℕ) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent) (count : ℕ)
    (solved : Finset (findClass config mode live).Index)
    (each : ∀ target ∈ solved, Kernel.SolvesOnVisit (findClass config mode live)
      (fun _ => completion config mode cap) cap agent count target) :
    solved.card ≤ 49 + 7 * cap :=
  Kernel.visits_need (find_conceals mode live cap) (find_covered config mode live cap) free
    count solved each

/-- The uniform-random comparator, whatever its stream, solves at most `49 + 7 cap` concealed
targets on each visit of `cap` steps. -/
theorem comparator_find_visits (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (cap : ℕ) (stream : Rng.Xoshiro256) (count : ℕ)
    (solved : Finset (findClass config mode live).Index)
    (each : ∀ target ∈ solved, Kernel.SolvesOnVisit (findClass config mode live)
      (fun _ => completion config mode cap) cap (comparator stream) count target) :
    solved.card ≤ 49 + 7 * cap :=
  find_visits_need config mode live cap (comparator_openLoop stream).experienceFree count
    solved each

/-- First success. On each visit of `cap` steps every agent solves at most `49 + 7 cap`
concealed targets it solved on no earlier visit. -/
theorem find_visits_first_success (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (cap : ℕ) (agent : Kernel.Agent Grid.interface) (count : ℕ)
    (solved : Finset (findClass config mode live).Index)
    (each : ∀ target ∈ solved,
      Kernel.SolvesOnVisit (findClass config mode live) (fun _ => completion config mode cap)
        cap agent count target ∧
      ∀ earlier, earlier < count → ¬ Kernel.SolvesOnVisit (findClass config mode live)
        (fun _ => completion config mode cap) cap agent earlier target) :
    solved.card ≤ 49 + 7 * cap :=
  Kernel.visits_first_success (find_conceals mode live cap) (find_covered config mode live cap)
    agent count solved each

/-- Over its first `count` visits of `cap` steps every agent solves at most
`count (49 + 7 cap)` concealed targets. -/
theorem find_visits_ever (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (cap : ℕ) (agent : Kernel.Agent Grid.interface) (count : ℕ)
    (solved : Finset (findClass config mode live).Index)
    (each : ∀ target ∈ solved, ∃ earlier, earlier < count ∧
      Kernel.SolvesOnVisit (findClass config mode live) (fun _ => completion config mode cap)
        cap agent earlier target) :
    solved.card ≤ count * (49 + 7 * cap) :=
  Kernel.visits_ever (find_conceals mode live cap) (find_covered config mode live cap) agent
    count solved each

/-! ## Re-solving -/

/-- The signal of the achievement flag: whether the percept's preceding transition met the
installed goal. -/
def achievedSignal (percept : Percept Grid.interface) : Bool := percept.frame.achieved

/-- After every step of the grid world, the percept's achievement flag is set exactly when the
step meets the installed goal. -/
theorem achieved_decodes (config : Host.WorldConfig) (mode : TaskFeatureMode) (cap : ℕ)
    (state : Option (Live config)) (action : Kernel.Act Grid.interface) :
    achievedSignal ((gridWorld config mode).percept ((gridWorld config mode).step state action)) =
        true ↔
      (completion config mode cap).satisfied ((gridWorld config mode).step state action) := by
  have refused : achievedSignal ((gridWorld config mode).percept none) = true ↔
      (completion config mode cap).satisfied none := by
    constructor
    · intro shown
      exact absurd shown Bool.false_ne_true
    · rintro ⟨_, never, _⟩
      cases never
  cases state with
  | none => exact refused
  | some live =>
    change achievedSignal ((gridWorld config mode).percept (advance live action)) = true ↔
      (completion config mode cap).satisfied (advance live action)
    cases stepped : live.world.step (Host.Action.fromIndex action.val) with
    | error refusal =>
      have gone : advance live action = none := by simp only [advance, stepped]
      rw [gone]
      exact refused
    | ok pair =>
      obtain ⟨world, events⟩ := pair
      rw [advance_ok live action world events stepped]
      change events.done = true ↔ ∃ found : Live config,
        some (⟨world, events.raw⟩ : Live config) = some found ∧
          found.world.goalSatisfied = true
      rw [Host.World.step_completion _ _ _ _ stepped]
      exact ⟨fun met => ⟨⟨world, events.raw⟩, rfl, met⟩,
        fun ⟨found, same, met⟩ => by cases same; exact met⟩

/-- The replaying agent with the achievement flag as its signal, one agent for the whole
class, solves on every later visit of `cap` steps each concealed target it has solved on
one visit. -/
theorem find_replay (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (cap : ℕ) (explore : ℕ → ℕ → Kernel.Act Grid.interface)
    (target : (findClass config mode live).Index) (count later : ℕ) (after : count < later)
    (solved : Kernel.SolvesOnVisit (findClass config mode live)
      (fun _ => completion config mode cap) cap
      (Kernel.replay Grid.interface cap achievedSignal explore) count target) :
    Kernel.SolvesOnVisit (findClass config mode live) (fun _ => completion config mode cap) cap
      (Kernel.replay Grid.interface cap achievedSignal explore) later target :=
  Kernel.replay_solves (findClass config mode live) (fun _ => completion config mode cap) cap
    achievedSignal explore target (achieved_decodes config mode cap) count later after solved

/-- The replaying agent with the achievement flag as its signal is not experience-free: what
it stores depends on whether its percept shows the flag. -/
theorem find_replay_learns (mode : TaskFeatureMode) (cap : ℕ)
    (explore : ℕ → ℕ → Kernel.Act Grid.interface) :
    ¬ Kernel.ExperienceFree (Kernel.replay Grid.interface cap achievedSignal explore) :=
  Kernel.replay_not_experienceFree cap achievedSignal explore
    (Grid.percept mode blank ⟨0⟩ true) (Grid.percept mode blank ⟨0⟩ false) rfl rfl

/-- The separation in the grid world. If the replaying agent's explorations of the visits up to
`last` meet, from the host world within `cap` steps, more concealed targets than
`49 + 7 cap`, then on visit `last` it solves all of them, while on every visit every
experience-free agent solves fewer. Whether an exploration meets a target depends on the
terrain; it is a hypothesis here. -/
theorem find_replay_separates (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (cap : ℕ) (explore : ℕ → ℕ → Kernel.Act Grid.interface)
    (members : Finset (findClass config mode live).Index) (last : ℕ)
    (explored : ∀ target ∈ members, ∃ visit, visit ≤ last ∧
      ∃ step, 1 ≤ step ∧ step ≤ cap ∧ (completion config mode cap).satisfied
        (Kernel.path (gridWorld config mode) (member live target.1) (explore visit) step))
    (many : 49 + 7 * cap < members.card) :
    (∀ target ∈ members, Kernel.SolvesOnVisit (findClass config mode live)
      (fun _ => completion config mode cap) cap
      (Kernel.replay Grid.interface cap achievedSignal explore) last target) ∧
    ∀ agent : Kernel.Agent Grid.interface, Kernel.ExperienceFree agent →
      ∀ (count : ℕ) (solved : Finset (findClass config mode live).Index),
        (∀ target ∈ solved, Kernel.SolvesOnVisit (findClass config mode live)
          (fun _ => completion config mode cap) cap agent count target) →
          solved.card < members.card :=
  Kernel.replay_separates (find_conceals mode live cap) (find_covered config mode live cap)
    achievedSignal explore (fun _ => achieved_decodes config mode cap) members last explored many

/-! ## The far window -/

/-- A target is a member of the class exactly when its tile is not within three tiles of the
body's start. -/
theorem member_tile (live : Live config) (target : Host.Position) :
    ¬ InGoalBox target live.world.body.position.position ↔
      tile target ∉ box 3 (tile live.world.body.position.position) :=
  not_congr ⟨box_of_goalBox target _, fun near => by
    have close := mem_box.mp near
    exact close⟩

/-- At a cap of 3000 steps and a window of radius 120, every experience-free agent solves on
each visit at most 21049 of the members in the window. The window has 57600 tiles; the tiles
of the members in it are those not within three tiles of the start, at least 57551 of them,
and at least 36502 of those are tiles of no member the agent solves. 21049 is under 36.6
percent of 57551. -/
theorem far_window_visits (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (side : Host.Coordinate) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent) (count : ℕ)
    (solved : Finset (findClass config mode live).Index)
    (window : ∀ target ∈ solved, InWindow side 120 target.1)
    (each : ∀ target ∈ solved, Kernel.SolvesOnVisit (findClass config mode live)
      (fun _ => completion config mode 3000) 3000 agent count target) :
    solved.card ≤ 21049 ∧
      57551 ≤ (windowTiles side 120 \ box 3 (tile live.world.body.position.position)).card ∧
      36502 ≤ ((windowTiles side 120 \ box 3 (tile live.world.body.position.position)) \
        solved.image (fun target => tile target.1)).card ∧
      21049 * 1000 < 366 * 57551 := by
  have few : solved.card ≤ 21049 :=
    find_visits_need config mode live 3000 free count solved each
  have admitted := Finset.le_card_sdiff (box 3 (tile live.world.body.position.position))
    (windowTiles side 120)
  rw [card_windowTiles, card_box] at admitted
  have inside : solved.image (fun target => tile target.1) ⊆
      windowTiles side 120 \ box 3 (tile live.world.body.position.position) := by
    intro point chosen
    obtain ⟨target, picked, rfl⟩ := Finset.mem_image.mp chosen
    exact Finset.mem_sdiff.mpr ⟨(mem_windowTiles side 120 target.1).mpr (window target picked),
      (member_tile live target.1).mp target.2⟩
  have split := Finset.card_sdiff_add_card_eq_card inside
  have image : (solved.image (fun target => tile target.1)).card = solved.card :=
    Finset.card_image_of_injective solved
      (fun first second same => Subtype.ext (tile_injective same))
  refine ⟨few, by omega, by omega, by decide⟩

/-! ## A world in which the separation holds -/

/-- The configuration of the separation witness: the standard configuration at seed 1 and the
smallest side, 64, with no food and no deer (`witness_standard`). Seed 1 is the least seed at
which the host's own world was observed to start at the box's center, where this world starts
(`docs/roadmap.md` records the observation; no theorem says it). -/
def witnessConfig : Host.WorldConfig :=
  ⟨⟨1, ⟨64, by decide⟩, 2048, 400, 48, 0, 0, ⟨0x41000000⟩⟩, by decide, by decide⟩

/-- The witness's configuration is the one the host's standard constructor builds at seed 1 and
side 64, with its two capacities set to zero: it keeps that configuration's day, regrowth, food
interval and noise scale, and so its terrain. -/
theorem witness_standard :
    ∃ standard, Host.WorldConfig.standard 1 ⟨64, by decide⟩ = .ok standard ∧
      witnessConfig.raw = { standard.raw with foodCap := 0, deerCap := 0 } :=
  ⟨_, rfl, rfl⟩

/-- The host world of the witness: the configuration's empty world, with the body at the box's
center and its energy full, and an empty carried result. It is not the world the host generates
for a run, which holds deer and starts where its spawn search ends. -/
def witnessLive : Live witnessConfig := ⟨Host.World.empty witnessConfig, {}⟩

/-- The exploration of the witness: east at every step of visit 0, west on visit 1 and south
on every later visit. -/
def witnessExplore (visit : ℕ) (_ : ℕ) : Kernel.Act Grid.interface :=
  code (match visit with | 0 => .east | 1 => .west | _ => .south)

/-- The tile each visit of the witness ends on: seven tiles east, west and south of the
center `(32, 32)`. -/
def witnessEnd : ℕ → ℤ × ℤ
  | 0 => (39, 32)
  | 1 => (25, 32)
  | _ => (32, 39)

/-- The body of the witness starts on the center `(32, 32)`. -/
theorem witness_start : tile witnessLive.world.body.position.position = (32, 32) := by
  decide

/-- The elevation-field seed of `witnessConfig`. -/
private def witnessElevSeed : UInt64 := 1 ^^^ 0xe1e0e1e000000001

/-- A coordinate in the witness's `[25, 39]` walk window. -/
private def windowCoord (n : Fin 15) : Host.Coordinate := ⟨25 + n.val, by omega⟩

/-- The four octave scales of `witnessConfig`, starting from `baseScale = 8.0`. -/
private def octaveBaseScale : Fin 4 → Binary32
  | ⟨0, _⟩ => ⟨0x41000000⟩
  | ⟨1, _⟩ => ⟨0x41800000⟩
  | ⟨2, _⟩ => ⟨0x42000000⟩
  | ⟨3, _⟩ => ⟨0x42800000⟩

/-- Memoized 1D octave lattice indices and smoothstep weights for coordinates `25..39`. -/
private def axisTable : Fin 4 → Fin 15 → Nat × UInt32
  | ⟨0, _⟩, c => (#[
      (3, 1026555904), (3, 1042284544), (3, 1050804224), (3, 1056964608), (3, 1060044800),
      (3, 1062731776), (3, 1064632320), (4, 0), (4, 1026555904), (4, 1042284544),
      (4, 1050804224), (4, 1056964608), (4, 1060044800), (4, 1062731776), (4, 1064632320)
    ] : Array (Nat × UInt32))[c.val]'(c.isLt)
  | ⟨1, _⟩, c => (#[
      (1, 1058529280), (1, 1060044800), (1, 1061462016), (1, 1062731776), (1, 1063804928),
      (1, 1064632320), (1, 1065164800), (2, 0), (2, 1010302976), (2, 1026555904),
      (2, 1035796480), (2, 1042284544), (2, 1047363584), (2, 1050804224), (2, 1053835264)
    ] : Array (Nat × UInt32))[c.val]'(c.isLt)
  | ⟨2, _⟩, c => (#[
      (0, 1063296000), (0, 1063804928), (0, 1064252416), (0, 1064632320), (0, 1064938496),
      (0, 1065164800), (0, 1065305088), (1, 0), (1, 993787904), (1, 1010302976),
      (1, 1019904000), (1, 1026555904), (1, 1032216576), (1, 1035796480), (1, 1039867904)
    ] : Array (Nat × UInt32))[c.val]'(c.isLt)
  | ⟨3, _⟩, c => (#[
      (0, 1051547392), (0, 1052301312), (0, 1053064448), (0, 1053835264), (0, 1054612224),
      (0, 1055393792), (0, 1056178432), (0, 1056964608), (0, 1057357696), (0, 1057750016),
      (0, 1058140800), (0, 1058529280), (0, 1058914688), (0, 1059296256), (0, 1059673216)
    ] : Array (Nat × UInt32))[c.val]'(c.isLt)

/-- Memoized elevation lattice noise values on `[0, 5]²` at `witnessElevSeed`. -/
private def latticeTable : Fin 6 → Fin 6 → UInt32
  | ⟨0, _⟩, yi => (#[1022074183, 1057848264, 1061288971, 1059690444, 1058456244, 1045630691] :
      Array UInt32)[yi.val]'(yi.isLt)
  | ⟨1, _⟩, yi => (#[1057262375, 1053661255, 1044119020, 1064255264, 1063264140, 1059251203] :
      Array UInt32)[yi.val]'(yi.isLt)
  | ⟨2, _⟩, yi => (#[1050224774, 1048907377, 1063679903, 1055284872, 1045398178, 1063393422] :
      Array UInt32)[yi.val]'(yi.isLt)
  | ⟨3, _⟩, yi => (#[1062967426, 1058086814, 1063637944, 1058390499, 1064191531, 1064095516] :
      Array UInt32)[yi.val]'(yi.isLt)
  | ⟨4, _⟩, yi => (#[1062790061, 1059264925, 1060310859, 1061616455, 1052267734, 1059236817] :
      Array UInt32)[yi.val]'(yi.isLt)
  | ⟨5, _⟩, yi => (#[1063663349, 1056095266, 1055274743, 1020443018, 1034418930, 1030576842] :
      Array UInt32)[yi.val]'(yi.isLt)

/-- Every entry of `axisTable` equals the executed 1D noise coordinate, smoothstep weight and
valid lattice index at `windowCoord c` and `octaveBaseScale oct`. -/
private theorem axisTable_spec : ∀ (oct : Fin 4) (c : Fin 15),
    let fx := (Host.coordinateFloat (windowCoord c)).div (octaveBaseScale oct)
    let x0 := Host.floor32 fx
    (Host.coordinateCast x0).val = ((axisTable oct c).1 : Int) ∧
      (axisTable oct c).1 < 5 ∧
      Host.smooth (fx.sub x0) = ⟨(axisTable oct c).2⟩ := by
  decide +kernel

/-- Every entry of `latticeTable` equals the executed elevation lattice hash at `(xi, yi)`. -/
private theorem latticeTable_spec : ∀ (xi yi : Fin 6),
    Host.lattice ⟨xi.val, by omega⟩ ⟨yi.val, by omega⟩ witnessElevSeed =
      ⟨latticeTable xi yi⟩ := by
  decide +kernel

/-- Bilinear interpolation of one elevation octave from the memoized axis and lattice tables. -/
private def fastOctave (oct : Fin 4) (x y : Fin 15) : Binary32 :=
  let ax := axisTable oct x
  let ay := axisTable oct y
  let xi := ax.1 % 5
  let yi := ay.1 % 5
  let tx : Binary32 := ⟨ax.2⟩
  let ty : Binary32 := ⟨ay.2⟩
  let h00 : Binary32 := ⟨latticeTable ⟨xi, by omega⟩ ⟨yi, by omega⟩⟩
  let h10 : Binary32 := ⟨latticeTable ⟨xi + 1, by omega⟩ ⟨yi, by omega⟩⟩
  let h01 : Binary32 := ⟨latticeTable ⟨xi, by omega⟩ ⟨yi + 1, by omega⟩⟩
  let h11 : Binary32 := ⟨latticeTable ⟨xi + 1, by omega⟩ ⟨yi + 1, by omega⟩⟩
  let top := h00.add ((h10.sub h00).mul tx)
  let bot := h01.add ((h11.sub h01).mul tx)
  top.add ((bot.sub top).mul ty)

/-- Four-octave elevation field inside `[25, 39]²`, reading only memoized 1D axes and lattice
corners. -/
def fastFbm (x y : Fin 15) : Binary32 :=
  let s0 : Binary32 := (⟨0⟩ : Binary32).add ((⟨0x3f000000⟩ : Binary32).mul (fastOctave 0 x y))
  let s1 : Binary32 := s0.add ((⟨0x3e800000⟩ : Binary32).mul (fastOctave 1 x y))
  let s2 : Binary32 := s1.add ((⟨0x3e000000⟩ : Binary32).mul (fastOctave 2 x y))
  s2.add ((⟨0x3d800000⟩ : Binary32).mul (fastOctave 3 x y))

/-- Helper: `Host.valueNoise` rewrites purely algebraically once axis and lattice terms match. -/
private theorem valueNoise_of_eq (pos : Host.Position) (scale : Binary32) (seed : UInt64)
    (xi yi x1 y1 : Host.Coordinate) (tx ty h00 h10 h01 h11 : Binary32)
    (hcx : Host.coordinateCast (Host.floor32 ((Host.coordinateFloat pos.x).div scale)) = xi)
    (hcy : Host.coordinateCast (Host.floor32 ((Host.coordinateFloat pos.y).div scale)) = yi)
    (htx : Host.smooth (((Host.coordinateFloat pos.x).div scale).sub
      (Host.floor32 ((Host.coordinateFloat pos.x).div scale))) = tx)
    (hty : Host.smooth (((Host.coordinateFloat pos.y).div scale).sub
      (Host.floor32 ((Host.coordinateFloat pos.y).div scale))) = ty)
    (hchkx : Host.Coordinate.checked (xi.val + 1) = some x1)
    (hchky : Host.Coordinate.checked (yi.val + 1) = some y1)
    (hl00 : Host.lattice xi yi seed = h00)
    (hl10 : Host.lattice x1 yi seed = h10)
    (hl01 : Host.lattice xi y1 seed = h01)
    (hl11 : Host.lattice x1 y1 seed = h11) :
    Host.valueNoise pos scale seed =
      .ok ((h00.add ((h10.sub h00).mul tx)).add
        (((h01.add ((h11.sub h01).mul tx)).sub (h00.add ((h10.sub h00).mul tx))).mul ty)) := by
  unfold Host.valueNoise
  dsimp only
  rw [hcx, hcy, htx, hty]
  rw [hchkx, hchky]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hl00, hl10, hl01, hl11]

/-- One octave of `Host.valueNoise` at `witnessElevSeed` equals `fastOctave`. -/
private theorem valueNoise_eq_fastOctave (oct : Fin 4) (x y : Fin 15) :
    Host.valueNoise ⟨windowCoord x, windowCoord y⟩ (octaveBaseScale oct) witnessElevSeed =
      .ok (fastOctave oct x y) := by
  obtain ⟨hxi, hxiLt, htx⟩ := axisTable_spec oct x
  obtain ⟨hyi, hyiLt, hty⟩ := axisTable_spec oct y
  have hxiMod : (axisTable oct x).1 % 5 = (axisTable oct x).1 := Nat.mod_eq_of_lt hxiLt
  have hyiMod : (axisTable oct y).1 % 5 = (axisTable oct y).1 := Nat.mod_eq_of_lt hyiLt
  let xiC : Host.Coordinate := ⟨((axisTable oct x).1 : Int), by omega⟩
  let yiC : Host.Coordinate := ⟨((axisTable oct y).1 : Int), by omega⟩
  let x1C : Host.Coordinate := ⟨(((axisTable oct x).1 + 1 : Nat) : Int), by omega⟩
  let y1C : Host.Coordinate := ⟨(((axisTable oct y).1 + 1 : Nat) : Int), by omega⟩
  have hchkx : Host.Coordinate.checked (xiC.val + 1) = some x1C := by
    unfold Host.Coordinate.checked
    rw [dite_eq_left (by dsimp [xiC]; omega)]
    exact congrArg some (Subtype.ext (by dsimp [xiC, x1C]))
  have hchky : Host.Coordinate.checked (yiC.val + 1) = some y1C := by
    unfold Host.Coordinate.checked
    rw [dite_eq_left (by dsimp [yiC]; omega)]
    exact congrArg some (Subtype.ext (by dsimp [yiC, y1C]))
  have heq := valueNoise_of_eq ⟨windowCoord x, windowCoord y⟩ (octaveBaseScale oct) witnessElevSeed
    xiC yiC x1C y1C ⟨(axisTable oct x).2⟩ ⟨(axisTable oct y).2⟩
    ⟨latticeTable ⟨(axisTable oct x).1, by omega⟩ ⟨(axisTable oct y).1, by omega⟩⟩
    ⟨latticeTable ⟨(axisTable oct x).1 + 1, by omega⟩ ⟨(axisTable oct y).1, by omega⟩⟩
    ⟨latticeTable ⟨(axisTable oct x).1, by omega⟩ ⟨(axisTable oct y).1 + 1, by omega⟩⟩
    ⟨latticeTable ⟨(axisTable oct x).1 + 1, by omega⟩ ⟨(axisTable oct y).1 + 1, by omega⟩⟩
    (Subtype.ext hxi) (Subtype.ext hyi) htx hty hchkx hchky
    (latticeTable_spec ⟨(axisTable oct x).1, by omega⟩ ⟨(axisTable oct y).1, by omega⟩)
    (latticeTable_spec ⟨(axisTable oct x).1 + 1, by omega⟩ ⟨(axisTable oct y).1, by omega⟩)
    (latticeTable_spec ⟨(axisTable oct x).1, by omega⟩ ⟨(axisTable oct y).1 + 1, by omega⟩)
    (latticeTable_spec ⟨(axisTable oct x).1 + 1, by omega⟩ ⟨(axisTable oct y).1 + 1, by omega⟩)
  rw [heq]
  unfold fastOctave
  simp only [hxiMod, hyiMod]

/-- **Executed elevation equals `fastFbm` on `[25, 39]²`.** -/
theorem fbm_eq_fastFbm (x y : Fin 15) :
    Host.fbm ⟨windowCoord x, windowCoord y⟩ witnessElevSeed ⟨0x41000000⟩ = .ok (fastFbm x y) := by
  have hs0 : (⟨0x41000000⟩ : Binary32).mul ⟨0x40000000⟩ = ⟨0x41800000⟩ := by decide
  have hs1 : (⟨0x41800000⟩ : Binary32).mul ⟨0x40000000⟩ = ⟨0x42000000⟩ := by decide
  have hs2 : (⟨0x42000000⟩ : Binary32).mul ⟨0x40000000⟩ = ⟨0x42800000⟩ := by decide
  have ha0 : (⟨0x3f000000⟩ : Binary32).mul ⟨0x3f000000⟩ = ⟨0x3e800000⟩ := by decide
  have ha1 : (⟨0x3e800000⟩ : Binary32).mul ⟨0x3f000000⟩ = ⟨0x3e000000⟩ := by decide
  have ha2 : (⟨0x3e000000⟩ : Binary32).mul ⟨0x3f000000⟩ = ⟨0x3d800000⟩ := by decide
  unfold Host.fbm fastFbm
  rw [Host.octaveLoop]
  dsimp only [bind, Except.bind]
  rw [show (⟨0x41000000⟩ : Binary32) = octaveBaseScale 0 from rfl, valueNoise_eq_fastOctave 0 x y]
  dsimp only
  rw [show octaveBaseScale 0 = ⟨0x41000000⟩ from rfl, hs0, ha0, Host.octaveLoop]
  dsimp only [bind, Except.bind]
  rw [show (⟨0x41800000⟩ : Binary32) = octaveBaseScale 1 from rfl, valueNoise_eq_fastOctave 1 x y]
  dsimp only
  rw [show octaveBaseScale 1 = ⟨0x41800000⟩ from rfl, hs1, ha1, Host.octaveLoop]
  dsimp only [bind, Except.bind]
  rw [show (⟨0x42000000⟩ : Binary32) = octaveBaseScale 2 from rfl, valueNoise_eq_fastOctave 2 x y]
  dsimp only
  rw [show octaveBaseScale 2 = ⟨0x42000000⟩ from rfl, hs2, ha2, Host.octaveLoop]
  dsimp only [bind, Except.bind]
  rw [show (⟨0x42800000⟩ : Binary32) = octaveBaseScale 3 from rfl, valueNoise_eq_fastOctave 3 x y]
  rfl

/-- Whether the elevation at `(25 + x, 25 + y)` lies in the walkable band `[0.30, 0.80)`. -/
def fastWalkable (x y : Fin 15) : Bool :=
  !decide ((fastFbm x y).Less ⟨Acorn.Constants.band030Bits⟩) &&
    decide ((fastFbm x y).Less ⟨Acorn.Constants.band080Bits⟩)

/-- Every coordinate in `[24, 40]` has valid octave quotients at `witnessConfig`'s noise scale,
covering all tiles entered or faced from `[25, 39]²`. -/
private theorem admits_24_40 : ∀ (c : Fin 17) (oct : Fin 4),
    ¬CurrentTerrain.PastLast
      ((Host.coordinateFloat ⟨24 + c.val, by omega⟩).div
        (CurrentTerrain.octaveScale ⟨0x41000000⟩ oct.val)) := by
  decide +kernel

/-- Every tile in `[24, 40]²` is admitted by the value noise of `witnessConfig`. -/
private theorem latticeAdmits_24_40 (pos : Host.Position)
    (hx : 24 ≤ pos.x.val ∧ pos.x.val ≤ 40) (hy : 24 ≤ pos.y.val ∧ pos.y.val ≤ 40) :
    CurrentTerrain.LatticeAdmits pos ⟨0x41000000⟩ := by
  intro oct hlt
  have hpx : pos.x = ⟨24 + ((pos.x.val - 24).toNat : Int), by omega⟩ :=
    Subtype.ext (show pos.x.val = 24 + ((pos.x.val - 24).toNat : Int) by omega)
  have hpy : pos.y = ⟨24 + ((pos.y.val - 24).toNat : Int), by omega⟩ :=
    Subtype.ext (show pos.y.val = 24 + ((pos.y.val - 24).toNat : Int) by omega)
  rw [hpx, hpy]
  exact ⟨admits_24_40 ⟨(pos.x.val - 24).toNat, by omega⟩ ⟨oct, hlt⟩,
    admits_24_40 ⟨(pos.y.val - 24).toNat, by omega⟩ ⟨oct, hlt⟩⟩

/-- Any tile in `[25, 39]²` accepted by `fastWalkable` is enterable in any world of
`witnessConfig`, independently of the moisture field and harvest state. -/
theorem witness_enterable_fast (world : Host.World witnessConfig) (x y : Fin 15)
    (ok : fastWalkable x y = true) :
    world.enterable ⟨windowCoord x, windowCoord y⟩ = .ok true := by
  unfold fastWalkable at ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at ok
  obtain ⟨hlow, hhigh⟩ := ok
  have helev := fbm_eq_fastFbm x y
  have hadmits : CurrentTerrain.LatticeAdmits ⟨windowCoord x, windowCoord y⟩ ⟨0x41000000⟩ := by
    rw [← CurrentTerrain.fbm_isOk _ witnessElevSeed, helev]
    rfl
  have hmoistOk : (Host.fbm ⟨windowCoord x, windowCoord y⟩ (1 ^^^ 0xe1e0e1e000000002)
      ⟨0x41000000⟩).isOk = true := (CurrentTerrain.fbm_isOk _ _ _).mpr hadmits
  cases hmoist : Host.fbm ⟨windowCoord x, windowCoord y⟩ (1 ^^^ 0xe1e0e1e000000002)
      ⟨0x41000000⟩ with
  | error err => rw [hmoist] at hmoistOk; simp [Except.isOk, Except.toBool] at hmoistOk
  | ok moist =>
    have hter : Host.terrain ⟨windowCoord x, windowCoord y⟩ witnessConfig.raw.seed
        witnessConfig.raw.baseScale =
        .ok (Host.classifyTerrain ⟨windowCoord x, windowCoord y⟩ 1 (fastFbm x y) moist) := by
      unfold Host.terrain
      change (do
        let elevation ← Host.fbm ⟨windowCoord x, windowCoord y⟩ witnessElevSeed ⟨0x41000000⟩
        let moisture ← Host.fbm ⟨windowCoord x, windowCoord y⟩ (1 ^^^ 0xe1e0e1e000000002)
          ⟨0x41000000⟩
        return Host.classifyTerrain ⟨windowCoord x, windowCoord y⟩ 1 elevation moisture) = _
      rw [helev, hmoist]
      rfl
    have hbaseWalk : (Host.classifyTerrain ⟨windowCoord x, windowCoord y⟩ 1 (fastFbm x y)
        moist).Walkable := by
      simp only [Host.classifyTerrain, hlow, hhigh, ↓reduceIte]
      repeat' split
      all_goals decide
    have htkWalk : ∃ kind, world.tileKind ⟨windowCoord x, windowCoord y⟩ = .ok kind ∧
        kind.Walkable := by
      unfold Host.World.tileKind
      simp only [hter, bind, Except.bind, pure, Except.pure]
      split
      · split
        · split
          · split
            · exact ⟨.forest, rfl, by decide⟩
            · exact ⟨_, rfl, hbaseWalk⟩
          · exact ⟨_, rfl, hbaseWalk⟩
        · exact ⟨_, rfl, hbaseWalk⟩
      · exact ⟨_, rfl, hbaseWalk⟩
    obtain ⟨kind, htk, hkw⟩ := htkWalk
    unfold Host.World.enterable
    rw [htk]
    dsimp only [bind, Except.bind, pure, Except.pure]
    cases kind with
    | water => exact absurd rfl hkw.1
    | mountain => exact absurd rfl hkw.2
    | sand | grass | forest | tree | stone | ore => rfl

/-- Passive dynamics in `witnessConfig` (zero deer and food capacity) always succeed and leave
the body untouched. -/
private theorem witness_passive_ok (world : Host.World witnessConfig) :
    ∃ passive, Host.passiveChange world = .ok passive := by
  have hdeer : world.deer.entries.size = 0 := by
    have := world.deer.bounded
    change world.deer.entries.size ≤ 0 at this
    omega
  have hempty : world.deer.entries = #[] := Array.eq_empty_of_size_eq_zero hdeer
  have hmap : (Vector.mapM (m := StateT Rng.Xoshiro256 (Except Host.WorldError))
      (fun position rng => Host.wanderDeer world position rng)
      ⟨world.deer.entries, rfl⟩).run world.rng =
      .ok (⟨world.deer.entries, rfl⟩, world.rng) := by
    cases world with
    | mk time body goal goalStart harvested deer food rng =>
      cases deer with
      | mk entries bounded =>
        dsimp only at hempty
        subst hempty
        rw [Vector.mapM_mk_empty]
        rfl
  unfold Host.passiveChange Host.wanderPopulation Host.spawnFood
  simp only [hmap, bind, Except.bind, pure, Except.pure]
  have hfood : world.food.entries.size < witnessConfig.raw.foodCap.toNat → False := by
    change world.food.entries.size < 0 → False
    omega
  have hcond : (decide (Host.FoodDue world.time witnessConfig.raw.foodInterval) &&
      decide (world.food.entries.size < witnessConfig.raw.foodCap.toNat)) = false := by
    simp [decide_eq_false hfood]
  rw [hcond]
  exact ⟨_, rfl⟩

/-- Every host action costs at most 4 energy. -/
private theorem action_energyCost_le (action : Host.Action) (night : Bool) :
    action.energyCost night ≤ 4 := by
  cases action <;> cases night <;> decide

/-- One physical step in `witnessConfig` from a world with energy at least 4 and body in
`[25, 39]²`: directional moves into a `fastWalkable` tile in `[25, 39]²` advance to that tile,
and non-directional actions keep the tile. Energy drops by at most 4. -/
theorem witness_physicalStep_fast (world : Host.World witnessConfig) (action : Host.Action)
    (energyOk : 4 ≤ world.body.energy.val)
    (inWin : 25 ≤ (tile world.body.position.position).1 ∧
      (tile world.body.position.position).1 ≤ 39 ∧
      25 ≤ (tile world.body.position.position).2 ∧
      (tile world.body.position.position).2 ≤ 39)
    (stepOk : match action.direction with
      | some dir =>
        let nx := (tile world.body.position.position).1 + dir.delta.1
        let ny := (tile world.body.position.position).2 + dir.delta.2
        ∃ (hx : 25 ≤ nx ∧ nx ≤ 39) (hy : 25 ≤ ny ∧ ny ≤ 39),
          fastWalkable ⟨(nx - 25).toNat, by omega⟩ ⟨(ny - 25).toNat, by omega⟩ = true
      | none => True) :
    ∃ next, physicalStep world (code action) = some next ∧
      tile next.body.position.position = (match action.direction with
        | some dir => ((tile world.body.position.position).1 + dir.delta.1,
            (tile world.body.position.position).2 + dir.delta.2)
        | none => tile world.body.position.position) ∧
      world.body.energy.val - 4 ≤ next.body.energy.val := by
  have hcost := action_energyCost_le action (decide (world.dayPhase.val ≥ 4))
  let spent : Host.Energy :=
    ⟨world.body.energy.val - action.energyCost (decide (world.dayPhase.val ≥ 4)),
      by have := world.body.energy.isLt; omega⟩
  have hspend : world.body.energy.spend (action.energyCost (decide (world.dayPhase.val ≥ 4))) =
      some spent := by
    unfold Host.Energy.spend
    rw [ite_eq_left (by omega)]
  have hspentVal : world.body.energy.val - 4 ≤ spent.val := by
    change world.body.energy.val - 4 ≤ world.body.energy.val - _
    omega
  let world' : Host.World witnessConfig :=
    { world with body := { world.body with energy := spent } }
  have hfinish : ∀ (active : Host.ActionChange witnessConfig),
      Host.performAction world' action = .ok active →
      tile active.body.position.position = (match action.direction with
        | some dir => ((tile world.body.position.position).1 + dir.delta.1,
            (tile world.body.position.position).2 + dir.delta.2)
        | none => tile world.body.position.position) →
      world.body.energy.val - 4 ≤ active.body.energy.val →
      ∃ next, physicalStep world (code action) = some next ∧
        tile next.body.position.position = (match action.direction with
          | some dir => ((tile world.body.position.position).1 + dir.delta.1,
              (tile world.body.position.position).2 + dir.delta.2)
          | none => tile world.body.position.position) ∧
        world.body.energy.val - 4 ≤ next.body.energy.val := by
    intro active hact hpos hene
    have hpay : Host.payAndAct world action = .ok active := by
      unfold Host.payAndAct
      rw [hspend]
      exact hact
    obtain ⟨passive, hpass⟩ := witness_passive_ok
      { world.applyActive active with time := (world.applyActive active).time + 1 }
    refine ⟨physical ((world.applyActive active).applyPassive passive), ?_, hpos, hene⟩
    unfold physicalStep
    rw [show Host.Action.fromIndex (code action).val = action from
      Host.Action.index_roundtrip action]
    unfold Host.World.step
    simp only [hpay, hpass, bind, Except.bind, pure, Except.pure]
  cases hdir : action.direction with
  | some dir =>
    simp only [hdir] at stepOk
    obtain ⟨hx, hy, hwalk⟩ := stepOk
    let fx : Fin 15 := ⟨((tile world.body.position.position).1 + dir.delta.1 - 25).toNat, by omega⟩
    let fy : Fin 15 := ⟨((tile world.body.position.position).2 + dir.delta.2 - 25).toNat, by omega⟩
    have htrans : world'.body.position.position.translate dir.delta.1 dir.delta.2 =
        some ⟨windowCoord fx, windowCoord fy⟩ := by
      have hwx : (tile world.body.position.position).1 + dir.delta.1 = (windowCoord fx).val := by
        dsimp [windowCoord, fx]; omega
      have hwy : (tile world.body.position.position).2 + dir.delta.2 = (windowCoord fy).val := by
        dsimp [windowCoord, fy]; omega
      unfold Host.Position.translate Host.Coordinate.checked
      have hxRange : -(2 ^ 63 : Int) ≤ world'.body.position.position.x.val + dir.delta.1 ∧
          world'.body.position.position.x.val + dir.delta.1 < 2 ^ 63 := by
        change -(2 ^ 63 : Int) ≤ (tile world.body.position.position).1 + dir.delta.1 ∧
          (tile world.body.position.position).1 + dir.delta.1 < 2 ^ 63
        omega
      have hyRange : -(2 ^ 63 : Int) ≤ world'.body.position.position.y.val + dir.delta.2 ∧
          world'.body.position.position.y.val + dir.delta.2 < 2 ^ 63 := by
        change -(2 ^ 63 : Int) ≤ (tile world.body.position.position).2 + dir.delta.2 ∧
          (tile world.body.position.position).2 + dir.delta.2 < 2 ^ 63
        omega
      rw [dite_eq_left hxRange, dite_eq_left hyRange]
      simp only [bind, Option.bind, pure, Option.some.injEq]
      congr 1
      · exact Subtype.ext hwx
      · exact Subtype.ext hwy
    let boxPos : Host.BoxPosition witnessConfig :=
      ⟨⟨25 + fx.val, by change 25 + fx.val < 64; omega⟩,
       ⟨25 + fy.val, by change 25 + fy.val < 64; omega⟩⟩
    have hbox : Host.BoxPosition.checked witnessConfig (windowCoord fx).val (windowCoord fy).val =
        some boxPos := by
      unfold Host.BoxPosition.checked
      rw [dite_eq_left (by change 0 ≤ _ ∧ _ < (64 : Int); dsimp [windowCoord]; omega),
        dite_eq_left (by change 0 ≤ _ ∧ _ < (64 : Int); dsimp [windowCoord]; omega)]
      rfl
    have hent := witness_enterable_fast world' fx fy hwalk
    let moved : Host.World witnessConfig :=
      { world' with body := { world'.body with position := boxPos, facing := dir } }
    have hact : Host.performAction world' action = .ok
        ⟨moved.pickupFood.1.body, moved.pickupFood.1.harvested, moved.pickupFood.1.food,
          { moved := true, pickedFood := moved.pickupFood.2 }⟩ := by
      unfold Host.performAction
      rw [hdir]
      dsimp only
      rw [htrans]
      dsimp only [bind, Except.bind]
      rw [hbox]
      dsimp only
      rw [hent]
      rfl
    rw [← hdir]
    refine hfinish _ hact ?_ ?_
    · rw [hdir]
      dsimp only [tile, Host.BoxPosition.position] at hx hy
      dsimp only [Host.World.pickupFood, moved, boxPos, tile, Host.BoxPosition.position, fx, fy]
      apply Prod.ext <;> omega
    · exact hspentVal
  | none =>
    cases action with
    | north | south | east | west => simp [Host.Action.direction] at hdir
    | wait =>
      exact hfinish (Host.ActionChange.unchanged world')
        (by unfold Host.performAction; rfl) (by simp [hdir, Host.ActionChange.unchanged, world'])
        hspentVal
    | craftAxe =>
      cases hcraft : world'.body.inventory.craft .axe with
      | error _ =>
        exact hfinish (Host.ActionChange.unchanged world')
          (by unfold Host.performAction; simp [Host.Action.direction, hcraft, pure, Except.pure])
          (by simp [hdir, Host.ActionChange.unchanged, world']) hspentVal
      | ok inv =>
        exact hfinish
          { Host.ActionChange.unchanged world' with
            body := { world'.body with inventory := inv }
            events := { crafted := some .axe } }
          (by unfold Host.performAction; simp [Host.Action.direction, hcraft, pure, Except.pure])
          (by simp [hdir, world']) hspentVal
    | craftBoat =>
      cases hcraft : world'.body.inventory.craft .boat with
      | error _ =>
        exact hfinish (Host.ActionChange.unchanged world')
          (by unfold Host.performAction; simp [Host.Action.direction, hcraft, pure, Except.pure])
          (by simp [hdir, Host.ActionChange.unchanged, world']) hspentVal
      | ok inv =>
        exact hfinish
          { Host.ActionChange.unchanged world' with
            body := { world'.body with inventory := inv }
            events := { crafted := some .boat } }
          (by unfold Host.performAction; simp [Host.Action.direction, hcraft, pure, Except.pure])
          (by simp [hdir, world']) hspentVal
    | eat =>
      by_cases hfood : world'.body.inventory.food.toNat ≥ 1
      · have hgain : spent.val ≤ (spent.gain .eat).val := by
          unfold Host.Energy.gain Host.Energy.new
          have := spent.isLt
          dsimp [FeatureConstants.energyMax] at this ⊢
          omega
        exact hfinish
          { Host.ActionChange.unchanged world' with
            body := { world'.body with
              inventory := { world'.body.inventory with food := world'.body.inventory.food - 1 },
              energy := world'.body.energy.gain .eat }
            events := { ate := true } }
          (by unfold Host.performAction; simp [Host.Action.direction, hfood, pure, Except.pure])
          (by simp [hdir, world']) (Nat.le_trans hspentVal hgain)
      · exact hfinish (Host.ActionChange.unchanged world')
          (by unfold Host.performAction; simp [Host.Action.direction, hfood, pure, Except.pure])
          (by simp [hdir, Host.ActionChange.unchanged, world']) hspentVal
    | harvest =>
      let faced := world'.body.position.facingPosition world'.body.facing
      have hwx : 25 ≤ (world.body.position.x.val : Int) ∧ (world.body.position.x.val : Int) ≤ 39 :=
        ⟨inWin.1, inWin.2.1⟩
      have hwy : 25 ≤ (world.body.position.y.val : Int) ∧ (world.body.position.y.val : Int) ≤ 39 :=
        ⟨inWin.2.2.1, inWin.2.2.2⟩
      have hfaced : 24 ≤ faced.x.val ∧ faced.x.val ≤ 40 ∧
          24 ≤ faced.y.val ∧ faced.y.val ≤ 40 := by
        cases hfac : world.body.facing <;>
          simp [faced, world', Host.BoxPosition.facingPosition, Host.Direction.delta, hfac] <;>
          omega
      have htkOk : (world'.tileKind faced).isOk = true :=
        (CurrentTerrain.tileKind_isOk world' faced).mpr
          (latticeAdmits_24_40 faced ⟨hfaced.1, hfaced.2.1⟩ ⟨hfaced.2.2.1, hfaced.2.2.2⟩)
      cases htk : world'.tileKind faced with
      | error _ => rw [htk] at htkOk; simp [Except.isOk, Except.toBool] at htkOk
      | ok kind =>
        cases hyield : kind.harvestYield with
        | none =>
          exact hfinish (Host.ActionChange.unchanged world')
            (by unfold Host.performAction; simp [Host.Action.direction, faced, htk, hyield,
              bind, Except.bind, pure, Except.pure])
            (by simp [hdir, Host.ActionChange.unchanged, world']) hspentVal
        | some item =>
          let amount : UInt32 := if item == .wood && world'.body.inventory.axe then 3 else 1
          let body' := { world'.body with inventory := world'.body.inventory.add item amount }
          let harv' := if kind == .tree then
              world'.harvested.insert
                (world'.body.position.facingKey world'.body.facing) world'.time
            else world'.harvested
          exact hfinish ⟨body', harv', world'.food, { harvested := some item }⟩
            (by unfold Host.performAction; simp [Host.Action.direction, faced, htk, hyield,
              amount, body', harv', bind, Except.bind, pure, Except.pure])
            (by simp [hdir, body', world']) hspentVal

/-- Pure fast-terrain walk check inside `[25, 39]²`: every entered tile lies in the window and
passes `fastWalkable`. -/
def witnessWalkFast (point : ℤ × ℤ) : List Host.Action → Bool
  | [] => true
  | action :: rest =>
    match action.direction with
    | some dir =>
      let nx := point.1 + dir.delta.1
      let ny := point.2 + dir.delta.2
      if hx : 25 ≤ nx ∧ nx ≤ 39 then
        if hy : 25 ≤ ny ∧ ny ≤ 39 then
          fastWalkable ⟨(nx - 25).toNat, by omega⟩ ⟨(ny - 25).toNat, by omega⟩ &&
            witnessWalkFast (nx, ny) rest
        else false
      else false
    | none => witnessWalkFast point rest

/-- Expected final tile after executing a list of actions assuming every entered tile is
walkable. -/
def witnessWalkEnd (point : ℤ × ℤ) : List Host.Action → ℤ × ℤ
  | [] => point
  | action :: rest =>
    let next := match action.direction with
      | some dir => (point.1 + dir.delta.1, point.2 + dir.delta.2)
      | none => point
    witnessWalkEnd next rest

/-- Executing a constant directional action `count` times in `witnessConfig` reaches the
expected tile whenever `witnessWalkFast` accepts `List.replicate count action`. -/
theorem witness_physicalPath_const (world : Host.World witnessConfig) (action : Host.Action)
    (count : ℕ) (energyOk : 4 * count ≤ world.body.energy.val)
    (inWin : 25 ≤ (tile world.body.position.position).1 ∧
      (tile world.body.position.position).1 ≤ 39 ∧
      25 ≤ (tile world.body.position.position).2 ∧
      (tile world.body.position.position).2 ≤ 39)
    (ok : witnessWalkFast (tile world.body.position.position)
      (List.replicate count action) = true) :
    (physicalPath world (fun _ => code action) count).map
      (fun w => tile w.body.position.position) =
        some (witnessWalkEnd (tile world.body.position.position)
          (List.replicate count action)) := by
  induction count generalizing world with
  | zero => rfl
  | succ count ih =>
    have hstep : ∃ next, physicalStep world (code action) = some next ∧
        tile next.body.position.position = (match action.direction with
          | some dir => ((tile world.body.position.position).1 + dir.delta.1,
              (tile world.body.position.position).2 + dir.delta.2)
          | none => tile world.body.position.position) ∧
        world.body.energy.val - 4 ≤ next.body.energy.val ∧
        25 ≤ (tile next.body.position.position).1 ∧ (tile next.body.position.position).1 ≤ 39 ∧
        25 ≤ (tile next.body.position.position).2 ∧ (tile next.body.position.position).2 ≤ 39 ∧
        witnessWalkFast (tile next.body.position.position)
          (List.replicate count action) = true := by
      simp only [List.replicate_succ, witnessWalkFast] at ok
      cases hdir : action.direction with
      | none =>
        simp only [hdir] at ok
        obtain ⟨next, hnext, hpos, hene⟩ := witness_physicalStep_fast world action (by omega) inWin
          (by simp [hdir])
        have hpos' : tile next.body.position.position = tile world.body.position.position := by
          simpa [hdir] using hpos
        exact ⟨next, hnext, hpos', hene,
          by rw [hpos']; exact inWin.1, by rw [hpos']; exact inWin.2.1,
          by rw [hpos']; exact inWin.2.2.1, by rw [hpos']; exact inWin.2.2.2,
          by rw [hpos']; exact ok⟩
      | some dir =>
        simp only [hdir] at ok
        split at ok
        · rename_i hx
          split at ok
          · rename_i hy
            simp only [Bool.and_eq_true] at ok
            obtain ⟨next, hnext, hpos, hene⟩ := witness_physicalStep_fast world action (by omega)
              inWin (by simp only [hdir]; exact ⟨hx, hy, ok.1⟩)
            have hpos' : tile next.body.position.position =
                ((tile world.body.position.position).1 + dir.delta.1,
                 (tile world.body.position.position).2 + dir.delta.2) := by
              simpa [hdir] using hpos
            exact ⟨next, hnext, hpos', hene,
              by rw [hpos']; exact hx.1, by rw [hpos']; exact hx.2,
              by rw [hpos']; exact hy.1, by rw [hpos']; exact hy.2,
              by rw [hpos']; exact ok.2⟩
          · cases ok
        · cases ok
    obtain ⟨next, hnext, hpos, hene, hnx1, hnx2, hny1, hny2, hrest⟩ := hstep
    have hshift : ∀ n (w : Host.World witnessConfig),
        physicalPath w (fun _ => code action) (n + 1) =
          (physicalStep w (code action)).bind
            (fun w' => physicalPath w' (fun _ => code action) n) := by
      intro n
      induction n with
      | zero =>
        intro w
        change physicalStep w (code action) = (physicalStep w (code action)).bind some
        cases h : physicalStep w (code action) <;> rfl
      | succ n ihn =>
        intro w
        change (physicalPath w (fun _ => code action) (n + 1)).bind
          (physicalStep · (code action)) = _
        rw [ihn w]
        cases physicalStep w (code action) <;> rfl
    rw [hshift count world, hnext]
    dsimp only [Option.bind]
    rw [ih next (by omega) ⟨hnx1, hnx2, hny1, hny2⟩ hrest]
    simp only [List.replicate_succ, witnessWalkEnd, hpos]

/-- Seven steps east from `(32, 32)` stay in the walkable elevation band. -/
theorem witness_east_walkable :
    witnessWalkFast (32, 32) (List.replicate 7 .east) = true := by
  decide +kernel

/-- Seven steps west from `(32, 32)` stay in the walkable elevation band. -/
theorem witness_west_walkable :
    witnessWalkFast (32, 32) (List.replicate 7 .west) = true := by
  decide +kernel

/-- Seven steps south from `(32, 32)` stay in the walkable elevation band. -/
theorem witness_south_walkable :
    witnessWalkFast (32, 32) (List.replicate 7 .south) = true := by
  decide +kernel

/-- Seven steps of each of the first three visits' explorations carry the body, from the
witness world, to that visit's end tile. The proof reduces the executed world step structurally
to elevation-only terrain checks on the 21 entered tiles, discharging moisture via
`CurrentTerrain.fbm_isOk`. -/
theorem witness_walk (visit : ℕ) (within : visit ≤ 2) :
    (physicalPath (physical witnessLive.world) (witnessExplore visit) 7).map
      (fun world => tile world.body.position.position) = some (witnessEnd visit) := by
  have hstart : tile (physical witnessLive.world).body.position.position = (32, 32) := witness_start
  have hen : 4 * 7 ≤ (physical witnessLive.world).body.energy.val := by decide
  have hwin : 25 ≤ (tile (physical witnessLive.world).body.position.position).1 ∧
      (tile (physical witnessLive.world).body.position.position).1 ≤ 39 ∧
      25 ≤ (tile (physical witnessLive.world).body.position.position).2 ∧
      (tile (physical witnessLive.world).body.position.position).2 ≤ 39 := by
    rw [hstart]; omega
  rcases (by omega : visit = 0 ∨ visit = 1 ∨ visit = 2) with rfl | rfl | rfl
  · change (physicalPath (physical witnessLive.world) (fun _ => code .east) 7).map
      (fun world => tile world.body.position.position) = some (39, 32)
    simpa [hstart, witnessWalkEnd, Host.Action.direction, Host.Direction.delta] using
      witness_physicalPath_const (physical witnessLive.world) .east 7 hen hwin
        (hstart ▸ witness_east_walkable)
  · change (physicalPath (physical witnessLive.world) (fun _ => code .west) 7).map
      (fun world => tile world.body.position.position) = some (25, 32)
    simpa [hstart, witnessWalkEnd, Host.Action.direction, Host.Direction.delta] using
      witness_physicalPath_const (physical witnessLive.world) .west 7 hen hwin
        (hstart ▸ witness_west_walkable)
  · change (physicalPath (physical witnessLive.world) (fun _ => code .south) 7).map
      (fun world => tile world.body.position.position) = some (32, 39)
    simpa [hstart, witnessWalkEnd, Host.Action.direction, Host.Direction.delta] using
      witness_physicalPath_const (physical witnessLive.world) .south 7 hen hwin
        (hstart ▸ witness_south_walkable)

/-- Every concealed target within three tiles of a visit's end tile is met by that visit's
exploration at its seventh step. -/
theorem witness_meets (mode : TaskFeatureMode) (cap visit : ℕ) (within : visit ≤ 2)
    (target : Host.Position) (near : tile target ∈ box 3 (witnessEnd visit)) :
    (completion witnessConfig mode cap).satisfied
      (Kernel.path (gridWorld witnessConfig mode) (member witnessLive target)
        (witnessExplore visit) 7) :=
  find_near_met mode witnessLive cap (witnessExplore visit) 7 (witnessEnd visit)
    (witness_walk visit within) target near

/-- The coordinate of an integer, clamped to the signed 64-bit range. -/
def clampCoordinate (value : ℤ) : Host.Coordinate :=
  ⟨max (-(2 ^ 63)) (min value (2 ^ 63 - 1)), by omega⟩

/-- The position of a lattice point, each coordinate clamped to the signed range. -/
def pointPosition (point : ℤ × ℤ) : Host.Position :=
  ⟨clampCoordinate point.1, clampCoordinate point.2⟩

/-- The tiles of the witness's members: those within three tiles of the three end tiles. -/
def witnessTiles : Finset (ℤ × ℤ) :=
  box 3 (witnessEnd 0) ∪ box 3 (witnessEnd 1) ∪ box 3 (witnessEnd 2)

/-- A tile of the witness is within three tiles of one of the three end tiles. -/
theorem witnessTiles_near (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    ∃ visit, visit ≤ 2 ∧ point ∈ box 3 (witnessEnd visit) := by
  simp only [witnessTiles, Finset.mem_union] at inside
  rcases inside with (first | second) | third
  · exact ⟨0, by omega, first⟩
  · exact ⟨1, by omega, second⟩
  · exact ⟨2, by omega, third⟩

/-- Every tile of the witness is the tile of its position, and lies more than three tiles
from the start. -/
theorem witnessTiles_admitted (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    tile (pointPosition point) = point ∧ point ∉ box 3 (32, 32) := by
  obtain ⟨visit, within, near⟩ := witnessTiles_near point inside
  rw [mem_box] at near
  rcases (by omega : visit = 0 ∨ visit = 1 ∨ visit = 2) with rfl | rfl | rfl <;>
    simp only [witnessEnd] at near <;>
    refine ⟨Prod.ext ?_ ?_, fun far => ?_⟩ <;>
    (try rw [mem_box] at far) <;>
    simp only [tile, pointPosition, clampCoordinate] at * <;>
    omega

/-- The witness has 147 member tiles: the three boxes are disjoint. -/
theorem card_witnessTiles : witnessTiles.card = 147 := by
  have apart : ∀ (first second : ℤ × ℤ) (point : ℤ × ℤ),
      7 ≤ (first.1 - second.1).natAbs ∨ 7 ≤ (first.2 - second.2).natAbs →
      point ∈ box 3 first → point ∉ box 3 second := by
    intro first second point far near close
    rw [mem_box] at near close
    omega
  rw [witnessTiles, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_box,
    card_box, card_box]
  · exact Finset.disjoint_left.mpr fun point near =>
      apart _ _ point (by simp only [witnessEnd]; omega) near
  · refine Finset.disjoint_left.mpr fun point near => ?_
    rcases Finset.mem_union.mp near with first | second
    · exact apart _ _ point (by simp only [witnessEnd]; omega) first
    · exact apart _ _ point (by simp only [witnessEnd]; omega) second

/-- The 147 concealed targets within three tiles of the three end tiles of the witness's
explorations. Each is met, from the witness world, by the exploration of one of the visits 0 to 2 at
its seventh step. -/
theorem witness_explored (mode : TaskFeatureMode) :
    ∃ members : Finset (findClass witnessConfig mode witnessLive).Index,
      members.card = 147 ∧
      ∀ target ∈ members, ∃ visit, visit ≤ 2 ∧
        ∃ step, 1 ≤ step ∧ step ≤ 7 ∧ (completion witnessConfig mode 7).satisfied
          (Kernel.path (gridWorld witnessConfig mode) (member witnessLive target.1)
            (witnessExplore visit) step) := by
  let admit :
      { point // point ∈ witnessTiles } → (findClass witnessConfig mode witnessLive).Index :=
    fun point => ⟨pointPosition point.1, by
      rw [member_tile, witness_start, (witnessTiles_admitted point.1 point.2).1]
      exact (witnessTiles_admitted point.1 point.2).2⟩
  have injective : Function.Injective admit := by
    intro first second same
    have tiles := congrArg (fun target : (findClass witnessConfig mode witnessLive).Index =>
      tile target.1) same
    simp only [admit, (witnessTiles_admitted first.1 first.2).1,
      (witnessTiles_admitted second.1 second.2).1] at tiles
    exact Subtype.ext tiles
  let members := witnessTiles.attach.map ⟨admit, injective⟩
  have count : members.card = 147 := by
    rw [Finset.card_map, Finset.card_attach, card_witnessTiles]
  refine ⟨members, count, fun target chosen => ?_⟩
  obtain ⟨point, -, rfl⟩ := Finset.mem_map.mp chosen
  obtain ⟨visit, within, near⟩ := witnessTiles_near point.1 point.2
  refine ⟨visit, within, 7, by omega, le_refl 7, witness_meets mode 7 visit within _ ?_⟩
  change tile (pointPosition point.1) ∈ box 3 (witnessEnd visit)
  rw [(witnessTiles_admitted point.1 point.2).1]
  exact near

/-- The separation holds in the executed grid world. In the witness world, with visits of seven
steps, the replaying agent with the achievement flag as its signal solves on visit 2 the 147
concealed targets within three tiles of the three end tiles, while on every visit every
experience-free agent solves fewer: 147 is more than the covering bound 49 + 7 · 7 = 98. -/
theorem witness_separation (mode : TaskFeatureMode) :
    ∃ members : Finset (findClass witnessConfig mode witnessLive).Index,
      49 + 7 * 7 < members.card ∧
      (∀ target ∈ members, Kernel.SolvesOnVisit (findClass witnessConfig mode witnessLive)
        (fun _ => completion witnessConfig mode 7) 7
        (Kernel.replay Grid.interface 7 achievedSignal witnessExplore) 2 target) ∧
      ∀ agent : Kernel.Agent Grid.interface, Kernel.ExperienceFree agent →
        ∀ (count : ℕ) (solved : Finset (findClass witnessConfig mode witnessLive).Index),
          (∀ target ∈ solved, Kernel.SolvesOnVisit (findClass witnessConfig mode witnessLive)
            (fun _ => completion witnessConfig mode 7) 7 agent count target) →
            solved.card < members.card := by
  obtain ⟨members, count, explored⟩ := witness_explored mode
  have separated := find_replay_separates witnessConfig mode witnessLive 7 witnessExplore members
    2 explored (by rw [count]; decide)
  exact ⟨members, by rw [count]; decide, separated⟩

/-! ## A class with the kernel's form of conditions (a) to (c) -/

/-- The concealed targets some action sequence meets within a visit of `length` steps. -/
def feasibleFind (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (length : ℕ) : Kernel.WorldClass Grid.interface where
  Index := { target : (findClass config mode live).Index //
    Kernel.Feasible (completion config mode length) (member live target.1) }
  world := fun _ => gridWorld config mode
  start := fun target => member live target.1.1

/-- The feasible concealed targets conceal their goals behind the world with no target met,
as all concealed targets do. -/
theorem feasibleFind_conceals (mode : TaskFeatureMode) (live : Live config) (length cap : ℕ) :
    Kernel.Conceals (feasibleFind config mode live length) (fun _ => completion config mode cap)
      (gridWorld config mode) (member live nowhere) :=
  fun target actions time unmet => find_conceals mode live cap target.1 actions time unmet

/-- A walk of `length` steps meets at most `49 + 7 length` feasible concealed targets, as it does
of all concealed targets. -/
theorem feasibleFind_covered (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (length : ℕ) :
    Kernel.Covered (feasibleFind config mode live length)
      (Kernel.visitGoals (fun _ => completion config mode length) length) (49 + 7 * length) := by
  classical
  intro actions solved each
  have injective : Function.Injective
      (fun target : (feasibleFind config mode live length).Index => target.1) :=
    fun _ _ same => Subtype.ext same
  rw [← Finset.card_image_of_injective solved injective]
  apply find_covered config mode live length actions
  intro target chosen
  obtain ⟨original, picked, rfl⟩ := Finset.mem_image.mp chosen
  exact each original picked

/-- **The window.** A concealed target that some action sequence meets within `length` steps lies
within `3 + length` tiles of the start on both axes. So the window of that radius around the start
holds every member of a class of feasible concealed targets, whatever the terrain. -/
theorem feasible_window (mode : TaskFeatureMode) (live : Live config) (length : ℕ)
    (target : Host.Position)
    (feasible : Kernel.Feasible (completion config mode length) (member live target)) :
    tile target ∈ box (3 + length) (tile live.world.body.position.position) := by
  obtain ⟨actions, met⟩ := feasible
  exact swept_subset_box 3 (walk (physical live.world) actions)
    (walk_near (physical live.world) actions) length
    (find_met_swept mode live length actions target met)

/-- A class of feasible concealed targets has at most `(2 (3 + length) + 1)² - 49` members: the
tiles of its window less those within three tiles of the start. -/
theorem feasible_count (mode : TaskFeatureMode) (live : Live config) (length : ℕ)
    (members : Finset (feasibleFind config mode live length).Index) :
    members.card ≤ (2 * (3 + length) + 1) * (2 * (3 + length) + 1) - 49 := by
  classical
  have inside : members.image (fun target => tile target.1.1) ⊆
      box (3 + length) (tile live.world.body.position.position) \
        box 3 (tile live.world.body.position.position) := by
    intro point chosen
    obtain ⟨target, -, rfl⟩ := Finset.mem_image.mp chosen
    exact Finset.mem_sdiff.mpr ⟨feasible_window mode live length target.1.1 target.2,
      (member_tile live target.1.1).mp target.1.2⟩
  have nested : box 3 (tile live.world.body.position.position) ⊆
      box (3 + length) (tile live.world.body.position.position) := by
    intro point close
    have near := mem_box.mp close
    exact mem_box.mpr ⟨by omega, by omega⟩
  calc members.card
      = (members.image (fun target => tile target.1.1)).card :=
        (Finset.card_image_of_injective members fun first second same =>
          Subtype.ext (Subtype.ext (tile_injective same))).symm
    _ ≤ (box (3 + length) (tile live.world.body.position.position) \
          box 3 (tile live.world.body.position.position)).card := Finset.card_le_card inside
    _ = (2 * (3 + length) + 1) * (2 * (3 + length) + 1) - 49 := by
        rw [Finset.card_sdiff_of_subset nested, card_box, card_box]

/-- In every admitted world, a finite set of more feasible concealed targets than the covering
bound makes the class a `Kernel.ConcealedClass`. Feasibility holds by how the class is indexed, so
the theorem's content is the concealment, the bound and the count. -/
theorem feasibleFind_concealed_of (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (length : ℕ)
    (members : Finset (feasibleFind config mode live length).Index)
    (many : 49 + 7 * length < members.card) :
    Nonempty (Kernel.ConcealedClass (feasibleFind config mode live length)
      (fun _ => completion config mode length) length (49 + 7 * length)) :=
  ⟨{ reference := gridWorld config mode
     origin := member live nowhere
     conceals := feasibleFind_conceals mode live length length
     covered := feasibleFind_covered config mode live length
     feasible := fun target => target.2
     members := members
     large := many }⟩

/-- **A class meeting the kernel's form of conditions (a) to (c).** In the witness's world, at
seed 1 and side 64, with visits of seven steps, the feasible concealed targets are a
`Kernel.ConcealedClass` with the bound 98: the
147 members of `witness_separation` are each feasible, since each is solved on a visit. This is a
lemma the mission theorem on the first class of the ladder uses. It says nothing about obligation 4
of `docs/mission-contract.md`, the goal-information and exploration premises, and it is no result
about learning. That structure states condition (c) as fewer than all, so the class is not thereby
shown to be a concealed class (sentence 5 of contract 2 there). The bound 98 is the one this
theorem is stated at; `AcornVerif.CurrentForkedTargetBoth.feasibleFind_covered_sharp` proves the
sharper covering bound 49 of the same class. -/
theorem witness_concealed (mode : TaskFeatureMode) :
    Nonempty (Kernel.ConcealedClass (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 (49 + 7 * 7)) := by
  classical
  obtain ⟨members, many, solved, -⟩ := witness_separation mode
  have feasible : ∀ target ∈ members,
      Kernel.Feasible (completion witnessConfig mode 7) (member witnessLive target.1) := by
    intro target chosen
    have once := (Kernel.solvesOnVisit_iff _ _ 7 _ 2 target).mp (solved target chosen)
    exact Kernel.Achieves.feasible once
  let admitted : { target // target ∈ members } →
      (feasibleFind witnessConfig mode witnessLive 7).Index :=
    fun target => ⟨target.1, feasible target.1 target.2⟩
  have injective : Function.Injective admitted := by
    intro first second same
    exact Subtype.ext (congrArg
      (fun target : (feasibleFind witnessConfig mode witnessLive 7).Index => target.1) same)
  refine feasibleFind_concealed_of witnessConfig mode witnessLive 7
    (members.attach.map ⟨admitted, injective⟩) ?_
  rw [Finset.card_map, Finset.card_attach]
  exact many

end AcornVerif.CurrentConcealedTarget
