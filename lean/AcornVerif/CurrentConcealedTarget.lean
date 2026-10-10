/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentGridWorld
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
  radius 120 that is at most 21049 of the window's 57600 targets (`far_window_visits`).
- **First success, every agent.** On each visit every agent solves at most `49 + 7 cap`
  members it has not solved before, and over `n` visits at most `n (49 + 7 cap)`
  (`find_visits_first_success`, `find_visits_ever`).
- **Re-solving.** The percept's achievement flag after a step is the goal's completion
  (`achieved_decodes`), so the replaying agent solves on every later visit each member it
  has solved once (`find_replay`).

Hypotheses and limits. The class is of target positions over one host world: reading a bound
as a fraction of seeds would assume that the seed hash places targets independently of the
agent's walk (assumed). A visit is the kernel's world in visits of the executed grid world;
no executed host loop returns the world to its start between attempts, and no theorem relates
one to it. A step the host refuses leads to the absorbing refused state, where no goal is
met, in a member and the reference alike.
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
        some (⟨world, events.raw⟩ : Live config) = some found ∧ found.world.goalSatisfied = true
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

/-! ## The far window -/

/-- At a cap of 3000 steps and a window of radius 120, every experience-free agent solves on
each visit at most 21049 of the window's 57600 concealed targets: at least 36551 are
unsolved, and 21049 is under 36.6 percent of 57600. -/
theorem far_window_visits (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (side : Host.Coordinate) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent) (count : ℕ)
    (solved : Finset (findClass config mode live).Index)
    (window : ∀ target ∈ solved, InWindow side 120 target.1)
    (each : ∀ target ∈ solved, Kernel.SolvesOnVisit (findClass config mode live)
      (fun _ => completion config mode 3000) 3000 agent count target) :
    solved.card ≤ 21049 ∧ (windowTiles side 120).card = 57600 ∧
      36551 ≤ (windowTiles side 120 \ solved.image (fun target => tile target.1)).card ∧
      21049 * 1000 < 366 * 57600 := by
  have few : solved.card ≤ 21049 :=
    find_visits_need config mode live 3000 free count solved each
  have total : (windowTiles side 120).card = 57600 := card_windowTiles side 120
  have inside : solved.image (fun target => tile target.1) ⊆ windowTiles side 120 := by
    intro point chosen
    obtain ⟨target, picked, rfl⟩ := Finset.mem_image.mp chosen
    exact (mem_windowTiles side 120 target.1).mpr (window target picked)
  have split := Finset.card_sdiff_add_card_eq_card inside
  have image : (solved.image (fun target => tile target.1)).card = solved.card :=
    Finset.card_image_of_injective solved
      (fun first second same => Subtype.ext (tile_injective same))
  refine ⟨few, total, ?_, by decide⟩
  omega

end AcornVerif.CurrentConcealedTarget
