/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentInterface
import AcornVerif.Coverage
import AcornVerif.CurrentCertificates
import AcornVerif.CurrentCurriculum
import AcornVerif.WorldClass
import Mathlib.Data.Finset.Image

/-!
# The executed grid world as a kernel world

`gridWorld` is the grid world as a world of `AcornVerif.Kernel`, built from the
executed host definitions. A live state is a host world with the raw result of the step
that produced it; its transition is `World.step` on the host action of the kernel
action's code, and a step the host refuses leads to the absorbing refused state. Its
percept is the grid adapter's `Grid.percept` on the host observation and the carried
result. Where the host refuses to observe, and at the refused state, the percept is
built from a blank observation that no executed run delivers: the executed attempt
stops there instead.

`foldl_world` shows that the kernel world's states under a list of actions are the
executed `World.advanceActions` fold, refusals included. `completion` is the installed
goal's own completion flag as an attempt goal, and `feasible_iff_replay` shows that it
is feasible exactly when some list of one to cap host actions, replayed by the executed
fold, ends in a world that reports the goal satisfied. `feasible_iff_certificate` shows
that, from a host world with a goal installed, this kernel feasibility is
`AcornVerif.CurrentCertificates.Feasible`: the notion an accepted replay certificate
proves and a blocked certificate of mountains alone refutes.

`executedAgent` is the executed agent's decision function as a kernel agent, and
`executed_callback` shows that the host's callback returns that agent's action and
memory on the kernel world's percept. The host also calls `recordEnvironment` and
`recordAttempt` between decisions; they are outside this instance, and no theorem here
shows that the host's run and the kernel's closed loop take the same actions.

`comparator` is the uniform-random comparator as a kernel agent. It is open-loop
(`comparator_openLoop`): its action sequence is fixed before any world is consulted
(`comparator_actions`), and its kernel action decodes to the executed draw
(`comparator_action`).

## The reach targets one action sequence can meet

`step_physical` shows that the world's dynamics do not read the installed goal. So from
one host world, the body follows the same walk under one action sequence whichever
reach target is installed (`path_physical`), each step moves it at most one tile along
one axis (`step_near`), and a reach goal is met only within three tiles of its target.
`reach_covered` concludes that one action sequence meets the reach goal of at most
`49 + 7 cap` targets, and `reach_need` that every agent that is blind on the class of
targets solves at most that many. `far_window_unsolved` applies it at a cap of 3000
steps and a far radius of 120: of the window's 57600 target tiles, at least 36551 are
outside any set of targets one action sequence meets.

The bound concerns agents whose actions do not depend on the target until it is
reached. Acorn's frame gives the displacement to the target, which makes that
dependence possible. The executed agent is not shown blind on the class of targets, so
the theorem supplies no bound for it; that its actions do depend on the target is not
proved either. The bound counts target positions: it becomes a statement about seeds
only under an assumption on how the seed hash places targets relative to the walk.
-/

namespace AcornVerif.CurrentGridWorld
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentStep AcornVerif.CurrentGoals
open AcornVerif.CurrentCurriculum

variable {config : Host.WorldConfig}

/-! ## The world -/

/-- A live state of the grid world: the host world and the raw result of the step that
produced it, which the next percept carries. -/
structure Live (config : Host.WorldConfig) where
  /-- The executed world state. -/
  world : Host.World config
  /-- The raw result the agent's next decision consumes. -/
  carried : Host.RawStepResult

/-- The observation that stands in where the host refuses to observe. No executed run
delivers it. -/
def blank : Host.Observation :=
  ⟨Vector.replicate _ (Vector.replicate _ ⟨0, 0, 0⟩), 0, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩

/-- The host's observation of a world, or the blank one where the host refuses. -/
def sensed (world : Host.World config) : Host.Observation :=
  match world.observe with
  | .ok observation => observation
  | .error _ => blank

/-- Where the host observes, the sensed observation is the host's. -/
theorem sensed_ok (world : Host.World config) (observation : Host.Observation)
    (seen : world.observe = .ok observation) : sensed world = observation := by
  simp only [sensed, seen]

/-- One executed world step from a live state on the host action of a kernel action's
code. A refused step has no successor. -/
def advance (live : Live config) (action : Kernel.Act Grid.interface) : Option (Live config) :=
  match live.world.step (Host.Action.fromIndex action.val) with
  | .ok (next, result) => some ⟨next, result.raw⟩
  | .error _ => none

/-- The grid adapter's percept at a state. -/
def percept (mode : TaskFeatureMode) : Option (Live config) → Percept Grid.interface
  | some live => Grid.percept mode (sensed live.world) live.carried.reward live.carried.events.done
  | none => Grid.percept mode blank ⟨0⟩ false

/-- The grid world of a configuration as a kernel world. Its states are the live states
and one absorbing refused state. -/
abbrev gridWorld (config : Host.WorldConfig) (mode : TaskFeatureMode) :
    Kernel.World Grid.interface where
  State := Option (Live config)
  step := fun state action => state.bind (advance · action)
  percept := percept mode

/-- A successful host step is the kernel world's step, and its raw result is carried. -/
theorem advance_ok (live : Live config) (action : Kernel.Act Grid.interface)
    (next : Host.World config) (events : Host.StepResult)
    (stepped : live.world.step (Host.Action.fromIndex action.val) = .ok (next, events)) :
    advance live action = some ⟨next, events.raw⟩ := by
  simp only [advance, stepped]

/-- A kernel step between live states is a successful host step whose raw result the
successor carries. -/
theorem advance_some (live next : Live config) (action : Kernel.Act Grid.interface)
    (h : advance live action = some next) :
    ∃ events, live.world.step (Host.Action.fromIndex action.val) = .ok (next.world, events) ∧
      next.carried = events.raw := by
  cases stepped : live.world.step (Host.Action.fromIndex action.val) with
  | error refusal =>
    have gone : advance live action = none := by simp only [advance, stepped]
    rw [gone] at h
    cases h
  | ok pair =>
    obtain ⟨world, events⟩ := pair
    rw [advance_ok live action world events stepped] at h
    cases Option.some.inj h
    exact ⟨events, rfl, rfl⟩

/-- At a live state the host observes, the percept is the grid adapter's on the host's
observation and the carried result. -/
theorem percept_live (mode : TaskFeatureMode) (live : Live config)
    (observation : Host.Observation) (seen : live.world.observe = .ok observation) :
    (gridWorld config mode).percept (some live) =
      Grid.percept mode observation live.carried.reward live.carried.events.done :=
  congrArg (fun sight => Grid.percept mode sight live.carried.reward live.carried.events.done)
    (sensed_ok live.world observation seen)

/-! ## Executed action lists -/

/-- The refused state is absorbing. -/
theorem foldl_refused (mode : TaskFeatureMode) (actions : List (Kernel.Act Grid.interface)) :
    actions.foldl (gridWorld config mode).step none = none := by
  induction actions with
  | nil => rfl
  | cons head rest ih => exact ih

/-- The kernel world's state under a list of actions holds the world of the executed
action-stream fold, and is refused exactly when that fold is. -/
theorem foldl_world (mode : TaskFeatureMode) (live : Live config)
    (actions : List (Kernel.Act Grid.interface)) :
    (actions.foldl (gridWorld config mode).step (some live)).map (fun state => state.world) =
      (live.world.advanceActions
        (actions.map fun action => Host.Action.fromIndex action.val)).toOption := by
  induction actions generalizing live with
  | nil => rfl
  | cons head rest ih =>
    cases stepped : live.world.step (Host.Action.fromIndex head.val) with
    | error refusal =>
      have gone : (gridWorld config mode).step (some live) head = none := by
        change advance live head = none
        simp only [advance, stepped]
      have refused : live.world.advanceActions
          ((head :: rest).map fun action => Host.Action.fromIndex action.val) =
            .error refusal := by
        simp only [List.map_cons, Host.World.advanceActions, stepped, bind, Except.bind]
      rw [List.foldl_cons, gone, foldl_refused, refused]
      rfl
    | ok pair =>
      obtain ⟨next, events⟩ := pair
      have moved : (gridWorld config mode).step (some live) head = some ⟨next, events.raw⟩ :=
        advance_ok live head next events stepped
      have continued : live.world.advanceActions
          ((head :: rest).map fun action => Host.Action.fromIndex action.val) =
            next.advanceActions (rest.map fun action => Host.Action.fromIndex action.val) := by
        simp only [List.map_cons, Host.World.advanceActions, stepped, bind, Except.bind]
      rw [List.foldl_cons, moved, continued]
      exact ih ⟨next, events.raw⟩

/-- The kernel code of a host action. -/
def code (action : Host.Action) : Kernel.Act Grid.interface := action.index

/-- Decoding the codes of a list of host actions returns the list. -/
theorem decode_code (actions : List Host.Action) :
    (actions.map code).map (fun action => Host.Action.fromIndex action.val) = actions := by
  induction actions with
  | nil => rfl
  | cons head rest ih =>
    exact (congrArg (List.cons (Host.Action.fromIndex head.index.val)) ih).trans
      (congrArg (fun action => action :: rest) (Host.Action.index_roundtrip head))

/-- The installed goal's completion as an attempt goal: a live state whose world
reports its goal satisfied, within `cap` steps. -/
def completion (config : Host.WorldConfig) (mode : TaskFeatureMode) (cap : ℕ) :
    Kernel.AttemptGoal (gridWorld config mode) where
  satisfied := fun (state : Option (Live config)) =>
    ∃ live, state = some live ∧ live.world.goalSatisfied = true
  cap := cap

/-- The installed goal is feasible in the kernel world exactly when the executed
action-stream fold of some list of one to `cap` host actions ends in a world that
reports the goal satisfied. -/
theorem feasible_iff_replay (mode : TaskFeatureMode) (live : Live config) (cap : ℕ) :
    Kernel.Feasible (completion config mode cap) (some live) ↔
      ∃ (actions : List Host.Action) (final : Host.World config),
        1 ≤ actions.length ∧ actions.length ≤ cap ∧
          live.world.advanceActions actions = .ok final ∧ final.goalSatisfied = true := by
  rw [Kernel.feasible_iff_list]
  constructor
  · rintro ⟨actions, low, high, state, reached, done⟩
    have bridge := foldl_world mode live actions
    refine ⟨actions.map fun action => Host.Action.fromIndex action.val, state.world, ?_, ?_, ?_,
      done⟩
    · rw [List.length_map]
      exact low
    · rw [List.length_map]
      exact high
    · rw [reached] at bridge
      cases replay : live.world.advanceActions
          (actions.map fun action => Host.Action.fromIndex action.val) with
      | error refusal =>
        rw [replay] at bridge
        simp [Except.toOption] at bridge
      | ok final =>
        rw [replay] at bridge
        exact congrArg Except.ok (Option.some.inj bridge).symm
  · rintro ⟨actions, final, low, high, replay, done⟩
    have bridge := foldl_world mode live (actions.map code)
    rw [decode_code, replay] at bridge
    refine ⟨actions.map code, ?_, ?_, ?_⟩
    · rw [List.length_map]
      exact low
    · rw [List.length_map]
      exact high
    · cases landed : (actions.map code).foldl (gridWorld config mode).step (some live) with
      | none =>
        rw [landed] at bridge
        simp [Except.toOption] at bridge
      | some state =>
        rw [landed] at bridge
        have same : state.world = final := Option.some.inj bridge
        exact ⟨state, rfl, by rw [same]; exact done⟩

/-- From a host world with a goal installed, the goal is feasible in the kernel world
exactly when it is feasible in the sense of the certificate proofs: some run of one to
`cap` executed steps ends in a world that satisfies it. The equivalence holds for every
carried result. -/
theorem feasible_iff_certificate (mode : TaskFeatureMode) (world : Host.World config)
    (goal : Host.Goal) (carried : Host.RawStepResult) (cap : ℕ) :
    Kernel.Feasible (completion config mode cap) (some ⟨world.setGoal goal, carried⟩) ↔
      CurrentCertificates.Feasible world goal cap := by
  rw [feasible_iff_replay]
  constructor
  · rintro ⟨actions, final, low, high, replay, done⟩
    obtain ⟨trace, run, same⟩ := actions_trace (world.setGoal goal) final actions replay
    have length : trace.length = actions.length := by
      rw [← same, List.length_map]
    exact ⟨trace, final, run, by omega, by omega, done⟩
  · rintro ⟨trace, final, run, low, high, done⟩
    refine ⟨trace.map (·.1), final, ?_, ?_, trace_actions run, done⟩
    · rw [List.length_map]
      exact low
    · rw [List.length_map]
      exact high

/-! ## The executed agent and the comparator -/

/-- The executed agent's decision function from a given agent state, as a kernel agent
over the agent's own interface. -/
def executedAgent {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
    (state : Agent interface profile features criterion dimension planning) :
    Kernel.Agent interface where
  Memory := Agent interface profile features criterion dimension planning
  initial := state
  act := fun memory percept => ((memory.act percept).2.action, (memory.act percept).1)

/-- At a live state the host observes, the host's callback returns the kernel agent's
action, as a host action, and its next memory, on the kernel world's percept. -/
theorem executed_callback {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
    (state : Agent Grid.interface profile features criterion dimension planning)
    (live : Live config) (observation : Host.Observation)
    (seen : live.world.observe = .ok observation) :
    (Agent.callbacks .learnThenAct).act state observation live.carried =
      (Host.Action.fromIndex ((executedAgent state).act state
          ((gridWorld config profile.taskMode).percept (some live))).1.val,
        ((executedAgent state).act state
          ((gridWorld config profile.taskMode).percept (some live))).2) := by
  rw [percept_live profile.taskMode live observation seen, Agent.callbacks_act]
  rfl

/-- The uniform-random comparator from a stream, as a kernel agent: its memory is the
stream, and its action is the code of the executed draw. A run's comparator starts from
`baselineStream` of the run's seed and carries its stream from attempt to attempt. -/
def comparator (stream : Rng.Xoshiro256) : Kernel.Agent Grid.interface where
  Memory := Rng.Xoshiro256
  initial := stream
  act := fun (stream : Rng.Xoshiro256) _ =>
    (code (Host.baselineAction stream).1, (Host.baselineAction stream).2)

/-- The comparator reads no percept. -/
theorem comparator_openLoop (stream : Rng.Xoshiro256) : Kernel.OpenLoop (comparator stream) :=
  ⟨fun (stream : Rng.Xoshiro256) => (Host.baselineAction stream).2,
    fun (stream : Rng.Xoshiro256) => code (Host.baselineAction stream).1, fun _ _ => rfl⟩

/-- The comparator's action sequence is fixed before any world is consulted: it is the
same in every world over the grid interface, from every start state. -/
theorem comparator_actions (stream : Rng.Xoshiro256) :
    ∃ actions : ℕ → Kernel.Act Grid.interface,
      ∀ (world : Kernel.World Grid.interface) (start : world.State) (time : ℕ),
        Kernel.actionAt world (comparator stream) start time = actions time :=
  Kernel.openLoop_actions (comparator_openLoop stream)

/-- The comparator's kernel action decodes to the executed draw, so the kernel world
takes the host step the comparator's attempt takes. -/
theorem comparator_action (initial stream : Rng.Xoshiro256) (percept : Percept Grid.interface) :
    Host.Action.fromIndex ((comparator initial).act stream percept).1.val =
      (Host.baselineAction stream).1 :=
  Host.Action.index_roundtrip (Host.baselineAction stream).1

/-! ## The dynamics do not read the goal -/

/-- A world with its goal removed: the fields the transition reads. -/
def physical (world : Host.World config) : Host.World config :=
  { world with goal := none, goalStart := 0 }

/-- The world's dynamics do not read the installed goal. A step of the world without
its goal succeeds exactly when the step of the world does, and its successor is the
world's successor without its goal. -/
theorem step_physical (world : Host.World config) (action : Host.Action) :
    (physical world).step action =
      match world.step action with
      | .ok (next, events) => .ok (physical next, { events with done := false })
      | .error refusal => .error refusal := by
  unfold Host.World.step
  rw [show Host.payAndAct (physical world) action = Host.payAndAct world action from rfl]
  cases Host.payAndAct world action with
  | error refusal => rfl
  | ok active =>
    simp only [bind, Except.bind]
    rw [show Host.passiveChange { (physical world).applyActive active with
          time := ((physical world).applyActive active).time + 1 } =
        Host.passiveChange { world.applyActive active with
          time := (world.applyActive active).time + 1 } from rfl]
    cases Host.passiveChange { world.applyActive active with
        time := (world.applyActive active).time + 1 } with
    | error refusal => rfl
    | ok passive => rfl

/-- One step of the dynamics without the goal. -/
def physicalStep (world : Host.World config) (action : Kernel.Act Grid.interface) :
    Option (Host.World config) :=
  match world.step (Host.Action.fromIndex action.val) with
  | .ok (next, _) => some (physical next)
  | .error _ => none

/-- A kernel step, with the goal removed, is a step of the dynamics without the goal. -/
theorem advance_physical (live : Live config) (action : Kernel.Act Grid.interface) :
    (advance live action).map (fun next => physical next.world) =
      physicalStep (physical live.world) action := by
  unfold advance physicalStep
  rw [step_physical]
  cases live.world.step (Host.Action.fromIndex action.val) with
  | error refusal => rfl
  | ok pair =>
    obtain ⟨next, events⟩ := pair
    rfl

/-- The worlds an action sequence drives the dynamics without the goal through. -/
def physicalPath (start : Host.World config) (actions : ℕ → Kernel.Act Grid.interface) :
    ℕ → Option (Host.World config)
  | 0 => some start
  | count + 1 => (physicalPath start actions count).bind (physicalStep · (actions count))

/-- A kernel path, with the goal removed, is the path of the dynamics without the goal
from the start world without its goal. -/
theorem path_physical (mode : TaskFeatureMode) (live : Live config)
    (actions : ℕ → Kernel.Act Grid.interface) (count : ℕ) :
    (Kernel.path (gridWorld config mode) (some live) actions count).map
        (fun state => physical state.world) =
      physicalPath (physical live.world) actions count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change ((Kernel.path (gridWorld config mode) (some live) actions count).bind
        (advance · (actions count))).map (fun state => physical state.world) =
      (physicalPath (physical live.world) actions count).bind (physicalStep · (actions count))
    rw [← ih]
    cases Kernel.path (gridWorld config mode) (some live) actions count with
    | none => rfl
    | some middle => exact advance_physical middle (actions count)

/-- No kernel step replaces the installed goal. -/
theorem path_goal (mode : TaskFeatureMode) (live final : Live config)
    (actions : ℕ → Kernel.Act Grid.interface) (count : ℕ)
    (reached : Kernel.path (gridWorld config mode) (some live) actions count = some final) :
    final.world.goal = live.world.goal := by
  induction count generalizing final with
  | zero =>
    cases Option.some.inj reached
    rfl
  | succ count ih =>
    cases before : Kernel.path (gridWorld config mode) (some live) actions count with
    | none =>
      have gone : Kernel.path (gridWorld config mode) (some live) actions (count + 1) = none :=
        congrArg (fun state => Option.bind state (advance · (actions count))) before
      rw [gone] at reached
      cases reached
    | some middle =>
      have unfolded : Kernel.path (gridWorld config mode) (some live) actions (count + 1) =
          advance middle (actions count) :=
        congrArg (fun state => Option.bind state (advance · (actions count))) before
      obtain ⟨events, stepped, -⟩ :=
        advance_some middle final (actions count) (unfolded.symm.trans reached)
      exact (Host.World.step_goal _ _ _ _ stepped).1.trans (ih middle before)

/-! ## The body's walk -/

/-- The tile of a position, as a lattice point. -/
def tile (position : Host.Position) : ℤ × ℤ := (position.x.val, position.y.val)

/-- Distinct positions have distinct tiles. -/
theorem tile_injective : Function.Injective tile := by
  intro first second same
  have horizontal : first.x = second.x := Subtype.ext (congrArg Prod.fst same)
  have vertical : first.y = second.y := Subtype.ext (congrArg Prod.snd same)
  cases first with
  | mk firstX firstY =>
    cases second with
    | mk secondX secondY =>
      have sameX : firstX = secondX := horizontal
      have sameY : firstY = secondY := vertical
      rw [sameX, sameY]

/-- A successful world step leaves the body on its tile or moves it one tile along one
axis. -/
theorem step_near (world next : Host.World config) (action : Host.Action)
    (events : Host.StepResult) (h : world.step action = .ok (next, events)) :
    Near (tile world.body.position.position) (tile next.body.position.position) := by
  rcases step_adjacent world next action events h with same | ⟨direction, -, moved, -, -⟩
  · rw [same]
    exact Near.refl _
  · obtain ⟨horizontal, vertical⟩ := CurrentCertificates.translate_some _ _ _ _ moved
    change (next.body.position.position.x.val - world.body.position.position.x.val).natAbs +
      (next.body.position.position.y.val - world.body.position.position.y.val).natAbs ≤ 1
    cases direction <;> simp only [Host.Direction.delta] at horizontal vertical <;> omega

/-- A step of the dynamics without the goal moves the body at most one tile along one
axis. -/
theorem physicalStep_near (world next : Host.World config) (action : Kernel.Act Grid.interface)
    (h : physicalStep world action = some next) :
    Near (tile world.body.position.position) (tile next.body.position.position) := by
  cases stepped : world.step (Host.Action.fromIndex action.val) with
  | error refusal => simp [physicalStep, stepped] at h
  | ok pair =>
    obtain ⟨after, events⟩ := pair
    simp only [physicalStep, stepped, Option.some.injEq] at h
    subst h
    exact step_near world after _ events stepped

/-- The body's tile along the dynamics without the goal. After a refused step the walk
stays on the last tile. -/
def walk (start : Host.World config) (actions : ℕ → Kernel.Act Grid.interface) : ℕ → ℤ × ℤ
  | 0 => tile start.body.position.position
  | count + 1 =>
    match physicalPath start actions (count + 1) with
    | some after => tile after.body.position.position
    | none => walk start actions count

/-- Where the dynamics reach a world, the walk is on that world's body tile. -/
theorem walk_live (start after : Host.World config) (actions : ℕ → Kernel.Act Grid.interface)
    (count : ℕ) (reached : physicalPath start actions count = some after) :
    walk start actions count = tile after.body.position.position := by
  cases count with
  | zero =>
    cases Option.some.inj reached
    rfl
  | succ count => simp only [walk, reached]

/-- Successive points of the walk are equal or one tile apart along one axis. -/
theorem walk_near (start : Host.World config) (actions : ℕ → Kernel.Act Grid.interface)
    (count : ℕ) : Near (walk start actions count) (walk start actions (count + 1)) := by
  cases later : physicalPath start actions (count + 1) with
  | none =>
    have same : walk start actions (count + 1) = walk start actions count := by
      simp only [walk, later]
    rw [same]
    exact Near.refl _
  | some after =>
    rw [walk_live start after actions (count + 1) later]
    cases before : physicalPath start actions count with
    | none =>
      have gone : physicalPath start actions (count + 1) = none :=
        congrArg (fun state => Option.bind state (physicalStep · (actions count))) before
      rw [gone] at later
      cases later
    | some middle =>
      have unfolded : physicalPath start actions (count + 1) =
          physicalStep middle (actions count) :=
        congrArg (fun state => Option.bind state (physicalStep · (actions count))) before
      rw [walk_live start middle actions count before]
      exact physicalStep_near middle after (actions count) (unfolded.symm.trans later)

/-! ## Reach targets -/

/-- The class of reach targets over one host world: each member installs a reach goal
for its target in the same world. -/
def reachClass (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config) :
    Kernel.WorldClass Grid.interface where
  Index := Host.Position
  world := fun _ => gridWorld config mode
  start := fun target => some ⟨live.world.setGoal (.reach target), live.carried⟩

/-- A target whose goal box holds a position has its tile within three of that
position's tile. -/
theorem box_of_goalBox (target position : Host.Position) (inside : InGoalBox target position) :
    tile target ∈ box 3 (tile position) :=
  mem_box.mpr inside

/-- A target whose reach goal an action sequence meets within `cap` steps lies within
three tiles of the first `cap + 1` points of the body's walk. -/
theorem met_swept (mode : TaskFeatureMode) (live : Live config) (cap : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface) (target : Host.Position)
    (met : (completion config mode cap).MetBy
      (some ⟨live.world.setGoal (.reach target), live.carried⟩) actions) :
    tile target ∈ swept 3 (walk (physical live.world) actions) cap := by
  obtain ⟨time, -, high, final, reached, done⟩ := met
  have installed : final.world.goal = some (.reach target) :=
    path_goal mode ⟨live.world.setGoal (.reach target), live.carried⟩ final actions time reached
  have inside : InGoalBox target final.world.body.position.position :=
    (reach_goal_iff final.world target installed).mp done
  have track : (Kernel.path (gridWorld config mode)
      (some ⟨live.world.setGoal (.reach target), live.carried⟩) actions time).map
        (fun state => physical state.world) =
      physicalPath (physical live.world) actions time :=
    path_physical mode ⟨live.world.setGoal (.reach target), live.carried⟩ actions time
  rw [reached] at track
  have here : walk (physical live.world) actions time = tile final.world.body.position.position :=
    walk_live (physical live.world) (physical final.world) actions time track.symm
  have near : tile target ∈ box 3 (walk (physical live.world) actions time) := by
    rw [here]
    exact box_of_goalBox target _ inside
  exact box_subset_swept 3 _ cap time high near

/-- One action sequence meets the reach goal of at most `49 + 7 cap` targets in `cap`
steps, from every host world and for every terrain. -/
theorem reach_covered (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (cap : ℕ) :
    Kernel.Covered (reachClass config mode live) (fun _ => completion config mode cap)
      (49 + 7 * cap) := by
  intro actions solved each
  have inside : solved.image tile ⊆ swept 3 (walk (physical live.world) actions) cap := by
    intro point member
    obtain ⟨target, chosen, rfl⟩ := Finset.mem_image.mp member
    exact met_swept mode live cap actions target (each target chosen)
  calc solved.card
      = (solved.image tile).card := (Finset.card_image_of_injective solved tile_injective).symm
    _ ≤ (swept 3 (walk (physical live.world) actions) cap).card := Finset.card_le_card inside
    _ ≤ (2 * 3 + 1) * (2 * 3 + 1) + (2 * 3 + 1) * cap :=
        card_swept 3 _ cap (fun index _ => walk_near _ actions index)
    _ = 49 + 7 * cap := rfl

/-- Every agent that is blind on the class of reach targets solves at most
`49 + 7 cap` of them. -/
theorem reach_need (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (cap : ℕ) :
    Kernel.Need (reachClass config mode live) (fun _ => completion config mode cap)
      (Kernel.Blind (reachClass config mode live) (fun _ => completion config mode cap))
      (49 + 7 * cap) :=
  Kernel.need_of_covered (reach_covered config mode live cap)

/-- The uniform-random comparator solves at most `49 + 7 cap` reach targets from one
host world, whatever its stream. -/
theorem comparator_reach (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (cap : ℕ) (stream : Rng.Xoshiro256) (solved : Finset Host.Position)
    (each : ∀ target ∈ solved, Kernel.Solves (reachClass config mode live)
      (fun _ => completion config mode cap) (comparator stream) target) :
    solved.card ≤ 49 + 7 * cap :=
  reach_need config mode live cap (comparator stream)
    (Kernel.openLoop_blind _ _ (comparator_openLoop stream)) solved each

/-- At the studies' cap of 3000 steps a clocked script's counter fits 12 bits. -/
theorem script_fits_attempt (actions : ℕ → Kernel.Act Grid.interface) :
    Kernel.MemoryWithin (Kernel.script Grid.interface 3000 actions) 12 :=
  Kernel.script_memoryWithin 3000 12 actions (by decide)

/-! ## The far window -/

/-- The tiles of the square window of a radius around the campaign center. -/
def windowTiles (side : Host.Coordinate) (radius : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Ico (side.val.tdiv 2 - radius) (side.val.tdiv 2 + radius) ×ˢ
    Finset.Ico (side.val.tdiv 2 - radius) (side.val.tdiv 2 + radius)

/-- A target is in a window exactly when its tile is one of the window's tiles. -/
theorem mem_windowTiles (side : Host.Coordinate) (radius : ℕ) (target : Host.Position) :
    tile target ∈ windowTiles side radius ↔ InWindow side radius target := by
  simp only [windowTiles, tile, Finset.mem_product, Finset.mem_Ico, InWindow]
  omega

/-- A window of a radius has `(2 radius)²` tiles. -/
theorem card_windowTiles (side : Host.Coordinate) (radius : ℕ) :
    (windowTiles side radius).card = (2 * radius) * (2 * radius) := by
  have width : (side.val.tdiv 2 + radius - (side.val.tdiv 2 - radius)).toNat = 2 * radius := by
    omega
  rw [windowTiles, Finset.card_product, Int.card_Ico, width]

/-- From a side of 720 the far radius of the standard curriculum is 120. -/
theorem farRadius_large (side : Host.Coordinate) (large : 720 ≤ side.val) :
    farRadius side = 120 := by
  unfold farRadius
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

/-- At a cap of 3000 steps and a far radius of 120, of the far window's 57600 target
tiles at least 36551 are outside every set of window targets whose reach goal one action
sequence meets: it meets at most 21049 of them, under 36.6 percent. -/
theorem far_window_unsolved (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (side : Host.Coordinate) (actions : ℕ → Kernel.Act Grid.interface)
    (solved : Finset Host.Position) (window : ∀ target ∈ solved, InWindow side 120 target)
    (each : ∀ target ∈ solved, (completion config mode 3000).MetBy
      (some ⟨live.world.setGoal (.reach target), live.carried⟩) actions) :
    solved.card ≤ 21049 ∧ (windowTiles side 120).card = 57600 ∧
      36551 ≤ (windowTiles side 120 \ solved.image tile).card ∧
      21049 * 1000 < 366 * 57600 := by
  have few : solved.card ≤ 21049 := reach_covered config mode live 3000 actions solved each
  have total : (windowTiles side 120).card = 57600 := card_windowTiles side 120
  have inside : solved.image tile ⊆ windowTiles side 120 := by
    intro point member
    obtain ⟨target, chosen, rfl⟩ := Finset.mem_image.mp member
    exact (mem_windowTiles side 120 target).mpr (window target chosen)
  have split := Finset.card_sdiff_add_card_eq_card inside
  have image : (solved.image tile).card = solved.card :=
    Finset.card_image_of_injective solved tile_injective
  refine ⟨few, total, ?_, by decide⟩
  omega

end AcornVerif.CurrentGridWorld
