import Acorn.Host.AgentInterface
import AcornVerif.Coverage
import AcornVerif.CurrentCertificates
import AcornVerif.CurrentCurriculum
import AcornVerif.WorldClass
import Mathlib.Data.Finset.Image

namespace AcornVerif.CurrentGridWorld
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentStep AcornVerif.CurrentGoals
open AcornVerif.CurrentCurriculum

variable {config : Host.WorldConfig}

structure Live (config : Host.WorldConfig) where
  world : Host.World config
  carried : Host.RawStepResult

def blank : Host.Observation :=
  ⟨Vector.replicate _ (Vector.replicate _ ⟨0, 0, 0⟩), 0, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩

def sensed (world : Host.World config) : Host.Observation :=
  match world.observe with
  | .ok observation => observation
  | .error _ => blank

theorem sensed_ok (world : Host.World config) (observation : Host.Observation)
    (seen : world.observe = .ok observation) : sensed world = observation := by
  simp only [sensed, seen]

def advance (live : Live config) (action : Kernel.Act Grid.interface) : Option (Live config) :=
  match live.world.step (Host.Action.fromIndex action.val) with
  | .ok (next, result) => some ⟨next, result.raw⟩
  | .error _ => none

def percept (mode : TaskFeatureMode) : Option (Live config) → Percept Grid.interface
  | some live => Grid.percept mode (sensed live.world) live.carried.reward live.carried.events.done
  | none => Grid.percept mode blank ⟨0⟩ false

abbrev gridWorld (config : Host.WorldConfig) (mode : TaskFeatureMode) :
    Kernel.World Grid.interface where
  State := Option (Live config)
  step := fun state action => state.bind (advance · action)
  percept := percept mode

theorem advance_ok (live : Live config) (action : Kernel.Act Grid.interface)
    (next : Host.World config) (events : Host.StepResult)
    (stepped : live.world.step (Host.Action.fromIndex action.val) = .ok (next, events)) :
    advance live action = some ⟨next, events.raw⟩ := by
  simp only [advance, stepped]

theorem grid_step_live (mode : TaskFeatureMode) (live : Live config)
    (action : Kernel.Act Grid.interface) :
    (gridWorld config mode).step (some live) action = advance live action := rfl

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

theorem percept_live (mode : TaskFeatureMode) (live : Live config)
    (observation : Host.Observation) (seen : live.world.observe = .ok observation) :
    (gridWorld config mode).percept (some live) =
      Grid.percept mode observation live.carried.reward live.carried.events.done :=
  congrArg (fun sight => Grid.percept mode sight live.carried.reward live.carried.events.done)
    (sensed_ok live.world observation seen)

theorem foldl_refused (mode : TaskFeatureMode) (actions : List (Kernel.Act Grid.interface)) :
    actions.foldl (gridWorld config mode).step none = none := by
  induction actions with
  | nil => rfl
  | cons head rest ih => exact ih

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

def code (action : Host.Action) : Kernel.Act Grid.interface := action.index

theorem decode_code (actions : List Host.Action) :
    (actions.map code).map (fun action => Host.Action.fromIndex action.val) = actions := by
  induction actions with
  | nil => rfl
  | cons head rest ih =>
    exact (congrArg (List.cons (Host.Action.fromIndex head.index.val)) ih).trans
      (congrArg (fun action => action :: rest) (Host.Action.index_roundtrip head))

def completion (config : Host.WorldConfig) (mode : TaskFeatureMode) (cap : ℕ) :
    Kernel.AttemptGoal (gridWorld config mode) where
  satisfied := fun (state : Option (Live config)) =>
    ∃ live, state = some live ∧ live.world.goalSatisfied = true
  cap := cap

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

def executedAgent {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
    (state : Agent interface profile features criterion dimension planning) :
    Kernel.Agent interface where
  Memory := Agent interface profile features criterion dimension planning
  initial := state
  act := fun memory percept => ((memory.act percept).2.action, (memory.act percept).1)

theorem executed_defeated {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
    (state : Agent Grid.interface profile features criterion dimension planning)
    (shown : Percept Grid.interface) :
    ∃ (world : Kernel.World Grid.interface) (start : world.State) (goal : Kernel.AttemptGoal world),
      (∀ state, world.percept state = shown) ∧ goal.cap = 1 ∧
        Kernel.Feasible goal start ∧ ¬ Kernel.Achieves (executedAgent state) goal start :=
  Kernel.no_agent_achieves_every_world (by decide) shown (executedAgent state)

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

def comparator (stream : Rng.Xoshiro256) : Kernel.Agent Grid.interface where
  Memory := Rng.Xoshiro256
  initial := stream
  act := fun (stream : Rng.Xoshiro256) _ =>
    (code (Host.baselineAction stream).1, (Host.baselineAction stream).2)

theorem comparator_openLoop (stream : Rng.Xoshiro256) : Kernel.OpenLoop (comparator stream) :=
  ⟨fun (stream : Rng.Xoshiro256) => (Host.baselineAction stream).2,
    fun (stream : Rng.Xoshiro256) => code (Host.baselineAction stream).1, fun _ _ => rfl⟩

theorem comparator_actions (stream : Rng.Xoshiro256) :
    ∃ actions : ℕ → Kernel.Act Grid.interface,
      ∀ (world : Kernel.World Grid.interface) (start : world.State) (time : ℕ),
        Kernel.actionAt world (comparator stream) start time = actions time :=
  Kernel.openLoop_actions (comparator_openLoop stream)

theorem comparator_action (initial stream : Rng.Xoshiro256) (percept : Percept Grid.interface) :
    Host.Action.fromIndex ((comparator initial).act stream percept).1.val =
      (Host.baselineAction stream).1 :=
  Host.Action.index_roundtrip (Host.baselineAction stream).1

def physical (world : Host.World config) : Host.World config :=
  { world with goal := none, goalStart := 0 }

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

def physicalStep (world : Host.World config) (action : Kernel.Act Grid.interface) :
    Option (Host.World config) :=
  match world.step (Host.Action.fromIndex action.val) with
  | .ok (next, _) => some (physical next)
  | .error _ => none

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

def physicalPath (start : Host.World config) (actions : ℕ → Kernel.Act Grid.interface) :
    ℕ → Option (Host.World config)
  | 0 => some start
  | count + 1 => (physicalPath start actions count).bind (physicalStep · (actions count))

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

def tile (position : Host.Position) : ℤ × ℤ := (position.x.val, position.y.val)

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

def walk (start : Host.World config) (actions : ℕ → Kernel.Act Grid.interface) : ℕ → ℤ × ℤ
  | 0 => tile start.body.position.position
  | count + 1 =>
    match physicalPath start actions (count + 1) with
    | some after => tile after.body.position.position
    | none => walk start actions count

theorem walk_live (start after : Host.World config) (actions : ℕ → Kernel.Act Grid.interface)
    (count : ℕ) (reached : physicalPath start actions count = some after) :
    walk start actions count = tile after.body.position.position := by
  cases count with
  | zero =>
    cases Option.some.inj reached
    rfl
  | succ count => simp only [walk, reached]

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

def reachClass (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config) :
    Kernel.WorldClass Grid.interface where
  Index := Host.Position
  world := fun _ => gridWorld config mode
  start := fun target => some ⟨live.world.setGoal (.reach target), live.carried⟩

theorem box_of_goalBox (target position : Host.Position) (inside : InGoalBox target position) :
    tile target ∈ box 3 (tile position) :=
  mem_box.mpr inside

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

theorem reach_need (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (cap : ℕ) :
    Kernel.Need (reachClass config mode live) (fun _ => completion config mode cap)
      (Kernel.Blind (reachClass config mode live) (fun _ => completion config mode cap))
      (49 + 7 * cap) :=
  Kernel.need_of_covered (reach_covered config mode live cap)

theorem comparator_reach (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (cap : ℕ) (stream : Rng.Xoshiro256) (solved : Finset Host.Position)
    (each : ∀ target ∈ solved, Kernel.Solves (reachClass config mode live)
      (fun _ => completion config mode cap) (comparator stream) target) :
    solved.card ≤ 49 + 7 * cap :=
  reach_need config mode live cap (comparator stream)
    (Kernel.openLoop_blind _ _ (comparator_openLoop stream)) solved each

theorem script_fits_attempt (actions : ℕ → Kernel.Act Grid.interface) :
    Kernel.MemoryWithin (Kernel.script Grid.interface 3000 actions) 12 :=
  Kernel.script_memoryWithin 3000 12 actions (by decide)

def windowTiles (side : Host.Coordinate) (radius : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Ico (side.val.tdiv 2 - radius) (side.val.tdiv 2 + radius) ×ˢ
    Finset.Ico (side.val.tdiv 2 - radius) (side.val.tdiv 2 + radius)

theorem mem_windowTiles (side : Host.Coordinate) (radius : ℕ) (target : Host.Position) :
    tile target ∈ windowTiles side radius ↔ InWindow side radius target := by
  simp only [windowTiles, tile, Finset.mem_product, Finset.mem_Ico, InWindow]
  omega

theorem card_windowTiles (side : Host.Coordinate) (radius : ℕ) :
    (windowTiles side radius).card = (2 * radius) * (2 * radius) := by
  have width : (side.val.tdiv 2 + radius - (side.val.tdiv 2 - radius)).toNat = 2 * radius := by
    omega
  rw [windowTiles, Finset.card_product, Int.card_Ico, width]

theorem farRadius_large (side : Host.Coordinate) (large : 720 ≤ side.val) :
    farRadius side = 120 := by
  unfold farRadius
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

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
