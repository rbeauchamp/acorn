import AcornVerif.CurrentConcealedTargetRungChoice

namespace AcornVerif.CurrentConcealedTargetRungFirstVisit
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetFinding
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentConcealedTargetRungFinds AcornVerif.CurrentConcealedTargetRungCredit
open AcornVerif.CurrentConcealedTargetRungChoice
open AcornVerif.CurrentCreditHorizon AcornVerif.CurrentExplorer AcornVerif.CurrentFirstChoice
open AcornVerif.CurrentFirstCredit AcornVerif.CurrentFrameSize AcornVerif.CurrentFrameSlots
open AcornVerif.CurrentPreReward

section Cold

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}

theorem loop_frame_kept (primitive : profile.usesHierarchy = false)
    (planning : PlanningSelection) (world : Kernel.World interface) (start : world.State)
    (young : 0 < config.tester.maturity) (early late : ℕ) (first : early = 0)
    (second : late = 1)
    (words : (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config
        criterion dimension planning)) start late).frame.words =
      (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config criterion
        dimension planning)) start early).frame.words)
    (symbols : (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config
        criterion dimension planning)) start late).frame.symbols =
      (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config criterion
        dimension planning)) start early).frame.symbols) :
    (laidAt (Agent.initial interface profile config criterion dimension planning) world start
        late).features =
      (laidAt (Agent.initial interface profile config criterion dimension planning) world start
        early).features := by
  subst first second
  have features := choose_features_congr
    (((Agent.initial interface profile config criterion dimension planning).choose .learnThenAct
      (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config criterion
        dimension planning)) start 0)).learn)
    (Agent.initial interface profile config criterion dimension planning) .learnThenAct
    .learnThenAct _ _ words symbols
    (young_bank primitive _ _ young)
    (cold_step_predictions (primitive_learns primitive) .learnThenAct _)
  exact (congrArg (fun memory : Agent interface profile config criterion dimension planning =>
    (memory.choose .learnThenAct (Kernel.perceptAt world (executedAgent (Agent.initial interface
      profile config criterion dimension planning)) start 1)).features)
    (loop_step (Agent.initial interface profile config criterion dimension planning) world start
      0)).trans features

end Cold

theorem craft_keeps :
    (physicalStep (physical witnessLive.world) (code .craftAxe)).map (fun world =>
        (world.body.inventory.wood, world.body.inventory.stone, world.body.inventory.food)) =
        some (0, 0, 0) ∧
      (physicalStep (physical witnessLive.world) (code .craftAxe)).map (fun world =>
        (world.body.inventory.gold, world.body.inventory.axe, world.body.inventory.boat)) =
        some (0, false, false) ∧
      (physicalStep (physical witnessLive.world) (code .craftAxe)).map (fun world =>
        (min (world.body.energy.val / 100) 10, world.harvested.isEmpty)) = some (10, true) := by
  decide +kernel

theorem first_step_body (target : Host.Position) (action : Kernel.Act Grid.interface)
    (crafts : Host.Action.fromIndex action.val = .craftAxe) :
    ∃ next, advance ⟨witnessLive.world.setGoal (.find target), witnessLive.carried⟩ action =
        some next ∧
      next.world.body.inventory = witnessLive.world.body.inventory ∧
      min (next.world.body.energy.val / 100) 10 = 10 ∧
      next.world.harvested.isEmpty = true := by
  have tracked := advance_physical
    ⟨witnessLive.world.setGoal (.find target), witnessLive.carried⟩ action
  have same : physicalStep (physical (witnessLive.world.setGoal (.find target))) action =
      physicalStep (physical witnessLive.world) (code .craftAxe) := by
    unfold physicalStep
    rw [crafts]
    rfl
  have kept := craft_keeps
  rw [← same, ← tracked] at kept
  cases stepped : advance ⟨witnessLive.world.setGoal (.find target), witnessLive.carried⟩
      action with
  | none =>
    rw [stepped] at kept
    cases kept.1
  | some next =>
    rw [stepped] at kept
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at kept
    obtain ⟨⟨wood, stone, food⟩, ⟨gold, axe, boat⟩, energy, unharvested⟩ := kept
    refine ⟨next, rfl, ?_, energy, unharvested⟩
    change (physical next.world).body.inventory = ⟨0, 0, 0, 0, false, false⟩
    cases held : (physical next.world).body.inventory with
    | mk heldWood heldStone heldFood heldGold heldAxe heldBoat =>
      rw [held] at wood stone food gold axe boat
      simp only at wood stone food gold axe boat
      subst wood stone food gold axe boat
      rfl

theorem first_step_sensed (target : Host.Position)
    (outside : ¬ InGoalBox target witnessLive.world.body.position.position)
    (action : Kernel.Act Grid.interface)
    (crafts : Host.Action.fromIndex action.val = .craftAxe) :
    ∃ next, advance ⟨witnessLive.world.setGoal (.find target), witnessLive.carried⟩ action =
        some next ∧
      sensed next.world = sensed (witnessLive.world.setGoal (.find target)) := by
  obtain ⟨next, stepped, inventory, energy, unharvested⟩ := first_step_body target action crafts
  refine ⟨next, stepped, ?_⟩
  obtain ⟨events, taken, -⟩ := advance_some _ next action stepped
  have still : (Host.Action.fromIndex action.val).direction = none := by
    rw [crafts]
    rfl
  have place := AcornVerif.CurrentStep.step_stays _ next.world _ events taken still
  have goal : next.world.goal = some (.find target) := (Host.World.step_goal _ _ _ _ taken).1
  have clock := Host.World.step_clock _ next.world _ events taken
  have unmet : (witnessLive.world.setGoal (.find target)).goalSatisfied = false :=
    Bool.eq_false_iff.mpr fun met => outside
      ((find_goal_iff (witnessLive.world.setGoal (.find target)) target rfl).mp met)
  have unmetNext : next.world.goalSatisfied = false :=
    Bool.eq_false_iff.mpr fun met => outside (by
      have inside := (find_goal_iff next.world target goal).mp met
      rw [place] at inside
      exact inside)
  have observed : next.world.observe = (witnessLive.world.setGoal (.find target)).observe :=
    observe_congr _ next.world place
      (fun position => by
        rw [tileKind_unharvested next.world unharvested,
          tileKind_unharvested _ Std.TreeMap.isEmpty_emptyc])
      ((occupancy_empty witness_unpopulated next.world).trans
        (occupancy_empty witness_unpopulated _).symm)
      (by
        change _ = min (witnessLive.world.body.energy.val / 100) 10
        rw [energy]
        decide)
      (Fin.ext (by
        rw [dayPhase_early next.world (by
            rw [clock]
            change (witnessLive.world.time + 1).toNat < _
            decide),
          dayPhase_early (witnessLive.world.setGoal (.find target)) (by
            change witnessLive.world.time.toNat < _
            decide)]))
      (by rw [find_task next.world target goal, find_task _ target rfl, unmet, unmetNext])
      inventory
  exact sensed_congr _ _ observed

theorem first_codes : ∀ index, index < 4 →
    rungRows.flatten.getD index 0 =
      ([Host.Action.craftAxe, .south, .east, .eat].getD index .wait).index.val := by
  decide +kernel

theorem first_actions (time : ℕ) (within : time < 4) :
    Host.Action.fromIndex (rungExplorer.actionAt time).val =
      [Host.Action.craftAxe, .south, .east, .eat].getD time .wait := by
  rw [rung_action time (by omega), first_codes time within]
  exact Host.Action.index_roundtrip _

theorem rung_start_actions (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (time : ℕ) (early : time ≤ 1) :
    Kernel.actionAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      time = rungExplorer.actionAt time :=
  cold_actions (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl planning
    (rungVisits planning index) (rungOrigin planning index) time
    (fun earlier sooner => by
      obtain rfl : earlier = 0 := by omega
      have start := start_reward (rungConstruction planning).profile.taskMode witnessLive
        index.1.1 7 (rungAgent planning) 0
      rw [Nat.zero_mul] at start
      exact (congrArg Binary32.isZero start).trans (by decide))

theorem rung_frame_kept (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (early late : ℕ) (first : early = 0) (second : late = 1) :
    (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) late).features =
      (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) early).features := by
  have step := rung_step_state planning index (rungAgent planning) 0 (by omega)
  rw [show 0 + 1 = late from by omega] at step
  have explored := rung_start_actions planning index 0 (by omega)
  have crafts := first_actions 0 (by omega)
  rw [← explored] at crafts
  generalize Kernel.actionAt (rungVisits planning index) (rungAgent planning)
    (rungOrigin planning index) 0 = action at step crafts
  have start : (Kernel.stateAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) 0).1 =
      some ⟨witnessLive.world.setGoal (.find index.1.1), witnessLive.carried⟩ := rfl
  rw [start] at step
  obtain ⟨next, stepped, same⟩ := first_step_sensed index.1.1 index.1.2 action crafts
  have alive : (Kernel.stateAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) late).1 = some next :=
    step.trans ((grid_step_live (rungConstruction planning).profile.taskMode
      ⟨witnessLive.world.setGoal (.find index.1.1), witnessLive.carried⟩ action).trans stepped)
  obtain ⟨words, symbols⟩ := percept_frame_congr
    (rungConstruction planning).profile.taskMode next
    ⟨witnessLive.world.setGoal (.find index.1.1), witnessLive.carried⟩ same
  have one : Kernel.perceptAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) late =
      (gridWorld witnessConfig (rungConstruction planning).profile.taskMode).percept
        (some next) :=
    (Kernel.visits_percept _ _ _ _ _ _).trans (congrArg
      (gridWorld witnessConfig (rungConstruction planning).profile.taskMode).percept alive)
  have zero : Kernel.perceptAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) early =
      (gridWorld witnessConfig (rungConstruction planning).profile.taskMode).percept
        (some ⟨witnessLive.world.setGoal (.find index.1.1), witnessLive.carried⟩) := by
    have begun := start_percept (rungConstruction planning).profile.taskMode witnessLive
      index.1.1 7 (rungAgent planning) 0
    rw [Nat.zero_mul, member, ← first] at begun
    exact begun
  have wordsEq : (Kernel.perceptAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) late).frame.words =
      (Kernel.perceptAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) early).frame.words := by
    rw [one, zero]
    exact words
  have symbolsEq : (Kernel.perceptAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) late).frame.symbols =
      (Kernel.perceptAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) early).frame.symbols := by
    rw [one, zero]
    exact symbols
  exact loop_frame_kept (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl planning
    (rungVisits planning index) (rungOrigin planning index) (by
      change 0 < 1000
      decide) early late first second wordsEq symbolsEq

theorem rung_frame_counts (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (early late : ℕ) (first : early = 0) (second : late = 1)
    (frame : SwiftTd.ActiveSet (rungConstruction planning).dimension) :
    (frame.indices.countP fun slot => decide (slot ∈ (laidAt
        (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) early).features.indices)) =
      frame.indices.countP fun slot => decide (slot ∈ (laidAt
        (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) late).features.indices) := by
  rw [rung_frame_kept planning index early late first second]

theorem second_step_repeat (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (first : FirstSuccess planning index (rungAgent planning) 0 2) :
    Kernel.actionAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      3 = rungExplorer.actionAt 1 :=
  rung_early_repeat planning index 1 first fun earlier before => by
    obtain rfl : earlier = 0 := by omega
    exact (rung_frame_counts planning index 0 1 rfl rfl _).le

theorem first_walk :
    tileTrace (some (physical witnessLive.world)) [.craftAxe, .south] =
      [some (32, 32), some (32, 33)] := by
  decide +kernel

theorem first_walk_tile :
    (physicalPath (physical witnessLive.world)
        (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) (0 + 1 + 1)).map
      (fun world => tile world.body.position.position) = some (32, 33) := by
  have taken : ∀ index, index < [Host.Action.craftAxe, .south].length →
      (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) (0 + index) =
        code ([Host.Action.craftAxe, .south].getD index .wait) := by
    intro index inside
    have small : index < 2 := inside
    apply Fin.ext
    change (rungExplorer.actionAt (0 * (7 + 1) + (0 + index))).val = _
    rw [Nat.zero_mul, Nat.zero_add, Nat.zero_add, rung_action index (by omega),
      first_codes index (by omega)]
    obtain rfl | rfl : index = 0 ∨ index = 1 := by omega
    all_goals rfl
  have traced := tileTrace_path (physical witnessLive.world)
    (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) [.craftAxe, .south] 0 taken
    1 (by decide)
  have start : physicalPath (physical witnessLive.world)
      (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) 0 =
        some (physical witnessLive.world) := rfl
  rw [start, first_walk] at traced
  exact (Option.some.inj traced).symm

theorem rung_early_state (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) : ∀ time, time ≤ 7 →
    (∀ earlier, earlier < time →
      Kernel.actionAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) earlier = rungExplorer.actionAt earlier) →
    (Kernel.stateAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
        time).1 =
      Kernel.path (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
        (member witnessLive index.1.1) (fun step => rungExplorer.actionAt step) time
  | 0, _, _ => rfl
  | time + 1, within, explored => by
    rw [rung_step_state planning index (rungAgent planning) time (by omega),
      rung_early_state planning index time (by omega)
        (fun earlier before => explored earlier (by omega)),
      explored time (by omega)]
    rfl

theorem second_step_success (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (near : tile index.1.1 ∈ box 3 (32, 33)) :
    FirstSuccess planning index (rungAgent planning) 0 2 := by
  have met := find_near_met (rungConstruction planning).profile.taskMode witnessLive 7
    (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) (0 + 1 + 1) (32, 33)
    first_walk_tile index.1.1 near
  have solved : ∃ visit, visit < 1 ∧ Kernel.SolvesOnVisit
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
      (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
      (executedAgent (Agent.initial Grid.interface (rungConstruction planning).profile
        (rungConstruction planning).config .discounted (rungConstruction planning).dimension
        planning)) visit index := by
    refine (cold_found_within (profile := (rungConstruction planning).profile) rfl rfl
      planning witnessLive rfl 7 1 index).mpr ⟨0, by omega, 0 + 1 + 1, by omega, by
        change 0 + 1 + 1 ≤ 7
        omega, ?_⟩
    rw [rung_explorer planning]
    exact met
  obtain ⟨visit, step, before, first⟩ :=
    rung_first_success planning index (rungAgent planning) 1 solved
  obtain rfl : visit = 0 := by omega
  rcases rung_first_visit planning index step first with rfl | rfl
  · exact first
  · exfalso
    obtain ⟨silent, -⟩ := rung_first_rewards planning index (rungAgent planning) 0 3 first
    obtain ⟨-, -, -, unmet, -⟩ := first
    refine unmet (0 + 1 + 1) (by omega) (by omega) ?_
    rw [rung_early_state planning index (0 * 8 + (0 + 1 + 1)) (by omega)
      fun earlier before =>
        cold_actions (profile := (rungConstruction planning).profile)
          (config := (rungConstruction planning).config)
          (dimension := (rungConstruction planning).dimension) rfl rfl planning
          (rungVisits planning index) (rungOrigin planning index) earlier
          (fun sooner soonest =>
            (congrArg Binary32.isZero (silent sooner (by omega))).trans (by decide)),
      show 0 * 8 + (0 + 1 + 1) = 0 + 1 + 1 from rfl,
      ← Kernel.path_congr _ _ (fun step => rungExplorer.actionAt (0 * (7 + 1) + step))
        (fun step => rungExplorer.actionAt step) (0 + 1 + 1) fun step _ => by
          rw [Nat.zero_mul, Nat.zero_add]]
    exact met

theorem second_step_near (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (first : FirstSuccess planning index (rungAgent planning) 0 2) :
    tile index.1.1 ∈ box 3 (32, 33) := by
  obtain ⟨-, -, -, -, met⟩ := first
  obtain ⟨live, reached, satisfied⟩ := met
  have goal : live.world.goal = some (.find index.1.1) :=
    visits_goal (rungConstruction planning).profile.taskMode witnessLive index.1.1 7
      (Kernel.actionAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index)) (0 * 8 + 2) live (by
          rw [← Kernel.stateAt_eq_path]
          exact reached)
  have near := box_of_goalBox index.1.1 live.world.body.position.position
    ((find_goal_iff live.world index.1.1 goal).mp satisfied)
  rw [rung_early_state planning index (0 * 8 + 2) (by omega)
      fun earlier before => rung_start_actions planning index earlier (by omega),
    show 0 * 8 + 2 = 0 + 1 + 1 from rfl,
    ← Kernel.path_congr _ _ (fun step => rungExplorer.actionAt (0 * (7 + 1) + step))
      (fun step => rungExplorer.actionAt step) (0 + 1 + 1) fun step _ => by
        rw [Nat.zero_mul, Nat.zero_add],
    member] at reached
  have track := path_physical (rungConstruction planning).profile.taskMode
    ⟨witnessLive.world.setGoal (.find index.1.1), witnessLive.carried⟩
    (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) (0 + 1 + 1)
  rw [reached, show physical (witnessLive.world.setGoal (.find index.1.1)) =
    physical witnessLive.world from rfl] at track
  have walked := first_walk_tile
  rw [← track] at walked
  have here : tile live.world.body.position.position = (32, 33) := Option.some.inj walked
  rw [here] at near
  exact near

theorem second_step_iff (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) :
    FirstSuccess planning index (rungAgent planning) 0 2 ↔ tile index.1.1 ∈ box 3 (32, 33) :=
  ⟨second_step_near planning index, second_step_success planning index⟩

theorem second_step_codes :
    Host.Action.fromIndex (rungExplorer.actionAt 1).val = .south ∧
      Host.Action.fromIndex (rungExplorer.actionAt 3).val = .eat :=
  ⟨first_actions 1 (by omega), first_actions 3 (by omega)⟩

theorem second_step_south (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (first : FirstSuccess planning index (rungAgent planning) 0 2) :
    Host.Action.fromIndex (Kernel.actionAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) 3).val = .south ∧
      Kernel.actionAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) 3 ≠ rungExplorer.actionAt 3 := by
  have south : Host.Action.fromIndex (Kernel.actionAt (rungVisits planning index)
      (rungAgent planning) (rungOrigin planning index) 3).val = .south :=
    (congrArg (fun action : Kernel.Act Grid.interface => Host.Action.fromIndex action.val)
      (second_step_repeat planning index first)).trans second_step_codes.1
  exact ⟨south, fun same => (by decide : Host.Action.south ≠ Host.Action.eat)
    ((south.symm.trans (congrArg
      (fun action : Kernel.Act Grid.interface => Host.Action.fromIndex action.val) same)).trans
        second_step_codes.2)⟩

def rungSecondStep : List (ℤ × ℤ) :=
  [(29, 36), (30, 36), (31, 36), (32, 36), (33, 36), (34, 36), (35, 36)]

theorem second_step_tiles (point : ℤ × ℤ) :
    point ∈ box 3 (32, 33) ∧ point ∉ box 3 (32, 32) ↔ point ∈ rungSecondStep := by
  obtain ⟨column, row⟩ := point
  simp only [mem_box, rungSecondStep, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  omega

theorem second_step_listed : ∀ point ∈ rungSecondStep, point ∈ rungFound := by
  decide +kernel

theorem second_step_repeats (planning : PlanningSelection) :
    ∃ counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index,
      counted.Nodup ∧ counted.length = 7 ∧
        counted.map (fun index => tile index.1.1) = rungSecondStep ∧
        (∀ index, index ∈ counted ↔ FirstSuccess planning index (rungAgent planning) 0 2) ∧
        ∀ index ∈ counted,
          Host.Action.fromIndex (Kernel.actionAt (rungVisits planning index)
              (rungAgent planning) (rungOrigin planning index) 3).val = .south ∧
            Kernel.actionAt (rungVisits planning index) (rungAgent planning)
              (rungOrigin planning index) 3 ≠ rungExplorer.actionAt 3 := by
  classical
  let admit : { point // point ∈ rungSecondStep } →
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
        7).Index :=
    fun point => ⟨⟨pointPosition point.1, by
      obtain ⟨own, far, -⟩ := found_listed point.1 (second_step_listed point.1 point.2)
      rw [member_tile, witness_start, own, mem_box]
      exact far⟩,
      (found_met (rungConstruction planning).profile.taskMode point.1
        (second_step_listed point.1 point.2)).elim fun _ met => ⟨_, met.2⟩⟩
  have own : ∀ point : { point // point ∈ rungSecondStep }, tile (admit point).1.1 = point.1 :=
    fun point => (found_listed point.1 (second_step_listed point.1 point.2)).1
  have injective : Function.Injective admit := fun first second same =>
    Subtype.ext (((own first).symm.trans (congrArg (fun target :
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
        7).Index => tile target.1.1) same)).trans (own second))
  have firsts : ∀ index, index ∈ rungSecondStep.attach.map admit ↔
      FirstSuccess planning index (rungAgent planning) 0 2 := by
    intro index
    rw [second_step_iff]
    constructor
    · intro listed
      obtain ⟨point, -, rfl⟩ := List.mem_map.mp listed
      rw [own point]
      exact ((second_step_tiles point.1).mpr point.2).1
    · intro near
      have far : tile index.1.1 ∉ box 3 (32, 32) := by
        rw [← witness_start]
        exact (member_tile witnessLive index.1.1).mp index.1.2
      have listed := (second_step_tiles (tile index.1.1)).mp ⟨near, far⟩
      refine List.mem_map.mpr ⟨⟨tile index.1.1, listed⟩, List.mem_attach _ _, ?_⟩
      exact Subtype.ext (Subtype.ext (tile_injective (own ⟨tile index.1.1, listed⟩)))
  refine ⟨rungSecondStep.attach.map admit,
    (List.nodup_attach.mpr (by decide)).map injective, by
      rw [List.length_map, List.length_attach]
      rfl, ?_, firsts, fun index listed =>
      second_step_south planning index ((firsts index).mp listed)⟩
  rw [List.map_map]
  exact (List.map_congr_left fun point _ => own point).trans
    (List.attach_map_subtype_val rungSecondStep)

end AcornVerif.CurrentConcealedTargetRungFirstVisit
