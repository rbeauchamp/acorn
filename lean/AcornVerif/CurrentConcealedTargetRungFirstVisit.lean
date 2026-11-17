/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetRungChoice

/-!
# On the first rung, the agent repeats the step that first met a target on its second step

Question 3 of rbeauchamp/acorn#232 asks whether, after a first success, the greedy choice away
from the route repeats one action.
`AcornVerif.CurrentConcealedTargetRungChoice.rung_early_repeat` names the agent's first action
after a first success on the first visit, under a hypothesis that compares how many slots its
frames share. This module proves that hypothesis for a first success at the first visit's second
step, and names seven members that have one. For each of them the rung's agent, at its first
decision after the step that learns the reward, takes again the action that met the target, a
step south, where its explorer's action at that time is to eat (`rung_second_repeats`,
`rung_second_codes`). It does not answer the question, which is of the decisions after that one.

Times count the agent's decisions from zero. A tile is a pair of a column and a row, and a step
south adds one to the row. A step's *frame* is the list of feature slots its percept turns on,
and the step lays a trace on each of them.

- **The first visit's walk.** Up to a first reward the agent's actions are its explorer's
  (`AcornVerif.CurrentExplorer.cold_actions`), whose first two are to craft an axe and to step
  south (`AcornVerif.CurrentConcealedTargetRungFinds.rungRows`). From the rung's start, where the
  body stands on the tile (32, 32), the craft leaves the body there and the step south takes it
  to (32, 33) (`first_walk`, which Lean's kernel evaluates over the executed world step).
- **The members.** A member's target is met where the body is within three tiles of it in each
  coordinate, and no member's target is within three tiles of the start. Every member whose
  target is within three tiles of (32, 33) has its first success at the first visit's second step
  (`rung_second_first`): the walk meets it there, and a first success on the first visit is at
  the second or the third step
  (`AcornVerif.CurrentConcealedTargetRungChoice.rung_first_visit`). `rungSecond` lists seven such
  targets, the tiles of row 36 from column 29 to column 35, each a target of
  `AcornVerif.CurrentConcealedTargetRungFinds.rungFound` (`second_listed`).
- **The first two frames are one frame.** A step's frame is decided by the words and the symbols
  of its percept's frame, by the feature bank and by the predictions the agent stored on the step
  before (`AcornVerif.CurrentFrameSlots.choose_features_congr`). The agent's first step changes
  none of them.
  - The percept. The craft at the start leaves the body where it stood
    (`AcornVerif.CurrentStep.step_stays`), with what it held and with its energy in the same
    bucket, and harvests no tile (`craft_keeps`, `first_step_body`). The day stays in its first
    phase, the target stays unmet, and the rung's world holds neither food nor deer. So after it
    the host shows the observation it showed at the start (`first_step_sensed`, from
    `AcornVerif.CurrentFrameSlots.observe_congr`). No tile's terrain is evaluated for this.
  - The bank. Before a unit matures, a step keeps the feature bank
    (`AcornVerif.CurrentFirstCredit.young_bank`).
  - The stored predictions. A cold agent's first step stores the predictions its fresh demons
    return, which are the ones it started with
    (`AcornVerif.CurrentFirstCredit.cold_step_predictions`).

  So a cold agent of a profile with no hierarchy lays at the time one the frame it laid at the
  time zero, wherever the two percepts' frames carry the same words and symbols
  (`loop_second_frame`), and the rung's agent does so in every member's visits
  (`rung_second_frame`).
- **The repeat.** `rung_early_repeat` asks that the frame the decision at the time three reads
  hold at least as many slots of the frame laid at the time one as of the frame laid at the time
  zero. Those two are one frame, so the two counts are equal (`rung_second_most`). So after a
  first success at the first visit's second step, the agent's action at the time three is its
  action at the time one (`rung_second_repeat`), which is the step south (`rung_second_south`).

What this does not say.

- Anything of a decision after the time three, and so nothing of whether the agent goes on
  repeating the step south. After the first reward the error of a later step need not be a zero
  word, and nothing is proved of those steps.
- Anything of a member first met at the first visit's third step. `rung_early_repeat` there
  compares the frame at the time four with the frames at the times zero to two, and after the
  step south the body sees other tiles: the comparison counts the slots two different frames
  share, which no theorem does.
- That the seven listed members are the only ones with a first success at the second step. That
  is *argued*: the tiles within three of (32, 33) and not within three of (32, 32) are those of
  row 36 from column 29 to column 35, and a target met at the second step is within three tiles
  of the body there. No theorem states it.
- Anything of another seed, world, profile, criterion, rate policy or step order.

Proof cost, and what breaks it. The kernel re-evaluates two world steps for `first_walk` and one
for `craft_keeps` each time this module is rebuilt (`docs/roadmap.md` records the timing and the
owner's decision to pay it). A change to the generator, to the world step or to the terrain can
make `first_walk`, `first_codes` or `craft_keeps` fail; the walk's tiles are then `tileTrace` of
the explorer's first two actions from the rung's world.

Trust. The statements are about executed binary32 words. Lean's kernel, its model of binary32
arithmetic and the agreement of the native operations with that model on finite operands remain
trusted, as for every proof of executed words in this library.
-/

namespace AcornVerif.CurrentConcealedTargetRungFirstVisit
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetFinding
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentConcealedTargetRungFinds AcornVerif.CurrentConcealedTargetRungCredit
open AcornVerif.CurrentConcealedTargetRungChoice
open AcornVerif.CurrentCreditHorizon AcornVerif.CurrentExplorer AcornVerif.CurrentFirstChoice
open AcornVerif.CurrentFirstCredit AcornVerif.CurrentFrameSlots AcornVerif.CurrentPreReward

/-! ## The second frame of a cold agent -/

section Cold

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}

/-- **A cold agent's second frame is its first, where the percept's frame is unchanged.** For a
profile with no hierarchy, from cold initialization, under a tester whose maturity threshold is
positive, in every world of the interface from every start: where the percepts at the times zero
and one carry frames with the same words and the same symbols, the agent lays at the time one the
frame it laid at the time zero. Its first step keeps the feature bank
(`AcornVerif.CurrentFirstCredit.young_bank`) and stores the predictions it started with
(`AcornVerif.CurrentFirstCredit.cold_step_predictions`). The two times are variables whose values
are hypotheses, so that a use at a closed run compares no term at a literal time: Lean's
elaborator would unfold the run to compare such terms. -/
theorem loop_second_frame (primitive : profile.usesHierarchy = false)
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

/-! ## Two readings of a run by unfolding

Each holds by unfolding definitions. They are stated as lemmas so that a proof about a closed run
rewrites with them at a variable time or state, and compares no closed term by unfolding it. -/

/-- The percept at a time of a run in visits is the world's percept of the world state at that
time: the visit's step count is not shown. -/
theorem visits_percept {interface : Interface} (world : Kernel.World interface)
    (start : world.State) (length : ℕ) (agent : Kernel.Agent interface)
    (origin : (Kernel.visits world start length).State) (time : ℕ) :
    Kernel.perceptAt (Kernel.visits world start length) agent origin time =
      world.percept (Kernel.stateAt (Kernel.visits world start length) agent origin time).1 :=
  rfl

/-- The grid world's step from a live state is the host's step of that state. -/
theorem grid_step_live {config : Host.WorldConfig} (mode : TaskFeatureMode) (live : Live config)
    (action : Kernel.Act Grid.interface) :
    (gridWorld config mode).step (some live) action = advance live action := rfl

/-! ## The first step changes nothing the host shows -/

/-- **The craft at the rung's start changes nothing the body holds.** After one step of the
rung's world from its start on the action to craft an axe, the body holds no wood, stone, food or
gold and neither an axe nor a boat, as at the start; its energy is in the top bucket, as at the
start; and no tile is harvested. Lean's kernel evaluates that one step over the executed world
step, in the world with its goal removed (`AcornVerif.CurrentGridWorld.physical`). -/
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

/-- In a member's world the same holds of the step from the start on an action whose code is
that of crafting an axe: the step is not refused, and it leaves the body's inventory, the top
bucket of its energy and the empty harvest log. The world's dynamics do not read the installed
goal (`AcornVerif.CurrentGridWorld.advance_physical`). -/
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
    obtain ⟨⟨wood, stone, food⟩, ⟨gold, axe, boat⟩, energy, bare⟩ := kept
    refine ⟨next, rfl, ?_, energy, bare⟩
    change (physical next.world).body.inventory = ⟨0, 0, 0, 0, false, false⟩
    cases held : (physical next.world).body.inventory with
    | mk heldWood heldStone heldFood heldGold heldAxe heldBoat =>
      rw [held] at wood stone food gold axe boat
      simp only at wood stone food gold axe boat
      subst wood stone food gold axe boat
      rfl

/-- **The first step leaves the observation.** In the world of a member whose target is not met
at the start, the step from the start on an action whose code is that of crafting an axe is not
refused, and after it the host shows the observation it showed at the start. The body stands
where it stood (`AcornVerif.CurrentStep.step_stays`) and holds what it held, its energy is in the
same bucket, no tile is harvested so every tile shows its base terrain
(`AcornVerif.CurrentFrameSlots.tileKind_bare`), the rung's world holds neither food nor deer, the
day is in its first phase before and after, and the target is unmet before and after. -/
theorem first_step_sensed (target : Host.Position)
    (outside : ¬ InGoalBox target witnessLive.world.body.position.position)
    (action : Kernel.Act Grid.interface)
    (crafts : Host.Action.fromIndex action.val = .craftAxe) :
    ∃ next, advance ⟨witnessLive.world.setGoal (.find target), witnessLive.carried⟩ action =
        some next ∧
      sensed next.world = sensed (witnessLive.world.setGoal (.find target)) := by
  obtain ⟨next, stepped, inventory, energy, bare⟩ := first_step_body target action crafts
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
        rw [tileKind_bare next.world bare, tileKind_bare _ Std.TreeMap.isEmpty_emptyc])
      (population_unique (by decide) _ _) (population_unique (by decide) _ _)
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

/-! ## The first two frames of the rung's agent -/

/-- The rung's agent takes its explorer's actions at the times zero and one: the percept at the
time zero carries no reward. -/
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

/-- **The rung's agent lays at the time one the frame it laid at the time zero.** In the visits of
every member of the rung's class. The agent's first action is its explorer's, to craft an axe,
which leaves the observation (`first_step_sensed`); so the percepts at the two times carry frames
with the same words and symbols, and `loop_second_frame` applies. The times are variables whose
values are hypotheses, as there. -/
theorem rung_second_frame (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (early late : ℕ) (first : early = 0) (second : late = 1) :
    (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) late).features =
      (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) early).features := by
  have step := rung_step_state planning index (rungAgent planning) 0 (by omega)
  rw [show 0 + 1 = late from by omega] at step
  have explored := rung_start_actions planning index 0 (by omega)
  generalize Kernel.actionAt (rungVisits planning index) (rungAgent planning)
    (rungOrigin planning index) 0 = action at step explored
  have crafts : Host.Action.fromIndex action.val = .craftAxe := by
    rw [explored, rung_action 0 (by omega)]
    decide +kernel
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
    (visits_percept _ _ _ _ _ _).trans (congrArg
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
  exact loop_second_frame (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl planning
    (rungVisits planning index) (rungOrigin planning index) (by
      change 0 < 1000
      decide) early late first second wordsEq symbolsEq

/-- Every frame holds as many slots of the frame the rung's agent laid at the time zero as of
the frame it laid at the time one: they are one frame (`rung_second_frame`). The times are
variables whose values are hypotheses, as there. -/
theorem rung_second_most (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (early late : ℕ) (first : early = 0) (second : late = 1)
    (frame : SwiftTd.ActiveSet (rungConstruction planning).dimension) :
    (frame.indices.countP fun slot => decide (slot ∈ (laidAt
        (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) early).features.indices)) ≤
      frame.indices.countP fun slot => decide (slot ∈ (laidAt
        (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) late).features.indices) :=
  le_of_eq (by rw [rung_second_frame planning index early late first second])

/-- **After a first success at the first visit's second step, the agent takes again the action
that met the target.** At a member's first success by the rung's agent at the second step of the
first visit, the agent's action at the time three, the first it takes after the step that learns
the reward, is the explorer's action at the time one, after which the target was met. This is
`AcornVerif.CurrentConcealedTargetRungChoice.rung_early_repeat` with its hypothesis on the frames
proved: the frames laid at the times zero and one are one frame (`rung_second_most`). -/
theorem rung_second_repeat (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (first : FirstSuccess planning index (rungAgent planning) 0 2) :
    Kernel.actionAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      3 = rungExplorer.actionAt 1 :=
  rung_early_repeat planning index 1 first fun earlier before => by
    obtain rfl : earlier = 0 := by omega
    exact rung_second_most planning index 0 1 rfl rfl _

/-! ## The members first met at the second step -/

/-- **The first visit's first two steps.** From the rung's start, the action to craft an axe
leaves the body on the tile (32, 32) and the step south then takes it to (32, 33). Lean's kernel
evaluates the two world steps over the executed world step, the terrain of the tile entered
included. -/
theorem first_walk :
    tileTrace (some (physical witnessLive.world)) [.craftAxe, .south] =
      [some (32, 32), some (32, 33)] := by
  decide +kernel

/-- The first two codes that `rungRows` lists are those of crafting an axe and of a step south. -/
theorem first_codes : ∀ index, index < 2 →
    rungRows.flatten.getD index 0 =
      ([Host.Action.craftAxe, .south].getD index .wait).index.val := by
  decide +kernel

/-- After the first two of the explorer's actions on the first visit, the body stands on the tile
(32, 33), in the world with its goal removed. -/
theorem first_walk_second :
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
      first_codes index small]
    rfl
  have traced := tileTrace_path (physical witnessLive.world)
    (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) [.craftAxe, .south] 0 taken
    1 (by decide)
  have start : physicalPath (physical witnessLive.world)
      (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) 0 =
        some (physical witnessLive.world) := rfl
  rw [start, first_walk] at traced
  exact (Option.some.inj traced).symm

/-- While the rung's agent takes its explorer's actions, the state of a member's first visit is
the state those actions drive the member's world to. -/
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

/-- The explorer of the rung's feature configuration is `rungExplorer`: the configuration's seed
is the seed of the rung's world. -/
theorem rung_explorer (planning : PlanningSelection) :
    Explorer.cold Grid.interface.actions (rungConstruction planning).config.seed =
      rungExplorer := rfl

/-- **A member whose target is within three tiles of (32, 33) is first met at the first visit's
second step.** The explorer's first two actions take the body to that tile (`first_walk_second`),
so the agent solves the member on the first visit
(`AcornVerif.CurrentConcealedTargetFinding.cold_found_within`). A first success on the first
visit is at the second or the third step
(`AcornVerif.CurrentConcealedTargetRungChoice.rung_first_visit`), and it is not at the third:
the agent's first two actions are the explorer's, so the target is met after the second. -/
theorem rung_second_first (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (near : tile index.1.1 ∈ box 3 (32, 33)) :
    FirstSuccess planning index (rungAgent planning) 0 2 := by
  have met := find_near_met (rungConstruction planning).profile.taskMode witnessLive 7
    (fun step => rungExplorer.actionAt (0 * (7 + 1) + step)) (0 + 1 + 1) (32, 33)
    first_walk_second index.1.1 near
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

/-- The explorer's action at the time one is the step south, and its action at the time three is
to eat. -/
theorem rung_second_codes :
    Host.Action.fromIndex (rungExplorer.actionAt 1).val = .south ∧
      Host.Action.fromIndex (rungExplorer.actionAt 3).val = .eat := by
  rw [rung_action 1 (by omega), rung_action 3 (by omega)]
  decide +kernel

/-- **A member whose target is within three tiles of (32, 33): the agent steps south again.** Its
first success is at the first visit's second step (`rung_second_first`), and the agent's action
at the time three is the step south, the action after which the target was met
(`rung_second_repeat`). The explorer's own action at the time three is to eat
(`rung_second_codes`). -/
theorem rung_second_south (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (near : tile index.1.1 ∈ box 3 (32, 33)) :
    FirstSuccess planning index (rungAgent planning) 0 2 ∧
      Host.Action.fromIndex (Kernel.actionAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) 3).val = .south :=
  ⟨rung_second_first planning index near,
    (congrArg (fun action : Kernel.Act Grid.interface => Host.Action.fromIndex action.val)
      (rung_second_repeat planning index (rung_second_first planning index near))).trans
        rung_second_codes.1⟩

/-- Seven tiles within three of (32, 33) and more than three from the start: those of row 36
from column 29 to column 35. -/
def rungSecond : List (ℤ × ℤ) :=
  [(29, 36), (30, 36), (31, 36), (32, 36), (33, 36), (34, 36), (35, 36)]

/-- Each tile of `rungSecond` is a tile of
`AcornVerif.CurrentConcealedTargetRungFinds.rungFound`, and lies within three tiles of
(32, 33). -/
theorem second_listed : ∀ point ∈ rungSecond,
    point ∈ rungFound ∧ (point.1 - 32).natAbs ≤ 3 ∧ (point.2 - 33).natAbs ≤ 3 := by
  decide +kernel

/-- **Seven members after whose first success the rung's agent steps south again.** There are
seven distinct members of the rung's class, with the targets of `rungSecond`, each first met at
the second step of the first visit, and after each the agent's action at the time three is the
step south, the action after which the target was met. It is the agent's first action after the
step that learns the reward, and the explorer's own action at that time is to eat
(`rung_second_codes`). -/
theorem rung_second_repeats (planning : PlanningSelection) :
    ∃ counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index,
      counted.Nodup ∧ counted.map (fun index => tile index.1.1) = rungSecond ∧
        ∀ index ∈ counted,
          FirstSuccess planning index (rungAgent planning) 0 2 ∧
            Host.Action.fromIndex (Kernel.actionAt (rungVisits planning index)
              (rungAgent planning) (rungOrigin planning index) 3).val = .south := by
  classical
  let admit : { point // point ∈ rungSecond } →
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
        7).Index :=
    fun point => ⟨⟨pointPosition point.1, by
      obtain ⟨own, far, -⟩ := found_listed point.1 (second_listed point.1 point.2).1
      rw [member_tile, witness_start, own, mem_box]
      exact far⟩,
      (found_met (rungConstruction planning).profile.taskMode point.1
        (second_listed point.1 point.2).1).elim fun _ met => ⟨_, met.2⟩⟩
  have own : ∀ point : { point // point ∈ rungSecond }, tile (admit point).1.1 = point.1 :=
    fun point => (found_listed point.1 (second_listed point.1 point.2).1).1
  have injective : Function.Injective admit := fun first second same =>
    Subtype.ext (((own first).symm.trans (congrArg (fun target :
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
        7).Index => tile target.1.1) same)).trans (own second))
  refine ⟨rungSecond.attach.map admit,
    (List.nodup_attach.mpr (by decide)).map injective, ?_, fun index listed => ?_⟩
  · rw [List.map_map]
    exact (List.map_congr_left fun point _ => own point).trans
      (List.attach_map_subtype_val rungSecond)
  · obtain ⟨point, -, rfl⟩ := List.mem_map.mp listed
    exact rung_second_south planning (admit point) (by
      rw [own point]
      exact mem_box.mpr (second_listed point.1 point.2).2)

end AcornVerif.CurrentConcealedTargetRungFirstVisit
