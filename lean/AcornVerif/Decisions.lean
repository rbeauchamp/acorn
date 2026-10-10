/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Regula.Contract
import Acorn.Host.Attempt
import AcornVerif.AgreementTelemetryPrecision
import AcornVerif.CurrentActions
import AcornVerif.CurrentAgent
import AcornVerif.CurrentCertificates
import AcornVerif.CurrentCheckpoint
import AcornVerif.CurrentExponential
import AcornVerif.CurrentRunner
import AcornVerif.CurrentSpawn
import AcornVerif.CurrentTemporal
import AcornVerif.CurrentTerrain
import AcornVerif.Endurance

/-!
# Decision contracts proved in the proof library

`Acorn.Decisions` registers the decisions of the executing library whose contracts follow
from Lean core alone. A contract here states a direction whose proof needs this library. The
legality of every stored lifetime total rests on the real-valued bounds of
`CurrentLifetime.stored_sum_legal`. What an accepted certificate establishes is a statement
about runs of the executed world step, proved in `CurrentCertificates`.

No certificate checker is complete: each kind below states what an accepted certificate
establishes, and a refused certificate establishes nothing. The blocked checker and the stance
checker carry the sound kind, with an accepted certificate as the witness, and so do the
constructors of their certificates. The replay checker keeps a requirement with no kind. The
walkable test is not a certificate checker, and it carries the two-way kind.

A function of this module with an argument or result type that depends on an earlier argument
states its kind in the forms that `Acorn.Decisions` describes: about the function applied to
every field of a structure of its arguments, and about `Regula.Dependent.isSome` or
`Regula.Dependent.isOk` of it where the result type depends on the input. A statement of what a
kind does not state stands beside it as a requirement with no kind: the value of an accepted
result, under the name of the kind with `_value`, or a set of refused inputs beside a one-way
kind, under the name of the kind with `_refused`. `payload_admit_value` and
`candidate_load_value` stand in the same way beside the requirements `payload_admit` and
`candidate_load`, which also keep no kind. `interest_potential_declared` states pointwise a
class of refused inputs that the two-way kind `interest_potential` also gives.
`world_enterable`, `tile_kind` and `terrain_read` keep their names beside the kinds of the
terrain: the verdict of an accepted entry, the refusal of a refused tile, and what the readers
of the terrain do with its result. `pay_and_act` and `perform_action` keep their names beside
the kinds of the paid actions: what an accepted paid action does with the energy, and where an
accepted move puts the body. `execute_prefix` states the safe path that the compiled fold
follows.

The round trips of the composed checkpoint admissions, the goal completion predicate, checked
translation and precision derivation are stated here because their theorems are in this
library, and so are the results of the spawn search and an accepted input of world generation,
the correspondence of the comparator with
the agent's attempt and the bounds
of the comparator's campaigns. The accepted inputs of the observation, of finishing and of the
fold, and the two-way kind of `Host.Released.environment`, are stated here because the
observation of their inputs succeeds by the terrain admission of `CurrentTerrain`. Each contract
states only what its theorem proves.

## Statements that keep no kind

A requirement with no kind is a statement that the Regula audit does not examine: that audit
checks only that its theorem is proved about the executing definition. Such a statement can
fix one direction only, and it need not show that both outcomes occur for its function.
Each docstring says what its statement gives and what it does not claim.

Sixteen functions of this module have a contract and no kind. The reasons are five. Two more,
`Agent.input` and `AgentConstruction.execute`, refuse no input, so they are no decisions, and
their statements say what their results are.

* The specification is a statement about runs of the executed world step, which the function
  runs: `Host.replayCertified`, `Host.ReplayCertificate.check` and
  `Host.World.advanceActions`. The step runs tests, and Regula's RG1009
  (https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/) refuses a kind whose
  specification reaches a test that its function runs. A kind needs the world step stated with
  propositions in the place of those tests.
* The input holds a state whose invariant names tests that the function runs, and Regula reads
  the type of the input of a specification (https://github.com/rbeauchamp/regula/issues/270):
  `Checkpoint.load`, and `Checkpoint.admitPayload` and `Checkpoint.loadCandidate`, whose
  specifications quantify over agent images whose learners name the stored-word check
  `NumericState.resumable` that the admissions run.
* The statement gives an accepted input of a host transition whose statement in
  `Acorn.Decisions` keeps no kind: `Host.World.observe`, `Host.Attempt.finish`,
  `Host.Attempt.complete` and `Host.World.initial`. No theorem states which observations or
  steps succeed or which configurations initialize, and a specification of the accepted inputs
  would name `Host.World.observe`, `Host.World.step` or `Host.World.tileKind`, which run tests
  that these functions run.
* The statement relates the comparator to the agent's attempt, or bounds where a campaign ends
  unfinished: `Host.BaselineAttempt.tick`, `Host.runBaselineCampaign` and
  `Host.runRandomBaseline`. Their acceptance is the world step's or world generation's, and no
  theorem states which steps succeed or which configurations initialize. The comparator's
  campaign also refuses as unfinished when its fuel runs out, and the random baseline also
  refuses at campaign admission and on an unbounded plan.
* The statement is about a result of the spawn search of world generation: `Host.countKindNear`,
  `Host.considerSpawn` and `Host.selectSpawn`. A specification of their accepted inputs would
  name `Host.World.tileKind`, which runs tests that they run. Each carries an accepted input.

Kinds for the functions of the first two reasons are remaining work of
https://github.com/rbeauchamp/acorn/issues/105.

## Tests that a specification does not share

No specification of a contract with a kind here reaches a test that its function runs: Regula's
RG1009 refuses such a contract, and `Acorn.Decisions` states the rule and lists the propositions
that take the place of the tests. The specification of `exp_saturation` names the strict order
`Binary32.Less`, and `Attained` names the ownership `Host.Inventory.Owns`. The specifications of
the requirements `payload_admit` and `candidate_load`, which keep no kind, likewise name the
resumable profile `FeatureProfile.Resumable` in the place of the test that the admissions run.

A specification also names no reader that its function calls where the data has constructors
or stored fields to state it by. `Attained` states a goal on the box indices, the inventory
fields and the clock of the world, with no observation, no count reader and no embedding of a
box position. `Harvests` states the tiles of a stance by equations on indices and coordinates
and the move by `Offset` and `Heads`, with no offset table, no facing position and no checked
translation. `squared_admit_exact` states the discrepancy of two words by their rational
values, with no unit map. A private lemma beside each connects the reader with the statement.

The kind of `sum_admit` names the writer `sumWords` of the form that it reads, which the
admission does not call.

The kinds of the terrain name the binary32 quotient of a coordinate by an octave scale, which the
generator computes: `Host.coordinateFloat`, `Binary32.div` and `Binary32.mul` are shared with it,
and none of them is a test. The kinds of its two readers also share `Host.WorldConfig.side`, which
the type of their world argument reads. The floor, the saturating cast and the checked successor
of the lattice coordinate are not shared: `CurrentTerrain.PastLast` bounds the exact value of the
quotient in their place.

The kinds of the paid actions share the same quotient through `CurrentTerrain.LatticeAdmits` and
the side of the box `Host.WorldConfig.side`, and the kind of `Host.payAndAct` also shares the
phase of the day `Host.World.dayPhase`, which the cost of an action reads; none of them is a
test. `CurrentActions.ActionAdmits` states the tile that an action reads by equations on the
coordinates and the box indices and by the constructors of the action and the direction, and
`CurrentActions.Cost` states the cost by the constructors of the action and the constants of
`FeatureConstants`. They name no direction table, offset table, checked translation, box
admission, facing position or cost function. The paid action compares the action with a
harvest by its derived `BEq`; the specification states that comparison as an equality.

RG1009 does not examine a statement with no kind, and statements with no kind here do reach
tests that their functions run. This module keeps no list of them, and the examples that follow
are not one. `replay_certified`, `replay_check` and `advance_actions` reach each test that the
world step runs, through `CurrentStep.Trace`. `task_observed` names `Host.Inventory.owns` in its
craft clause.

Regula counts only a contract of the function's own library toward a decision registration,
so the functions below carry no registration. The ownership audit requires each contract by
name instead, with a statement that still refers to the executing definition.
-/

namespace AcornVerif.Decisions
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime
open Acorn.Handcrafted.FeatureProfile (Resumable)

/-- A world configuration whose box reaches the last coordinate, with a noise scale of one.
The kernel evaluates the terrain of its tiles at that scale, so a tile of this configuration
is the accepted input of `terrain_walkable`. -/
def wide : Host.WorldConfig :=
  ⟨⟨0, ⟨2 ^ 63 - 1, by decide⟩, 1, 0, 0, 0, 0, ⟨0x3f800000⟩⟩, by decide, by decide⟩

/-- The position with the last horizontal coordinate. At the noise scale of `wide` the terrain
generator refuses it with a coordinate overflow, and the kernel evaluates that refusal. -/
def last : Host.Position := ⟨⟨2 ^ 63 - 1, by decide⟩, ⟨0, by decide⟩⟩

/-- The configuration of `wide` with another noise scale. -/
def wideAt (scale : Binary32) : Host.WorldConfig :=
  ⟨{ wide.raw with baseScale := scale }, wide.positiveSide, wide.positiveDay⟩

/-- A two-way decision from an acceptance equivalence about the function, an input that
satisfies the specification and one that does not. -/
private theorem decides.{u, v} {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
    {f : α → ρ} (iff : ∀ x, accepts (f x) ↔ spec x) (holds : ∃ x, spec x)
    (fails : ∃ x, ¬spec x) : Regula.Decides accepts spec f :=
  .of_iff iff (holds.elim fun x satisfied => ⟨x, (iff x).mpr satisfied⟩)
    (fails.elim fun x unsatisfied => ⟨x, fun accepted => unsatisfied ((iff x).mp accepted)⟩)

/-! ## Closed inputs of the kinds with a dependent type

The witnesses of a kind are inputs of the function. Each definition below is a closed value,
or makes a value from closed parts, and is an input or a part of an input of the kinds of
this module. -/

/-- A bank configuration with one unit. -/
def bank : Features.Config :=
  ⟨0, 1, by decide, ⟨1, by decide, by decide⟩, ⟨1, by decide, by decide, 0, .zero, .zero⟩⟩

/-- The feature space with one index. -/
def narrow : Dimension := ⟨1, by decide, ⟨0, rfl⟩, by decide⟩

/-- The resumable profile. -/
def resumable : FeatureProfile := ⟨.final, .perStep, .declared, .learned⟩

/-- A construction of the given profile over `bank` and `narrow`. -/
def construction (profile : FeatureProfile) : AgentConstruction :=
  ⟨profile, .discounted, .none, .learnThenAct, bank, narrow⟩

/-- A tile of `wide` from which a tree to the west can be harvested. -/
def stand : Host.BoxPosition wide := ⟨⟨0, by decide⟩, ⟨6, by decide⟩⟩

/-- The stance checker accepts the wood stance on `stand`, facing west. The kernel evaluates
the terrain of its three tiles. -/
private theorem stood : Host.stanceCertified wide stand .west .wood = true := by
  decide +kernel

/-- An admitted total holds the two input words unchanged: admission makes the record from
the words and the proof of their legality. -/
private theorem sum_written {quantity : Quantity} {words : SumWords}
    {record : SumCount quantity} (admitted : admitSum quantity words = some record) :
    words = sumWords record := by
  unfold admitSum SumCount.admit at admitted
  split at admitted
  · cases admitted
    rfl
  · exact nomatch admitted

/-- Total admission accepts exactly the words of a stored total of the receiving quantity. An
accepted pair is the words of the total that admission returns (`sum_written`), and the words
of every stored total are accepted (`CurrentImage.sum_roundtrip`). The accepted input is
the zero total of the reward quantity. The refused input is a count of one with the sum two
under the reward quantity, whose bound for one observation is one. `sum_admit_value` states
the total that admission returns. -/
theorem sum_admit : Regula.ExecutableContract admitSum (fun admit =>
    Regula.Decides (· = true)
      (fun input : Quantity × SumWords => ∃ record : SumCount input.1, input.2 = sumWords record)
      (Regula.Dependent.isSome fun input : Quantity × SumWords => admit input.1 input.2)) :=
  ⟨.of_iff
    (fun input => ⟨fun accepted => by
        obtain ⟨record, admitted⟩ := Option.isSome_iff_exists.mp accepted
        exact ⟨record, sum_written admitted⟩,
      fun ⟨record, written⟩ => by
        change (admitSum input.1 input.2).isSome = true
        rw [written, CurrentImage.sum_roundtrip]
        rfl⟩)
    ⟨(.reward, (0, ⟨0⟩)), by decide⟩
    ⟨(.reward, (1, ⟨0x4000000000000000⟩)), by decide⟩⟩

/-- Total admission returns the total whose words it reads (`CurrentImage.sum_roundtrip`).
A kind does not state the value of a result, so this statement is a requirement with no kind
beside the kind `sum_admit`. -/
theorem sum_admit_value : Regula.ExecutableContract admitSum (fun admit =>
    ∀ (quantity : Quantity) (record : SumCount quantity),
      admit quantity (sumWords record) = some record) :=
  ⟨fun _ => CurrentImage.sum_roundtrip⟩

/-! ## Certificate checkers -/

/-- A goal is achieved at a position, with an inventory, after an elapsed time: the position
is in the goal box of a reach goal, the inventory holds the count of a collect goal or owns
the tool of a craft goal, and the elapsed time is at least the duration of a survive goal. -/
def Achieved (goal : Host.Goal) (position : Host.Position) (inventory : Host.Inventory)
    (elapsed : UInt64) : Prop :=
  match goal with
  | .reach target => CurrentGoals.InGoalBox target position
  | .collect item count => count.toNat ≤ (inventory.count item).toNat
  | .craft tool => inventory.owns tool = true
  | .survive required => required.toNat ≤ elapsed.toNat

/-- An observation that the completion predicate accepts is the observation of an achieved
goal. -/
private theorem satisfied_achieved (goal : Host.Goal) (position : Host.Position)
    (inventory : Host.Inventory) (elapsed : UInt64)
    (satisfied : (goal.observe position inventory elapsed).satisfied = true) :
    Achieved goal position inventory elapsed := by
  cases goal with
  | reach target => exact (CurrentGoals.reach_satisfied_iff _ _ _ _).mp satisfied
  | collect item count => exact (CurrentGoals.collect_satisfied_iff _ _ _ _ _).mp satisfied
  | craft tool =>
    rw [CurrentGoals.craft_satisfied] at satisfied
    exact satisfied
  | survive required => exact (CurrentGoals.survive_satisfied_iff _ _ _ _).mp satisfied

/-- A goal is reached from a world within a cap: some run of at least one and at most `cap`
executed steps, from the world with the goal installed, ends in a world in which the goal is
achieved. The end is stated on the final position, inventory and elapsed time, and it names no
completion test. For a craft goal `Achieved` names the ownership test `Host.Inventory.owns`.
The run is a run of the executed world step, which is the subject of the claim. -/
def Reaches {config : Host.WorldConfig} (world : Host.World config) (goal : Host.Goal)
    (cap : Nat) : Prop :=
  ∃ (trace : List (Host.Action × Host.StepResult)) (final : Host.World config),
    CurrentStep.Trace (world.setGoal goal) trace final ∧ 0 < trace.length ∧
      trace.length ≤ cap ∧
      Achieved goal final.body.position.position final.body.inventory
        (final.time.toNat - final.goalStart.toNat).toUInt64

/-- An accepted action list shows that its goal is reached. -/
private theorem replay_reaches {config : Host.WorldConfig} {world : Host.World config}
    {goal : Host.Goal} {cap : Nat} {actions : List Host.Action}
    (accepted : Host.replayCertified world goal cap actions = true) : Reaches world goal cap := by
  obtain ⟨trace, final, run, nonempty, short, satisfied⟩ :=
    CurrentCertificates.replay_feasible accepted
  have installed : final.goal = some goal := by
    rw [CurrentCertificates.trace_goal run]
    rfl
  rw [CurrentGoals.goalSatisfied_eq final goal installed] at satisfied
  exact ⟨trace, final, run, nonempty, short, satisfied_achieved _ _ _ _ satisfied⟩

/-- The replay checker accepts only an action list that shows its goal reached from its world
within its cap (`CurrentCertificates.replay_feasible` with the four goal-family theorems): some
run of at least one and at most `cap` executed steps, from the world with the goal installed,
ends in a world in which the goal is achieved. It refuses the empty action list and every list
longer than the cap.

The statement keeps no kind. Its specification is a statement about runs of the executed world
step, which is the subject of the claim and which the checker runs. The step runs tests, among
them `Host.Inventory.owns`, `Host.TaskObservation.satisfied`, `Host.foodDue` and the
comparisons of actions, positions and tile kinds, and Regula's RG1009
(https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/) refuses a kind whose specification
reaches a test that its function runs. A kind needs the world step stated with propositions in
the place of those tests, which is remaining work of
https://github.com/rbeauchamp/acorn/issues/105.

**Not claimed:** completeness. The checker refuses an action list that does not itself reach
the goal, whether or not the goal can be reached. -/
theorem replay_certified : Regula.ExecutableContract @Host.replayCertified (fun check =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (goal : Host.Goal) (cap : Nat),
      (∀ actions : List Host.Action, @check config world goal cap actions = true →
        Reaches world goal cap) ∧
        @check config world goal cap [] = false ∧
        ∀ actions : List Host.Action, cap < actions.length →
          @check config world goal cap actions = false) :=
  ⟨fun _ _ _ cap =>
      ⟨fun _ => replay_reaches, by simp [Host.replayCertified],
        fun actions longer => by simp [Host.replayCertified, Nat.not_le.mpr longer]⟩⟩

/-- The goal box of a target is unreachable from a start tile: after any run of steps and goal
installations from a world whose body is on the start tile, the body is outside the goal box.
With `boat` false the statement covers only the runs that end without a boat. -/
def Unreachable (config : Host.WorldConfig) (boat : Bool) (target start : Host.Position) :
    Prop :=
  ∀ world final : Host.World config, world.body.position.position = start →
    CurrentGoals.Later world final → (boat = false → final.body.inventory.boat = false) →
      ¬CurrentGoals.InGoalBox target final.body.position.position

/-- The blocked checker accepts only a region that shows the goal box of its target
unreachable from its start tile (`CurrentCertificates.blocked_outside`), and it accepts the
empty region for a goal box that lies outside the box of the world.

**Not claimed:** completeness. The checker refuses every region that is not closed, whether or
not the goal box is reachable. -/
theorem region_blocked : Regula.ExecutableContract Host.regionBlocked (fun check =>
    Regula.DecidesSoundly (· = true)
      (fun input :
          (((Host.WorldConfig × Bool) × Host.Position) × List Host.Position) × Host.Position =>
        Unreachable input.1.1.1.1 input.1.1.1.2 input.1.1.2 input.2)
      (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry check))))) :=
  ⟨{ sound := fun input accepted world final located later boatless =>
       CurrentCertificates.blocked_outside (cells := input.1.2)
         (by rw [located]; exact accepted) later boatless
     accepted := ⟨((((⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩, true),
       ⟨⟨100, by decide⟩, ⟨100, by decide⟩⟩), []), ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩),
       by decide⟩ }⟩

/-- A movement action and the direction it heads in, stated by their constructors. -/
def Heads (action : Host.Action) (direction : Host.Direction) : Prop :=
  (action = .north ∧ direction = .north) ∨ (action = .south ∧ direction = .south) ∨
    (action = .east ∧ direction = .east) ∨ (action = .west ∧ direction = .west)

/-- The direction table gives the direction that a movement action heads in. -/
private theorem heads_direction {action : Host.Action} {direction : Host.Direction}
    (heads : Heads action direction) : action.direction = some direction := by
  rcases heads with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- No stance of a box with one tile is accepted: no tile of that box is behind the stance. -/
private theorem single_refused {config : Host.WorldConfig} (single : config.side = 1)
    (stance : Host.BoxPosition config) (direction : Host.Direction) (item : Host.Item) :
    Host.stanceCertified config stance direction item = false := by
  cases refused : Host.stanceCertified config stance direction item with
  | false => rfl
  | true =>
    obtain ⟨approach, moved, -⟩ := CurrentCertificates.stance_approach refused
    obtain ⟨column, row⟩ := CurrentCertificates.translate_some _ _ _ _ moved
    have approachColumn := approach.x.isLt
    have stanceColumn := stance.x.isLt
    have approachRow := approach.y.isLt
    have stanceRow := stance.y.isLt
    simp only [Host.BoxPosition.position] at column row
    cases direction <;> simp only [Host.Direction.delta] at column row <;> omega

/-- The offset of one move in a direction, stated by the constructors: north is one tile
toward negative y, south one toward positive y, east one toward positive x and west one toward
negative x. It names no offset table. -/
def Offset (direction : Host.Direction) (dx dy : Int) : Prop :=
  (direction = .north ∧ dx = 0 ∧ dy = -1) ∨ (direction = .south ∧ dx = 0 ∧ dy = 1) ∨
    (direction = .east ∧ dx = 1 ∧ dy = 0) ∨ (direction = .west ∧ dx = -1 ∧ dy = 0)

/-- The offset table `Host.Direction.delta` gives the offset that `Offset` states. -/
private theorem offset_delta {direction : Host.Direction} {dx dy : Int}
    (offset : Offset direction dx dy) : direction.delta = (dx, dy) := by
  rcases offset with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rfl

/-- What an accepted stance shows, in every world of the configuration, for the offset of one
move in the direction: a paid harvest from the stance, facing the direction, yields the item,
when the tile one offset ahead holds a standing tree for a wood stance; a paid move in the
direction from the tile one offset behind the stance enters it facing the resource; and the
tile one offset behind is in the box and can be entered. The tiles are stated by equations
on the stored box indices and on coordinates, the move by the constructors of the action and
the direction (`Heads`, `Offset`), with no checked translation, no direction table and no
offset table. A successful step is a hypothesis. -/
def Harvests (config : Host.WorldConfig) (stance : Host.BoxPosition config)
    (direction : Host.Direction) (item : Host.Item) : Prop :=
  ∀ dx dy : Int, Offset direction dx dy →
    (∀ (world next : Host.World config) (events : Host.StepResult) (ahead : Host.Position),
      ahead.x.val = stance.x.val + dx → ahead.y.val = stance.y.val + dy →
      world.body.position = stance → world.body.facing = direction →
      (item = .wood → world.tileKind ahead = .ok .tree) →
      world.step .harvest = .ok (next, events) → events.exhausted = false →
        events.harvested = some item ∧
          next.body.inventory = world.body.inventory.add item
            (if item == .wood && world.body.inventory.axe then 3 else 1)) ∧
    (∀ (world next : Host.World config) (action : Host.Action) (events : Host.StepResult),
      Heads action direction →
      (stance.x.val : Int) = world.body.position.x.val + dx →
      (stance.y.val : Int) = world.body.position.y.val + dy →
      world.step action = .ok (next, events) → events.exhausted = false →
        next.body.position = stance ∧ next.body.facing = direction) ∧
    ∃ approach : Host.BoxPosition config,
      (stance.x.val : Int) = approach.x.val + dx ∧ (stance.y.val : Int) = approach.y.val + dy ∧
        ∀ (world : Host.World config) (tile : Host.Position),
          tile.x.val = approach.x.val → tile.y.val = approach.y.val →
            world.enterable tile = .ok true

/-- An accepted stance has the properties of `Harvests`
(`CurrentCertificates.stance_harvest`, `stance_enter`, `stance_approach`,
`walkable_enterable`). -/
private theorem stance_sound {config : Host.WorldConfig} {stance : Host.BoxPosition config}
    {direction : Host.Direction} {item : Host.Item}
    (accepted : Host.stanceCertified config stance direction item = true) :
    Harvests config stance direction item := by
  intro dx dy offset
  have delta := offset_delta offset
  have first : direction.delta.1 = dx := by rw [delta]
  have second : direction.delta.2 = dy := by rw [delta]
  refine ⟨fun world next events ahead column row standing faced grown stepped paid => ?_,
    fun world next action events heads column row stepped paid => ?_, ?_⟩
  · have same : stance.facingPosition direction = ahead :=
      CurrentActions.position_ext (by rw [column, ← first]; rfl) (by rw [row, ← second]; rfl)
    exact CurrentCertificates.stance_harvest accepted world next events standing faced
      (by rw [same]; exact grown) stepped paid
  · exact CurrentCertificates.stance_enter accepted world next action events
      (heads_direction heads)
      (CurrentCertificates.translate_of_eq _ _ _ _ (by rw [first]; exact column)
        (by rw [second]; exact row)) stepped paid
  · obtain ⟨approach, moved, walkable⟩ := CurrentCertificates.stance_approach accepted
    obtain ⟨column, row⟩ := CurrentCertificates.translate_some _ _ _ _ moved
    refine ⟨approach, by rw [← first]; exact column, by rw [← second]; exact row,
      fun world tile tileColumn tileRow => ?_⟩
    have same : tile = approach.position := CurrentActions.position_ext tileColumn tileRow
    rw [same]
    exact CurrentCertificates.walkable_enterable world approach.position walkable

/-- The arguments of `Host.stanceCertified`, in order. -/
structure StanceCertified where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The stance tile. -/
  stance : Host.BoxPosition config
  /-- The direction the body faces. -/
  direction : Host.Direction
  /-- The item. -/
  item : Host.Item

/-- The stance checker accepts only a stance that `Harvests` holds of (`stance_sound`). The
specification states the geometry by constructors and stored indices; the checker reads the
offset table `Host.Direction.delta`, the facing position and the checked translation, and
`offset_delta` connects the table. The accepted input is the wood stance on `stand`, whose
three tiles the kernel evaluates. `stance_certified_refused` states a class of refused inputs.

**Not claimed:** completeness, or that a step succeeds. -/
theorem stance_certified : Regula.ExecutableContract Host.stanceCertified (fun check =>
    Regula.DecidesSoundly (· = true)
      (fun input : StanceCertified =>
        Harvests input.config input.stance input.direction input.item)
      (fun input : StanceCertified =>
        check input.config input.stance input.direction input.item)) :=
  ⟨{ sound := fun _ accepted => stance_sound accepted
     accepted := ⟨⟨wide, stand, .west, .wood⟩, stood⟩ }⟩

/-- The stance checker refuses every stance of a box with one tile, because no tile of that
box is behind the stance. A sound kind does not state a set of refused inputs, so this
statement is a requirement with no kind beside the kind `stance_certified`. -/
theorem stance_certified_refused : Regula.ExecutableContract Host.stanceCertified (fun check =>
    ∀ (config : Host.WorldConfig) (stance : Host.BoxPosition config)
      (direction : Host.Direction) (item : Host.Item),
      config.side = 1 → check config stance direction item = false) :=
  ⟨fun _ stance direction item single => single_refused single stance direction item⟩

/-- Replay checking returns a certificate only for an action list that shows its goal reached
(`replay_certified` states the relation), and it refuses the empty action list. The statement
names the relation and not the Boolean checker that the constructor calls.

The statement keeps no kind. Its specification is a statement about runs of the executed world
step, which is the subject of the claim and which the checker runs. The step runs tests, among
them `Host.Inventory.owns`, `Host.TaskObservation.satisfied`, `Host.foodDue` and the
comparisons of actions, positions and tile kinds, and Regula's RG1009
(https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/) refuses a kind whose specification
reaches a test that its function runs. A kind needs the world step stated with propositions in
the place of those tests, which is remaining work of
https://github.com/rbeauchamp/acorn/issues/105. -/
theorem replay_check : Regula.ExecutableContract @Host.ReplayCertificate.check (fun check =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (goal : Host.Goal) (cap : Nat),
      (∀ actions : List Host.Action, (@check config world goal cap actions).isSome = true →
        Reaches world goal cap) ∧
        @check config world goal cap [] = none) :=
  ⟨fun _ world goal cap =>
      ⟨fun actions present => by
          obtain ⟨certificate, -⟩ := Option.isSome_iff_exists.mp present
          exact replay_reaches certificate.accepted,
        by simp [Host.ReplayCertificate.check, Host.replayCertified]⟩⟩

/-- The arguments of `Host.BlockedCertificate.check`, in order. -/
structure BlockedCheck where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- Whether the runs may end with a boat. -/
  boat : Bool
  /-- The target of the goal box. -/
  target : Host.Position
  /-- The start tile. -/
  start : Host.Position
  /-- The cells of the region. -/
  cells : List Host.Position

/-- Blocked checking returns a certificate only for a region that shows the goal box
unreachable from the start tile (`CurrentCertificates.blocked_outside`). The specification
names the unreachability relation and not the Boolean checker. The accepted input is the one
of `region_blocked`: the empty region for a goal box outside the box of the world.
`blocked_check_refused` states a class of refused inputs. -/
theorem blocked_check : Regula.ExecutableContract Host.BlockedCertificate.check (fun check =>
    Regula.DecidesSoundly (· = true)
      (fun input : BlockedCheck => Unreachable input.config input.boat input.target input.start)
      (Regula.Dependent.isSome fun input : BlockedCheck =>
        check input.config input.boat input.target input.start input.cells)) :=
  ⟨{ sound := fun input present world final located later boatless => by
       have present : (Host.BlockedCertificate.check input.config input.boat input.target
         input.start input.cells).isSome = true := present
       obtain ⟨certificate, -⟩ := Option.isSome_iff_exists.mp present
       exact CurrentCertificates.blocked_outside (cells := certificate.cells)
         (by rw [located]; exact certificate.accepted) later boatless
     accepted := ⟨⟨⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩, true,
       ⟨⟨100, by decide⟩, ⟨100, by decide⟩⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, []⟩,
       by decide⟩ }⟩

/-- Blocked checking refuses the region that holds only the start tile. A sound kind does not
state a set of refused inputs, so this statement is a requirement with no kind beside the kind
`blocked_check`. -/
theorem blocked_check_refused : Regula.ExecutableContract Host.BlockedCertificate.check
    (fun check =>
      ∀ (config : Host.WorldConfig) (boat : Bool) (target start : Host.Position),
        check config boat target start [start] = none) :=
  ⟨fun _ _ _ _ => by simp [Host.BlockedCertificate.check, Host.regionBlocked, Host.inRegion]⟩

/-- The arguments of `Host.StanceCertificate.check`, in order. -/
structure StanceCheck where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The item. -/
  item : Host.Item
  /-- The stance tile. -/
  stance : Host.BoxPosition config
  /-- The direction the body faces. -/
  direction : Host.Direction

/-- Stance checking returns a certificate only for a stance that `Harvests` holds of
(`stance_certified` states the relation). The specification names the relation and not the
Boolean checker. The accepted input is the one of `stance_certified`.
`stance_check_refused` states a class of refused inputs. -/
theorem stance_check : Regula.ExecutableContract Host.StanceCertificate.check (fun check =>
    Regula.DecidesSoundly (· = true)
      (fun input : StanceCheck => Harvests input.config input.stance input.direction input.item)
      (Regula.Dependent.isSome fun input : StanceCheck =>
        check input.config input.item input.stance input.direction)) :=
  ⟨{ sound := fun input present => by
       have present : (Host.StanceCertificate.check input.config input.item input.stance
         input.direction).isSome = true := present
       obtain ⟨certificate, built⟩ := Option.isSome_iff_exists.mp present
       have accepted : Host.stanceCertified input.config input.stance input.direction
           input.item = true := by
         unfold Host.StanceCertificate.check at built
         split at built
         · assumption
         · exact absurd built (by simp)
       exact stance_certified.evidence.sound ⟨input.config, input.stance, input.direction,
         input.item⟩ accepted
     accepted := ⟨⟨wide, .wood, stand, .west⟩,
       Option.isSome_iff_exists.mpr
         ⟨⟨stand, .west, stood⟩, dite_eq_left_of_eq_true (eq_true stood)⟩⟩ }⟩

/-- Stance checking refuses every stance of a box with one tile. A sound kind does not state a
set of refused inputs, so this statement is a requirement with no kind beside the kind
`stance_check`. -/
theorem stance_check_refused : Regula.ExecutableContract Host.StanceCertificate.check
    (fun check =>
      ∀ (config : Host.WorldConfig) (item : Host.Item) (stance : Host.BoxPosition config)
        (direction : Host.Direction),
        config.side = 1 → check config item stance direction = none) :=
  ⟨fun _ item stance direction single => by
    simp [Host.StanceCertificate.check, single_refused single stance direction item]⟩

/-- A tile that the body may enter in every world of a configuration is walkable: the empty
world has no boat, so the terrain of the tile is not water. -/
private theorem enterable_walkable {config : Host.WorldConfig} {tile : Host.Position}
    (enterable : ∀ world : Host.World config, world.enterable tile = .ok true) :
    Host.walkableTile config tile = true := by
  have empty := enterable (Host.World.empty config)
  rw [CurrentStep.enterable_static] at empty
  unfold Host.walkableTile
  cases located : Host.terrain tile config.raw.seed config.raw.baseScale with
  | error refusal =>
    rw [located] at empty
    exact absurd empty (by simp [Except.map])
  | ok kind =>
    rw [located] at empty
    cases kind <;>
      simp_all [Except.map, CurrentStep.passable, Host.TileKind.walkable, Host.World.empty]

/-- The walkable test accepts exactly a tile that the body may enter in every world of the
configuration, with or without a boat (`CurrentCertificates.walkable_enterable`, and
`enterable_walkable` for the converse). Enterability is the executed test of the world, which
is the subject of the claim. The accepted input is a tile of the wide world, and the refused
input is the last coordinate, whose terrain the generator refuses. -/
theorem terrain_walkable : Regula.ExecutableContract Host.walkableTile (fun test =>
    Regula.Decides (· = true)
      (fun input : Host.WorldConfig × Host.Position =>
        ∀ world : Host.World input.1, world.enterable input.2 = .ok true)
      (Function.uncurry test)) :=
  ⟨.of_iff
    (fun input =>
      ⟨fun accepted world => CurrentCertificates.walkable_enterable world input.2 accepted,
        enterable_walkable⟩)
    ⟨(wide, ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩), by decide +kernel⟩
    ⟨(wide, last), by decide +kernel⟩⟩

/-! ## Checkpoint admissions

Each admission below composes the admissions of its parts, and its round trip is proved in
`CurrentCheckpoint`. Each statement gives the inputs that an admission accepts: an accepted input
is the written form of the value that it returns (`payload_written`, `candidate_written`), and
the value that it returns is a separate statement, under its name with `_value`. Neither keeps a
kind, for the reason `payload_admit` gives. -/

/-- An admitted payload is the payload of the image that admission returns, and the receiving
profile is resumable. Header admission fixes every header word but the clock and the reward
rate (`admitHeader_checks`); the image format reads exactly the encodings of images, so the
body is the image's encoding (`CurrentImage.imageFormat_exact`); and admission requires the
header's clock and rate words to be the image's. -/
private theorem payload_written {construction : AgentConstruction}
    {payload : Payload} {image : construction.Image}
    (admitted : admitPayload construction payload = .ok image) :
    Resumable construction.profile ∧ payload = imagePayload construction image := by
  obtain ⟨⟨version, capacity, learners, seed, clock, criterion, gain, tilings, units, supported,
    order⟩, body⟩ := payload
  unfold admitPayload at admitted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    at admitted
  split at admitted <;> try contradiction
  rename_i rate headerAdmitted
  split at admitted <;> try contradiction
  rename_i read rest decoded
  split at admitted <;> try contradiction
  rename_i checks
  cases admitted
  obtain ⟨empty, clockWord, gainWord⟩ := checks
  subst empty
  have body := (CurrentImage.imageFormat_exact construction).canonical _ _ _ decoded
  rw [List.append_nil] at body
  subst body
  obtain ⟨rfl, rfl, rateAdmitted, rfl, rfl, rfl, enabled, rfl, rfl, unitsCount, rfl⟩ :=
    (admitHeader_checks construction _ rate).mp headerAdmitted
  have resumable : Resumable construction.profile :=
    (FeatureProfile.checkpoint_iff _).mp enabled
  have countWord : construction.config.units.count.toUInt32.toNat =
      construction.config.units.count :=
    Nat.mod_eq_of_lt (by have := construction.config.units.bounded; omega)
  have unitsWord : units = construction.config.units.count.toUInt32 :=
    UInt32.toNat_inj.mp (unitsCount.trans countWord.symm)
  subst unitsWord clockWord gainWord
  refine ⟨resumable, ?_⟩
  simp only [imagePayload, resumable, ↓reduceIte]

/-- An accepted byte list is the encoding of the payload of the image that loading returns,
and the receiving profile is resumable: decoding reads only the bytes that the writer writes
(`Checkpoint.decode_written`), and payload admission accepts only the payload of its image
(`payload_written`). -/
private theorem candidate_written {construction : AgentConstruction} {bytes : List UInt8}
    {image : construction.Image} (loaded : loadCandidate construction bytes = .ok image) :
    Resumable construction.profile ∧
      bytes = encode (imagePayload construction image) := by
  unfold loadCandidate at loaded
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at loaded
  split at loaded <;> try contradiction
  split at loaded <;> try contradiction
  split at loaded <;> try contradiction
  split at loaded <;> try contradiction
  rename_i payload decoded
  obtain ⟨resumable, written⟩ := payload_written loaded
  exact ⟨resumable, by rw [decode_written _ _ decoded, written]⟩

/-- Payload admission accepts exactly the payloads of the agent images of a resumable
construction (`CurrentCheckpoint.image_roundtrip`, and `payload_written` for the converse). -/
private theorem payload_iff (construction : AgentConstruction)
    (payload : Payload) :
    (admitPayload construction payload).isOk = true ↔
      ∃ image : construction.Image, Resumable construction.profile ∧
        payload = imagePayload construction image := by
  constructor
  · intro accepted
    cases admitted : admitPayload construction payload with
    | error refusal =>
      rw [admitted] at accepted
      exact absurd accepted Bool.false_ne_true
    | ok image => exact ⟨image, payload_written admitted⟩
  · rintro ⟨image, supported, written⟩
    rw [written, CurrentCheckpoint.image_roundtrip construction image
      ((FeatureProfile.checkpoint_iff _).mpr supported)]
    rfl

/-- Payload admission accepts exactly the payloads of the agent images of a resumable
construction (`payload_iff`). `payload_admit_value` states the image that it returns.

The statement keeps no kind. Regula v0.10.0 refuses the kind under RG1009
(https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/): an agent image holds learners
whose admission names the stored-word check `NumericState.resumable`, which the admission
runs, and the rule reads the type of the input of the specification
(https://github.com/rbeauchamp/regula/issues/270). The specification names none of those
tests. -/
theorem payload_admit : Regula.ExecutableContract admitPayload (fun admit =>
    ∀ (construction : AgentConstruction) (payload : Payload),
      (admit construction payload).isOk = true ↔
        ∃ image : construction.Image, Resumable construction.profile ∧
          payload = imagePayload construction image) :=
  ⟨payload_iff⟩

/-- Payload admission returns the image whose payload it reads
(`CurrentCheckpoint.image_roundtrip`). A kind does not state the value of a result, so this
statement is a requirement with no kind beside the requirement `payload_admit`, which also keeps
no kind. -/
theorem payload_admit_value : Regula.ExecutableContract admitPayload (fun admit =>
    ∀ (construction : AgentConstruction) (image : construction.Image),
      construction.profile.checkpointSupported = true →
        admit construction (imagePayload construction image) = .ok image) :=
  ⟨CurrentCheckpoint.image_roundtrip⟩

/-- Candidate loading accepts exactly the encoded payloads of the agent images of a resumable
construction (`CurrentCheckpoint.candidate_roundtrip`, and `candidate_written` for the
converse). -/
private theorem candidate_iff (construction : AgentConstruction) (bytes : List UInt8) :
    (loadCandidate construction bytes).isOk = true ↔
      ∃ image : construction.Image, Resumable construction.profile ∧
        bytes = encode (imagePayload construction image) := by
  constructor
  · intro accepted
    cases loaded : loadCandidate construction bytes with
    | error refusal =>
      rw [loaded] at accepted
      exact absurd accepted Bool.false_ne_true
    | ok image => exact ⟨image, candidate_written loaded⟩
  · rintro ⟨image, supported, written⟩
    rw [written, CurrentCheckpoint.candidate_roundtrip construction image
      ((FeatureProfile.checkpoint_iff _).mpr supported)]
    rfl

/-- Candidate loading accepts exactly the encoded payloads of the agent images of a resumable
construction (`candidate_iff`). `candidate_load_value` states the image that it returns.

The statement keeps no kind, for the reason `payload_admit` gives: RG1009 reads the learner
check that an agent image's type names and that loading runs. -/
theorem candidate_load : Regula.ExecutableContract loadCandidate (fun load =>
    ∀ (construction : AgentConstruction) (bytes : List UInt8),
      (load construction bytes).isOk = true ↔
        ∃ image : construction.Image, Resumable construction.profile ∧
          bytes = encode (imagePayload construction image)) :=
  ⟨candidate_iff⟩

/-- Candidate loading returns the image whose encoded payload it reads
(`CurrentCheckpoint.candidate_roundtrip`). A kind does not state the value of a result, so
this statement is a requirement with no kind beside the requirement `candidate_load`, which also
keeps no kind. -/
theorem candidate_load_value : Regula.ExecutableContract loadCandidate (fun load =>
    ∀ (construction : AgentConstruction) (image : construction.Image),
      construction.profile.checkpointSupported = true →
        load construction (encode (imagePayload construction image)) = .ok image) :=
  ⟨CurrentCheckpoint.candidate_roundtrip⟩

/-! ## World and goal tests -/

/-- Checked translation accepts exactly an origin and two offsets whose exact sums are the
coordinates of a position (`CurrentCertificates.translate_some`, `translate_of_eq`). -/
theorem position_translate : Regula.ExecutableContract Host.Position.translate (fun translate =>
    Regula.Decides (·.isSome = true)
      (fun input : (Host.Position × Int) × Int =>
        ∃ tile : Host.Position, tile.x.val = input.1.1.x.val + input.1.2 ∧
          tile.y.val = input.1.1.y.val + input.2)
      (Function.uncurry (Function.uncurry translate))) :=
  ⟨.of_iff
    (fun input =>
      ⟨fun accepted => by
        obtain ⟨tile, moved⟩ := Option.isSome_iff_exists.mp accepted
        exact ⟨tile, CurrentCertificates.translate_some input.1.1 tile input.1.2 input.2 moved⟩,
      fun ⟨tile, column, row⟩ => by
        change (input.1.1.translate input.1.2 input.2).isSome = true
        rw [CurrentCertificates.translate_of_eq input.1.1 tile input.1.2 input.2 column row]
        rfl⟩)
    ⟨((⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, 0), 0), by decide⟩
    ⟨((⟨⟨2 ^ 63 - 1, by decide⟩, ⟨0, by decide⟩⟩, 1), 0), by decide⟩⟩

/-- The completion predicate accepts the observation that `Goal.observe` produces for every
achieved goal (`CurrentGoals.reach_satisfied_iff`, `collect_satisfied_iff`,
`survive_satisfied_iff`, `craft_satisfied`), and it refuses the observation of no goal.

**Not claimed:** soundness for an observation that `Goal.observe` did not produce. The four
theorems state the converse for the observations it does produce. -/
theorem task_satisfied : Regula.ExecutableContract Host.TaskObservation.satisfied
    (Regula.DecidesCompletely (· = true)
      (fun observation => ∃ goal position inventory elapsed,
        Achieved goal position inventory elapsed ∧
          observation = goal.observe position inventory elapsed)) :=
  ⟨{ complete := fun observation ⟨goal, position, inventory, elapsed, achieved, same⟩ => by
       rw [same]
       cases goal with
       | reach target =>
         exact (CurrentGoals.reach_satisfied_iff target position inventory elapsed).mpr achieved
       | collect item count =>
         exact (CurrentGoals.collect_satisfied_iff item count position inventory elapsed).mpr
           achieved
       | craft tool =>
         rw [CurrentGoals.craft_satisfied]
         exact achieved
       | survive required =>
         exact (CurrentGoals.survive_satisfied_iff required position inventory elapsed).mpr
           achieved
     refused := ⟨.none, by decide⟩ }⟩

/-- The completion predicate, on the observation of each goal family, is exactly: a position
in the goal box for a reach goal, an inventory that holds the count for a collect goal and
an elapsed time of at least the duration for a survive goal; for a craft goal it is the
ownership of the tool (`CurrentGoals.reach_satisfied_iff`, `collect_satisfied_iff`,
`survive_satisfied_iff`, `craft_satisfied`). These equivalences are both directions for the
observations that `Goal.observe` produces; `task_satisfied` states the kind. -/
theorem task_observed : Regula.ExecutableContract Host.TaskObservation.satisfied
    (fun satisfied =>
    (∀ (target position : Host.Position) (inventory : Host.Inventory) (elapsed : UInt64),
        satisfied ((Host.Goal.reach target).observe position inventory elapsed) = true ↔
          CurrentGoals.InGoalBox target position) ∧
      (∀ (item : Host.Item) (count : UInt32) (position : Host.Position)
        (inventory : Host.Inventory) (elapsed : UInt64),
        satisfied ((Host.Goal.collect item count).observe position inventory elapsed) = true ↔
          count.toNat ≤ (inventory.count item).toNat) ∧
      (∀ (required : UInt64) (position : Host.Position) (inventory : Host.Inventory)
        (elapsed : UInt64),
        satisfied ((Host.Goal.survive required).observe position inventory elapsed) = true ↔
          required.toNat ≤ elapsed.toNat) ∧
      ∀ (tool : Host.Craftable) (position : Host.Position) (inventory : Host.Inventory)
        (elapsed : UInt64),
        satisfied ((Host.Goal.craft tool).observe position inventory elapsed) =
          inventory.owns tool) :=
  ⟨⟨CurrentGoals.reach_satisfied_iff, CurrentGoals.collect_satisfied_iff,
    CurrentGoals.survive_satisfied_iff, CurrentGoals.craft_satisfied⟩⟩

/-- The exponential classifier sends a word to reduction, with no saturated result, exactly
when the word is finite and strictly between the underflow and the overflow thresholds
(`CurrentExponential.expSaturation_ends`). The strict order is the proposition
`Binary32.Less`, which names no test, and `Binary32.less_iff` connects it with the word
comparison that the classifier runs. -/
theorem exp_saturation : Regula.ExecutableContract Portable.expSaturation
    (Regula.Decides (· = none)
      (fun value : Binary32 => value.Finite ∧
        (Binary32.mk Acorn.Constants.expUnderflowBits).Less value ∧
          value.Less ⟨Acorn.Constants.expOverflowBits⟩)) :=
  ⟨{ sound := fun value admitted => by
       have ends := CurrentExponential.expSaturation_ends value
       rw [admitted] at ends
       exact ⟨ends.1, (Binary32.less_iff _ _).mp ends.2.1, (Binary32.less_iff _ _).mp ends.2.2⟩
     accepted := ⟨.zero, by decide⟩
     complete := fun value ⟨finite, above, below⟩ => by
       have above := (Binary32.less_iff _ _).mpr above
       have below := (Binary32.less_iff _ _).mpr below
       have ends := CurrentExponential.expSaturation_ends value
       cases saturated : Portable.expSaturation value with
       | none => rfl
       | some result =>
         rw [saturated] at ends
         have number : value.isNaN = false := by
           cases nan : value.isNaN with
           | false => rfl
           | true =>
             rw [Binary32.isNaN_eq_magnitude] at nan
             have high := of_decide_eq_true nan
             unfold Binary32.Finite at finite
             omega
         simp [number, above, below] at ends
     refused := ⟨⟨0x7fc00000⟩, by decide⟩ }⟩

/-- Rank selection returns an index only when the cumulative count through some bin reaches
the target rank (`Endurance.rankIndex_spec`, which also states that no earlier bin does).

**Not claimed:** completeness. No theorem states that a reachable rank is always found. -/
theorem rank_index : Regula.ExecutableContract Host.Endurance.rankIndex (fun index =>
    Regula.DecidesSoundly (·.isSome = true)
      (fun input : ((Nat × Nat) × Nat) × List Nat =>
        ∃ i, input.1.1.1 ≤ input.1.1.2 * (input.1.2 + (input.2.take (i + 1)).sum))
      (Function.uncurry (Function.uncurry (Function.uncurry index)))) :=
  ⟨{ sound := fun input accepted => by
       obtain ⟨i, found⟩ := Option.isSome_iff_exists.mp accepted
       exact ⟨i, (Endurance.rankIndex_spec input.1.1.1 input.1.1.2 input.1.2 input.2 i found).1⟩
     accepted := ⟨(((0, 1), 0), [0]), by decide⟩ }⟩

/-! ## Refusals of the terrain

The terrain generator and its two readers in the world refuse a position exactly when the value
noise reaches a lattice coordinate with no successor, `CurrentTerrain.LatticeAdmits`, which states
the condition on the exact value of the quotient of each coordinate by each octave scale. The
witnesses of the three kinds are the last coordinate at the noise scales of two and of one half.
A generator that read every scale as one would fail each kind: at the scale one it refuses the
last coordinate. -/

/-- The arguments of `Host.World.tileKind` and `Host.World.enterable`, in order. -/
structure WorldTile where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The world. -/
  world : Host.World config
  /-- The tile. -/
  position : Host.Position

/-- The terrain generator admits exactly a position whose value noise has a lattice successor at
each of the four octave scales of the base scale (`CurrentTerrain.terrain_isOk`): the quotient of
neither coordinate by an octave scale is positive infinity or a finite value of at least
`2 ^ 63 - 1`. The seed enters no refusal. The accepted input is the last coordinate at the scale
two, whose horizontal quotients are `2 ^ 62` to `2 ^ 59`. The refused input is the last coordinate
at the scale one half, whose first horizontal quotient is `2 ^ 64`. -/
theorem terrain_lattice : Regula.ExecutableContract Host.terrain (fun terrain =>
    Regula.Decides (·.isOk = true)
      (fun input : (Host.Position × UInt64) × Binary32 =>
        CurrentTerrain.LatticeAdmits input.1.1 input.2)
      (Function.uncurry (Function.uncurry terrain))) :=
  ⟨decides (fun input => CurrentTerrain.terrain_isOk input.1.1 input.1.2 input.2)
    ⟨((last, 0), ⟨0x40000000⟩), by decide +kernel⟩
    ⟨((last, 0), ⟨0x3f000000⟩), by decide +kernel⟩⟩

/-- The effective kind of a tile is refused exactly when the value noise refuses its position at
the base scale of the world (`CurrentTerrain.tileKind_isOk`). The witnesses are the inputs of
`terrain_lattice` in an empty world with the box of `wide`. -/
theorem tile_kind_lattice : Regula.ExecutableContract @Host.World.tileKind (fun tileKind =>
    Regula.Decides (·.isOk = true)
      (fun input : WorldTile =>
        CurrentTerrain.LatticeAdmits input.position input.config.raw.baseScale)
      (fun input : WorldTile => @tileKind input.config input.world input.position)) :=
  ⟨decides (fun input => CurrentTerrain.tileKind_isOk input.world input.position)
    ⟨⟨wideAt ⟨0x40000000⟩, Host.World.empty _, last⟩, by decide +kernel⟩
    ⟨⟨wideAt ⟨0x3f000000⟩, Host.World.empty _, last⟩, by decide +kernel⟩⟩

/-- An entry into a tile is refused exactly when the value noise refuses its position at the base
scale of the world (`CurrentTerrain.enterable_isOk`). The witnesses are those of
`tile_kind_lattice`. -/
theorem world_enterable_lattice : Regula.ExecutableContract @Host.World.enterable
    (fun enterable =>
    Regula.Decides (·.isOk = true)
      (fun input : WorldTile =>
        CurrentTerrain.LatticeAdmits input.position input.config.raw.baseScale)
      (fun input : WorldTile => @enterable input.config input.world input.position)) :=
  ⟨decides (fun input => CurrentTerrain.enterable_isOk input.world input.position)
    ⟨⟨wideAt ⟨0x40000000⟩, Host.World.empty _, last⟩, by decide +kernel⟩
    ⟨⟨wideAt ⟨0x3f000000⟩, Host.World.empty _, last⟩, by decide +kernel⟩⟩

/-- Whether the body may enter a tile is exactly the static passability of the tile's terrain
with the body's boat, and it refuses exactly when the terrain refuses
(`CurrentStep.enterable_static`).

The statement is a requirement with no kind beside the kind `world_enterable_lattice`, which
states the refused positions. It gives the verdict of an accepted entry, which that kind does
not state. -/
theorem world_enterable : Regula.ExecutableContract @Host.World.enterable (fun enterable =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (position : Host.Position),
      @enterable config world position =
        (Host.terrain position config.raw.seed config.raw.baseScale).map
          (fun base => CurrentStep.passable base world.body.inventory.boat)) :=
  ⟨fun _ => CurrentStep.enterable_static⟩

/-- The inventory holds a count of an item: the stored field of that item is at least the
count. Stated by the constructor of the item, with no count reader. -/
def Holds (inventory : Host.Inventory) (item : Host.Item) (count : UInt32) : Prop :=
  (item = .wood ∧ count.toNat ≤ inventory.wood.toNat) ∨
    (item = .stone ∧ count.toNat ≤ inventory.stone.toNat) ∨
    (item = .food ∧ count.toNat ≤ inventory.food.toNat) ∨
    (item = .gold ∧ count.toNat ≤ inventory.gold.toNat)

/-- The count reader `Host.Inventory.count` reads the field that `Holds` names. -/
private theorem holds_count (inventory : Host.Inventory) (item : Host.Item) (count : UInt32) :
    Holds inventory item count ↔ count.toNat ≤ (inventory.count item).toNat := by
  cases item <;> simp [Holds, Host.Inventory.count]

/-- A goal is attained in a world, on the stored fields of the world: the two box indices of
the body are within three tiles of the target of a reach goal, the inventory holds the count
of a collect goal or owns the tool of a craft goal, and the clock is at least the duration of
a survive goal after the clock of the installation. The radius is the literal three, and the
elapsed time is a difference of natural numbers. -/
def Attained {config : Host.WorldConfig} (world : Host.World config) (goal : Host.Goal) : Prop :=
  match goal with
  | .reach target =>
    (target.x.val - (world.body.position.x.val : Int)).natAbs ≤ 3 ∧
      (target.y.val - (world.body.position.y.val : Int)).natAbs ≤ 3
  | .collect item count => Holds world.body.inventory item count
  | .craft tool => world.body.inventory.Owns tool
  | .survive required => required.toNat ≤ world.time.toNat - world.goalStart.toNat

/-- The completion predicate accepts the observation of a world's goal exactly when the goal
is attained in the world. The observation embeds the box indices as coordinates, reads the
count and the ownership through their readers, and converts the elapsed time to a word; the
four family theorems and the bound of the clock connect them with `Attained`. -/
private theorem attained_iff {config : Host.WorldConfig} (world : Host.World config)
    (goal : Host.Goal) :
    Attained world goal ↔ (goal.observe world.body.position.position world.body.inventory
      (world.time.toNat - world.goalStart.toNat).toUInt64).satisfied = true := by
  cases goal with
  | reach target =>
    refine Iff.trans ?_ (CurrentGoals.reach_satisfied_iff _ _ _ _).symm
    exact Iff.rfl
  | collect item count =>
    exact (holds_count _ _ _).trans (CurrentGoals.collect_satisfied_iff _ _ _ _ _).symm
  | craft tool =>
    rw [CurrentGoals.craft_satisfied]
    exact (Host.Inventory.owns_iff _ _).symm
  | survive required =>
    rw [CurrentGoals.survive_satisfied_iff]
    have elapsed : ((world.time.toNat - world.goalStart.toNat).toUInt64).toNat =
        world.time.toNat - world.goalStart.toNat := by
      have bound := world.time.toNat_lt
      exact Nat.mod_eq_of_lt (by omega)
    rw [elapsed]
    exact Iff.rfl

/-- The world's completion flag is set exactly when a goal is installed and attained
(`CurrentGoals.goalSatisfied_eq` with the four family theorems). The specification is
`Attained`, on the installed goal and the stored fields of the world. It names neither the
completion predicate `Host.TaskObservation.satisfied` nor `Host.Goal.observe`, which the flag
applies, and no reader of a position or of an inventory. The accepted input is the empty world
of `wide` with the goal to survive no step, and the refused input is that world with no
goal. -/
theorem goal_satisfied : Regula.ExecutableContract @Host.World.goalSatisfied (fun satisfied =>
    Regula.Decides (· = true)
      (fun input : (config : Host.WorldConfig) × Host.World config => ∃ goal,
        input.2.goal = some goal ∧ Attained input.2 goal)
      (fun input : (config : Host.WorldConfig) × Host.World config =>
        @satisfied input.1 input.2)) :=
  ⟨decides
    (fun input => by
      show input.2.goalSatisfied = true ↔ _
      cases installed : input.2.goal with
      | none =>
        refine ⟨fun satisfied => ?_, fun ⟨_, same, _⟩ => (nomatch same)⟩
        have flag : input.2.goalSatisfied = false := by
          unfold Host.World.goalSatisfied Host.World.taskObservation
          rw [installed]
          rfl
        rw [flag] at satisfied
        exact absurd satisfied Bool.false_ne_true
      | some goal =>
        rw [CurrentGoals.goalSatisfied_eq input.2 goal installed]
        exact ⟨fun satisfied => ⟨goal, rfl, (attained_iff _ _).mpr satisfied⟩,
          fun ⟨other, same, attained⟩ => by
            cases same
            exact (attained_iff _ _).mp attained⟩)
    ⟨⟨wide, (Host.World.empty wide).setGoal (.survive 0)⟩, .survive 0, rfl, Nat.zero_le _⟩
    ⟨⟨wide, .empty wide⟩, fun ⟨_, installed, _⟩ => (nomatch installed)⟩⟩

/-- An action replay returns a world exactly when a run of the executed world step over those
actions ends in that world (`CurrentStep.trace_actions`, `CurrentStep.actions_trace`).

The statement keeps no kind. Its specification is a statement about runs of the executed world
step, which is the subject of the claim and which the replay runs. The step runs tests, among
them `Host.Inventory.owns`, `Host.TaskObservation.satisfied`, `Host.foodDue` and the
comparisons of actions, positions and tile kinds, and Regula's RG1009
(https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/) refuses a kind whose specification
reaches a test that its function runs. A kind needs the world step stated with propositions in
the place of those tests, which is remaining work of
https://github.com/rbeauchamp/acorn/issues/105. -/
theorem advance_actions : Regula.ExecutableContract @Host.World.advanceActions (fun advance =>
    ∀ (config : Host.WorldConfig) (world final : Host.World config)
      (actions : List Host.Action),
      @advance config world actions = .ok final ↔
        ∃ trace, CurrentStep.Trace world trace final ∧ trace.map (·.1) = actions) :=
  ⟨fun _ world final actions =>
    ⟨CurrentStep.actions_trace world final actions,
      fun ⟨_, run, same⟩ => same ▸ CurrentStep.trace_actions run⟩⟩

/-- What the readers of the terrain do with its result: enterability is the terrain result
mapped through static passability with the body's boat, so a terrain refusal is the only
refusal of an entry (`CurrentStep.enterable_static`), and no successful step moves the body
onto a tile whose terrain is a mountain, or water without a boat (`CurrentStep.step_terrain`).

The statement names `Host.World.enterable` and `Host.World.step`, which are defined through
the terrain. It is a statement about those readers, and it is not independent of the terrain
generator. It is a requirement with no kind beside the kind `terrain_lattice`, which states the
refused positions.

**Not claimed:** the kind of any tile. -/
theorem terrain_read : Regula.ExecutableContract Host.terrain (fun terrain =>
    ∀ (config : Host.WorldConfig),
      (∀ (world : Host.World config) (position : Host.Position),
        world.enterable position =
          (terrain position config.raw.seed config.raw.baseScale).map
            (fun base => CurrentStep.passable base world.body.inventory.boat)) ∧
        ∀ (world next : Host.World config) (action : Host.Action) (events : Host.StepResult),
          world.step action = .ok (next, events) →
          next.body.position ≠ world.body.position →
            terrain next.body.position.position config.raw.seed config.raw.baseScale ≠
                .ok .mountain ∧
              (terrain next.body.position.position config.raw.seed config.raw.baseScale =
                  .ok .water → world.body.inventory.boat = true)) :=
  ⟨fun _ => ⟨CurrentStep.enterable_static, CurrentStep.step_terrain⟩⟩

/-- The effective kind of a tile is refused exactly when the terrain of the tile is refused,
with the same refusal.

The statement is a requirement with no kind beside the kind `tile_kind_lattice`, which states the
refused positions. It gives the refusal of a refused tile, which that kind does not state.

**Not claimed:** the kind of an accepted tile. `CurrentStep.enterable_static` states what an
entry reads from it. -/
theorem tile_kind : Regula.ExecutableContract @Host.World.tileKind (fun tileKind =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (position : Host.Position)
      (refusal : Host.WorldError),
      @tileKind config world position = .error refusal ↔
        Host.terrain position config.raw.seed config.raw.baseScale = .error refusal) :=
  ⟨fun config world position refusal => by
    unfold Host.World.tileKind
    cases Host.terrain position config.raw.seed config.raw.baseScale with
    | error other => simp [bind, Except.bind]
    | ok base =>
      simp only [bind, Except.bind, pure, Except.pure, reduceCtorEq, iff_false]
      repeat' split
      all_goals simp⟩

/-! ## Refusals of the paid actions

A paid action reads the terrain of at most one tile: the tile one step ahead of a move when that
tile is in the box, and the tile that the body faces for a harvest
(`CurrentActions.ActionAdmits`). Its effect is refused exactly when the terrain refuses that
tile, and the paid action exactly when, in addition, the energy pays its cost
(`CurrentActions.Affords`). The witnesses of the two kinds are a harvest in the empty world of
`wideAt` at the noise scales of two and of one half, whose body faces the tile `faced`. A
generator that read every scale as one would fail each kind: at the scale one it admits that
tile. -/

/-- The arguments of `Host.performAction` and `Host.payAndAct`, in order. -/
structure WorldAction where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The world. -/
  world : Host.World config
  /-- The action. -/
  action : Host.Action

/-- The tile north of the center of the box of `wide`, which the body of an empty world of
`wideAt` faces. -/
def faced : Host.Position := ⟨⟨2 ^ 62 - 1, by decide⟩, ⟨2 ^ 62 - 2, by decide⟩⟩

/-- A harvest in the empty world of `wideAt` reads the tile `faced`. -/
private theorem harvest_faced (scale : Binary32) :
    CurrentActions.ActionAdmits (Host.World.empty (wideAt scale)) .harvest ↔
      CurrentTerrain.LatticeAdmits faced scale := by
  have column : ((Host.World.empty (wideAt scale)).body.position.x.val : Int) =
      ((Host.World.empty wide).body.position.x.val : Int) := rfl
  have row : ((Host.World.empty (wideAt scale)).body.position.y.val : Int) =
      ((Host.World.empty wide).body.position.y.val : Int) := rfl
  have center : ((Host.World.empty wide).body.position.x.val : Int) = 2 ^ 62 - 1 ∧
      ((Host.World.empty wide).body.position.y.val : Int) = 2 ^ 62 - 1 := by decide
  constructor
  · intro admits
    exact admits faced (by rw [column, center.1]; decide) (by rw [row, center.2]; decide)
  · intro admits tile tileColumn tileRow
    have same : tile = faced :=
      CurrentActions.position_ext (by rw [tileColumn, column, center.1]; decide)
        (by rw [tileRow, row, center.2]; decide)
    rw [same]
    exact admits

/-- The energy of the body of the empty world of `wideAt` at the scale one half pays for a
harvest: at the clock zero with a day of length one the phase is the fifth, and the cost four is
below the full energy. -/
private theorem harvest_paid :
    CurrentActions.Affords (Host.World.empty (wideAt ⟨0x3f000000⟩)) .harvest :=
  ⟨FeatureConstants.harvestCost * FeatureConstants.nightMultiplier,
    .inl ⟨rfl, by decide, rfl⟩, by decide⟩

/-- A paid action's effect is refused exactly when the terrain refuses the tile that the action
reads (`CurrentActions.performAction_isOk`): the tile one step ahead of a move when that tile is
in the box, and the tile that the body faces for a harvest. The other actions read no tile. The
accepted input is a harvest in the empty world of `wideAt` at the scale two, and the refused
input is that harvest at the scale one half. -/
theorem perform_action_lattice : Regula.ExecutableContract @Host.performAction (fun perform =>
    Regula.Decides (· = true)
      (fun input : WorldAction => CurrentActions.ActionAdmits input.world input.action)
      (Regula.Dependent.isOk fun input : WorldAction =>
        @perform input.config input.world input.action)) :=
  ⟨decides (fun input => CurrentActions.performAction_isOk input.world input.action)
    ⟨⟨wideAt ⟨0x40000000⟩, Host.World.empty _, .harvest⟩,
      (harvest_faced ⟨0x40000000⟩).mpr (by decide +kernel)⟩
    ⟨⟨wideAt ⟨0x3f000000⟩, Host.World.empty _, .harvest⟩,
      fun admits => absurd ((harvest_faced ⟨0x3f000000⟩).mp admits) (by decide +kernel)⟩⟩

/-- A paid action is refused exactly when the energy pays its cost and the terrain refuses the
tile that the action reads (`CurrentActions.payAndAct_isOk`). An action that the energy does not
pay for rests the body and is accepted. The witnesses are those of `perform_action_lattice`,
where the energy pays for the harvest. -/
theorem pay_and_act_lattice : Regula.ExecutableContract @Host.payAndAct (fun pay =>
    Regula.Decides (· = true)
      (fun input : WorldAction =>
        CurrentActions.Affords input.world input.action →
          CurrentActions.ActionAdmits input.world input.action)
      (Regula.Dependent.isOk fun input : WorldAction =>
        @pay input.config input.world input.action)) :=
  ⟨decides (fun input => CurrentActions.payAndAct_isOk input.world input.action)
    ⟨⟨wideAt ⟨0x40000000⟩, Host.World.empty _, .harvest⟩,
      fun _ => (harvest_faced ⟨0x40000000⟩).mpr (by decide +kernel)⟩
    ⟨⟨wideAt ⟨0x3f000000⟩, Host.World.empty _, .harvest⟩, fun admits =>
      absurd ((harvest_faced ⟨0x3f000000⟩).mp (admits harvest_paid)) (by decide +kernel)⟩⟩

/-- A paid action that succeeds either found the energy short, rested and set the exhausted
flag, or spent the cost of the action with the exhausted flag clear
(`CurrentStep.payAndAct_outcome`). The statement is a requirement with no kind beside the kind
`pay_and_act_lattice`, which states the refused actions.

**Not claimed:** the effect of the action on the body. `CurrentStep.payAndAct_outcome` states
it through the relation `CurrentStep.Performed`. -/
theorem pay_and_act : Regula.ExecutableContract @Host.payAndAct (fun pay =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (action : Host.Action)
      (active : Host.ActionChange config), @pay config world action = .ok active →
        ∃ night,
          (world.body.energy.spend (action.energyCost night) = none ∧
            active.body = { world.body with energy := world.body.energy.gain .rest } ∧
            active.events.exhausted = true) ∨
          (∃ energy, world.body.energy.spend (action.energyCost night) = some energy ∧
            active.events.exhausted = false)) :=
  ⟨fun _ world action active paid => by
      obtain ⟨night, short | ⟨energy, spent, -, awake⟩⟩ :=
        CurrentStep.payAndAct_outcome world action active paid
      · exact ⟨night, .inl short⟩
      · exact ⟨night, .inr ⟨energy, spent, awake⟩⟩⟩

/-- The hypotheses of the movement claim, apart from the success of the action: the action
heads in the direction, the position is the tile next to the body in that direction, and the
body may enter it. The tile and the move are stated by coordinate equations and constructors.
Enterability is the executed test of the world, which is the subject of that hypothesis. -/
def Moves {config : Host.WorldConfig} (world : Host.World config) (action : Host.Action)
    (direction : Host.Direction) (position : Host.BoxPosition config) : Prop :=
  Heads action direction ∧
    position.position.x.val = world.body.position.position.x.val + direction.delta.1 ∧
    position.position.y.val = world.body.position.position.y.val + direction.delta.2 ∧
    world.enterable position.position = .ok true

/-- A movement action that succeeds, toward an in-box tile that the body may enter, puts the
body on that tile facing the direction of the move (`CurrentCertificates.perform_move`). The
hypotheses are the predicate `Moves`. The statement is a requirement with no kind beside the kind
`perform_action_lattice`, which states the refused actions.

**Not claimed:** that some input satisfies the hypotheses. -/
theorem perform_action : Regula.ExecutableContract @Host.performAction (fun perform =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (action : Host.Action)
      (direction : Host.Direction) (position : Host.BoxPosition config)
      (active : Host.ActionChange config), Moves world action direction position →
      @perform config world action = .ok active →
        active.body.position = position ∧ active.body.facing = direction) :=
  ⟨fun _ world action direction position active ⟨heads, column, row, enter⟩ performed =>
    CurrentCertificates.perform_move world action direction position (heads_direction heads)
      (CurrentCertificates.translate_of_eq _ _ _ _ column row) enter active performed⟩

/-! ## Accepted inputs of the host transitions

`Acorn.Decisions` states the host transitions of an attempt and of the world with no kind. Its
statements of the observation and of finishing are about an accepted result alone, and its
statement of the fold is about a refusal that holds a stage. A function that refuses every input,
with no stage for the fold, satisfies each of the three. The statements below give each of the
three an accepted input, and state the two-way kind of `Host.Released.environment`, whose
accepted input holds a stage with an observation that succeeded.

Each input is made from the attempt `fresh`, whose body is at the center of the box of `wide`,
`2 ^ 62 - 1` on both axes, at the noise scale one. Its observation succeeds by the terrain
admission of `CurrentTerrain` (`fresh_observes`): each tile of the window translates inside the
signed range, and the quotients of its coordinates by the four octave scales are `2 ^ 62` to
`2 ^ 59`, below the last coordinate, so the value noise admits the tile. The kernel evaluates
those quotients, of eleven coordinates by four scales, and not the observation. It evaluates the
world's step on the action `wait` from that attempt (`fresh_waits`), which reads no terrain. -/

/-- An attempt of `wide` at its first step, with the given step cap: the attempt
`Acorn.Decisions.fresh`, which no module may import. -/
def fresh (cap : UInt64) : Host.Attempt wide Unit (.survive 0) cap :=
  ⟨⟨(Host.World.empty wide).setGoal (.survive 0), (), {}, 0⟩, rfl, 0, .zero, .wait⟩

/-- A success holds a value. -/
private theorem ok_of_isOk {ε α : Type} {result : Except ε α} (accepted : result.isOk = true) :
    ∃ value, result = .ok value := by
  cases result with
  | error error => exact absurd accepted (by simp [Except.isOk, Except.toBool])
  | ok value => exact ⟨value, rfl⟩

/-- A vector made by a fallible function succeeds where each of its entries succeeds. -/
private theorem ofFnM_isOk {ε α : Type} {n : Nat} (f : Fin n → Except ε α)
    (each : ∀ index, (f index).isOk = true) : (Vector.ofFnM f).isOk = true := by
  have values : f = fun index => pure (Classical.choose (ok_of_isOk (each index))) :=
    funext fun index => Classical.choose_spec (ok_of_isOk (each index))
  rw [values, Vector.ofFnM_pure]
  rfl

/-- The observation of a world succeeds where each tile of its window translates inside the
signed range and the value noise admits the tile at the noise scale of the world
(`CurrentTerrain.tileKind_isOk`). -/
private theorem observe_isOk {config : Host.WorldConfig} (world : Host.World config)
    (window : ∀ row column : Fin Host.patchSide, ∃ tile,
      world.body.position.position.translate ((column.val : Int) - (Host.patchSide / 2 : Nat))
          ((row.val : Int) - (Host.patchSide / 2 : Nat)) = some tile ∧
        CurrentTerrain.LatticeAdmits tile config.raw.baseScale) :
    world.observe.isOk = true := by
  have tiles : ∀ row column, (world.observeTile world.occupancy row column).isOk = true := by
    intro row column
    obtain ⟨tile, translated, admits⟩ := window row column
    obtain ⟨kind, kinded⟩ := ok_of_isOk ((CurrentTerrain.tileKind_isOk world tile).mpr admits)
    unfold Host.World.observeTile
    simp only [translated, kinded]
    rfl
  obtain ⟨rows, built⟩ := ok_of_isOk (ofFnM_isOk _ fun row => ofFnM_isOk _ (tiles row))
  unfold Host.World.observe
  simp only [built, bind, Except.bind, pure, Except.pure]
  rfl

/-- Each coordinate of the window of `fresh`, `2 ^ 62 - 6` to `2 ^ 62 + 4`, has a quotient by each
octave scale of the noise scale one that is not past the last coordinate. The kernel evaluates
the forty-four quotients. -/
private theorem window_admits : ∀ offset : Fin Host.patchSide, ∀ octave : Fin 4,
    ¬CurrentTerrain.PastLast
      ((Host.coordinateFloatWord (Int64.ofInt (2 ^ 62 - 6 + offset.val))).div
        (CurrentTerrain.octaveScale ⟨0x3f800000⟩ octave.val)) := by
  decide +kernel

/-- The observation of the world of `fresh` succeeds: each tile of the window translates inside
the signed range, and the value noise admits it (`window_admits`). -/
private theorem fresh_observes (cap : UInt64) : ((fresh cap).run.world.observe).isOk = true := by
  have center : ((Host.World.empty wide).body.position.x.val : Int) = 2 ^ 62 - 1 ∧
      ((Host.World.empty wide).body.position.y.val : Int) = 2 ^ 62 - 1 := by decide
  have radius : ((Host.patchSide / 2 : Nat) : Int) = 5 := rfl
  refine observe_isOk _ fun row column => ?_
  have columnBound := column.isLt
  have rowBound := row.isLt
  have side : Host.patchSide = 11 := rfl
  refine ⟨⟨⟨2 ^ 62 - 6 + column.val, by omega⟩, ⟨2 ^ 62 - 6 + row.val, by omega⟩⟩,
    CurrentCertificates.translate_of_eq _ _ _ _ ?_ ?_,
    fun octave below => ⟨window_admits column ⟨octave, below⟩, window_admits row ⟨octave, below⟩⟩⟩
  · change (2 ^ 62 - 6 + column.val : Int) = ((Host.World.empty wide).body.position.x.val : Int) + _
    rw [center.1]
    omega
  · change (2 ^ 62 - 6 + row.val : Int) = ((Host.World.empty wide).body.position.y.val : Int) + _
    rw [center.2]
    omega

/-- The world's step on the action `wait` from the attempt `fresh` at the step cap one succeeds.
The step reads no terrain: the action changes nothing, the world has no deer, and food is due only
at the clock zero. The kernel evaluates it. -/
private theorem fresh_waits : ((fresh 1).run.world.step .wait).isOk = true := by
  decide +kernel

/-- Finishing an attempt succeeds where the world's observation of the attempt succeeds. -/
private theorem finish_isOk {order : StepOrder} {config : Host.WorldConfig} {α β : Type}
    {goal : Host.Goal} {cap : UInt64} (callbacks : Host.AgentCallbacks order α β)
    (context : Host.GoalContext) (attempt : Host.Attempt config α goal cap)
    (observed : attempt.run.world.observe.isOk = true) :
    (attempt.finish callbacks context).isOk = true := by
  obtain ⟨observation, observed⟩ := ok_of_isOk observed
  unfold Host.Attempt.finish
  simp only [observed, bind, Except.bind, pure, Except.pure]
  rfl

/-- The fold of an attempt at the fuel zero succeeds where finishing the attempt succeeds. -/
private theorem complete_isOk {order : StepOrder} {config : Host.WorldConfig} {α β : Type}
    {goal : Host.Goal} {cap : UInt64} (callbacks : Host.AgentCallbacks order α β)
    (context : Host.GoalContext) (attempt : Host.Attempt config α goal cap)
    (finished : (attempt.finish callbacks context).isOk = true) :
    (Host.Attempt.complete callbacks context 0 attempt).isOk = true := by
  obtain ⟨result, finished⟩ := ok_of_isOk finished
  simp only [Host.Attempt.complete, Host.Attempt.close, finished]
  rfl

/-- The observation accepts the world of `fresh` (`fresh_observes`).
`Acorn.Decisions.world_observe` states what an accepted observation carries and keeps no kind for
the reason given there; this statement is a requirement with no kind beside it, and a function
that refuses every world fails it.

**Not claimed:** which other worlds observe without a refusal. -/
theorem world_observe_accepts : Regula.ExecutableContract @Host.World.observe (fun observe =>
    ∀ cap : UInt64, (observe (fresh cap).run.world).isOk = true) :=
  ⟨fresh_observes⟩

/-- Finishing accepts the attempt `fresh`, for every step cap, callbacks and context: its final
observation is that of `fresh_observes`. `Acorn.Decisions.attempt_finish` states what an accepted
finish returns and keeps no kind for the reason given there; this statement is a requirement
with no kind beside it, and a function that refuses every attempt fails it.

**Not claimed:** which other attempts finish without a refusal. -/
theorem attempt_finish_accepts : Regula.ExecutableContract @Host.Attempt.finish (fun finish =>
    ∀ {order β} (callbacks : Host.AgentCallbacks order Unit β) (context : Host.GoalContext)
      (cap : UInt64), (finish callbacks context (fresh cap)).isOk = true) :=
  ⟨fun callbacks context cap => finish_isOk callbacks context (fresh cap) (fresh_observes cap)⟩

/-- The fold accepts the attempt `fresh` at the fuel zero, for every step cap, callbacks and
context: at the fuel zero it finishes the attempt, which `attempt_finish_accepts` accepts.
`Acorn.Decisions.attempt_complete` states what a fold that ends in a refused action holds and
keeps no kind for the reason given there; this statement is a requirement with no kind beside
it, and a function that refuses every input fails it.

**Not claimed:** which other folds end without a refusal. -/
theorem attempt_complete_accepts : Regula.ExecutableContract @Host.Attempt.complete
    (fun complete =>
      ∀ {order β} (callbacks : Host.AgentCallbacks order Unit β) (context : Host.GoalContext)
        (cap : UInt64), (complete callbacks context 0 (fresh cap)).isOk = true) :=
  ⟨fun callbacks context cap => complete_isOk callbacks context (fresh cap)
    (finish_isOk callbacks context (fresh cap) (fresh_observes cap))⟩

/-- The arguments of `Host.Released.environment`, in order. -/
structure ReleasedEnvironment where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The type of the value that the stage holds. -/
  agent : Type
  /-- The goal of the attempt. -/
  goal : Host.Goal
  /-- The step cap. -/
  cap : UInt64
  /-- The world's answer to the released action. -/
  released : Host.Released config agent goal cap

/-- The transition result of a release succeeds exactly when the world accepted the released
action. The accepted input is the acceptance of the stage of `fresh` that waits, whose
observation and step succeed (`fresh_observes`, `fresh_waits`), and the refused input is the
refusal of that stage. `Acorn.Decisions.released_environment` states the value of the result, as
a requirement with no kind. -/
theorem released_environment_exact : Regula.ExecutableContract @Host.Released.environment
    (fun environment =>
      Regula.Decides (· = true)
        (fun input : ReleasedEnvironment => ∃ accepted, input.released = .accepted accepted)
        (Regula.Dependent.isOk fun input : ReleasedEnvironment =>
          @environment input.config input.agent input.goal input.cap input.released)) := by
  obtain ⟨observation, sensed⟩ := ok_of_isOk (fresh_observes 1)
  obtain ⟨⟨world, result⟩, stepped⟩ := ok_of_isOk fresh_waits
  let stage : Host.OwnedStep wide Unit (.survive 0) 1 :=
    ⟨fresh 1, by decide, observation, sensed, .wait, ()⟩
  exact ⟨decides
    (fun input => by
      cases input with
      | mk config agent goal cap released =>
        cases released <;> simp [Regula.Dependent.isOk, Host.Released.environment, Except.isOk,
          Except.toBool])
    ⟨⟨_, _, _, _, .accepted ⟨stage, world, result, stepped⟩⟩, _, rfl⟩
    ⟨⟨_, _, _, _, .refused .coordinateOverflow stage⟩, fun ⟨_, refused⟩ => nomatch refused⟩⟩

/-! ## The comparator and the attempt runner

The random comparator of an attempt corresponds with the agent's attempt step by step. A
campaign from a cursor within its cycle budget, with fuel that covers the attempts left in its
budget (`plan.attemptBudget ≤ fuel + cursorRank cursor`), never ends unfinished, and neither does
the campaign over an admitted plan with at least one cycle. The theorems of
`AcornVerif.CurrentRunner` state these. -/

/-- A tick of the comparator from a state that corresponds with an agent's attempt follows the
agent's tick: where the agent's tick takes no step the comparator's returns its state, and where
it takes a step whose action the comparator's stream draws, the comparator's tick is accepted
with a state that corresponds with the agent's next attempt and the advanced stream
(`CurrentRunner.idle_corresponds`, `CurrentRunner.tick_corresponds`).

The statement keeps no kind. It relates the comparator to the agent's tick through
`CurrentRunner.Corresponds`, a relation of this library, and the acceptance of a tick is the
world step's, which no theorem states (`Acorn.Decisions.baseline_tick`). -/
theorem baseline_corresponds : Regula.ExecutableContract @Host.BaselineAttempt.tick
    (fun tick =>
      ∀ {order config α β goal cap} (callbacks : Host.AgentCallbacks order α β)
        (context : Host.GoalContext) (attempt next : Host.Attempt config α goal cap)
        (state : Host.BaselineAttempt config cap), CurrentRunner.Corresponds attempt state →
        (attempt.tick callbacks context = .ok (next, none) → tick state = .ok state) ∧
          ∀ frame, attempt.tick callbacks context = .ok (next, some frame) →
            (Host.baselineAction state.rng).1 = frame.action →
            ∃ after, tick state = .ok after ∧ CurrentRunner.Corresponds next after ∧
              after.rng = (Host.baselineAction state.rng).2) :=
  ⟨fun callbacks context attempt next state related =>
    ⟨fun idle => CurrentRunner.idle_corresponds callbacks context attempt next state related idle,
      fun frame acted drawn => CurrentRunner.tick_corresponds callbacks context attempt next frame
        state related acted drawn⟩⟩

/-- A comparator campaign with no fuel ends unfinished, and a comparator campaign from a cursor
within its cycle budget (its cycle is below the plan's cycle count), with fuel that covers the
attempts left in its budget (`plan.attemptBudget ≤ fuel + cursorRank cursor`), never ends
unfinished (`CurrentRunner.baseline_campaign_finishes`).

The statement keeps no kind. A constant function fails it: with no fuel the result is the
refusal `unfinished`, and with fuel that covers the budget the result is not. A campaign that
does not end unfinished can still refuse where the world refuses a step, and no theorem states
which steps succeed.

**Not claimed:** which campaigns return a record, or the record. -/
theorem campaign_finishes : Regula.ExecutableContract @Host.runBaselineCampaign (fun run =>
    (∀ {config} (curriculum : Host.Curriculum) (plan : Host.CampaignPlan curriculum.size)
      (cursor : Host.CampaignCursor plan) (world : Host.World config) (rng : Rng.Xoshiro256)
      (outcomes : Array Host.BaselineOutcome),
      run curriculum plan 0 cursor world rng outcomes = .error .unfinished) ∧
    ∀ {config} (curriculum : Host.Curriculum) (plan : Host.CampaignPlan curriculum.size)
      (fuel : Nat) (cursor : Host.CampaignCursor plan) (world : Host.World config)
      (rng : Rng.Xoshiro256) (outcomes : Array Host.BaselineOutcome),
      cursor.cycle.toNat < plan.cycles.toNat →
      plan.attemptBudget ≤ fuel + CurrentRunner.cursorRank cursor →
      run curriculum plan fuel cursor world rng outcomes ≠ .error .unfinished) :=
  ⟨⟨fun _ _ _ _ _ _ => rfl,
    fun curriculum plan fuel cursor world rng outcomes before covered =>
      CurrentRunner.baseline_campaign_finishes curriculum plan fuel cursor world rng outcomes
        before covered⟩⟩

/-- The comparator's campaign refuses at campaign admission a specification with no steps
(`stepCapZero`) and a specification with steps, no goals and no cycles (`emptyUnbounded`,
`CurrentRunner.empty_unbounded_refused`), and over an admitted plan with at least one cycle it
never ends unfinished (`CurrentRunner.baseline_finishes`).

The statement keeps no kind. A constant function fails it: the two refusals of admission
differ. The campaign over an admitted plan can still refuse where world generation or a world
step refuses, and no theorem states which configurations initialize or which steps succeed
(`Acorn.Decisions.world_initial`).

**Not claimed:** which campaigns return a record, or the record. -/
theorem random_baseline_finishes : Regula.ExecutableContract Host.runRandomBaseline (fun run =>
    (∀ (config : Host.WorldConfig) (seed attempts goals cycles : UInt64),
      run config seed ⟨0, attempts, goals, cycles⟩ = .error (.campaign .stepCapZero)) ∧
    (∀ (config : Host.WorldConfig) (seed steps attempts : UInt64), 0 < steps.toNat →
      run config seed ⟨steps, attempts, 0, 0⟩ = .error (.campaign .emptyUnbounded)) ∧
    ∀ (config : Host.WorldConfig) (seed : UInt64) (spec : Host.CampaignSpec)
      (plan : Host.CampaignPlan (Host.standardCurriculum config seed).size),
      Host.CampaignPlan.admit (Host.standardCurriculum config seed).size spec = .ok plan →
      plan.cycles.toNat ≠ 0 → run config seed spec ≠ .error .unfinished) :=
  ⟨⟨fun _ _ _ _ _ => by simp [Host.runRandomBaseline, Host.CampaignPlan.admit],
    fun _ _ _ _ positive => by
      simp only [Host.runRandomBaseline, CurrentRunner.empty_unbounded_refused, positive,
        ↓reduceIte],
    fun config seed spec plan admitted bounded =>
      CurrentRunner.baseline_finishes config seed spec plan admitted bounded⟩⟩

/-! ## The spawn search of world generation

The theorems of `AcornVerif.CurrentSpawn` state what a successful count, a successful application
of the spawn rule and a successful spawn search return. Each statement below also gives an
accepted input, so a function that refuses every input fails it, and `world_initial_accepts`
gives one of world generation.

The search and world generation accept the configuration `oneTile`: a box of one tile, no deer
and the noise scale one. The spiral of its box has one candidate, the center of the box, and the
rule there counts the trees and the stone within four tiles and reads the kind of the center.
Each of the eighty-one tiles within four tiles of the center translates inside the signed range,
and the quotients of its coordinates, `-4` to `4`, by the four octave scales of the noise scale
are not past the last coordinate, so the value noise admits the tile
(`CurrentTerrain.tileKind_isOk`). The kernel evaluates those quotients, of nine coordinates by
four scales, and not the terrain. A loop over a range in `Except` succeeds where every pass
succeeds (`forIn_range_isOk`), which carries the success of each pass through the loops of the
count and of the search. The placement of the deer runs no pass at the deer cap zero. -/

/-- A successful count of a kind near a position is the number of tiles of that kind among the
`(2 r + 1) × (2 r + 1)` tiles within `r` of the position (`CurrentSpawn.countKindNear_eq`). The
count of trees at the body position of the empty world of `wide`, within radius zero, succeeds;
the kernel evaluates that one tile.

The statement keeps no kind. A count refuses where a tile of the square leaves the signed range
or the world refuses its kind, and a specification of the accepted inputs would name
`Host.World.tileKind`, which runs tests that the count runs. -/
theorem spawn_count : Regula.ExecutableContract @Host.countKindNear (fun count =>
    (∀ {config} (world : Host.World config) (position : Host.Position) (radius found : Nat)
      (kind : Host.TileKind), count world position radius kind = .ok found →
        found = CurrentSpawn.squareCount world position radius kind (2 * radius + 1)) ∧
      ∃ (config : Host.WorldConfig) (world : Host.World config) (position : Host.Position)
        (radius : Nat) (kind : Host.TileKind), (count world position radius kind).isOk = true) :=
  ⟨⟨fun world position radius found kind counted =>
      CurrentSpawn.countKindNear_eq world position radius found kind counted,
    ⟨wide, Host.World.empty wide, (Host.World.empty wide).body.position.position, 0, .tree,
      by decide +kernel⟩⟩⟩

/-- Every successful application of the spawn rule is one of the outcomes that
`CurrentSpawn.Considered` lists (`CurrentSpawn.considerSpawn_outcome`). The rule accepts a
coordinate outside the box, which it skips with no count.

The statement keeps no kind, for the reason that `spawn_count` states: the rule counts kinds
near a coordinate inside the box. -/
theorem spawn_consider : Regula.ExecutableContract @Host.considerSpawn (fun consider =>
    (∀ {config} (world : Host.World config) (x y : Int)
      (best selected : Option (Host.SpawnCandidate config)) (finished : Bool),
      consider world x y best = .ok (selected, finished) →
        CurrentSpawn.Considered world x y best selected finished) ∧
      ∃ (config : Host.WorldConfig) (world : Host.World config) (x y : Int)
        (best : Option (Host.SpawnCandidate config)), (consider world x y best).isOk = true) :=
  ⟨⟨fun world x y best selected finished considered =>
      CurrentSpawn.considerSpawn_outcome world x y best selected finished considered,
    ⟨wide, Host.World.empty wide, -1, 0, none, by decide +kernel⟩⟩⟩

/-- A bind succeeds where its first part succeeds and its rest succeeds on every value. -/
private theorem bind_isOk {ε α β : Type} (first : Except ε α) (rest : α → Except ε β)
    (accepted : first.isOk = true) (each : ∀ value, (rest value).isOk = true) :
    (first >>= rest).isOk = true := by
  obtain ⟨value, same⟩ := ok_of_isOk accepted
  rw [same]
  exact each value

/-- A loop over a list of consecutive indices in `Except` succeeds where every pass at an index
below the bound succeeds. -/
private theorem forIn_range'_isOk {ε σ : Type} (count : Nat)
    (body : Nat → σ → Except ε (ForInStep σ))
    (each : ∀ index state, index < count → (body index state).isOk = true) :
    ∀ (remaining start : Nat) (init : σ), start + remaining = count →
      (forIn (List.range' start remaining 1) init body).isOk = true
  | 0, start, init, _ => by simp [Except.isOk, Except.toBool, pure, Except.pure]
  | remaining + 1, start, init, total => by
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨next, taken⟩ := ok_of_isOk (each start init (by omega))
    rw [taken]
    cases next with
    | done after => rfl
    | yield after =>
      exact forIn_range'_isOk count body each remaining (start + 1) after (by omega)

/-- A loop over a range in `Except` succeeds where every pass succeeds. -/
private theorem forIn_range_isOk {ε σ : Type} (count : Nat) (init : σ)
    (body : Nat → σ → Except ε (ForInStep σ))
    (each : ∀ index state, index < count → (body index state).isOk = true) :
    (forIn [:count] init body).isOk = true := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have size : ([:count] : Std.Legacy.Range).size = count := by simp [Std.Legacy.Range.size]
  rw [size]
  exact forIn_range'_isOk count body each count 0 init (by omega)

/-- A count of a kind near a position succeeds where every tile of its square translates inside
the signed range and the world accepts its kind. -/
private theorem countKindNear_isOk {config : Host.WorldConfig} (world : Host.World config)
    (position : Host.Position) (radius : Nat) (kind : Host.TileKind)
    (tiles : ∀ row column, row < 2 * radius + 1 → column < 2 * radius + 1 → ∃ tile,
      position.translate ((column : Int) - radius) ((row : Int) - radius) = some tile ∧
        (world.tileKind tile).isOk = true) :
    (Host.countKindNear world position radius kind).isOk = true := by
  unfold Host.countKindNear
  dsimp only
  refine bind_isOk _ _ ?_ fun _ => rfl
  refine forIn_range_isOk _ _ _ fun row state rowBound => ?_
  refine bind_isOk _ _ ?_ fun _ => rfl
  refine forIn_range_isOk _ _ _ fun column count columnBound => ?_
  obtain ⟨tile, translated, kinded⟩ := tiles row column rowBound columnBound
  obtain ⟨found, located⟩ := ok_of_isOk kinded
  simp only [translated, located, bind, Except.bind]
  split <;> rfl

/-- A world configuration whose box is one tile, with no deer and the noise scale one. -/
def oneTile : Host.WorldConfig :=
  ⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, ⟨0x3f800000⟩⟩, by decide, by decide⟩

/-- Each coordinate from `-4` to `4` has a quotient by each octave scale of the noise scale one
that is not past the last coordinate. The kernel evaluates the thirty-six quotients. -/
private theorem near_admits : ∀ offset : Fin 9, ∀ octave : Fin 4,
    ¬CurrentTerrain.PastLast
      ((Host.coordinateFloatWord (Int64.ofInt ((offset.val : Int) - 4))).div
        (CurrentTerrain.octaveScale ⟨0x3f800000⟩ octave.val)) := by
  decide +kernel

/-- Every tile within four tiles of the center of the box of `oneTile` translates inside the
signed range, and the empty world of `oneTile` accepts its kind (`near_admits`). -/
private theorem center_square : ∀ row column : Nat, row < 9 → column < 9 → ∃ tile,
    (Host.BoxPosition.center oneTile).position.translate ((column : Int) - (4 : Nat))
        ((row : Int) - (4 : Nat)) = some tile ∧
      ((Host.World.empty oneTile).tileKind tile).isOk = true := by
  intro row column rowBound columnBound
  refine ⟨⟨⟨(column : Int) - 4, by omega⟩, ⟨(row : Int) - 4, by omega⟩⟩,
    CurrentCertificates.translate_of_eq _ _ _ _ ?_ ?_, ?_⟩
  · change (column : Int) - 4 = (0 : Int) + ((column : Int) - (4 : Nat))
    omega
  · change (row : Int) - 4 = (0 : Int) + ((row : Int) - (4 : Nat))
    omega
  · exact (CurrentTerrain.tileKind_isOk _ _).mpr fun octave below =>
      ⟨near_admits ⟨column, columnBound⟩ ⟨octave, below⟩,
        near_admits ⟨row, rowBound⟩ ⟨octave, below⟩⟩

/-- The empty world of `oneTile` accepts the kind of the center of its box (`near_admits`). -/
private theorem center_kind :
    ((Host.World.empty oneTile).tileKind (Host.BoxPosition.center oneTile).position).isOk =
      true :=
  (CurrentTerrain.tileKind_isOk _ _).mpr fun octave below =>
    ⟨near_admits ⟨4, by decide⟩ ⟨octave, below⟩, near_admits ⟨4, by decide⟩ ⟨octave, below⟩⟩

/-- The spawn rule succeeds at the center of the box of `oneTile`, whatever the best candidate
so far: both counts within four tiles and the kind of the center succeed. -/
private theorem consider_center (best : Option (Host.SpawnCandidate oneTile)) :
    (Host.considerSpawn (Host.World.empty oneTile) 0 0 best).isOk = true := by
  unfold Host.considerSpawn
  have checked : Host.BoxPosition.checked oneTile 0 0 = some (Host.BoxPosition.center oneTile) :=
    rfl
  simp only [checked]
  refine bind_isOk _ _ (countKindNear_isOk _ _ _ _ center_square) fun _ => ?_
  refine bind_isOk _ _ (countKindNear_isOk _ _ _ _ center_square) fun _ => ?_
  refine bind_isOk _ _ center_kind fun _ => ?_
  split <;> rfl

/-- The spawn search succeeds in the empty world of `oneTile`: its spiral has the radius zero
and the offset zero alone, whose candidate is the center of the box (`consider_center`). -/
private theorem select_oneTile : (Host.selectSpawn (Host.World.empty oneTile)).isOk = true := by
  unfold Host.selectSpawn
  dsimp only
  refine bind_isOk _ _ ?_ fun _ => ?_
  · refine forIn_range_isOk _ _ _ fun radius state radiusBound => ?_
    refine bind_isOk _ _ ?_ fun _ => ?_
    · refine forIn_range_isOk _ _ _ fun direction state _ => ?_
      refine bind_isOk _ _ ?_ fun _ => ?_
      · refine forIn_range_isOk _ _ _ fun offset state offsetBound => ?_
        have side : oneTile.side = 1 := rfl
        have radiusZero : radius = 0 := by rw [side] at radiusBound; omega
        subst radiusZero
        have offsetZero : offset = 0 := by omega
        subst offsetZero
        have column : Host.Coordinate.checked
            (((oneTile.side / 2 : Nat) : Int) +
              (Host.Direction.fromIndex ⟨direction % 4, Nat.mod_lt _ (by decide)⟩).delta.1 *
                ((0 : Nat) : Int) +
              (Host.Direction.fromIndex ⟨direction % 4, Nat.mod_lt _ (by decide)⟩).delta.2 *
                (((0 : Nat) : Int) - ((0 : Nat) : Int))) = some ⟨0, by decide⟩ := by
          simp only [side, Nat.cast_zero, mul_zero, sub_self, add_zero]
          rfl
        have row : Host.Coordinate.checked
            (((oneTile.side / 2 : Nat) : Int) +
              (Host.Direction.fromIndex ⟨direction % 4, Nat.mod_lt _ (by decide)⟩).delta.2 *
                ((0 : Nat) : Int) +
              (Host.Direction.fromIndex ⟨direction % 4, Nat.mod_lt _ (by decide)⟩).delta.1 *
                (((0 : Nat) : Int) - ((0 : Nat) : Int))) = some ⟨0, by decide⟩ := by
          simp only [side, Nat.cast_zero, mul_zero, sub_self, add_zero]
          rfl
        rw [column, row]
        dsimp only
        refine bind_isOk _ _ (consider_center _) fun _ => ?_
        split <;> rfl
      · split <;> rfl
    · split <;> rfl
  · split <;> rfl

/-- The placement of the deer succeeds in the empty world of `oneTile`: at the deer cap zero its
loop runs no pass. -/
private theorem deer_oneTile : (Host.initializeDeer (Host.World.empty oneTile)).isOk = true := by
  unfold Host.initializeDeer
  dsimp only
  refine bind_isOk _ _ (forIn_range_isOk _ _ _ fun index _ bound => ?_) fun _ => rfl
  exact absurd bound (Nat.not_lt_zero index)

/-- A spawn that the search returns is a walkable tile whose trees plus stone within four tiles
are at least two; or no tile of the box is rich, and the spawn is a walkable tile whose score no
scored candidate of the box exceeds, or the center of the box when no tile is walkable
(`CurrentSpawn.selectSpawn_post`). The search accepts the empty world of `oneTile`
(`select_oneTile`).

The statement keeps no kind, for the reason that `spawn_count` states: the search applies the
rule to each candidate of its spiral. -/
theorem spawn_select : Regula.ExecutableContract @Host.selectSpawn (fun select =>
    (∀ {config} (world : Host.World config) (spawn : Host.BoxPosition config),
      select world = .ok spawn →
        CurrentSpawn.Exited world spawn ∨
          ((∀ tile, ¬CurrentSpawn.Rich world tile) ∧
            ((∃ chosen, CurrentSpawn.Scored world chosen ∧ chosen.position = spawn ∧
                ∀ other, CurrentSpawn.Scored world other → other.score ≤ chosen.score) ∨
              (spawn = Host.BoxPosition.center config ∧
                ∀ tile, ¬CurrentSpawn.Walkable world tile)))) ∧
      ∃ (config : Host.WorldConfig) (world : Host.World config), (select world).isOk = true) :=
  ⟨⟨fun world spawn selected => CurrentSpawn.selectSpawn_post world spawn selected,
    ⟨oneTile, Host.World.empty oneTile, select_oneTile⟩⟩⟩

/-- World generation accepts the configuration `oneTile`: its spawn search succeeds
(`select_oneTile`), and at the deer cap zero the placement of the deer runs no pass
(`deer_oneTile`). `Acorn.Decisions.world_initial` states what an initial world holds and keeps
no kind for the reason given there; this statement is a requirement with no kind beside it, and
a function that refuses every configuration fails it.

**Not claimed:** which other configurations initialize, or that the spawn search returns a spawn
for every seed. -/
theorem world_initial_accepts : Regula.ExecutableContract Host.World.initial (fun initial =>
    (initial oneTile).isOk = true) :=
  ⟨by
    unfold Host.World.initial
    dsimp only
    exact bind_isOk _ _ select_oneTile fun _ => bind_isOk _ _ deer_oneTile fun _ => rfl⟩

/-! ## Learner admissions -/

/-- The arguments of `Features.Interest.potential`, in order. -/
structure InterestPotential where
  /-- The bank configuration. -/
  config : Features.Config
  /-- The dimension of the feature space. -/
  dimension : Dimension
  /-- The interest of a slot. -/
  interest : Interest config
  /-- The active features. -/
  features : SwiftTd.ActiveSet dimension
  /-- The declared potentials. -/
  declared : DeclaredPotentials

/-- The potential of an interest accepts exactly a learned interest, with every source of
declared potentials (`CurrentTemporal.learned_potential`), and a declared interest with a
source of its own origin (`CurrentTemporal.declared_refusal` for a source of another origin).
The specification states the interest by its constructors and the origin by an equation. The
accepted input is a declared interest with a source of its own origin, and the refused input
is a declared interest with a source of another origin. -/
theorem interest_potential : Regula.ExecutableContract @Interest.potential (fun potential =>
    Regula.Decides (·.isSome = true)
      (fun input : InterestPotential => (∃ assignment, input.interest = .learned assignment) ∨
        ∃ origin tag, input.interest = .declared origin tag ∧ origin = input.declared.origin)
      (fun input : InterestPotential =>
        @potential input.config input.dimension input.interest input.features
          input.declared)) :=
  ⟨decides
    (fun ⟨config, _, interest, features, declared⟩ => by
      change (interest.potential features declared).isSome = true ↔
        (∃ assignment, interest = .learned assignment) ∨
          ∃ origin tag, interest = .declared origin tag ∧ origin = declared.origin
      cases interest with
      | learned assignment => exact ⟨fun _ => .inl ⟨assignment, rfl⟩, fun _ => rfl⟩
      | declared origin tag =>
        by_cases same : origin = declared.origin
        · rw [show (Interest.declared (config := config) origin tag).potential features
            declared = some (declared.values.get tag) from ite_eq_left same]
          exact ⟨fun _ => .inr ⟨origin, tag, rfl, same⟩, fun _ => rfl⟩
        · rw [CurrentTemporal.declared_refusal origin tag features declared same]
          refine ⟨fun accepted => absurd accepted (by decide), ?_⟩
          rintro (⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩, matched⟩)
          exact absurd matched same)
    ⟨⟨bank, narrow, .declared .cumulants ⟨0, by decide⟩, .empty narrow,
      ⟨.cumulants, .replicate _ false⟩⟩, .inr ⟨.cumulants, ⟨0, by decide⟩, rfl, rfl⟩⟩
    ⟨⟨bank, narrow, .declared .spatialPotentials ⟨0, by decide⟩, .empty narrow,
      ⟨.cumulants, .replicate _ false⟩⟩, by rintro (⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩, ⟨⟩⟩)⟩⟩

/-- A declared interest refuses a source of declared potentials with another origin
(`CurrentTemporal.declared_refusal`). This requirement with no kind states that class of
refused inputs pointwise, about the arguments of the function; the two-way kind
`interest_potential` also gives it. -/
theorem interest_potential_declared : Regula.ExecutableContract @Interest.potential
    (fun potential =>
    ∀ {config : Features.Config} {dimension : Dimension} (origin : Departure)
      (tag : Fin Acorn.FeatureConstants.skillCount) (features : SwiftTd.ActiveSet dimension)
      (declared : DeclaredPotentials), origin ≠ declared.origin →
        potential (Interest.declared (config := config) origin tag) features declared = none) :=
  ⟨CurrentTemporal.declared_refusal⟩

/-- Loading returns the state that a resumable construction saved, every field of its agent,
for every receiver of that construction (`CurrentCheckpoint.save_load`). The refusal under
every other profile is `checkpoint_load` in `Acorn.Decisions`.

The statement keeps no kind. Regula v0.10.0 refuses the kind under RG1009
(https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/): the input holds an agent state, an
invariant of that state names tests that loading runs, and the rule reads the type of the input
(https://github.com/rbeauchamp/regula/issues/270). -/
theorem checkpoint_load_accepts : Regula.ExecutableContract Checkpoint.load (fun load =>
    ∀ (construction : AgentConstruction) (source receiver : construction.State),
      construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
        construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned →
      load construction receiver (encode (snapshot construction source)) = .ok source) :=
  ⟨fun construction source receiver resumable =>
    CurrentCheckpoint.save_load construction receiver source
      ((FeatureProfile.checkpoint_iff construction.profile).mpr resumable)⟩

/-- Each event satisfies the contract of its edge: an act runs the agent's step and returns its
decision, the bookkeeping events keep the learners, a clear returns the initial agent and a
stop keeps the state (`CurrentAgent.edge_contract`). The operation refuses no event, so it is
no decision and this statement is a requirement with no kind. -/
theorem agent_input_edges : Regula.ExecutableContract @Agent.input (fun input =>
    ∀ {profile config criterion dimension planning}
      (before after : Agent Grid.interface profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (stopped : Bool),
      input before event = (after, stopped) → CurrentAgent.EdgeContract before event after) :=
  ⟨fun before after event stopped executed =>
    CurrentAgent.edge_contract before after event stopped executed⟩

/-- The compiled fold from cold initialization follows a safe path from the initial agent:
every intermediate agent keeps the invariant, and each edge satisfies its contract
(`CurrentAgent.native_prefix`). The fold refuses no event, so this statement is a requirement
with no kind. -/
theorem execute_prefix : Regula.ExecutableContract AgentConstruction.execute (fun execute =>
    ∀ (admitted : DefaultConstruction)
      (events : List (AgentInput admitted.construction.config admitted.construction.criterion
        admitted.construction.dimension)),
      CurrentAgent.SafePath admitted.construction.initial.agent events
        (execute admitted events).1.agent (execute admitted events).2) :=
  ⟨CurrentAgent.native_prefix⟩

/-- The arguments of `Agreement.admitSquared`, in order. -/
structure SquaredAdmit where
  /-- The receiving envelope. -/
  envelope : Nat
  /-- The forecast word. -/
  forecast : Binary32
  /-- The outcome word. -/
  outcome : Binary32

/-- Squared-discrepancy admission accepts exactly when both words are finite and the squared
discrepancy of their units is within the squared envelope. -/
private theorem squared_iff (envelope : Nat) (forecast outcome : Binary32) :
    (Agreement.admitSquared envelope forecast outcome).isSome = true ↔
      forecast.Finite ∧ outcome.Finite ∧
        Agreement.squaredUnits forecast outcome ≤ envelope ^ 2 := by
  unfold Agreement.admitSquared
  split
  · next finite =>
    split
    · next within =>
      exact ⟨fun _ => ⟨finite.1, finite.2, Nat.lt_succ_iff.mp within⟩, fun _ => rfl⟩
    · next outside =>
      exact ⟨fun present => (nomatch present),
        fun accepted => absurd (Nat.lt_succ_iff.mpr accepted.2.2) outside⟩
  · next infinite =>
    exact ⟨fun present => (nomatch present),
      fun accepted => absurd ⟨accepted.1, accepted.2.1⟩ infinite⟩

/-- The squared units of two finite words are within a squared envelope exactly when the
exact discrepancy of the words is within the envelope at the scale of one unit
(`CurrentAgreement.squaredUnits_numerical`). -/
private theorem squared_within (forecast outcome : Binary32) (envelope : Nat)
    (forecastFinite : forecast.Finite) (outcomeFinite : outcome.Finite) :
    Agreement.squaredUnits forecast outcome ≤ envelope ^ 2 ↔
      |CurrentArithmetic.numerical32 forecast - CurrentArithmetic.numerical32 outcome| ≤
        (envelope : ℚ) * (2 : ℚ) ^ (-149 : Int) := by
  have scale : (0 : ℚ) < (2 : ℚ) ^ (-149 : Int) := by positivity
  have exact := CurrentAgreement.squaredUnits_numerical forecast outcome forecastFinite
    outcomeFinite
  rw [← abs_of_nonneg (mul_nonneg (Nat.cast_nonneg envelope) scale.le), ← sq_le_sq, mul_pow,
    ← exact, mul_le_mul_iff_left₀ (pow_pos scale 2)]
  exact_mod_cast Iff.rfl

/-- Squared-discrepancy admission accepts exactly two finite words whose exact discrepancy,
as a rational number, is at most the envelope in units of `2 ^ (-149)`, the least positive
binary32 magnitude. The specification names the rational value of a word, and no unit map and
no squared units, which the admission computes: `squared_iff` and `squared_within` connect
them. `squared_admit` in `Acorn.Decisions` states the two-way kind against the squared units,
and `squared_admit_value` the admitted sample. The accepted input is two zeros under the
envelope zero, and the refused input is one and zero under that envelope. -/
theorem squared_admit_exact : Regula.ExecutableContract Agreement.admitSquared (fun admit =>
    Regula.Decides (· = true)
      (fun input : SquaredAdmit => input.forecast.Finite ∧ input.outcome.Finite ∧
        |CurrentArithmetic.numerical32 input.forecast -
            CurrentArithmetic.numerical32 input.outcome| ≤
          (input.envelope : ℚ) * (2 : ℚ) ^ (-149 : Int))
      (Regula.Dependent.isSome fun input : SquaredAdmit =>
        admit input.envelope input.forecast input.outcome)) :=
  ⟨.of_iff
    (fun input => (squared_iff input.envelope input.forecast input.outcome).trans
      ⟨fun accepted => ⟨accepted.1, accepted.2.1,
          (squared_within _ _ _ accepted.1 accepted.2.1).mp accepted.2.2⟩,
        fun within => ⟨within.1, within.2.1,
          (squared_within _ _ _ within.1 within.2.1).mpr within.2.2⟩⟩)
    ⟨⟨0, .zero, .zero⟩, by decide⟩ ⟨⟨0, ⟨0x3f800000⟩, .zero⟩, by decide⟩⟩

/-- Precision derivation accepts the pending power of every sample that tracks its exact
return and power within the settlement window under the ideal bound
(`AgreementTelemetryPrecision.precision_available`), and it refuses a NaN power.

**Not claimed:** soundness. The sound direction is not stated as a specification;
`AgreementTelemetryPrecision.precision_fields` states the fields of an accepted precision. -/
theorem precision_admit : Regula.ExecutableContract Agreement.precision (fun precision =>
    Regula.DecidesCompletely (·.isSome = true)
      (fun input : (Discount × Nat) × Binary32 =>
        ∃ (sample : Lifetime.PendingPrediction input.1.1) (returned power : ℚ),
          input.1.2 ≤ FeatureConstants.maxSettlement ∧
            AgreementReturn.Tracks sample input.1.2 returned power ∧
            AgreementReturn.IdealBound (CurrentArithmetic.numerical32 input.1.1.gamma)
              returned power ∧
            input.2 = sample.discountPower)
      (Function.uncurry (Function.uncurry precision))) :=
  ⟨{ complete := fun input ⟨sample, returned, power, room, tracked, ideal, same⟩ => by
       change (Agreement.precision input.1.1 input.1.2 input.2).isSome = true
       rw [same]
       exact AgreementTelemetryPrecision.precision_available input.1.1 sample input.1.2
         returned power room tracked ideal
     refused := ⟨((.g99, 0), ⟨0x7fc00000⟩), by decide⟩ }⟩

end AcornVerif.Decisions
