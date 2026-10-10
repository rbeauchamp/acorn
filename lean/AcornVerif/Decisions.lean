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
`Regula.Dependent.isOk` of it where the result type depends on the input. A statement of what
a kind does not state stands beside it as a requirement with no kind: the value of an accepted
result, under the name of the kind with `_value`, or a set of refused inputs beside a one-way
kind, under the name of the kind with `_refused`. `interest_potential_declared` states
pointwise a class of refused inputs that the two-way kind `interest_potential` also gives.
`world_enterable`, `tile_kind` and `terrain_read` keep their names beside the kinds of the
terrain: the verdict of an accepted entry, the refusal of a refused tile, and what the readers
of the terrain do with its result. `pay_and_act` and `perform_action` keep their names beside
the kinds of the paid actions: what an accepted paid action does with the energy, and where an
accepted move puts the body. `feature_image_admit` and `profile_admit_accepts` keep their
complete kinds about the feature words of an agent image of a construction beside the two-way
kinds `feature_image_admit_exact` and `profile_admit_exact`. `execute_prefix` keeps its name
beside the kind `agent_execute` of `Acorn.Decisions`: the safe path that an accepted fold
follows.

The round trips of the composed checkpoint admissions, the goal completion predicate, checked
translation and precision derivation are stated here because their theorems are in this
library, and so are the correspondence of the comparator with the agent's attempt and the bounds
of the comparator's campaigns. The accepted inputs of three host transitions and the two-way kind
of
`Host.Released.environment` are stated here because the observation of their inputs succeeds
by the terrain admission of `CurrentTerrain`. Each contract states only what its theorem
proves.

## Statements that keep no kind

A requirement with no kind is a statement that the Regula audit does not examine: that audit
checks only that its theorem is proved about the executing definition. Such a statement can
fix one direction only, and it need not show that both outcomes occur for its function.
Each docstring says what its statement gives and what it does not claim.

Eleven functions of this module have a contract and no kind. The reasons are four.

* The specification is a statement about runs of the executed world step, which the function
  runs: `Host.replayCertified`, `Host.ReplayCertificate.check` and
  `Host.World.advanceActions`. The step runs tests, and Regula's RG1009
  (https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/) refuses a kind whose
  specification reaches a test that its function runs. A kind needs the world step stated with
  propositions in the place of those tests.
* The input holds a state whose invariant names tests that the function runs, and Regula reads
  the type of the input of a specification (https://github.com/rbeauchamp/regula/issues/270):
  `Checkpoint.load` and `Agent.input`. For `Agent.input`, an audit of the kind stated with its
  witnesses named the eleven shared tests that `Acorn.Decisions.agent_input` lists.
* The statement gives an accepted input of a host transition whose statement in
  `Acorn.Decisions` keeps no kind: `Host.World.observe`, `Host.Attempt.finish` and
  `Host.Attempt.complete`. No theorem states which observations or
  steps succeed, and a specification of the accepted inputs would name `Host.World.observe` or
  `Host.World.step`, which run tests that these functions run.
* The statement relates the comparator to the agent's attempt, or bounds where a campaign ends
  unfinished: `Host.BaselineAttempt.tick`, `Host.runBaselineCampaign` and
  `Host.runRandomBaseline`. Their acceptance is the world step's or world generation's, and no
  theorem states which steps succeed or which configurations initialize. The comparator's
  campaign also refuses as unfinished when its fuel runs out, and the random baseline also
  refuses at campaign admission and on an unbounded plan.

Kinds for the functions of the first two reasons are remaining work of
https://github.com/rbeauchamp/acorn/issues/105.

## Tests that a specification does not share

No specification of a contract with a kind here reaches a test that its function runs: Regula's
RG1009 refuses such a contract, and `Acorn.Decisions` states the rule and lists the propositions
that take the place of the tests. The specification of `exp_saturation` names the strict order
`Binary32.Less`, `Attained` names the ownership `Host.Inventory.Owns`, and the specifications
of the checkpoint admissions name the resumable profile `FeatureProfile.Resumable`.

A specification also names no reader that its function calls where the data has constructors
or stored fields to state it by. `Attained` states a goal on the box indices, the inventory
fields and the clock of the world, with no observation, no count reader and no embedding of a
box position. `Harvests` states the tiles of a stance by equations on indices and coordinates
and the move by `Offset` and `Heads`, with no offset table, no facing position and no checked
translation. `squared_admit_exact` states the discrepancy of two words by their rational
values, with no unit map. A private lemma beside each connects the reader with the statement.

The kinds of the checkpoint admissions name the writers of the forms that they read, which
the admissions do not call.

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

/-- The feature words of a feature image of a receiving bank, criterion and feature space:
the words of the receiver's seed, tilings, unit capacity, feature capacity and criterion, the
clock and the tester words of the image's state, the words of its assignments and its primary
words. -/
def featureImageWords {actions : Word.Count} (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) {discounts : List Discount}
    (features : FeatureImage actions config criterion dimension discounts) :
    RawFeatureImage actions dimension discounts :=
  ⟨config.seed, config.tilings, config.units.count.toUInt32.toUInt16, dimension.capacity.toUInt32,
    criterion.tag.toUInt32.toUInt8, features.progress.clock,
    (testerWords features.progress).progress,
    features.assignments.map (Assignment.words dimension), features.primary⟩

/-- The feature words of an agent image of a construction: the raw image that the payload of
the image holds. -/
def featureWords (construction : AgentConstruction)
    (image : AgentImage Grid.interface construction.config construction.criterion
      construction.dimension) :
    RawFeatureImage Grid.actions construction.dimension demonLayout :=
  featureImageWords construction.config construction.criterion construction.dimension
    image.features

/-- The feature words of the initial agent of the construction of a profile. -/
def initialWords (profile : FeatureProfile) : RawFeatureImage Grid.actions narrow demonLayout :=
  featureWords (construction profile)
    (snapshotImage (construction profile) (AgentConstruction.initial _)).image

/-- The image of the initial agent of the resumable construction. -/
def initialImage : (construction resumable).Image :=
  snapshotImage (construction resumable) (AgentConstruction.initial _)

/-- The payload of the initial agent of the resumable construction. -/
def initialPayload : Payload narrow :=
  imagePayload (construction resumable)
    (snapshotImage (construction resumable) (AgentConstruction.initial _))

/-- The payload of the initial agent of the resumable construction with the format generation
zero in its header. Every other field is the field of `initialPayload`. -/
def stalePayload : Payload narrow :=
  { initialPayload with header := { initialPayload.header with version := 0 } }

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
of every stored total are accepted (`CurrentCheckpoint.sum_roundtrip`). The accepted input is
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
        rw [written, CurrentCheckpoint.sum_roundtrip]
        rfl⟩)
    ⟨(.reward, (0, ⟨0⟩)), by decide⟩
    ⟨(.reward, (1, ⟨0x4000000000000000⟩)), by decide⟩⟩

/-- Total admission returns the total whose words it reads (`CurrentCheckpoint.sum_roundtrip`).
A kind does not state the value of a result, so this statement is a requirement with no kind
beside the kind `sum_admit`. -/
theorem sum_admit_value : Regula.ExecutableContract admitSum (fun admit =>
    ∀ (quantity : Quantity) (record : SumCount quantity),
      admit quantity (sumWords record) = some record) :=
  ⟨fun _ => CurrentCheckpoint.sum_roundtrip⟩

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
`CurrentCheckpoint`. The kind of an admission states which inputs it accepts, and each admission
has a two-way kind: an accepted input is the written form of the value that it returns. The
demon columns and the lifetime image hold the input words unchanged, the feature image holds the
words of the receiver and of the admitted parts (`features_written`), and the payload and the
candidate are the forms of the image that they return (`payload_written`, `candidate_written`).
Apart from the lifetime admission, the type of a result depends on the receiving construction or
on the discounts, so each kind is about `Regula.Dependent.isSome` or `Regula.Dependent.isOk` of
the function, and the value that the admission returns is a separate requirement with no kind,
under the name of the kind with `_value`. -/

/-- The arguments of `Checkpoint.admitDemons`, in order. -/
structure DemonsAdmit where
  /-- The discounts of the prediction channels. -/
  discounts : List Discount
  /-- The column of totals. -/
  sums : List SumWords
  /-- The column of returns. -/
  returns : List Binary32
  /-- The column of errors. -/
  errors : List Binary32

/-- An admitted demon list holds the three input columns unchanged: each step of the
admission admits one total, one return and one error without changing a word
(`sum_written`, `Bounded32.admit_exact`), and columns of unequal lengths are refused. -/
private theorem demons_written (discounts : List Discount) :
    ∀ (sums : List SumWords) (returns errors : List Binary32)
      (records : DurableDemons discounts),
      admitDemons discounts sums returns errors = some records →
        sums = (demonColumns records).sums.toList ∧
          returns = (demonColumns records).returns.toList ∧
          errors = (demonColumns records).errors.toList := by
  induction discounts with
  | nil =>
    intro sums returns errors records admitted
    cases sums <;> cases returns <;> cases errors <;> simp only [admitDemons] at admitted
    · cases admitted
      exact ⟨rfl, rfl, rfl⟩
    all_goals exact nomatch admitted
  | cons discount rest ih =>
    intro sums returns errors records admitted
    cases sums <;> cases returns <;> cases errors <;> simp only [admitDemons] at admitted
    case cons.cons.cons sum sums value values error errors =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at admitted
      obtain ⟨total, totalAdmitted, prediction, predictionAdmitted, bounded, boundedAdmitted,
        tail, tailAdmitted, built⟩ := admitted
      cases built
      obtain ⟨tailSums, tailReturns, tailErrors⟩ := ih sums values errors tail tailAdmitted
      have first := sum_written totalAdmitted
      have second := (Bounded32.admit_exact _ _ _ predictionAdmitted).1
      have third := (Bounded32.admit_exact _ _ _ boundedAdmitted).1
      simp only [demonColumns, CurrentCheckpoint.prepend_toList]
      exact ⟨by rw [first, tailSums], by rw [← second, tailReturns], by rw [← third, tailErrors]⟩
    all_goals exact nomatch admitted

/-- Demon admission accepts exactly the columns of a durable demon list of the receiving
discounts. Accepted columns are the columns of the list that admission returns
(`demons_written`), and the columns of every durable list are accepted
(`CurrentCheckpoint.demons_roundtrip`). The accepted input is one channel with the zero total,
the zero return and the zero error, and the refused input is that channel with a NaN return.
`demons_admit_value` states the list that admission returns. -/
theorem demons_admit : Regula.ExecutableContract admitDemons (fun admit =>
    Regula.Decides (· = true)
      (fun input : DemonsAdmit => ∃ records : DurableDemons input.discounts,
        input.sums = (demonColumns records).sums.toList ∧
          input.returns = (demonColumns records).returns.toList ∧
          input.errors = (demonColumns records).errors.toList)
      (Regula.Dependent.isSome fun input : DemonsAdmit =>
        admit input.discounts input.sums input.returns input.errors)) :=
  ⟨.of_iff
    (fun input => ⟨fun accepted => by
        obtain ⟨records, admitted⟩ := Option.isSome_iff_exists.mp accepted
        exact ⟨records, demons_written _ _ _ _ records admitted⟩,
      fun ⟨records, written⟩ => by
        change (admitDemons input.discounts input.sums input.returns input.errors).isSome = true
        rw [written.1, written.2.1, written.2.2, CurrentCheckpoint.demons_roundtrip]
        rfl⟩)
    ⟨⟨[.g99], [(0, ⟨0⟩)], [.zero], [.zero]⟩, by decide +kernel⟩
    ⟨⟨[.g99], [(0, ⟨0⟩)], [⟨0x7fc00000⟩], [.zero]⟩, by decide +kernel⟩⟩

/-- Demon admission returns the durable list whose columns it reads
(`CurrentCheckpoint.demons_roundtrip`). A kind does not state the value of a result, so this
statement is a requirement with no kind beside the kind `demons_admit`. -/
theorem demons_admit_value : Regula.ExecutableContract admitDemons (fun admit =>
    ∀ (discounts : List Discount) (records : DurableDemons discounts),
      admit discounts (demonColumns records).sums.toList (demonColumns records).returns.toList
        (demonColumns records).errors.toList = some records) :=
  ⟨fun _ => CurrentCheckpoint.demons_roundtrip⟩

/-- An image whose overall reward total is a NaN word, with every other field zero. -/
def refusedLifetime : LifetimeWords :=
  ⟨(0, ⟨0x7ff8000000000000⟩), .replicate _ (0, ⟨0⟩), .replicate _ (0, ⟨0⟩),
    .replicate _ (0, ⟨0⟩), .replicate _ .zero, .replicate _ .zero, .replicate _ (0, ⟨0⟩),
    .replicate _ .initial, .replicate _ (0, 0, 0), .replicate _ (.replicate _ (0, 0, 0))⟩

/-- An admitted goal aggregate holds the three input counters unchanged. -/
private theorem goal_written {words : GoalWords} {record : GoalTotals}
    (admitted : admitGoal words = some record) : words = goalWords record := by
  unfold admitGoal at admitted
  split at admitted
  · cases admitted
    rfl
  · exact nomatch admitted

/-- A list that an admission accepts element by element holds the written words of the
admitted list, when each admitted element holds the written words of its value. -/
private theorem list_written {α β : Type} {encode : α → β} {admit : β → Option α}
    (written : ∀ {word : β} {value : α}, admit word = some value → word = encode value) :
    ∀ (words : List β) (values : List α), words.mapM admit = some values →
      words = values.map encode
  | [], values, admitted => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at admitted
    subst admitted
    rfl
  | word :: words, values, admitted => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at admitted
    obtain ⟨value, first, rest, others, built⟩ := admitted
    subst built
    rw [List.map_cons, ← written first, ← list_written written words rest others]

/-- A vector that an admission accepts element by element holds the written words of the
admitted vector, when each admitted element holds the written words of its value. -/
private theorem vector_written {α β : Type} {count : Nat} {encode : α → β}
    {admit : β → Option α}
    (written : ∀ {word : β} {value : α}, admit word = some value → word = encode value)
    {words : Vector β count} {values : Vector α count} (admitted : words.mapM admit = some values) :
    words = values.map encode := by
  have arrays : words.toArray.mapM admit = some values.toArray := by
    rw [← Vector.toArray_mapM, admitted]
    rfl
  have lists : words.toList.mapM admit = some values.toList := by
    rw [← Vector.toList_toArray, ← Vector.toList_toArray, ← Array.toList_mapM, arrays]
    rfl
  apply Vector.toList_inj.mp
  rw [Vector.toList_map]
  exact list_written written _ _ lists

/-- An admitted lifetime image holds the words of the durable record that admission returns,
and the option counters of that record are valid with no active option. Each part of the
admission admits its words without changing one (`sum_written`, `demons_written`,
`goal_written`), and the option counters are stored as read. -/
private theorem lifetime_written {raw : LifetimeWords} {record : Durable demonLayout}
    (admitted : admitLifetime raw = some record) :
    OptionsValid record.options none ∧ raw = lifetimeWords record := by
  unfold admitLifetime at admitted
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at admitted
  obtain ⟨reward, rewardAdmitted, family, familyAdmitted, history, historyAdmitted, demons,
    demonsAdmitted, errorHistory, errorHistoryAdmitted, goals, goalsAdmitted, cycles,
    cyclesAdmitted, built⟩ := admitted
  split at built
  · rename_i valid
    cases built
    obtain ⟨sums, returns, errors⟩ := demons_written _ _ _ _ _ demonsAdmitted
    have rewardWords := sum_written rewardAdmitted
    have familyWords := vector_written (admit := admitSum .reward)
      (encode := sumWords (quantity := .reward)) sum_written familyAdmitted
    have historyWords := vector_written (admit := admitSum .reward)
      (encode := sumWords (quantity := .reward)) sum_written historyAdmitted
    have errorHistoryWords := vector_written (admit := admitSum (.squaredError .g99))
      (encode := sumWords (quantity := .squaredError .g99)) sum_written errorHistoryAdmitted
    have goalsWords := vector_written (admit := admitGoal) (encode := goalWords) goal_written
      goalsAdmitted
    have cyclesWords := vector_written
      (admit := fun row : Vector GoalWords Acorn.FeatureConstants.cycleBins => row.mapM admitGoal)
      (encode := fun row : Vector GoalTotals Acorn.FeatureConstants.cycleBins => row.map goalWords)
      (fun admitted => vector_written (admit := admitGoal) (encode := goalWords) goal_written
        admitted) cyclesAdmitted
    refine ⟨valid, (show raw = ⟨raw.reward, raw.rewardByFamily, raw.rewardHistory,
      raw.squaredErrors, raw.returns, raw.errors, raw.errorHistory, raw.options, raw.goals,
      raw.goalCycles⟩ from rfl).trans ?_⟩
    rw [rewardWords, familyWords, historyWords, Vector.toList_inj.mp sums,
      Vector.toList_inj.mp returns, Vector.toList_inj.mp errors, errorHistoryWords, goalsWords,
      cyclesWords]
    rfl
  · exact nomatch built

/-- Lifetime admission accepts exactly the word image of a durable lifetime record whose
option counters are valid with no active option. An accepted image is the image of the record
that admission returns (`lifetime_written`), and the image of every such record is accepted
(`CurrentCheckpoint.lifetime_roundtrip`). The accepted input is the image of the lifetime
record of the initial agent of the resumable construction. The refused input is an image whose
overall reward total is a NaN word. -/
theorem lifetime_admit : Regula.ExecutableContract admitLifetime
    (Regula.Decides (·.isSome = true) (fun raw =>
      ∃ record : Durable demonLayout, OptionsValid record.options none ∧
        raw = lifetimeWords record)) :=
  ⟨decides
    (fun raw => ⟨fun accepted => by
        obtain ⟨record, admitted⟩ := Option.isSome_iff_exists.mp accepted
        exact ⟨record, lifetime_written admitted⟩,
      fun ⟨record, valid, written⟩ => by
        rw [written, CurrentCheckpoint.lifetime_roundtrip record valid]
        rfl⟩)
    ⟨lifetimeWords initialImage.image.lifetime, initialImage.image.lifetime,
      initialImage.image.episodes, rfl⟩
    ⟨refusedLifetime, fun ⟨record, valid, written⟩ => by
      have admitted := CurrentCheckpoint.lifetime_roundtrip record valid
      rw [← written] at admitted
      have illegal : ¬LegalSum .reward 0 ⟨0x7ff8000000000000⟩ := by decide
      simp [admitLifetime, admitSum, SumCount.admit, refusedLifetime, illegal] at admitted⟩⟩

/-- The arguments of `Features.FeatureImage.admit`, in order. -/
structure FeatureImageAdmit where
  /-- The action count. -/
  actions : Word.Count
  /-- The bank configuration. -/
  config : Features.Config
  /-- The criterion. -/
  criterion : Criterion
  /-- The dimension of the feature space. -/
  dimension : Dimension
  /-- The discounts of the prediction channels. -/
  discounts : List Discount
  /-- The raw image. -/
  raw : RawFeatureImage actions dimension discounts

/-- Feature-image admission accepts the feature words of every agent image of a construction
(`CurrentCheckpoint.feature_roundtrip`), and it refuses the words of an image with another
seed. `feature_image_admit_exact` states the two-way kind over every bank, criterion, feature
space, action count and horizon layout, and `feature_image_admit_value` states the features
that it returns. -/
theorem feature_image_admit : Regula.ExecutableContract @FeatureImage.admit (fun admit =>
    Regula.DecidesCompletely (· = true)
      (fun input : FeatureImageAdmit => ∃ (construction : AgentConstruction)
        (image : AgentImage Grid.interface construction.config construction.criterion
          construction.dimension),
        input = ⟨Grid.actions, construction.config, construction.criterion,
          construction.dimension, demonLayout, featureWords construction image⟩)
      (Regula.Dependent.isSome fun input : FeatureImageAdmit =>
        @admit input.actions input.config input.criterion input.dimension input.discounts
          input.raw)) :=
  ⟨{ complete := fun input ⟨construction, image, written⟩ => by
       subst written
       change (FeatureImage.admit construction.config construction.criterion construction.dimension
         (featureWords construction image)).isSome = true
       rw [featureWords, featureImageWords, CurrentCheckpoint.feature_roundtrip construction image]
       rfl
     refused := ⟨⟨Grid.actions, bank, .discounted, narrow, demonLayout,
       { initialWords resumable with seed := 1 }⟩, fun accepted =>
         absurd accepted (by decide)⟩ }⟩

/-- Feature-image admission returns the features of the image whose words it reads
(`CurrentCheckpoint.feature_roundtrip`). A kind does not state the value of a result, so this
statement is a requirement with no kind beside the kind `feature_image_admit`. -/
theorem feature_image_admit_value :
    Regula.ExecutableContract @FeatureImage.admit (fun admit =>
    ∀ (construction : AgentConstruction)
      (image : AgentImage Grid.interface construction.config construction.criterion
        construction.dimension),
      admit construction.config construction.criterion construction.dimension
        ⟨construction.config.seed, construction.config.tilings,
          construction.config.units.count.toUInt32.toUInt16,
          construction.dimension.capacity.toUInt32, construction.criterion.tag.toUInt32.toUInt8,
          image.features.progress.clock, (testerWords image.features.progress).progress,
          image.features.assignments.map (Assignment.words construction.dimension),
          image.features.primary⟩ = some image.features) :=
  ⟨CurrentCheckpoint.feature_roundtrip⟩

/-- An admitted raw feature image holds the feature words of the image that admission returns.
Admission compares the receiver's words with the stored ones, and the tester state and each
assignment are admitted without changing a word (`Progress.admit_words`,
`Assignment.admit_words`). -/
private theorem features_written {actions : Word.Count} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}
    {raw : RawFeatureImage actions dimension discounts}
    {features : FeatureImage actions config criterion dimension discounts}
    (admitted : FeatureImage.admit config criterion dimension raw = some features) :
    raw = featureImageWords config criterion dimension features := by
  obtain ⟨seed, tilings, units, capacity, tag, clock, progress, assignments, primary⟩ := raw
  unfold FeatureImage.admit at admitted
  split at admitted
  · contradiction
  · rename_i identity
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at identity
    obtain ⟨⟨⟨⟨rfl, rfl⟩, unitsCount⟩, capacityCount⟩, rfl⟩ := identity
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at admitted
    obtain ⟨state, stateAdmitted, admittedAssignments, assignmentsAdmitted, built⟩ := admitted
    split at built
    · cases built
      obtain ⟨rfl, rfl⟩ := Progress.admit_words _ _ _ stateAdmitted
      have assignmentsWords := vector_written (admit := Assignment.admit dimension config)
        (encode := Assignment.words dimension)
        (fun admitted => Assignment.admit_words dimension _ _ admitted) assignmentsAdmitted
      subst assignmentsWords
      have unitsWord : config.units.count.toUInt32.toUInt16 = units := by
        apply UInt16.toNat_inj.mp
        rw [unitsCount]
        have := config.units.bounded
        change (config.units.count % 2^32) % 2^16 = config.units.count
        omega
      have capacityWord : dimension.capacity.toUInt32 = capacity := by
        apply UInt32.toNat_inj.mp
        rw [capacityCount]
        exact Nat.mod_eq_of_lt dimension.wordBound
      have tagWord : criterion.tag.toUInt32.toUInt8 = criterion.tag := by
        cases criterion <;> rfl
      rw [featureImageWords, unitsWord, capacityWord, tagWord]
      rfl
    · contradiction

/-- Feature-image admission accepts exactly the feature words of a feature image of the
receiving bank, criterion and feature space (`CurrentCheckpoint.features_roundtrip`, and
`features_written` for the converse). -/
private theorem feature_image_iff {actions : Word.Count} (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) {discounts : List Discount}
    (raw : RawFeatureImage actions dimension discounts) :
    (FeatureImage.admit config criterion dimension raw).isSome = true ↔
      ∃ features : FeatureImage actions config criterion dimension discounts,
        raw = featureImageWords config criterion dimension features :=
  ⟨fun accepted => (Option.isSome_iff_exists.mp accepted).elim fun features admitted =>
      ⟨features, features_written admitted⟩,
    fun ⟨features, written⟩ => by
      rw [written, featureImageWords, CurrentCheckpoint.features_roundtrip]
      rfl⟩

/-- Feature-image admission accepts exactly the feature words of a feature image of the
receiving bank, criterion and feature space, for every action count and horizon layout
(`feature_image_iff`). The specification names the writer of the feature words, which
admission does not call. The accepted input is the feature words of the initial agent of the
resumable construction; the refused input is those words with the seed one in the place of the
seed of `bank`. -/
theorem feature_image_admit_exact : Regula.ExecutableContract @FeatureImage.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : FeatureImageAdmit =>
        ∃ features : FeatureImage input.actions input.config input.criterion input.dimension
            input.discounts,
          input.raw = featureImageWords input.config input.criterion input.dimension features)
      (Regula.Dependent.isSome fun input : FeatureImageAdmit =>
        @admit input.actions input.config input.criterion input.dimension input.discounts
          input.raw)) :=
  ⟨.of_iff (fun input => feature_image_iff input.config input.criterion input.dimension input.raw)
    ⟨⟨Grid.actions, bank, .discounted, narrow, demonLayout, initialWords resumable⟩,
      (feature_image_iff bank .discounted narrow (initialWords resumable)).mpr
        ⟨initialImage.image.features, rfl⟩⟩
    ⟨⟨Grid.actions, bank, .discounted, narrow, demonLayout,
      { initialWords resumable with seed := 1 }⟩, fun accepted => absurd accepted (by decide)⟩⟩

/-- An admitted payload is the payload of the image that admission returns, and the receiving
profile is resumable. Header admission fixes every header word but the clock
(`admitHeader_checks`); feature admission fixes the clock, the assignments, the primary words
and the tester words (`features_written`); lifetime admission fixes the lifetime words
(`lifetime_written`). -/
private theorem payload_written {construction : AgentConstruction}
    {payload : Payload construction.dimension} {image : construction.Image}
    (admitted : admitPayload construction payload = .ok image) :
    Resumable construction.profile ∧ payload = imagePayload construction image := by
  obtain ⟨⟨version, capacity, learners, seed, clock, criterion, gain, tilings, units, supported,
    order⟩, assignments, primary, lifetime, ⟨stream, credit, replaced, last, ⟨unitWords, bound⟩⟩⟩ :=
    payload
  unfold admitPayload at admitted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    at admitted
  split at admitted <;> try contradiction
  rename_i rate headerAdmitted
  split at admitted <;> try contradiction
  rename_i features featuresAdmitted
  split at admitted <;> try contradiction
  rename_i record lifetimeAdmitted
  split at admitted <;> try contradiction
  rename_i valid
  cases admitted
  obtain ⟨rfl, rfl, rateAdmitted, rfl, rfl, rfl, enabled, rfl, rfl, unitsCount, rfl⟩ :=
    (admitHeader_checks construction _ rate).mp headerAdmitted
  obtain rfl := (Bounded32.admit_exact _ _ _ rateAdmitted).1
  have written := features_written featuresAdmitted
  injection written with _ _ _ _ _ clockWord progressWords assignmentsWords primaryWord
  injection progressWords with streamWord creditWord replacedWord lastWord unitsWords
  subst clockWord assignmentsWords primaryWord streamWord creditWord replacedWord lastWord
    unitsWords
  obtain ⟨-, rfl⟩ := lifetime_written lifetimeAdmitted
  have resumable : Resumable construction.profile :=
    (FeatureProfile.checkpoint_iff _).mp enabled
  have countWord : construction.config.units.count.toUInt32.toNat =
      construction.config.units.count :=
    Nat.mod_eq_of_lt (by have := construction.config.units.bounded; omega)
  have unitsWord : units = construction.config.units.count.toUInt32 :=
    UInt32.toNat_inj.mp (unitsCount.trans countWord.symm)
  subst unitsWord
  refine ⟨resumable, ?_⟩
  simp only [imagePayload, resumable, ↓reduceIte]

/-- An accepted byte list is the encoding of the payload of the image that loading returns,
and the receiving profile is resumable: decoding reads only the bytes that the writer writes
(`Checkpoint.decode_written`), and payload admission accepts only the payload of its image
(`payload_written`). -/
private theorem candidate_written {construction : AgentConstruction} {bytes : List UInt8}
    {image : construction.Image} (loaded : loadCandidate construction bytes = .ok image) :
    Resumable construction.profile ∧
      bytes = encode construction.dimension (imagePayload construction image) := by
  unfold loadCandidate at loaded
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at loaded
  split at loaded <;> try contradiction
  split at loaded <;> try contradiction
  split at loaded <;> try contradiction
  split at loaded <;> try contradiction
  rename_i payload decoded
  obtain ⟨resumable, written⟩ := payload_written loaded
  exact ⟨resumable, by rw [decode_written _ _ _ decoded, written]⟩

/-- Payload admission accepts exactly the payloads of the agent images of a resumable
construction (`CurrentCheckpoint.image_roundtrip`, and `payload_written` for the converse). -/
private theorem payload_iff (construction : AgentConstruction)
    (payload : Payload construction.dimension) :
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
construction (`payload_iff`). The accepted input is `initialPayload` under the resumable
construction, and the refused input is `stalePayload` under the same construction: the two
payloads differ in the format generation of the header alone, so the refusal reads the
payload. `payload_admit_value` states the image that it returns. -/
theorem payload_admit : Regula.ExecutableContract admitPayload (fun admit =>
    Regula.Decides (· = true)
      (fun input : (construction : AgentConstruction) × Payload construction.dimension =>
        ∃ image : input.1.Image, Resumable input.1.profile ∧
          input.2 = imagePayload input.1 image)
      (Regula.Dependent.isOk fun input :
          (construction : AgentConstruction) × Payload construction.dimension =>
        admit input.1 input.2)) :=
  ⟨decides (fun input => payload_iff input.1 input.2)
    ⟨⟨construction resumable, initialPayload⟩, initialImage, by decide, rfl⟩
    ⟨⟨construction resumable, stalePayload⟩, fun accepted => by
      have accepted := (payload_iff (construction resumable) stalePayload).mpr accepted
      cases admitted : admitPayload (construction resumable) stalePayload with
      | error refusal =>
        rw [admitted] at accepted
        exact Bool.false_ne_true accepted
      | ok image =>
        unfold admitPayload at admitted
        cases header : admitHeader (construction resumable) stalePayload.header with
        | error refusal =>
          rw [header] at admitted
          exact nomatch admitted
        | ok gain =>
          exact absurd ((admitHeader_iff _ _ _).mp header).version (by decide)⟩⟩

/-- Payload admission returns the image whose payload it reads
(`CurrentCheckpoint.image_roundtrip`). A kind does not state the value of a result, so this
statement is a requirement with no kind beside the kind `payload_admit`. -/
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
        bytes = encode construction.dimension (imagePayload construction image) := by
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
construction (`candidate_iff`). The accepted input is the encoding of `initialPayload` under
the resumable construction; the refused input is the empty byte list. `candidate_load_value`
states the image that it returns. -/
theorem candidate_load : Regula.ExecutableContract loadCandidate (fun load =>
    Regula.Decides (· = true)
      (fun input : AgentConstruction × List UInt8 => ∃ image : input.1.Image,
        Resumable input.1.profile ∧
          input.2 = encode input.1.dimension (imagePayload input.1 image))
      (Regula.Dependent.isOk fun input : AgentConstruction × List UInt8 =>
        load input.1 input.2)) :=
  ⟨decides (fun input => candidate_iff input.1 input.2)
    ⟨(construction resumable, encode narrow initialPayload), initialImage, by decide, rfl⟩
    ⟨(construction resumable, []), fun ⟨image, _, written⟩ => by
      change ([] : List UInt8) = encode (construction resumable).dimension
        (imagePayload (construction resumable) image) at written
      have large := CurrentCheckpoint.encoded_minimum (construction resumable).dimension
        (imagePayload (construction resumable) image)
      rw [← written] at large
      exact absurd large (by decide)⟩⟩

/-- Candidate loading returns the image whose encoded payload it reads
(`CurrentCheckpoint.candidate_roundtrip`). A kind does not state the value of a result, so
this statement is a requirement with no kind beside the kind `candidate_load`. -/
theorem candidate_load_value : Regula.ExecutableContract loadCandidate (fun load =>
    ∀ (construction : AgentConstruction) (image : construction.Image),
      construction.profile.checkpointSupported = true →
        load construction (encode construction.dimension (imagePayload construction image)) =
          .ok image) :=
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

/-- The arguments of `Handcrafted.FeatureProfile.admit`, in order. -/
structure ProfileAdmit where
  /-- The profile. -/
  profile : FeatureProfile
  /-- The action count. -/
  actions : Word.Count
  /-- The bank configuration. -/
  config : Features.Config
  /-- The criterion. -/
  criterion : Criterion
  /-- The dimension of the feature space. -/
  dimension : Dimension
  /-- The discounts of the prediction channels. -/
  discounts : List Discount
  /-- The raw image. -/
  raw : RawFeatureImage actions dimension discounts

/-- Profile admission accepts only under a resumable profile
(`FeatureProfile.unsupported_refuses`). The specification names the four discriminants of the
profile. The accepted input is the feature words of the initial agent of a resumable
construction (`CurrentCheckpoint.feature_roundtrip`).

**Not claimed:** completeness for this specification. A resumable profile refuses an image that
`FeatureImage.admit` refuses; `profile_admit_exact` states what it accepts. -/
theorem profile_admit_sound : Regula.ExecutableContract @FeatureProfile.admit (fun admit =>
    Regula.DecidesSoundly (· = true) (fun input : ProfileAdmit => Resumable input.profile)
      (Regula.Dependent.isSome fun input : ProfileAdmit =>
        @admit input.profile input.actions input.config input.criterion input.dimension
          input.discounts input.raw)) :=
  ⟨{ sound := fun input accepted => by
       have accepted : (input.profile.admit input.config input.criterion input.dimension
         input.raw).isSome = true := accepted
       cases supported : input.profile.checkpointSupported with
       | true => exact (FeatureProfile.checkpoint_iff _).mp supported
       | false =>
         rw [FeatureProfile.unsupported_refuses input.profile input.config input.criterion
           input.dimension input.raw supported] at accepted
         exact absurd accepted Bool.false_ne_true
     accepted := ⟨⟨resumable, Grid.actions, bank, .discounted, narrow, demonLayout,
       initialWords resumable⟩, by
         change (FeatureProfile.admit resumable bank .discounted narrow
           (initialWords resumable)).isSome = true
         have supported : resumable.checkpointSupported = true := by decide
         simp only [FeatureProfile.admit, supported, ↓reduceIte]
         exact Option.isSome_iff_exists.mpr ⟨_, CurrentCheckpoint.feature_roundtrip
           (construction resumable)
           (snapshotImage (construction resumable) (AgentConstruction.initial _)).image⟩⟩ }⟩

/-- Profile admission accepts the feature words of every agent image of a resumable
construction (`CurrentCheckpoint.feature_roundtrip`), and it refuses, under the resumable
profile, the words of the initial agent with the seed one in the place of the seed of `bank`:
the refusal reads the raw image. `profile_admit_exact` states the two-way kind over every bank,
criterion, feature space, action count and horizon layout, `profile_admit` in `Acorn.Decisions`
states the refusal under another profile, and `profile_admit_accepts_value` states the
features that it returns. -/
theorem profile_admit_accepts : Regula.ExecutableContract @FeatureProfile.admit (fun admit =>
    Regula.DecidesCompletely (· = true)
      (fun input : ProfileAdmit => ∃ (construction : AgentConstruction)
        (image : AgentImage Grid.interface construction.config construction.criterion
          construction.dimension), Resumable construction.profile ∧
        input = ⟨construction.profile, Grid.actions, construction.config, construction.criterion,
          construction.dimension, demonLayout, featureWords construction image⟩)
      (Regula.Dependent.isSome fun input : ProfileAdmit =>
        @admit input.profile input.actions input.config input.criterion input.dimension
          input.discounts input.raw)) :=
  ⟨{ complete := fun input ⟨construction, image, supported, written⟩ => by
       subst written
       change (FeatureProfile.admit construction.profile construction.config construction.criterion
         construction.dimension (featureWords construction image)).isSome = true
       have enabled := (FeatureProfile.checkpoint_iff construction.profile).mpr supported
       simp only [FeatureProfile.admit, enabled, ↓reduceIte]
       rw [featureWords, featureImageWords, CurrentCheckpoint.feature_roundtrip construction image]
       rfl
     refused := ⟨⟨resumable, Grid.actions, bank, .discounted, narrow, demonLayout,
       { initialWords resumable with seed := 1 }⟩, fun accepted =>
         absurd accepted (by decide)⟩ }⟩

/-- Profile admission returns the features of the image whose words it reads, under a
resumable construction (`CurrentCheckpoint.feature_roundtrip`). A kind does not state the
value of a result, so this statement is a requirement with no kind beside the kind
`profile_admit_accepts`. -/
theorem profile_admit_accepts_value : Regula.ExecutableContract @FeatureProfile.admit (fun admit =>
    ∀ (construction : AgentConstruction)
      (image : AgentImage Grid.interface construction.config construction.criterion
        construction.dimension),
      construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
        construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned →
      admit construction.profile construction.config construction.criterion
        construction.dimension
        ⟨construction.config.seed, construction.config.tilings,
          construction.config.units.count.toUInt32.toUInt16,
          construction.dimension.capacity.toUInt32, construction.criterion.tag.toUInt32.toUInt8,
          image.features.progress.clock, (testerWords image.features.progress).progress,
          image.features.assignments.map (Assignment.words construction.dimension),
          image.features.primary⟩ = some image.features) :=
  ⟨fun construction image resumable => by
    have supported := (FeatureProfile.checkpoint_iff construction.profile).mpr resumable
    simp only [FeatureProfile.admit, supported, ↓reduceIte]
    exact CurrentCheckpoint.feature_roundtrip construction image⟩

/-- Profile admission accepts exactly, under a resumable profile, the feature words of a feature
image of the receiving bank, criterion and feature space, for every action count and horizon
layout (`feature_image_iff`, and `FeatureProfile.unsupported_refuses` under another profile).
The specification names the four discriminants of the profile and the writer of the feature
words, which admission does not call. The accepted input is the feature words of the initial
agent of the resumable construction under the resumable profile; the refused input is those
words with the seed one in the place of the seed of `bank`, under the same profile. -/
theorem profile_admit_exact : Regula.ExecutableContract @FeatureProfile.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : ProfileAdmit => Resumable input.profile ∧
        ∃ features : FeatureImage input.actions input.config input.criterion input.dimension
            input.discounts,
          input.raw = featureImageWords input.config input.criterion input.dimension features)
      (Regula.Dependent.isSome fun input : ProfileAdmit =>
        @admit input.profile input.actions input.config input.criterion input.dimension
          input.discounts input.raw)) :=
  ⟨.of_iff
    (fun input => by
      change (input.profile.admit input.config input.criterion input.dimension
        input.raw).isSome = true ↔ _
      cases supported : input.profile.checkpointSupported with
      | true =>
        simp only [FeatureProfile.admit, supported, ↓reduceIte]
        exact ⟨fun accepted => ⟨(FeatureProfile.checkpoint_iff _).mp supported,
            (feature_image_iff _ _ _ _).mp accepted⟩,
          fun ⟨_, written⟩ => (feature_image_iff _ _ _ _).mpr written⟩
      | false =>
        rw [FeatureProfile.unsupported_refuses _ _ _ _ _ supported]
        exact ⟨fun accepted => absurd accepted Bool.false_ne_true,
          fun ⟨resumable, _⟩ => absurd
            (supported.symm.trans ((FeatureProfile.checkpoint_iff _).mpr resumable))
            Bool.false_ne_true⟩)
    ⟨⟨resumable, Grid.actions, bank, .discounted, narrow, demonLayout, initialWords resumable⟩, by
      change (FeatureProfile.admit resumable bank .discounted narrow
        (initialWords resumable)).isSome = true
      have supported : resumable.checkpointSupported = true := by decide
      simp only [FeatureProfile.admit, supported, ↓reduceIte]
      exact (feature_image_iff bank .discounted narrow (initialWords resumable)).mpr
        ⟨initialImage.image.features, rfl⟩⟩
    ⟨⟨resumable, Grid.actions, bank, .discounted, narrow, demonLayout,
      { initialWords resumable with seed := 1 }⟩, fun accepted => absurd accepted (by decide)⟩⟩

/-- Loading accepts the bytes that a resumable construction saved from any state, for every
receiver of that construction (`CurrentCheckpoint.save_load`). The refusal under every other
profile is `checkpoint_load` in `Acorn.Decisions`.

The statement keeps no kind. Regula v0.10.0 refuses the kind under RG1009
(https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/): the input holds an agent state, an
invariant of that state names tests that loading runs, and the rule reads the type of the input
(https://github.com/rbeauchamp/regula/issues/270). -/
theorem checkpoint_load_accepts : Regula.ExecutableContract Checkpoint.load (fun load =>
    ∀ (construction : AgentConstruction) (source receiver : construction.State),
      construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
        construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned →
      (load construction receiver
        (encode construction.dimension (snapshot construction source))).isOk = true) :=
  ⟨fun construction source receiver resumable => by
    have supported := (FeatureProfile.checkpoint_iff construction.profile).mpr resumable
    obtain ⟨restored, -, loaded⟩ :=
      CurrentCheckpoint.save_load construction source receiver supported
    rw [loaded]
    rfl⟩

/-- Each event that the agent accepts satisfies the contract of its edge: an act runs the
agent's step and returns its decision, the bookkeeping events keep the learners, a clear
returns the initial agent, a restore returns the restored agent and a stop keeps the state
(`CurrentAgent.edge_contract`). `Acorn.Decisions.agent_input` states which events it accepts,
and keeps no kind for the reason given there; this statement is a requirement with no kind
beside it. -/
theorem agent_input_edges : Regula.ExecutableContract @Agent.input (fun input =>
    ∀ {profile config criterion dimension planning}
      (before after : Agent Grid.interface profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (stopped : Bool),
      input before event = .ok (after, stopped) → CurrentAgent.EdgeContract before event after) :=
  ⟨fun before after event stopped executed =>
    CurrentAgent.edge_contract before after event stopped executed⟩

/-- An accepted compiled fold from cold initialization follows a safe path from the initial
agent: every intermediate agent keeps the invariant, and each edge satisfies its contract
(`CurrentAgent.native_prefix`). `Acorn.Decisions.agent_execute` states the kind; a kind does
not state the value of a result, so this statement is a requirement with no kind beside it. -/
theorem execute_prefix : Regula.ExecutableContract AgentConstruction.execute (fun execute =>
    ∀ (admitted : DefaultConstruction) (finalState : admitted.construction.State)
      (events : List (AgentInput admitted.construction.config admitted.construction.criterion
        admitted.construction.dimension)) (stopped : Bool),
      execute admitted events = .ok (finalState, stopped) →
        CurrentAgent.SafePath admitted.construction.initial.agent events finalState.agent
          stopped) :=
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
