/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Regula.Contract
import Std.Data.String.ToNat
import Acorn.Host.AgentArguments
import Acorn.Host.Attempt
import Acorn.Host.Cli
import AcornVerif.AgreementLifecycle
import AcornVerif.AgreementTelemetryPrecision
import AcornVerif.CurrentActions
import AcornVerif.CurrentAgent
import AcornVerif.CurrentAgreement
import AcornVerif.CurrentCertificates
import AcornVerif.CurrentCheckpoint
import AcornVerif.CurrentControl
import AcornVerif.CurrentExponential
import AcornVerif.CurrentLifetime
import AcornVerif.CurrentOffPolicy
import AcornVerif.CurrentRunner
import AcornVerif.CurrentSpawn
import AcornVerif.CurrentTemporal
import AcornVerif.CurrentTerrain
import AcornVerif.Decimal
import AcornVerif.Endurance
import AcornVerif.FloatLibBridge
import AcornVerif.TemporalSupport

/-!
# Decision contracts proved in the proof library

`Acorn.Decisions` states the contracts of the executing library that follow from Lean core
alone, and it registers the decisions of that library, those whose kinds are stated here
included. A contract here states a direction whose proof needs this library. The
legality of every stored lifetime total rests on the real-valued bounds of
`CurrentLifetime.stored_sum_legal`. What an accepted certificate establishes is a statement
about runs of the executed world step, proved in `CurrentCertificates`.

No certificate checker is complete about its goal: a refused certificate establishes nothing
about whether the goal can be reached. The blocked checker and the stance checker carry the
sound kind, with an accepted certificate as the witness, and so do the constructors of their
certificates. The replay checker and the constructor of its certificate carry the two-way kind
about the action list: they accept exactly an action list of at least one and at most the cap
actions whose run of the executed world step, from the world with the goal installed, ends in a
world in which the goal is attained (`Replays`). The walkable test is not a certificate checker,
and it carries the two-way kind.

A function of this module with an argument or result type that depends on an earlier argument
states its kind in the forms that `Acorn.Decisions` describes: about the function applied to
every field of a structure of its arguments, and about `Regula.Dependent.isSome` or
`Regula.Dependent.isOk` of it where the result type depends on the input. A statement of what a
kind does not state stands beside it as a requirement with no kind: the value of an accepted
result, under the name of the kind with `_value`, or a set of refused inputs beside a one-way
kind, under the name of the kind with `_refused`. `payload_admit_value` and
`candidate_load_value` stand in the same way beside the requirements `payload_admit` and
`candidate_load`, which also keep no kind, `checkpoint_load_accepts` beside the sound kind
`checkpoint_load` states the saved bytes that loading accepts and the state that it returns, and
`checkpoint_resume_accepts` beside the sound kind `checkpoint_resume` states the state that
resuming them returns.
`interest_potential_declared` states pointwise a class of refused inputs that the two-way kind
`interest_potential` also gives.
`world_enterable`, `tile_kind` and `terrain_read` keep their names beside the kinds of the
terrain: the verdict of an accepted entry, the refusal of a refused tile, and what the readers
of the terrain do with its result. `pay_and_act` and `perform_action` keep their names beside
the kinds of the paid actions: what an accepted paid action does with the energy, and where an
accepted move puts the body. `execute_prefix` states the safe path that the compiled fold
follows.

The round trips of the composed checkpoint admissions, the goal completion predicate, checked
translation and precision derivation are stated here because their theorems are in this
library, and so are the kinds of the count and of the rule of the spawn search, the result of
the search, an accepted input of world generation, the correspondence of the comparator with
the agent's attempt, the bounds of the comparator's campaigns and the stored-word checks of a
learner. The accepted inputs of the observation, of finishing and of the fold, and the two-way
kind of `Host.Released.environment`, are stated here because the observation of their inputs
succeeds by the terrain admission of `CurrentTerrain`. The two-way kinds of the parsers
`Host.Cli.natural` and `Host.AgentArguments.admit` are stated here because their proofs use what
Lean's `Std.Data.String.ToNat` states about `String.toNat?`, and `Acorn.Decisions` imports no
module of `Std`. Each contract states only what its theorem proves.

## Statements that keep no kind

A requirement with no kind is a statement that the Regula audit does not examine: that audit
checks only that its theorem is proved about the executing definition. Such a statement can
fix one direction only, and it need not show that both outcomes occur for its function.
Each docstring says what its statement gives and what it does not claim.

Sixteen functions of this module have a contract and no kind. The reasons are six. Sixteen
more are no decisions, and their statements say what they are: `Agent.input`,
`AgentConstruction.execute` and `Checkpoint.managedWords` refuse no input, and thirteen
definitions that specifications share with their functions have the statements of the section
"Definitions that specifications share".

* The specification is a round trip of the written form: `Checkpoint.admitPayload` and
  `Checkpoint.loadCandidate` accept exactly the payloads, and their encodings, of the agent images
  of a resumable construction. The specification quantifies over agent images, and the type of an
  image declares the invariants of its learners, which name the stored-word check
  `NumericState.resumable` and the other tests that the admissions run. It names the writer
  `Checkpoint.imagePayload` too, whose format holds the reader of each field beside its writer and
  so reaches the reader's tests. An audit with Regula v0.11.0 refused the kind under RG1009 for
  those tests. Which images there are depends on them, so the two sides share them in substance and
  not only by the reading: a kind needs a statement of the written payloads that does not depend on
  those tests. Kinds for these two functions are remaining work of
  https://github.com/rbeauchamp/acorn/issues/105, and they need a statement of the written
  payloads that does not depend on the tests the admissions run.
* The statement gives an accepted input of a host transition whose statement in
  `Acorn.Decisions` keeps no kind: `Host.World.observe`, `Host.Attempt.finish`,
  `Host.Attempt.complete` and `Host.World.initial`. No theorem states which observations or
  steps succeed or which configurations initialize. A specification of the accepted inputs of
  the first three would name `Host.World.observe`, which runs the ownership test
  `Host.Inventory.owns` that they run.
* The statement relates the comparator to the agent's attempt, or bounds where a campaign ends
  unfinished: `Host.BaselineAttempt.tick`, `Host.runBaselineCampaign` and
  `Host.runRandomBaseline`. Their acceptance is the world step's or world generation's, and no
  theorem states which steps succeed or which configurations initialize. The comparator's
  campaign also refuses as unfinished when its fuel runs out, and the random baseline also
  refuses at campaign admission and on an unbounded plan.
* The statement is about the result of the spawn search of world generation, `Host.selectSpawn`,
  and carries an accepted input. The search stops at the first rich candidate of its spiral, so
  which tiles it reads depends on the kinds and walkability of the tiles before, and no theorem
  states which worlds it accepts.
* The specification reads a part of the input whose type declares an invariant that names tests
  that the function runs: the stored-word check of a learner, `NumericState.resumable`. Its kind
  was proved, and Regula's collector refuses it under RG1009 for `Binary32.isNaN` and
  `Binary32.less`, which the specification reaches only through the declaration of the learner
  state and the function runs in the interval test of a pruning reference
  (https://github.com/rbeauchamp/regula/issues/320). The kind is remaining work of
  https://github.com/rbeauchamp/acorn/issues/105.
* The verdict is one component of a pair, and a component of that pair has a type that depends
  on an earlier argument: whether `Features.beginExploration` begins a run, where the run that
  begins, the verdict component, depends on the action count; whether
  `Features.Preceding.advance` records a passage, whether `Lifetime.DemonStats.advanceSlot`
  settles a slot and whether `NumericState.firstLoopElement` prunes an index, beside a state that
  depends on the dimension, the discount or the configuration; and whether
  `Checkpoint.loadKeeping`, loading that keeps its receiver, refuses the bytes, beside a state
  that depends on the construction. Regula reads a result whose type depends on the input only
  through `Regula.Dependent.isSome` and `Regula.Dependent.isOk`, of an `Option` or an `Except`.
  Each statement states the verdict for every input and names an input of each verdict.

## Tests that a specification does not share

No specification of a contract with a kind here reaches a test that its function runs: Regula's
RG1009 refuses such a contract, and `Acorn.Decisions` states the rule and lists the propositions
that take the place of the tests. The specification of `exp_saturation` names the strict order
`Binary32.Less`, and `Host.World.Attained` names the ownership `Host.Inventory.Owns`. The
specifications of the requirements `payload_admit` and `candidate_load`, which keep no kind,
likewise name the resumable profile `FeatureProfile.Resumable` in the place of the test that the
admissions run. The specifications of `replay_certified`, `replay_check` and `advance_actions`
name runs of the world step, which decides `Host.World.GoalSatisfied`, `Host.FoodDue` and
`Host.Inventory.Owns` in the place of its tests and compares actions, tile kinds and positions by
their decidable equality.

A specification also names no reader that its function calls where the data has constructors
or stored fields to state it by. `Host.World.Attained` states a goal on the box indices, the
inventory fields and the clock of the world, with no observation, no count reader and no
embedding of a box position. `Harvests` states the tiles of a stance by equations on indices
and coordinates and the move by `Offset` and `Heads`, with no offset table, no facing position
and no checked translation. `SquareAdmits` states the tiles of a square by equations on the
coordinates, with no checked translation, and the kind of the spawn rule states the box by
bounds on the coordinates, with no box admission. `squared_admit_exact` states the discrepancy of
two words by their rational values, with no unit map. `Host.World.observe_satisfied_iff`
connects the observation with `Host.World.Attained`, and a private lemma beside each of the
others connects the reader with the statement.

The kind of `sum_admit` names the writer `sumWords` of the form that it reads, which the
admission does not call.

The kinds of the terrain name the binary32 quotient of a coordinate by an octave scale, which the
generator computes: `Host.coordinateFloat`, `Binary32.div` and `Binary32.mul` are shared with it,
and none of them is a test. Each is fixed apart from these kinds. `Binary32.div` and
`Binary32.mul` are Lean core's `Float32` division and multiplication on the words, and
`AcornVerif.FloatLibBridge.binary32_div_roundAt` and
`AcornVerif.FloatLibBridge.binary32_mul_roundAt` state them, on finite operands with a finite
result, as the exact real quotient and product rounded once to nearest-even. `Host.coordinateFloat`
has the statement `Acorn.Decisions.coordinate_float`, which reads the coordinate as a
mathematical integer and converts its magnitude with the library's conversion. The kinds of its two
readers also share `Host.WorldConfig.side`, which the type of their world argument reads and
`Acorn.Decisions.world_side` states as the stored side coordinate. The floor, the saturating cast
and the checked successor of the lattice coordinate are not shared:
`CurrentTerrain.PastLast` bounds the exact value of the quotient in their place.

The kinds of the paid actions share the same quotient through `CurrentTerrain.LatticeAdmits` and
the side of the box `Host.WorldConfig.side`, and the kind of `Host.payAndAct` also shares the
phase of the day `Host.World.dayPhase`, which the cost of an action reads and
`Acorn.Decisions.day_phase` states by bounds on the slot of the clock; none of them is a test.
`CurrentActions.ActionAdmits` states the tile that an action reads by equations on the
coordinates and the box indices and by the constructors of the action and the direction, and
`CurrentActions.Cost` states the cost by the constructors of the action and the constants of
`FeatureConstants`. They name no direction table, offset table, checked translation, box
admission, facing position or cost function. The paid action compares the action with a
harvest by `==`, which is Lean's `instBEqOfDecidableEq` over the derived decidable equality; the
specification states that comparison as an equality.

The kinds of the count and of the rule of the spawn search share the same quotient through
`CurrentTerrain.LatticeAdmits`, and `Host.WorldConfig.side`, which the type of their world
argument reads and which bounds the coordinates of the rule's box; none of them is a test. They
name neither the comparison of tile kinds that the count runs, Lean's `instBEqOfDecidableEq` over
the derived decidable equality, nor the walkability test `Host.TileKind.walkable` that the rule
runs, which refuse nothing.

RG1009 does not examine a statement with no kind, and statements with no kind here do reach
tests that their functions run. This module keeps no list of them, and the examples that follow
are not one: `task_observed` names `Host.Inventory.owns` in its craft clause.

The `AcornVerif` surface of the Regula manifest names `Acorn` in `decides`, so Regula counts the
decision contracts of this module toward the registrations of the executing library. Each
function with a kind here is registered in `Acorn.Decisions`, because Regula refuses a
registration that this library writes for a function of that one, and RG1008 requires the kind.
The ownership audit requires each statement with no kind by name, with a statement that still
refers to the executing definition, and so the second kind of `Agreement.admitSquared`, whose
registration a kind in `Acorn.Decisions` already meets.
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

/-- The control configuration of a learner, with the differential value rule. -/
def control : Acorn.Config := ⟨.control, .differential⟩

/-- The one index of `narrow`. -/
def first : FeatIdx narrow := ⟨0, by decide⟩

/-- The fresh learner of `control` over `narrow` with the trace of `first` set to one. -/
def traced : NumericState control narrow :=
  let fresh := NumericState.initial control narrow
  { fresh with transient := { fresh.transient with z := #v[⟨⟨0x3f800000⟩⟩] } }

/-- The active set of `narrow` that holds its one index. -/
def onlyFirst : SwiftTd.ActiveSet narrow := ⟨[first], List.nodup_singleton _⟩

/-- A pending sample of the discount `Discount.g99` at the largest age. -/
def oldestSample : PendingPrediction Discount.g99 :=
  ⟨⟨FeatureConstants.maxSettlement, by decide⟩, Prediction.project _ .zero, .zero, .one, 0⟩

/-- A tile of `wide` from which a tree to the west can be harvested. -/
def stand : Host.BoxPosition wide := ⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩

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
is in the goal box of a reach goal or of a concealed target, the inventory holds the count of
a collect goal or owns the tool of a craft goal, and the elapsed time is at least the duration
of a survive goal. -/
def Achieved (goal : Host.Goal) (position : Host.Position) (inventory : Host.Inventory)
    (elapsed : UInt64) : Prop :=
  match goal with
  | .reach target => CurrentGoals.InGoalBox target position
  | .collect item count => count.toNat ≤ (inventory.count item).toNat
  | .craft tool => inventory.Owns tool
  | .survive required => required.toNat ≤ elapsed.toNat
  | .find target => CurrentGoals.InGoalBox target position

/-- The arguments of `Host.replayCertified` and of `Host.ReplayCertificate.check`, in order. -/
structure Replay where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The world before the goal is installed. -/
  world : Host.World config
  /-- The goal to install. -/
  goal : Host.Goal
  /-- The most actions the list may hold. -/
  cap : Nat
  /-- The actions to replay. -/
  actions : List Host.Action

/-- An action list replays its goal from a world within a cap: the list holds at least one and
at most `cap` actions, and the run of the executed world step over them, from the world with the
goal installed, ends in a world in which the goal is attained (`Host.World.Attained`, on the
stored fields of the final world). The run is a run of the executed world step, which is the
subject of the claim. -/
def Replays {config : Host.WorldConfig} (world : Host.World config) (goal : Host.Goal) (cap : Nat)
    (actions : List Host.Action) : Prop :=
  0 < actions.length ∧ actions.length ≤ cap ∧
    ∃ (trace : List (Host.Action × Host.StepResult)) (final : Host.World config),
      CurrentStep.Trace (world.setGoal goal) trace final ∧ trace.map (·.1) = actions ∧
        final.Attained goal

/-- The replay checker accepts exactly an action list that replays its goal: the run of the
fold is a run of the step (`CurrentStep.actions_trace`, `CurrentStep.trace_actions`), it keeps
the installed goal (`CurrentCertificates.trace_goal`), and the completion flag of its final
world is set exactly when that goal is attained (`Host.World.goalSatisfied_iff`). -/
private theorem replayCertified_iff {config : Host.WorldConfig} (world : Host.World config)
    (goal : Host.Goal) (cap : Nat) (actions : List Host.Action) :
    Host.replayCertified world goal cap actions = true ↔ Replays world goal cap actions := by
  constructor
  · intro accepted
    unfold Host.replayCertified at accepted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    obtain ⟨⟨nonempty, short⟩, replayed⟩ := accepted
    cases run : (world.setGoal goal).advanceActions actions with
    | error error =>
      rw [run] at replayed
      exact absurd replayed Bool.false_ne_true
    | ok final =>
      rw [run] at replayed
      obtain ⟨trace, traced, mapped⟩ := CurrentStep.actions_trace _ _ _ run
      have installed : final.goal = some goal := by
        rw [CurrentCertificates.trace_goal traced]
        rfl
      obtain ⟨other, same, attained⟩ := (Host.World.goalSatisfied_iff final).mp replayed
      rw [installed] at same
      cases same
      refine ⟨?_, short, trace, final, traced, mapped, attained⟩
      cases actions with
      | nil => exact absurd nonempty (by decide)
      | cons action rest => exact Nat.succ_pos _
  · rintro ⟨positive, short, trace, final, traced, mapped, attained⟩
    have run := CurrentStep.trace_actions traced
    rw [mapped] at run
    have installed : final.goal = some goal := by
      rw [CurrentCertificates.trace_goal traced]
      rfl
    unfold Host.replayCertified
    simp only [run, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, short⟩, (Host.World.goalSatisfied_iff final).mpr ⟨goal, installed, attained⟩⟩
    cases actions with
    | nil => exact absurd positive (Nat.lt_irrefl 0)
    | cons action rest => rfl

/-- The replay checker accepts exactly an action list that replays its goal (`Replays`): at least
one and at most `cap` actions whose run of the executed world step, from the world with the goal
installed, ends in a world in which the goal is attained. The specification names the world
step, which decides the propositions `Host.World.GoalSatisfied`, `Host.FoodDue` and
`Host.Inventory.Owns` and compares actions, tile kinds and positions by their equality, and
`Host.World.Attained` in the place of the completion predicate that the checker runs. The
accepted input is the action `wait` from the empty world of `wide` with the goal to survive no
step, at the cap one; the kernel evaluates that step. The refused input is the empty action list.

**Not claimed:** completeness about the goal. The checker refuses an action list that does not
itself replay the goal, whether or not the goal can be reached. -/
theorem replay_certified : Regula.ExecutableContract @Host.replayCertified (fun check =>
    Regula.Decides (· = true)
      (fun input : Replay => Replays input.world input.goal input.cap input.actions)
      (fun input : Replay =>
        @check input.config input.world input.goal input.cap input.actions)) :=
  ⟨decides (fun input => replayCertified_iff input.world input.goal input.cap input.actions)
    ⟨⟨wide, Host.World.empty wide, .survive 0, 1, [.wait]⟩,
      (replayCertified_iff _ _ _ _).mp (by decide +kernel)⟩
    ⟨⟨wide, Host.World.empty wide, .survive 0, 1, []⟩,
      fun ⟨positive, _⟩ => absurd positive (Nat.lt_irrefl 0)⟩⟩

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

/-- Replay checking returns a certificate exactly for an action list that replays its goal
(`Replays`, which `replay_certified` states): the constructor returns a certificate exactly where
the checker accepts. The witnesses are those of `replay_certified`. -/
theorem replay_check : Regula.ExecutableContract @Host.ReplayCertificate.check (fun check =>
    Regula.Decides (· = true)
      (fun input : Replay => Replays input.world input.goal input.cap input.actions)
      (Regula.Dependent.isSome fun input : Replay =>
        @check input.config input.world input.goal input.cap input.actions)) :=
  ⟨.of_iff
    (fun input => by
      change (Host.ReplayCertificate.check input.world input.goal input.cap input.actions).isSome =
        true ↔ _
      rw [← replayCertified_iff]
      unfold Host.ReplayCertificate.check
      split
      · exact ⟨fun _ => by assumption, fun _ => rfl⟩
      · exact ⟨fun present => by simp at present, fun accepted => by contradiction⟩)
    ⟨⟨wide, Host.World.empty wide, .survive 0, 1, [.wait]⟩, by decide +kernel⟩
    ⟨⟨wide, Host.World.empty wide, .survive 0, 1, []⟩, by decide⟩⟩

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
is the subject of the claim. The accepted input is the grass tile (2, 0) of the wide world, and
the refused input is the last coordinate, whose terrain the generator refuses. -/
theorem terrain_walkable : Regula.ExecutableContract Host.walkableTile (fun test =>
    Regula.Decides (· = true)
      (fun input : Host.WorldConfig × Host.Position =>
        ∀ world : Host.World input.1, world.enterable input.2 = .ok true)
      (Function.uncurry test)) :=
  ⟨.of_iff
    (fun input =>
      ⟨fun accepted world => CurrentCertificates.walkable_enterable world input.2 accepted,
        enterable_walkable⟩)
    ⟨(wide, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩), by decide +kernel⟩
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

The statement keeps no kind. An audit with Regula v0.11.0 refused the two-way kind with this
specification under RG1009 (https://rbeauchamp.github.io/regula/v/0.11.0/rules/RG1009/). The
specification quantifies over agent images, whose type declares the invariants of their learners,
and it names the writer `imagePayload`, whose format holds the reader of each field beside its
writer. Both reach ten tests that the admission runs, among them the stored-word check
`NumericState.resumable`, `Binary32.isNaN` and `Binary32.less`. Which images there are depends on
those tests, so a kind needs a statement of the written payloads that does not depend on them. -/
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

The statement keeps no kind, for the reason that `payload_admit` gives: an audit with Regula
v0.11.0 refused the kind under RG1009 for the same ten tests. -/
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
`survive_satisfied_iff`, `craft_satisfied`, `find_satisfied_iff`), and it refuses the
observation of no goal.

**Not claimed:** soundness for an observation that `Goal.observe` did not produce. The five
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
         exact (Host.Inventory.owns_iff _ _).mpr achieved
       | survive required =>
         exact (CurrentGoals.survive_satisfied_iff required position inventory elapsed).mpr
           achieved
       | find target =>
         exact (CurrentGoals.find_satisfied_iff target position inventory elapsed).mpr achieved
     refused := ⟨.none, by decide⟩ }⟩

/-- The completion predicate, on the observation of each goal family, is exactly: a position
in the goal box for a reach goal or a concealed target, an inventory that holds the count for
a collect goal and an elapsed time of at least the duration for a survive goal; for a craft
goal it is the ownership of the tool (`CurrentGoals.reach_satisfied_iff`,
`collect_satisfied_iff`, `survive_satisfied_iff`, `craft_satisfied`, `find_satisfied_iff`).
These equivalences are both directions for the observations that `Goal.observe` produces;
`task_satisfied` states the kind. -/
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
      (∀ (tool : Host.Craftable) (position : Host.Position) (inventory : Host.Inventory)
        (elapsed : UInt64),
        satisfied ((Host.Goal.craft tool).observe position inventory elapsed) =
          inventory.owns tool) ∧
      ∀ (target position : Host.Position) (inventory : Host.Inventory) (elapsed : UInt64),
        satisfied ((Host.Goal.find target).observe position inventory elapsed) = true ↔
          CurrentGoals.InGoalBox target position) :=
  ⟨⟨CurrentGoals.reach_satisfied_iff, CurrentGoals.collect_satisfied_iff,
    CurrentGoals.survive_satisfied_iff, CurrentGoals.craft_satisfied,
    CurrentGoals.find_satisfied_iff⟩⟩

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

The value noise refuses a position exactly when the quotient of a coordinate by its scale
reaches a lattice coordinate with no successor, `CurrentTerrain.PastLast`, which states the
condition on the exact value of the quotient. The fold of the value noise over the octaves
refuses exactly when one of its octaves does, and a field of the terrain, the terrain generator
and its two readers in the world refuse exactly when one of the four octaves of the base scale
does, `CurrentTerrain.LatticeAdmits`. The witnesses of the six kinds are the last coordinate at
the noise scales of two and of one half. A generator that read every scale as one would fail
each kind: at the scale one it refuses the last coordinate. -/

/-- The value noise admits exactly a position and a scale at which the quotient of neither
coordinate by the scale is past the last lattice coordinate (`CurrentTerrain.valueNoise_isOk`):
positive infinity or a finite value of at least `2 ^ 63 - 1`. The seed enters no refusal. The
accepted input is the last coordinate at the scale two, whose horizontal quotient is `2 ^ 62`.
The refused input is the last coordinate at the scale one half, whose horizontal quotient is
`2 ^ 64`. -/
theorem value_noise_lattice : Regula.ExecutableContract Host.valueNoise (fun valueNoise =>
    Regula.Decides (·.isOk = true)
      (fun input : (Host.Position × Binary32) × UInt64 =>
        ¬CurrentTerrain.PastLast ((Host.coordinateFloat input.1.1.x).div input.1.2) ∧
          ¬CurrentTerrain.PastLast ((Host.coordinateFloat input.1.1.y).div input.1.2))
      (Function.uncurry (Function.uncurry valueNoise))) :=
  ⟨decides (fun input => CurrentTerrain.valueNoise_isOk input.1.1 input.1.2 input.2)
    ⟨((last, ⟨0x40000000⟩), 0), by decide +kernel⟩
    ⟨((last, ⟨0x3f000000⟩), 0), by decide +kernel⟩⟩

/-- The arguments of `Host.octaveLoop`, in order. -/
structure OctaveLoop where
  /-- The number of octaves still to add. -/
  count : Nat
  /-- The position. -/
  position : Host.Position
  /-- The seed. -/
  seed : UInt64
  /-- The scale of the next octave. -/
  scale : Binary32
  /-- The amplitude of the next octave. -/
  amplitude : Binary32
  /-- The sum of the octaves added. -/
  sum : Binary32

/-- The fold of the value noise over the octaves admits exactly a position that the value noise
admits at each octave scale that it adds, the scale doubled once per octave
(`CurrentTerrain.octaveLoop_isOk`). The seed, the amplitude and the sum enter no refusal. The
witnesses are the four octaves of a field of the terrain at the inputs of
`value_noise_lattice`. -/
theorem octave_loop_lattice : Regula.ExecutableContract Host.octaveLoop (fun octaveLoop =>
    Regula.Decides (·.isOk = true)
      (fun input : OctaveLoop =>
        ∀ octave < input.count,
          ¬CurrentTerrain.PastLast ((Host.coordinateFloat input.position.x).div
              (CurrentTerrain.octaveScale input.scale octave)) ∧
            ¬CurrentTerrain.PastLast ((Host.coordinateFloat input.position.y).div
              (CurrentTerrain.octaveScale input.scale octave)))
      (fun input : OctaveLoop => octaveLoop input.count input.position input.seed input.scale
        input.amplitude input.sum)) :=
  ⟨decides (fun input => CurrentTerrain.octaveLoop_isOk input.count input.position input.seed
      input.scale input.amplitude input.sum)
    ⟨⟨4, last, 0, ⟨0x40000000⟩, ⟨0x3f000000⟩, ⟨0⟩⟩, by decide +kernel⟩
    ⟨⟨4, last, 0, ⟨0x3f000000⟩, ⟨0x3f000000⟩, ⟨0⟩⟩, by decide +kernel⟩⟩

/-- A field of the terrain admits exactly a position whose value noise has a lattice successor at
each of the four octave scales of the base scale (`CurrentTerrain.fbm_isOk`). The seed enters no
refusal. The witnesses are those of `terrain_lattice`. -/
theorem fbm_lattice : Regula.ExecutableContract Host.fbm (fun fbm =>
    Regula.Decides (·.isOk = true)
      (fun input : (Host.Position × UInt64) × Binary32 =>
        CurrentTerrain.LatticeAdmits input.1.1 input.2)
      (Function.uncurry (Function.uncurry fbm))) :=
  ⟨decides (fun input => CurrentTerrain.fbm_isOk input.1.1 input.1.2 input.2)
    ⟨((last, 0), ⟨0x40000000⟩), by decide +kernel⟩
    ⟨((last, 0), ⟨0x3f000000⟩), by decide +kernel⟩⟩

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

/-- The world's completion flag is set exactly when a goal is installed and attained
(`Host.World.goalSatisfied_iff`). The specification is `Host.World.Attained`, on the installed
goal and the stored fields of the world. It names neither the completion predicate
`Host.TaskObservation.satisfied` nor `Host.Goal.observe`, which the flag applies, and no reader
of a position or of an inventory. The accepted input is the empty world of `wide` with the goal
to survive no step, and the refused input is that world with no goal. -/
theorem goal_satisfied : Regula.ExecutableContract @Host.World.goalSatisfied (fun satisfied =>
    Regula.Decides (· = true)
      (fun input : (config : Host.WorldConfig) × Host.World config => ∃ goal,
        input.2.goal = some goal ∧ input.2.Attained goal)
      (fun input : (config : Host.WorldConfig) × Host.World config =>
        @satisfied input.1 input.2)) :=
  ⟨decides (fun input => Host.World.goalSatisfied_iff input.2)
    ⟨⟨wide, (Host.World.empty wide).setGoal (.survive 0)⟩, .survive 0, rfl, Nat.zero_le _⟩
    ⟨⟨wide, .empty wide⟩, fun ⟨_, installed, _⟩ => (nomatch installed)⟩⟩

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

/-! ## Runs of the world step -/

/-- The arguments of `Host.World.advanceActions`, in order. -/
structure AdvanceActions where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The world the run starts from. -/
  world : Host.World config
  /-- The actions to replay. -/
  actions : List Host.Action

/-- An action replay returns a world exactly when a run of the executed world step over those
actions ends in that world (`CurrentStep.trace_actions`, `CurrentStep.actions_trace`). It is a
requirement with no kind beside the kind `advance_actions`: the world of an accepted replay. -/
theorem advance_actions_value : Regula.ExecutableContract @Host.World.advanceActions
    (fun advance =>
      ∀ (config : Host.WorldConfig) (world final : Host.World config)
        (actions : List Host.Action),
        @advance config world actions = .ok final ↔
          ∃ trace, CurrentStep.Trace world trace final ∧ trace.map (·.1) = actions) :=
  ⟨fun _ world final actions =>
    ⟨CurrentStep.actions_trace world final actions,
      fun ⟨_, run, same⟩ => same ▸ CurrentStep.trace_actions run⟩⟩

/-- A successful step has a successful paid action (`Host.payAndAct`); an action that the
energy does not pay for rests the body, and `Host.payAndAct` succeeds then too. -/
private theorem step_paid {config : Host.WorldConfig} {world middle : Host.World config}
    {action : Host.Action} {events : Host.StepResult}
    (stepped : world.step action = .ok (middle, events)) :
    (Host.payAndAct world action).isOk = true := by
  obtain ⟨active, paid, -⟩ := CurrentStep.step_active world middle action events stepped
  rw [paid]
  rfl

/-- An action replay succeeds exactly when a run of the executed world step over its actions
exists (`CurrentStep.trace_actions`, `CurrentStep.actions_trace`). The specification names the
world step, which decides the propositions `Host.World.GoalSatisfied`, `Host.FoodDue` and
`Host.Inventory.Owns` and compares actions, tile kinds and positions by their equality. The
accepted input is the empty action list from the empty world of `wide`. The refused input is a
harvest from the empty world of `wideAt` at the scale one half, whose paid action the terrain
refuses (`pay_and_act_lattice`). `advance_actions_value` states the world that an accepted
replay returns. -/
theorem advance_actions : Regula.ExecutableContract @Host.World.advanceActions (fun advance =>
    Regula.Decides (· = true)
      (fun input : AdvanceActions => ∃ (trace : List (Host.Action × Host.StepResult))
        (final : Host.World input.config),
        CurrentStep.Trace input.world trace final ∧ trace.map (·.1) = input.actions)
      (Regula.Dependent.isOk fun input : AdvanceActions =>
        @advance input.config input.world input.actions)) :=
  ⟨decides
    (fun input => by
      change (input.world.advanceActions input.actions).isOk = true ↔ _
      constructor
      · intro accepted
        cases run : input.world.advanceActions input.actions with
        | error error =>
          rw [run] at accepted
          exact absurd accepted (by simp [Except.isOk, Except.toBool])
        | ok final =>
          obtain ⟨trace, traced, mapped⟩ := CurrentStep.actions_trace _ _ _ run
          exact ⟨trace, final, traced, mapped⟩
      · rintro ⟨trace, final, traced, mapped⟩
        rw [← mapped, CurrentStep.trace_actions traced]
        rfl)
    ⟨⟨wide, Host.World.empty wide, []⟩, [], _, .done _, rfl⟩
    ⟨⟨wideAt ⟨0x3f000000⟩, Host.World.empty _, [.harvest]⟩, fun ⟨trace, final, traced, mapped⟩ => by
      cases traced with
      | done => exact absurd mapped (by simp)
      | step stepped later =>
        simp only [List.map_cons, List.cons.injEq] at mapped
        rw [mapped.1] at stepped
        exact absurd ((harvest_faced ⟨0x3f000000⟩).mp
          ((CurrentActions.payAndAct_isOk _ _).mp (step_paid stepped) harvest_paid))
          (by decide +kernel)⟩⟩

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

A count of a kind near a position has no early exit: it translates every tile of its square and
reads the kind of each. It is refused exactly when a tile of the square leaves the signed range or
the value noise refuses it (`SquareAdmits`). The spawn rule skips a coordinate outside the box,
and inside the box it reads both counts within four tiles and the kind of the coordinate, which
lies in their square, before it tests walkability. It is refused exactly when the coordinate is
inside the box and the value noise does not admit its square of radius four. The count and the
rule carry the two-way kind. The theorems of `AcornVerif.CurrentSpawn` state what a successful
count, a successful application of the rule and a successful spawn search return; the statements
of the count and of the rule stand beside their kinds under the names of the kinds with
`_value`. The search keeps a requirement with no kind with an accepted input, and
`world_initial_accepts` gives an accepted input of world generation.

The search and world generation accept the configuration `oneTile`: a box of one tile, no deer
and the noise scale one. The spiral of its box has one candidate, the center of the box, and the
value noise admits the square of radius four around it (`center_square`): each of its eighty-one
tiles is in the signed range, and the quotients of its coordinates, `-4` to `4`, by the four
octave scales of the noise scale are not past the last coordinate. The kernel evaluates those
quotients, of nine coordinates by four scales, and not the terrain. A loop over a range in
`Except` succeeds where every pass succeeds (`forIn_range_isOk`), which carries the success of
each pass through the loops of the count and of the search. A loop that succeeds and whose
every successful pass yields ran a successful pass at each index (`forIn_range_passes`), which
carries the success of the count back to each tile of its square. The placement of the deer
runs no pass at the deer cap zero. -/

/-- A bind succeeds where its first part succeeds and its rest succeeds on every value. -/
private theorem bind_isOk {ε α β : Type} (first : Except ε α) (rest : α → Except ε β)
    (accepted : first.isOk = true) (each : ∀ value, (rest value).isOk = true) :
    (first >>= rest).isOk = true := by
  obtain ⟨value, same⟩ := ok_of_isOk accepted
  rw [same]
  exact each value

/-- A bind that succeeds ran its first part successfully. -/
private theorem isOk_of_bind {ε α β : Type} {first : Except ε α} {rest : α → Except ε β}
    (accepted : (first >>= rest).isOk = true) : first.isOk = true := by
  cases first with
  | error refusal => exact accepted
  | ok value => rfl

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

/-- A loop over a range in `Except` that succeeds, and whose every successful pass yields, ran a
successful pass at each index below the bound (`CurrentSpawn.forIn_range_indexed`). -/
private theorem forIn_range_passes {ε σ : Type} (count : Nat) (init : σ)
    (body : Nat → σ → Except ε (ForInStep σ))
    (yields : ∀ index state next, body index state = .ok next → ∃ after, next = .yield after)
    (accepted : (forIn [:count] init body).isOk = true) :
    ∀ index, index < count → ∃ state, (body index state).isOk = true := by
  obtain ⟨result, finished⟩ := ok_of_isOk accepted
  refine (CurrentSpawn.forIn_range_indexed count
    (fun passed _ => ∀ index, index < passed → ∃ state, (body index state).isOk = true)
    (fun _ => False) body ?_ init result (fun _ below => absurd below (Nat.not_lt_zero _))
    finished).elim False.elim id
  intro index state next _ held taken
  refine ⟨fun _ _ earlier below => ?_, fun after done => ?_⟩
  · by_cases before : earlier < index
    · exact held earlier before
    · have same : earlier = index := by omega
      exact ⟨state, by rw [same, taken]; rfl⟩
  · obtain ⟨other, yielded⟩ := yields index state next taken
    rw [done] at yielded
    cases yielded

/-- The value noise admits at a scale every tile of the `(2 r + 1) × (2 r + 1)` square within `r`
of the coordinates `x` and `y`, each of which is in the signed range: for every row and column
below `2 r + 1` there is a tile whose coordinates are `x` plus `column - r` and `y` plus
`row - r`, and the value noise admits it. The tiles are stated by equations on the coordinates,
with no checked translation. -/
def SquareAdmits (x y : Int) (radius : Nat) (scale : Binary32) : Prop :=
  ∀ row column, row < 2 * radius + 1 → column < 2 * radius + 1 → ∃ tile : Host.Position,
    tile.x.val = x + ((column : Int) - radius) ∧ tile.y.val = y + ((row : Int) - radius) ∧
      CurrentTerrain.LatticeAdmits tile scale

/-- A count of a kind near a position succeeds where the value noise admits its square: each
tile translates inside the signed range (`CurrentCertificates.translate_of_eq`), and the world
accepts its kind (`CurrentTerrain.tileKind_isOk`). -/
private theorem countKindNear_isOk {config : Host.WorldConfig} (world : Host.World config)
    (position : Host.Position) (radius : Nat) (kind : Host.TileKind)
    (admits : SquareAdmits position.x.val position.y.val radius config.raw.baseScale) :
    (Host.countKindNear world position radius kind).isOk = true := by
  unfold Host.countKindNear
  dsimp only
  refine bind_isOk _ _ ?_ fun _ => rfl
  refine forIn_range_isOk _ _ _ fun row state rowBound => ?_
  refine bind_isOk _ _ ?_ fun _ => rfl
  refine forIn_range_isOk _ _ _ fun column count columnBound => ?_
  obtain ⟨tile, tileColumn, tileRow, admitted⟩ := admits row column rowBound columnBound
  have translated := CurrentCertificates.translate_of_eq _ _ _ _ tileColumn tileRow
  obtain ⟨found, located⟩ := ok_of_isOk ((CurrentTerrain.tileKind_isOk world tile).mpr admitted)
  simp only [translated, located, bind, Except.bind]
  split <;> rfl

/-- A count of a kind near a position that succeeds read every tile of its square: the passes of
its two loops always yield, so the pass at each row and column succeeded, which translated the
tile inside the signed range (`CurrentCertificates.translate_some`) and found its kind
(`CurrentTerrain.tileKind_isOk`). -/
private theorem countKindNear_admits {config : Host.WorldConfig} (world : Host.World config)
    (position : Host.Position) (radius : Nat) (kind : Host.TileKind)
    (accepted : (Host.countKindNear world position radius kind).isOk = true) :
    SquareAdmits position.x.val position.y.val radius config.raw.baseScale := by
  unfold Host.countKindNear at accepted
  dsimp only at accepted
  intro row column rowBound columnBound
  obtain ⟨state, rowPass⟩ := forIn_range_passes _ _ _
    (fun _ _ next taken => by
      obtain ⟨sum, -, rest⟩ := CurrentSpawn.bind_ok _ _ _ taken
      simp only [pure, Except.pure, Except.ok.injEq] at rest
      exact ⟨sum, rest.symm⟩)
    (isOk_of_bind accepted) row rowBound
  obtain ⟨count, columnPass⟩ := forIn_range_passes _ _ _
    (fun _ _ next taken => by
      split at taken
      · obtain ⟨_, -, rest⟩ := CurrentSpawn.bind_ok _ _ _ taken
        split at rest <;>
          simp only [pure, Except.pure, Except.ok.injEq] at rest <;> exact ⟨_, rest.symm⟩
      · simp [bind, Except.bind] at taken)
    (isOk_of_bind rowPass) column columnBound
  split at columnPass
  · rename_i tile translated
    obtain ⟨tileColumn, tileRow⟩ := CurrentCertificates.translate_some _ _ _ _ translated
    exact ⟨tile, tileColumn, tileRow,
      (CurrentTerrain.tileKind_isOk world tile).mp (isOk_of_bind columnPass)⟩
  · simp [bind, Except.bind, Except.isOk, Except.toBool] at columnPass

/-- A coordinate that box admission accepts is inside the box, and its box position embeds as
that coordinate. -/
private theorem checked_some {config : Host.WorldConfig} {x y : Int}
    {position : Host.BoxPosition config}
    (admitted : Host.BoxPosition.checked config x y = some position) :
    (0 ≤ x ∧ x < config.side ∧ 0 ≤ y ∧ y < config.side) ∧
      position.position.x.val = x ∧ position.position.y.val = y := by
  unfold Host.BoxPosition.checked at admitted
  split at admitted
  · split at admitted
    · rename_i column row
      cases admitted
      exact ⟨⟨column.1, column.2, row.1, row.2⟩, Int.toNat_of_nonneg column.1,
        Int.toNat_of_nonneg row.1⟩
    · cases admitted
  · cases admitted

/-- The spawn rule succeeds exactly where the coordinate is outside the box, or the value noise
admits the square of radius four around it: inside the box the rule reads both counts within
four tiles (`countKindNear_isOk`, `countKindNear_admits`) and the kind of the coordinate, the
center of that square, before it tests walkability. -/
private theorem considerSpawn_iff {config : Host.WorldConfig} (world : Host.World config)
    (x y : Int) (best : Option (Host.SpawnCandidate config)) :
    (Host.considerSpawn world x y best).isOk = true ↔
      ¬(0 ≤ x ∧ x < config.side ∧ 0 ≤ y ∧ y < config.side) ∨
        SquareAdmits x y 4 config.raw.baseScale := by
  unfold Host.considerSpawn
  cases admitted : Host.BoxPosition.checked config x y with
  | none =>
    refine ⟨fun _ => .inl fun ⟨column, columnBound, row, rowBound⟩ => ?_, fun _ => rfl⟩
    simp [Host.BoxPosition.checked, column, columnBound, row, rowBound] at admitted
  | some position =>
    obtain ⟨inside, column, row⟩ := checked_some admitted
    simp only
    constructor
    · intro accepted
      have admits := countKindNear_admits world position.position 4 .tree (isOk_of_bind accepted)
      rw [column, row] at admits
      exact .inr admits
    · rintro (outside | admits)
      · exact absurd inside outside
      · rw [← column, ← row] at admits
        obtain ⟨tile, tileColumn, tileRow, admitted⟩ := admits 4 4 (by decide) (by decide)
        have center : tile = position.position :=
          CurrentActions.position_ext (by omega) (by omega)
        rw [center] at admitted
        refine bind_isOk _ _ (countKindNear_isOk _ _ _ _ admits) fun _ => ?_
        refine bind_isOk _ _ (countKindNear_isOk _ _ _ _ admits) fun _ => ?_
        refine bind_isOk _ _ ((CurrentTerrain.tileKind_isOk _ _).mpr admitted) fun _ => ?_
        split <;> rfl

/-- The arguments of `Host.countKindNear`, in order. -/
structure KindSquare where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The world. -/
  world : Host.World config
  /-- The center of the square. -/
  position : Host.Position
  /-- The radius of the square. -/
  radius : Nat
  /-- The kind that the count counts. -/
  kind : Host.TileKind

/-- A count of a kind near a position is refused exactly when a tile of its square leaves the
signed range or the value noise refuses the tile at the base scale of the world: the count has
no early exit, so it reads every tile of its square (`countKindNear_isOk`,
`countKindNear_admits`). The accepted input is the count of trees within radius zero of the body
position of the empty world of `wide`, whose one tile is that position: its quotients by the four
octave scales are below the last coordinate, and the kernel evaluates them and not the terrain.
The refused input is that count at `last`, whose quotient by the first octave scale is past the
last coordinate. -/
theorem spawn_count : Regula.ExecutableContract @Host.countKindNear (fun count =>
    Regula.Decides (·.isOk = true)
      (fun input : KindSquare => SquareAdmits input.position.x.val input.position.y.val
        input.radius input.config.raw.baseScale)
      (fun input : KindSquare =>
        @count input.config input.world input.position input.radius input.kind)) :=
  ⟨decides
    (fun input => ⟨countKindNear_admits input.world input.position input.radius input.kind,
      countKindNear_isOk input.world input.position input.radius input.kind⟩)
    ⟨⟨wide, Host.World.empty wide, (Host.World.empty wide).body.position.position, 0, .tree⟩, by
      change SquareAdmits (Host.World.empty wide).body.position.position.x.val
        (Host.World.empty wide).body.position.position.y.val 0 wide.raw.baseScale
      intro row column rowBound columnBound
      exact ⟨(Host.World.empty wide).body.position.position, by omega, by omega,
        by decide +kernel⟩⟩
    ⟨⟨wide, Host.World.empty wide, last, 0, .tree⟩, fun admits => by
      have square : SquareAdmits last.x.val last.y.val 0 wide.raw.baseScale := admits
      obtain ⟨tile, tileColumn, tileRow, admitted⟩ := square 0 0 (by decide) (by decide)
      have same : tile = last := CurrentActions.position_ext (by omega) (by omega)
      rw [same] at admitted
      exact absurd admitted (by decide +kernel)⟩⟩

/-- A successful count of a kind near a position is the number of tiles of that kind among the
`(2 r + 1) × (2 r + 1)` tiles within `r` of the position (`CurrentSpawn.countKindNear_eq`). The
statement is a requirement with no kind beside the kind `spawn_count`, which states the refused
counts. -/
theorem spawn_count_value : Regula.ExecutableContract @Host.countKindNear (fun count =>
    ∀ {config} (world : Host.World config) (position : Host.Position) (radius found : Nat)
      (kind : Host.TileKind), count world position radius kind = .ok found →
        found = CurrentSpawn.squareCount world position radius kind (2 * radius + 1)) :=
  ⟨fun world position radius found kind counted =>
    CurrentSpawn.countKindNear_eq world position radius found kind counted⟩

/-- The arguments of `Host.considerSpawn`, in order. -/
structure SpawnCoordinate where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The world. -/
  world : Host.World config
  /-- The horizontal coordinate of the candidate. -/
  x : Int
  /-- The vertical coordinate of the candidate. -/
  y : Int
  /-- The best candidate so far. -/
  best : Option (Host.SpawnCandidate config)

/-- The spawn rule is refused exactly when the coordinate is inside the box and a tile within
four tiles of it leaves the signed range or the value noise refuses the tile at the base scale of
the world (`considerSpawn_iff`). The box is stated by bounds on the coordinates. The accepted
input is the coordinate `-1, 0` outside the box of `wide`. The refused input is the coordinate
`2 ^ 63 - 2, 0` inside that box, whose square reaches past the last coordinate. -/
theorem spawn_consider : Regula.ExecutableContract @Host.considerSpawn (fun consider =>
    Regula.Decides (· = true)
      (fun input : SpawnCoordinate =>
        ¬(0 ≤ input.x ∧ input.x < input.config.side ∧ 0 ≤ input.y ∧
            input.y < input.config.side) ∨
          SquareAdmits input.x input.y 4 input.config.raw.baseScale)
      (Regula.Dependent.isOk fun input : SpawnCoordinate =>
        @consider input.config input.world input.x input.y input.best)) :=
  ⟨decides (fun input => considerSpawn_iff input.world input.x input.y input.best)
    ⟨⟨wide, Host.World.empty wide, -1, 0, none⟩,
      .inl fun ⟨nonnegative, _⟩ => absurd nonnegative (by decide)⟩
    ⟨⟨wide, Host.World.empty wide, 2 ^ 63 - 2, 0, none⟩, fun
      | .inl outside => outside ⟨by decide, by decide, by decide, by decide⟩
      | .inr admits => by
        have square : SquareAdmits (2 ^ 63 - 2) 0 4 wide.raw.baseScale := admits
        obtain ⟨tile, tileColumn, -, -⟩ := square 4 8 (by decide) (by decide)
        have bound := tile.x.property.2
        rw [tileColumn] at bound
        omega⟩⟩

/-- Every successful application of the spawn rule is one of the outcomes that
`CurrentSpawn.Considered` lists (`CurrentSpawn.considerSpawn_outcome`). The statement is a
requirement with no kind beside the kind `spawn_consider`, which states the refused
applications. -/
theorem spawn_consider_value : Regula.ExecutableContract @Host.considerSpawn (fun consider =>
    ∀ {config} (world : Host.World config) (x y : Int)
      (best selected : Option (Host.SpawnCandidate config)) (finished : Bool),
      consider world x y best = .ok (selected, finished) →
        CurrentSpawn.Considered world x y best selected finished) :=
  ⟨fun world x y best selected finished considered =>
    CurrentSpawn.considerSpawn_outcome world x y best selected finished considered⟩

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

/-- The value noise of `oneTile` admits every tile within four tiles of the center of its box,
the coordinate `0, 0` (`near_admits`). -/
private theorem center_square : SquareAdmits 0 0 4 oneTile.raw.baseScale := by
  intro row column rowBound columnBound
  refine ⟨⟨⟨(column : Int) - 4, by omega⟩, ⟨(row : Int) - 4, by omega⟩⟩, ?_, ?_, ?_⟩
  · change (column : Int) - 4 = (0 : Int) + ((column : Int) - (4 : Nat))
    omega
  · change (row : Int) - 4 = (0 : Int) + ((row : Int) - (4 : Nat))
    omega
  · exact fun octave below =>
      ⟨near_admits ⟨column, columnBound⟩ ⟨octave, below⟩,
        near_admits ⟨row, rowBound⟩ ⟨octave, below⟩⟩

/-- The spawn rule succeeds at the center of the box of `oneTile`, whatever the best candidate
so far (`considerSpawn_iff`, `center_square`). -/
private theorem consider_center (best : Option (Host.SpawnCandidate oneTile)) :
    (Host.considerSpawn (Host.World.empty oneTile) 0 0 best).isOk = true :=
  (considerSpawn_iff _ _ _ _).mpr (.inr center_square)

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

The statement keeps no kind. The search stops at the first rich candidate of its spiral, so
which tiles it reads depends on the kinds and walkability of the tiles before, and no theorem
states which worlds it accepts. -/
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

/-- The arguments of `NumericState.clearAt`, in order. -/
structure ClearAt where
  /-- The learner configuration. -/
  config : Acorn.Config
  /-- The feature space. -/
  dimension : Dimension
  /-- The learner state. -/
  state : NumericState config dimension
  /-- The slot. -/
  index : FeatIdx dimension

/-- The test of a cleared slot accepts exactly a slot whose nine transient words are positive
zero (`CurrentLearnerCheck.clearAt_iff`). The specification is the vector of the nine words
that `CurrentLearner.registers` reads from the stored fields, equal to nine zeros; the function
compares each word with zero. The two inputs of the proof are the slot `first` of the fresh
learner of `control` over `narrow`, which is accepted, and the same slot of `traced`, whose trace
is one, which is refused. -/
theorem learner_clear : Regula.ExecutableContract @NumericState.clearAt (fun clearAt =>
    Regula.Decides (· = true)
      (fun input : ClearAt =>
        CurrentLearner.registers input.state input.index = Vector.replicate 9 .zero)
      (fun input : ClearAt => @clearAt input.config input.dimension input.state input.index)) :=
  ⟨decides (fun input => CurrentLearnerCheck.clearAt_iff input.state input.index)
    ⟨⟨control, narrow, NumericState.initial _ _, first⟩, by decide⟩
    ⟨⟨control, narrow, traced, first⟩, by decide⟩⟩

/-- The stored-word check of a learner read from an image accepts exactly a learner state that
satisfies the schedule invariant of the learner's capacity theorem at its phase
(`CurrentLearnerCheck.resumable_iff`): every slot that is not eligible holds nine positive-zero
transient words, every pruning reference is a finite word whose value lies in `[0, 5]`, no
eligible index repeats, and, when a standalone second loop is permitted, no eligible trace is
zero.

The statement keeps no kind. A two-way kind whose specification states the invariant with the
readiness of an eligible trace as a nonzero signed key, in the place of the zero test, was
proved, with the fresh learner of `control` over `narrow` as the accepted input and that learner
with `first` eligible as the refused one; Regula's collector refuses it under RG1009
(https://rbeauchamp.github.io/regula/v/0.11.0/rules/RG1009/) for `Binary32.isNaN` and
`Binary32.less`. The specification reaches them only through the declaration of the learner
state, whose step-size rails declare an invariant that names `Portable.ln`; the function runs them
in the interval test of a pruning reference. This is the reading of
https://github.com/rbeauchamp/regula/issues/320, and the kind is remaining work of
https://github.com/rbeauchamp/acorn/issues/105. -/
theorem learner_resumable : Regula.ExecutableContract @NumericState.resumable (fun resumable =>
    ∀ {config : Acorn.Config} {dimension : Dimension} (state : NumericState config dimension)
      (phase : Bool),
      resumable state phase = true ↔ CurrentLearner.ScheduleInv state phase) :=
  ⟨CurrentLearnerCheck.resumable_iff⟩

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

/-- Loading refuses every byte list under a profile that is not resumable: the admitted image's
restore refuses there (`AgentConstruction.State.restore_refuses`). -/
private theorem load_resumable (construction : AgentConstruction) (receiver : construction.State)
    (bytes : List UInt8) (accepted : (Checkpoint.load construction receiver bytes).isOk = true) :
    Resumable construction.profile := by
  cases supported : construction.profile.checkpointSupported with
  | true => exact (FeatureProfile.checkpoint_iff _).mp supported
  | false =>
    have refused : (Checkpoint.load construction receiver bytes).isOk = false := by
      unfold Checkpoint.load
      split
      · rfl
      · rename_i image admitted
        rw [AgentConstruction.State.restore_refuses receiver image ⟨_, admitted⟩ supported]
        rfl
    rw [refused] at accepted
    exact absurd accepted Bool.false_ne_true

/-- The arguments of `Checkpoint.load`, in order. -/
structure Load where
  /-- The construction. -/
  construction : AgentConstruction
  /-- The receiving state. -/
  receiver : construction.State
  /-- The bytes. -/
  bytes : List UInt8

/-- Loading accepts bytes only under a resumable profile (`load_resumable`). The accepted input
is the bytes that the initial state of the construction of `resumable` saves, which loading
accepts (`CurrentCheckpoint.save_load`). The specification names the four discriminants of the
profile and no function that loading calls. `checkpoint_load_accepts` states the state that
loading returns for saved bytes.

**Not claimed:** which other byte lists a resumable construction refuses. -/
theorem checkpoint_load : Regula.ExecutableContract Checkpoint.load (fun load =>
    Regula.DecidesSoundly (· = true)
      (fun input : Load => Resumable input.construction.profile)
      (Regula.Dependent.isOk fun input : Load =>
        load input.construction input.receiver input.bytes)) :=
  ⟨⟨fun input accepted => load_resumable input.construction input.receiver input.bytes accepted,
    ⟨⟨construction resumable, AgentConstruction.initial _,
        encode (snapshot (construction resumable) (AgentConstruction.initial _))⟩,
      (Regula.Dependent.isOk_eq_true_iff _ _).mpr ⟨_, CurrentCheckpoint.save_load _ _ _ rfl⟩⟩⟩⟩

/-- Loading returns the state that a resumable construction saved, every field of its agent,
for every receiver of that construction (`CurrentCheckpoint.save_load`). The sound kind
`checkpoint_load` states that loading accepts bytes only under a resumable profile.

The statement keeps no kind. The complete kind with these bytes as its specification quantifies
over the states of the construction, whose type declares the invariants of the learners, and names
the writer `Checkpoint.snapshot`, whose format holds the reader of each field beside its writer.
Both reach tests that loading runs, so by the documented reading of RG1009
(https://rbeauchamp.github.io/regula/v/0.11.0/rules/RG1009/) the rule refuses that kind. This is a
conclusion from the reading; no audit of the kind has run. -/
theorem checkpoint_load_accepts : Regula.ExecutableContract Checkpoint.load (fun load =>
    ∀ (construction : AgentConstruction) (source receiver : construction.State),
      construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
        construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned →
      load construction receiver (encode (snapshot construction source)) = .ok source) :=
  ⟨fun construction source receiver resumable =>
    CurrentCheckpoint.save_load construction receiver source
      ((FeatureProfile.checkpoint_iff construction.profile).mpr resumable)⟩

/-- Loading that keeps its receiver returns the receiver unchanged with the error of a refused
load (`Checkpoint.load_nonmutation`), and the loaded state with no error for an accepted one,
for every construction, receiver and byte list. Its verdict is the verdict of
`Checkpoint.load`, whose sound kind `checkpoint_load` and accepted bytes
`checkpoint_load_accepts` stand above. Both verdicts occur. The bytes that the initial state of
the construction of `resumable` saves load with no error (`CurrentCheckpoint.save_load`). The
bytes that the initial state of the construction whose profile declares spatial subtasks saves
are refused with an error, since that profile is not resumable and loading accepts bytes only
under a resumable profile (`load_resumable`).

The statement keeps no kind: the verdict is the second component of a pair whose state has a
type that depends on the construction, an earlier argument, and Regula reads a result whose
type depends on the input only through `Regula.Dependent.isSome` and
`Regula.Dependent.isOk`, of an `Option` or an `Except`. -/
theorem load_keeping : Regula.ExecutableContract Checkpoint.loadKeeping (fun keeping =>
    (∀ (construction : AgentConstruction) (receiver : construction.State) (bytes : List UInt8),
      (∀ error, Checkpoint.load construction receiver bytes = .error error →
        keeping construction receiver bytes = (receiver, some error)) ∧
        ∀ restored, Checkpoint.load construction receiver bytes = .ok restored →
          keeping construction receiver bytes = (restored, none)) ∧
      (keeping (construction resumable) (AgentConstruction.initial _)
        (encode (snapshot (construction resumable) (AgentConstruction.initial _)))).2 = none ∧
      (keeping (construction ⟨.final, .perStep, .declared, .spatial⟩)
        (AgentConstruction.initial _)
        (encode (snapshot (construction ⟨.final, .perStep, .declared, .spatial⟩)
          (AgentConstruction.initial _)))).2.isSome = true) :=
  ⟨⟨fun construction receiver bytes =>
    ⟨fun error rejected => Checkpoint.load_nonmutation construction receiver bytes error rejected,
      fun restored loaded => by simp [Checkpoint.loadKeeping, loaded]⟩,
    by
      simp [Checkpoint.loadKeeping, CurrentCheckpoint.save_load (construction resumable)
        (AgentConstruction.initial _) (AgentConstruction.initial _) rfl],
    by
      cases loading : Checkpoint.load (construction ⟨.final, .perStep, .declared, .spatial⟩)
          (AgentConstruction.initial _)
          (encode (snapshot (construction ⟨.final, .perStep, .declared, .spatial⟩)
            (AgentConstruction.initial _))) with
      | error error => simp [Checkpoint.loadKeeping, loading]
      | ok restored =>
        exact absurd (load_resumable _ _ _ (congrArg Except.isOk loading)) (by decide)⟩⟩

/-- Resuming the bytes that a supported construction saved returns the saved state with a new
evaluator session (`CurrentCheckpoint.save_load`). -/
private theorem resume_saved_state (construction : AgentConstruction)
    (receiver source : construction.State)
    (supported : construction.profile.checkpointSupported = true) :
    resume construction receiver (encode (snapshot construction source)) =
      .ok source.beginSession := by
  unfold resume
  rw [CurrentCheckpoint.save_load construction receiver source supported]
  rfl

/-- Resuming accepts bytes only under a resumable profile: it is loading followed by a new
evaluator session, which refuses nothing, so it accepts exactly what loading accepts
(`load_resumable`). The accepted input is that of `checkpoint_load`. `checkpoint_resume_accepts`
states the state that resuming returns for saved bytes.

**Not claimed:** which other byte lists a resumable construction refuses. -/
theorem checkpoint_resume : Regula.ExecutableContract Checkpoint.resume (fun resume =>
    Regula.DecidesSoundly (· = true)
      (fun input : Load => Resumable input.construction.profile)
      (Regula.Dependent.isOk fun input : Load =>
        resume input.construction input.receiver input.bytes)) :=
  ⟨⟨fun input accepted => load_resumable input.construction input.receiver input.bytes (by
      obtain ⟨state, resumed⟩ := (Regula.Dependent.isOk_eq_true_iff _ _).mp accepted
      change (Checkpoint.load input.construction input.receiver input.bytes).map _ = _ at resumed
      cases loading : Checkpoint.load input.construction input.receiver input.bytes with
      | error error => rw [loading] at resumed; cases resumed
      | ok restored => rfl),
    ⟨⟨construction resumable, AgentConstruction.initial _,
        encode (snapshot (construction resumable) (AgentConstruction.initial _))⟩,
      (Regula.Dependent.isOk_eq_true_iff _ _).mpr ⟨_, resume_saved_state _ _ _ rfl⟩⟩⟩⟩

/-- Resuming returns the state that a resumable construction saved with a new evaluator
session, every learned field the saved agent's, for every receiver of that construction
(`CurrentCheckpoint.save_load`). The sound kind `checkpoint_resume` states that resuming accepts
bytes only under a resumable profile. The statement keeps no kind for the reason that
`checkpoint_load_accepts` gives. -/
theorem checkpoint_resume_accepts : Regula.ExecutableContract Checkpoint.resume (fun resume =>
    ∀ (construction : AgentConstruction) (source receiver : construction.State),
      construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
        construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned →
      resume construction receiver (encode (snapshot construction source)) =
        .ok source.beginSession) :=
  ⟨fun construction source receiver resumable =>
    resume_saved_state construction receiver source
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

/-- The stored words of a learner are the learner's state and phase: reading the state back
from them (`managedState`) gives the learner's state (`CurrentImage.managedState_words`), and
their last word is the learner's phase, for every configuration, dimension and learner. The
learner format writes these words (`managedFormat`), so the checkpoint admissions and
`Checkpoint.saveBytes` reach the function.

The statement keeps no kind: the function refuses no learner, so it is no decision. -/
theorem managed_words : Regula.ExecutableContract @managedWords (fun words =>
    ∀ {config : Acorn.Config} {dimension : Dimension} (learner : Managed config dimension),
      managedState (words learner) = learner.state ∧ (words learner).2.2.2.2.2 = learner.phase) :=
  ⟨fun learner => ⟨CurrentImage.managedState_words learner, rfl⟩⟩

/-! ## Parsers of decimal numerals

`Host.Cli.natural` and `Host.AgentArguments.admit` read decimal numerals with Lean's
`String.toNat?`. What that reader accepts and returns is stated in Lean's
`Std.Data.String.ToNat` (`String.isNat_iff`, `String.toNat?_eq_some_ofDigitChars`), which this
library imports and the executing library's registry cannot, so the kinds of the two parsers
are stated here and registered in `Acorn.Decisions`. The specifications are the grammars
`Host.Cli.Natural` and `Host.AgentArguments.Admitted`, and the relation
`Host.AgentArguments.Constructs` between an argument list and what admission returns, written
beside the parsers with no executed function: each numeral has its value in positional
notation, which the private lemma `ofDigitChars_positional` connects with the left fold of
`Nat.ofDigitChars`. -/

/-- The positional value of a numeral with one more digit in front: that digit times ten to
the power of the number of digits after it, plus the value of the rest. -/
private theorem positional_cons (c : Char) (digits : List Char) :
    ((c :: digits).reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum =
      (c.toNat - 48) * 10 ^ digits.length +
        (digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum := by
  simp [List.zipIdx_append, Nat.add_comm]

/-- Lean's `Nat.ofDigitChars`, the value that `String.toNat?` gives, is the value of the
digits in positional notation. -/
private theorem ofDigitChars_positional (digits : List Char) :
    Nat.ofDigitChars 10 digits 0 =
      (digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum := by
  induction digits with
  | nil => simp
  | cons c more hold =>
    rw [Nat.ofDigitChars_cons, Nat.ofDigitChars_eq_ofDigitChars_zero, hold, positional_cons]
    simp [Nat.mul_comm]

/-- `String.toNat?` reads exactly the numerals of `AgentArguments.Decimal`, with their value. -/
private theorem toNat?_decimal (text : String) (n : Nat) :
    text.toNat? = some n ↔ Host.AgentArguments.Decimal text n := by
  have separators : text.toList.filter (· != '_') = text.toList.filter (· ≠ '_') := by
    congr; funext c; by_cases same : c = '_' <;> simp [same]
  constructor
  · intro read
    have accepted := String.isNat_of_toNat?_eq_some read
    rw [String.toNat?_eq_some_ofDigitChars accepted, Option.some.injEq] at read
    obtain ⟨nonempty, chars, doubled, first, last⟩ := String.isNat_iff.mp accepted
    refine ⟨by simpa using nonempty, fun c mem => ?_, doubled, first, last, ?_⟩
    · rcases chars c mem with digit | separator
      · exact .inl (by simpa using Char.isDigit_iff_toNat.mp digit)
      · exact .inr separator
    · rw [← read, ofDigitChars_positional, separators]
  · rintro ⟨nonempty, chars, doubled, first, last, value⟩
    have accepted : text.isNat = true := String.isNat_iff.mpr ⟨by simpa using nonempty,
      fun c mem => by
        rcases chars c mem with digit | separator
        · exact .inl (Char.isDigit_iff_toNat.mpr (by simpa using digit))
        · exact .inr separator, doubled, first, last⟩
    rw [String.toNat?_eq_some_ofDigitChars accepted, value, ofDigitChars_positional, separators]

/-- A text of digits alone is a numeral of `String.toNat?`, and its value is its positional
value. -/
private theorem toNat?_digits (digits : List Char) (nonempty : digits ≠ [])
    (each : ∀ c ∈ digits, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (String.ofList digits).toNat? =
      some (digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum := by
  rw [toNat?_decimal]
  have unseparated : digits.filter (· ≠ '_') = digits := List.filter_eq_self.mpr fun c mem => by
    have := each c mem
    simp only [decide_eq_true_eq]; rintro rfl; simp at this
  have head : ∀ c, digits.head? = some c → c ≠ '_' := fun c first => by
    have := each c (List.mem_of_head? first); rintro rfl; simp at this
  have last : ∀ c, digits.getLast? = some c → c ≠ '_' := fun c final => by
    have := each c (List.mem_of_getLast? final); rintro rfl; simp at this
  refine ⟨by simpa using nonempty, fun c mem => .inl (each c (by simpa using mem)), ?_,
    fun first => head _ (by simpa using first) rfl, fun final => last _ (by simpa using final) rfl,
    by rw [String.toList_ofList, unseparated]⟩
  rintro ⟨before, after, split⟩
  have := each '_' (by rw [← String.toList_ofList (l := digits), ← split]; simp)
  simp at this

/-- The digit test of `Cli.natural`, on a character, is the digit range. -/
private theorem digit_test (c : Char) :
    ('0' ≤ c && c ≤ '9') = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp [Char.le_def, UInt32.le_iff_toNat_le]

/-- `Cli.natural` accepts exactly the texts of `Cli.Natural`, with their value. -/
private theorem natural_iff (text : String) (n : Nat) :
    Host.Cli.natural text = some n ↔ Host.Cli.Natural text n := by
  have digitsOf : ∀ digits : String, ((if digits.isEmpty ||
      !digits.toList.all (fun c => '0' ≤ c && c ≤ '9') then none else digits.toNat?) = some n ↔
      digits.toList ≠ [] ∧ (∀ c ∈ digits.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧
        n = (digits.toList.reverse.zipIdx.map fun place =>
          (place.1.toNat - 48) * 10 ^ place.2).sum) := fun digits => by
    by_cases refused : (digits.isEmpty || !digits.toList.all (fun c => '0' ≤ c && c ≤ '9')) = true
    · rw [ite_eq_left_iff.mpr (fun h => absurd refused h)]
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_false,
        String.isEmpty_iff] at refused
      simp only [reduceCtorEq, false_iff, not_and, ne_eq, String.toList_eq_nil_iff]
      rintro nonempty each
      rcases refused with empty | ⟨c, mem, bad⟩
      · exact absurd empty nonempty
      · exact absurd ((digit_test c).mpr (each c mem)) (by simpa using bad)
    · rw [ite_eq_right_iff.mpr (fun h => absurd h refused)]
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false,
        List.all_eq_true, String.isEmpty_iff] at refused
      obtain ⟨nonempty, all⟩ := refused
      have each : ∀ c ∈ digits.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57 :=
        fun c mem => (digit_test c).mp (all c mem)
      have nonempty' : digits.toList ≠ [] := by simpa [String.toList_eq_nil_iff] using nonempty
      rw [← String.ofList_toList (s := digits), toNat?_digits _ nonempty' each,
        String.toList_ofList]
      simp only [Option.some.injEq]
      exact ⟨fun read => ⟨nonempty', each, read.symm⟩, fun read => read.2.2.symm⟩
  have notDigit : ¬ (48 ≤ ('+' : Char).toNat ∧ ('+' : Char).toNat ≤ 57) := by decide
  unfold Host.Cli.natural Host.Cli.Natural
  by_cases plus : text.startsWith "+" = true
  · simp only [plus, ↓reduceIte]
    rw [digitsOf, String.toList_ofList]
    obtain ⟨rest, split⟩ := String.startsWith_string_iff.mp plus
    simp only [String.reduceToList, List.cons_append, List.nil_append] at split
    rw [← split, List.tail_cons]
    constructor
    · rintro ⟨nonempty, each, value⟩
      exact ⟨['+'], rest, .inr rfl, nonempty, each, rfl, value⟩
    · rintro ⟨sign, digits, unsigned | signed, nonempty, each, spelled, value⟩
      · subst unsigned
        cases digits with
        | nil => exact absurd rfl nonempty
        | cons c more =>
          simp only [List.nil_append, List.cons.injEq] at spelled
          exact absurd (spelled.1 ▸ each c (by simp)) notDigit
      · subst signed
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at spelled
        exact ⟨spelled ▸ nonempty, spelled ▸ each, spelled ▸ value⟩
  · simp only [plus, Bool.false_eq_true, ↓reduceIte]
    rw [digitsOf]
    constructor
    · rintro ⟨nonempty, each, value⟩
      exact ⟨[], text.toList, .inl rfl, nonempty, each, rfl, value⟩
    · rintro ⟨sign, digits, unsigned | signed, nonempty, each, spelled, value⟩
      · subst unsigned
        simp only [List.nil_append] at spelled
        exact ⟨spelled ▸ nonempty, spelled ▸ each, spelled ▸ value⟩
      · subst signed
        exact absurd (String.startsWith_string_iff.mpr ⟨digits, by simp [spelled]⟩) plus

/-- The native word reader returns a machine word exactly for a decimal numeral of that word's
value (`toNat?_decimal`); a numeral of `2 ^ 64` or more is refused. -/
private theorem word_iff (text : String) (w : UInt64) :
    Host.AgentArguments.word text = some w ↔ Host.AgentArguments.Decimal text w.toNat := by
  rw [← toNat?_decimal]
  unfold Host.AgentArguments.word
  constructor
  · intro read
    obtain ⟨value, parsed, bounded⟩ := Option.bind_eq_some_iff.mp read
    by_cases below : value < 2 ^ 64
    · rw [ite_eq_left_iff.mpr (fun h => absurd below h), Option.some.injEq] at bounded
      rw [← bounded, parsed]
      simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' below]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h below)] at bounded
      cases bounded
  · intro parsed
    simp [parsed, w.toNat_lt]

/-- The native word reader accepts a text exactly when it is a decimal numeral below
`2 ^ 64`. -/
private theorem word_isSome (text : String) :
    (Host.AgentArguments.word text).isSome = true ↔
      ∃ n, Host.AgentArguments.Decimal text n ∧ n < 2 ^ 64 := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨w, read⟩
    exact ⟨w.toNat, (word_iff text w).mp read, w.toNat_lt⟩
  · rintro ⟨n, spelled, below⟩
    refine ⟨n.toUInt64, (word_iff text _).mpr ?_⟩
    simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' below] using spelled

/-- Reading every word of a list returns the words read one by one, in order: one word for
each text, each the value of its text. -/
private theorem words_iff (texts : List String) (words : List UInt64) :
    texts.mapM Host.AgentArguments.word = some words ↔
      words.length = texts.length ∧
        ∀ pair ∈ texts.zip words, Host.AgentArguments.Decimal pair.1 pair.2.toNat := by
  induction texts generalizing words with
  | nil =>
    cases words <;> simp
  | cons text more hold =>
    cases words with
    | nil =>
      simp only [List.mapM_cons, List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_and, iff_false]
      intro read
      obtain ⟨w, -, rest⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨ws, -, done⟩ := Option.bind_eq_some_iff.mp rest
      cases done
    | cons w ws =>
      simp only [List.mapM_cons, List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons,
        List.forall_mem_cons]
      constructor
      · intro read
        obtain ⟨w', first, rest⟩ := Option.bind_eq_some_iff.mp read
        obtain ⟨ws', others, done⟩ := Option.bind_eq_some_iff.mp rest
        cases done
        obtain ⟨length, each⟩ := (hold ws).mp others
        exact ⟨length, (word_iff text w).mp first, each⟩
      · rintro ⟨length, first, each⟩
        simp [(word_iff text w).mpr first, (hold ws).mpr ⟨length, each⟩]

/-- The native profile reader returns a profile exactly for its four words. -/
private theorem profile_iff (mode credit rate subtasks : String) (profile : FeatureProfile) :
    Host.AgentArguments.profile mode credit rate subtasks = some profile ↔
      Host.AgentArguments.ProfileSpelled mode credit rate subtasks profile := by
  unfold Host.AgentArguments.profile Host.AgentArguments.ProfileSpelled
    Host.AgentArguments.ModeSpelled Host.AgentArguments.CreditSpelled
    Host.AgentArguments.RateSpelled Host.AgentArguments.SubtasksSpelled
  simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.pure_def]
  obtain ⟨m, c, r, t⟩ := profile
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all [eq_comm]

open Host.AgentArguments in
/-- An argument list that the native drivers admit spells the construction they return and its
raw input words: ten words, with the four words of the construction's profile, the word of a
criterion and of a planning selection, and the decimal numerals of the seed, tiling word, bank
size and capacity exponent from which `AgentConstruction.admit` builds the construction under
the default step order, then one decimal numeral for each returned input word, with that word's
value. -/
private theorem admit_spelled (arguments : List String) (admitted : DefaultConstruction)
    (words : List UInt64) (accepted : admit arguments = some (admitted, words)) :
    ∃ (seed exponent tilings units mode credit rate subtasks criterion planning : String)
      (texts : List String) (profile : FeatureProfile) (selected : Criterion)
      (selection : PlanningSelection) (s t : UInt64) (u e : Nat),
      arguments = [seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion,
        planning] ++ texts ∧
      ProfileSpelled mode credit rate subtasks profile ∧ CriterionSpelled criterion selected ∧
      planning = PlanningSelection.name selection ∧ Decimal seed s.toNat ∧
      Decimal tilings t.toNat ∧ Decimal units u ∧ Decimal exponent e ∧
      AgentConstruction.admit profile selected selection .learnThenAct s t u e =
        some admitted.construction ∧
      words.length = texts.length ∧ ∀ pair ∈ texts.zip words, Decimal pair.1 pair.2.toNat := by
  unfold admit at accepted
  split at accepted
  · rename_i seed exponent tilings units mode credit rate subtasks criterion planning texts
    obtain ⟨profile, profiled, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    split at accepted <;>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at accepted
    all_goals
      obtain ⟨selection, planned, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨s, seeded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨t, tiled, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨u, banked, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨e, sized, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      split at accepted
      · cases accepted
      · rename_i construction made
        obtain ⟨ws, read, done⟩ := Option.bind_eq_some_iff.mp accepted
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at done
        obtain ⟨rfl, rfl⟩ := done
        exact ⟨_, _, _, _, _, _, _, _, _, _, texts, profile, _, selection, s, t, u, e, rfl,
          (profile_iff _ _ _ _ _).mp profiled, by simp [CriterionSpelled],
          (PlanningSelection.parse_accepted _ _).mp planned, (word_iff _ _).mp seeded,
          (word_iff _ _).mp tiled, (toNat?_decimal _ _).mp banked,
          (toNat?_decimal _ _).mp sized, made, (words_iff _ _).mp read⟩
  · cases accepted

/-- Reading a list of words succeeds exactly when every word is a decimal numeral below
`2 ^ 64`. -/
private theorem words_isSome (texts : List String) :
    (texts.mapM Host.AgentArguments.word).isSome = true ↔
      ∀ text ∈ texts, ∃ n, Host.AgentArguments.Decimal text n ∧ n < 2 ^ 64 := by
  have each : ∀ texts : List String, (texts.mapM Host.AgentArguments.word).isSome = true ↔
      ∀ text ∈ texts, (Host.AgentArguments.word text).isSome = true := fun texts => by
    induction texts with
    | nil => simp
    | cons text more hold =>
      rw [List.forall_mem_cons, ← hold, List.mapM_cons]
      cases Host.AgentArguments.word text <;> cases List.mapM Host.AgentArguments.word more <;>
        simp
  rw [each]
  exact forall₂_congr fun text _ => word_isSome text

open Host.AgentArguments in
/-- The native drivers admit exactly the argument lists of `Admitted`. -/
private theorem admit_isSome (arguments : List String) :
    (admit arguments).isSome = true ↔ Admitted arguments := by
  constructor
  · intro accepted
    obtain ⟨⟨admitted, words⟩, read⟩ := Option.isSome_iff_exists.mp accepted
    obtain ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
      texts, profile, selected, selection, s, t, u, e, rfl, profiled, criterioned, planned,
      seeded, tiled, banked, sized, made, length, each⟩ :=
      admit_spelled arguments admitted words read
    obtain ⟨positive, occupied, bounded, small⟩ :=
      (AgentConstruction.admit_iff profile selected selection .learnThenAct s t u e).mp
        (by rw [made]; rfl)
    refine ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
      texts, rfl, ⟨profile, profiled⟩, ⟨selected, criterioned⟩, ⟨selection, planned⟩,
      ⟨_, seeded, s.toNat_lt⟩, ⟨_, tiled, positive, t.toNat_lt⟩, ⟨u, banked, occupied, bounded⟩,
      ⟨e, sized, small⟩, fun text mem => ?_⟩
    obtain ⟨i, within, rfl⟩ := List.getElem_of_mem mem
    have paired := List.getElem_mem (h := (by simp [length, within] : i < (texts.zip words).length))
    exact ⟨_, by simpa using each _ paired, (words[i]'(length ▸ within)).toNat_lt⟩
  · rintro ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
      texts, rfl, ⟨profile, profiled⟩, ⟨selected, criterioned⟩, ⟨selection, planned⟩,
      ⟨s, seeded, sb⟩, ⟨t, tiled, tp, tb⟩, ⟨u, banked, up, ub⟩, ⟨e, sized, eb⟩, each⟩
    have seedRead : word seed = some s.toUInt64 :=
      (word_iff _ _).mpr (by simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' sb] using seeded)
    have tilingsRead : word tilings = some t.toUInt64 :=
      (word_iff _ _).mpr (by simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' tb] using tiled)
    obtain ⟨construction, made⟩ := Option.isSome_iff_exists.mp
      ((AgentConstruction.admit_iff profile selected selection .learnThenAct s.toUInt64
        t.toUInt64 u e).mpr
        ⟨by simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' tb] using tp, up, ub, eb⟩)
    obtain ⟨ws, read⟩ := Option.isSome_iff_exists.mp ((words_isSome texts).mpr each)
    unfold admit
    rcases criterioned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [List.cons_append, (profile_iff _ _ _ _ _).mpr profiled,
        (PlanningSelection.parse_accepted _ _).mpr planned, seedRead, tilingsRead,
        (toNat?_decimal _ _).mpr banked, (toNat?_decimal _ _).mpr sized, Option.bind_eq_bind,
        Option.bind_some] <;>
      split <;> simp_all

/-- Unsigned decimal parsing on the command line accepts exactly an optional plus sign followed
by at least one digit (`Host.Cli.Natural`). The specification is the grammar, which states each
character by its code, and shares no test with the function. The two inputs of the proof are
`0`, which is accepted, and the empty text, which is refused. -/
theorem cli_natural : Regula.ExecutableContract Host.Cli.natural
    (Regula.Decides (·.isSome = true) (fun text => ∃ n, Host.Cli.Natural text n)) :=
  ⟨decides
    (fun text => Option.isSome_iff_exists.trans (exists_congr fun n => natural_iff text n))
    ⟨"0", 0, [], ['0'], .inl rfl, by simp, by simp, by simp, by simp⟩
    ⟨"", fun ⟨_, sign, digits, _, nonempty, _, spelled, _⟩ => nonempty (by simp_all)⟩⟩

/-- The number that unsigned decimal parsing on the command line returns: for every text and
number, the parser returns the number exactly when the text is an optional plus sign and digits
whose value in positional notation is that number (`Host.Cli.Natural`). A kind states accepted
inputs and not the value of an accepted result, so this statement is a requirement with no
kind beside the kind `cli_natural`. -/
theorem cli_natural_value : Regula.ExecutableContract Host.Cli.natural (fun natural =>
    ∀ text n, natural text = some n ↔ Host.Cli.Natural text n) :=
  ⟨natural_iff⟩

/-- A text of one digit is a decimal numeral of that digit's value. -/
private theorem decimal_digit (text : String) (n : Nat) (c : Char) (spelled : text.toList = [c])
    (code : c.toNat = 48 + n) (small : n < 10) : Host.AgentArguments.Decimal text n := by
  unfold Host.AgentArguments.Decimal
  rw [spelled]
  have notSeparator : c ≠ '_' := by rintro rfl; simp at code; omega
  refine ⟨by simp, fun d mem => ?_, fun contained => absurd contained.length_le (by simp),
    by simp [notSeparator], by simp [notSeparator], ?_⟩
  · simp only [List.mem_singleton] at mem; subst mem; left; omega
  · simp [notSeparator, code]

/-- Native agent-argument admission accepts exactly the argument lists of the grammar
`Host.AgentArguments.Admitted`: ten words, which are a seed, a capacity exponent, a tiling word
and a bank size as decimal numerals within the bounds of `AgentConstruction.admit`, the four
words of a profile, the word of a criterion and the word of a planning selection, then decimal
numerals below `2 ^ 64` for the raw input words. A numeral can hold an underscore between two
digits, as Lean's `String.toNat?` reads it (`Host.AgentArguments.Decimal`). The specification
names the word relations, the planning names `PlanningSelection.name` and no function of the
parser. The two inputs of the proof are the ten words
`0 0 1 1 final per-step declared learned discounted expectation`, a construction of the default
step order with a seed of zero, a capacity exponent of zero, one tiling and a bank of one unit,
which are accepted, and the empty list, which is refused. -/
theorem agent_arguments_admit : Regula.ExecutableContract Host.AgentArguments.admit
    (Regula.Decides (·.isSome = true) Host.AgentArguments.Admitted) :=
  ⟨decides admit_isSome
    ⟨["0", "0", "1", "1", "final", "per-step", "declared", "learned", "discounted",
        "expectation"],
      ⟨"0", "0", "1", "1", "final", "per-step", "declared", "learned", "discounted",
        "expectation", [], rfl, ⟨⟨.final, .perStep, .declared, .learned⟩, .inl ⟨rfl, rfl⟩,
          .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩⟩, ⟨.discounted, .inl ⟨rfl, rfl⟩⟩,
        ⟨.expectation, rfl⟩, ⟨0, decimal_digit "0" 0 '0' (by simp) rfl (by decide), by decide⟩,
        ⟨1, decimal_digit "1" 1 '1' (by simp) rfl (by decide), by decide, by decide⟩,
        ⟨1, decimal_digit "1" 1 '1' (by simp) rfl (by decide), by decide, by decide⟩,
        ⟨0, decimal_digit "0" 0 '0' (by simp) rfl (by decide), by decide⟩, by simp⟩⟩
    ⟨[], fun ⟨_, _, _, _, _, _, _, _, _, _, _, spelled, _⟩ => by simp at spelled⟩⟩

/-- `AgentConstruction.admit` returns a construction exactly when each field of that construction
is the one stated: the profile, criterion, planning selection and step order given, the seed
and tiling word given, a bank of the units given, the declared tester, and a capacity of two to
the power of the exponent given. The conditions that the admission tests hold of every
construction, so they follow from the fields. -/
private theorem admit_fields (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (order : StepOrder) (seed tilings : UInt64)
    (units exponent : Nat) (construction : AgentConstruction) :
    AgentConstruction.admit profile criterion planning order seed tilings units exponent =
        some construction ↔
      construction.profile = profile ∧ construction.criterion = criterion ∧
        construction.planning = planning ∧ construction.order = order ∧
        construction.config.seed = seed ∧ construction.config.tilings = tilings ∧
        construction.config.units.count = units ∧ construction.config.tester = declaredTester ∧
        construction.dimension.capacity = 2 ^ exponent := by
  constructor
  · intro admitted
    unfold AgentConstruction.admit at admitted
    split at admitted
    · split at admitted
      · split at admitted
        · cases admitted
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · cases admitted
      · cases admitted
    · cases admitted
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, tested, sized⟩
    obtain ⟨profile, criterion, planning, order, ⟨seed, tilings, positive,
      ⟨units, occupied, bounded⟩, tester⟩, ⟨capacity, nonzero, power, below⟩⟩ := construction
    dsimp only at tested sized ⊢
    subst tested sized
    have small : exponent < 32 := (Nat.pow_lt_pow_iff_right (by decide)).mp below
    unfold AgentConstruction.admit
    rw [dite_eq_left positive, dite_eq_left ⟨occupied, bounded⟩, dite_eq_left small]

open Host.AgentArguments in
/-- An argument list that the native drivers admit spells, field by field, the construction
and the raw input words that they return. -/
private theorem admit_constructs (arguments : List String) (admitted : DefaultConstruction)
    (words : List UInt64) (accepted : admit arguments = some (admitted, words)) :
    Constructs arguments admitted.construction words := by
  obtain ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
    texts, profile, selected, selection, s, t, u, e, rfl, profiled, criterioned, planned,
    seeded, tiled, banked, sized, made, length, each⟩ :=
    admit_spelled arguments admitted words accepted
  obtain ⟨rfl, rfl, rfl, ordered, rfl, rfl, rfl, tested, capacity⟩ :=
    (admit_fields profile selected selection .learnThenAct s t u e admitted.construction).mp made
  exact ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
    texts, e, rfl, profiled, criterioned, planned, ordered, seeded, tiled, banked, sized,
    capacity, tested, length, each⟩

open Host.AgentArguments in
/-- The native drivers admit an argument list that spells a construction of the default step
order and raw input words, field by field, and return that construction and those words. -/
private theorem constructs_admit (arguments : List String) (construction : AgentConstruction)
    (default : construction.order = .learnThenAct) (words : List UInt64)
    (spelled : Constructs arguments construction words) :
    admit arguments = some (⟨construction, default⟩, words) := by
  obtain ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
    texts, e, rfl, profiled, criterioned, planned, -, seeded, tiled, banked, sized, capacity,
    tested, length, each⟩ := spelled
  have made := (admit_fields construction.profile construction.criterion construction.planning
    .learnThenAct construction.config.seed construction.config.tilings
    construction.config.units.count e construction).mpr
      ⟨rfl, rfl, rfl, default, rfl, rfl, rfl, tested, capacity⟩
  have read := (words_iff texts words).mpr ⟨length, each⟩
  unfold admit
  rcases criterioned with ⟨rfl, chosen⟩ | ⟨rfl, chosen⟩ <;> rw [chosen] at made <;>
    simp only [List.cons_append, (profile_iff _ _ _ _ _).mpr profiled,
      (PlanningSelection.parse_accepted _ _).mpr planned, (word_iff _ _).mpr seeded,
      (word_iff _ _).mpr tiled, (toNat?_decimal _ _).mpr banked, (toNat?_decimal _ _).mpr sized,
      Option.bind_eq_bind, Option.bind_some] <;>
    split <;> simp_all

/-- The construction and the raw input words that native agent-argument admission returns: for
every argument list, construction of the default step order and list of words, admission
returns them exactly when the list spells them field by field (`Host.AgentArguments.Constructs`):
the four words of a profile spell the construction's profile, the next two its criterion and
planning selection, the numerals of the seed, the tiling word and the bank size have the values
of its seed, its tiling word and its number of units, the exponent numeral has the value whose
power of two is its capacity, its tester is the declared one, and each input word is the value
of its numeral. The relation names the word relations, `PlanningSelection.name` and
`Handcrafted.declaredTester`, and no function of the parser. Since admission is a function, an
accepted list spells no other construction and no other list of words
(`agent_arguments_constructs_unique`), so a construction that differs from the returned one in
any field does not satisfy the relation; `agent_arguments_admit` names an accepted list. A kind
states accepted inputs and not the value of an accepted result, so this statement is a
requirement with no kind beside the kind `agent_arguments_admit`. -/
theorem agent_arguments_admit_value : Regula.ExecutableContract Host.AgentArguments.admit
    (fun admit => ∀ arguments admitted words, admit arguments = some (admitted, words) ↔
      Host.AgentArguments.Constructs arguments admitted.construction words) :=
  ⟨fun arguments admitted words => ⟨admit_constructs arguments admitted words,
    constructs_admit arguments admitted.construction admitted.default words⟩⟩

/-- An argument list spells at most one construction of the default step order and one list of
raw input words (`Host.AgentArguments.Constructs`): two that it spells are equal, so changing
any field of a spelled construction, or any input word, breaks the relation. -/
theorem agent_arguments_constructs_unique (arguments : List String)
    (first second : DefaultConstruction) (words others : List UInt64)
    (spelled : Host.AgentArguments.Constructs arguments first.construction words)
    (respelled : Host.AgentArguments.Constructs arguments second.construction others) :
    first = second ∧ words = others := by
  have one := constructs_admit arguments first.construction first.default words spelled
  have two := constructs_admit arguments second.construction second.default others respelled
  rw [one, Option.some.injEq, Prod.mk.injEq] at two
  exact two

/-! ## Definitions that specifications share

The specification of each contract named below applies a definition that its function also
applies. Each such definition has a statement of its own here, against a reading that does not
apply it: the rational value of a word, the exact real result rounded once, the place value of
digits, offsets stated by the constructors of a direction, the decimal that the name of a
discount declares, or the discounted return of a unit reward. None of them refuses an input, so
each statement keeps no kind. -/

/-- The squared discrepancy of two finite words, in the units of the least binary32 subnormal
`2 ^ -149` squared, is the square of the difference of their rational values
(`CurrentAgreement.squaredUnits_numerical`), for every pair of finite words. The specification
of `squared_admit` in `Acorn.Decisions` applies it. The witnesses are two zero words, at
discrepancy zero, and the least subnormal against zero, at one unit. -/
theorem squared_units : Regula.ExecutableContract Agreement.squaredUnits (fun squared =>
    (∀ forecast outcome : Binary32, forecast.Finite → outcome.Finite →
      (squared forecast outcome : ℚ) * ((2 : ℚ) ^ (-149 : Int)) ^ 2 =
        (CurrentArithmetic.numerical32 forecast - CurrentArithmetic.numerical32 outcome) ^ 2) ∧
      squared .zero .zero = 0 ∧ squared ⟨1⟩ .zero = 1) :=
  ⟨⟨CurrentAgreement.squaredUnits_numerical, by decide, by decide⟩⟩

/-- The cap of a total is finite, and it is the exact real product of the count's binary64
value and the rational value of the quantity's bound rounded once to nearest-even in binary64
(`AcornVerif.FloatLibBridge.binary64_mul_roundAt`, with `CurrentOrder.numerical_widen_exact`
for the widened bound and `CurrentLifetime.cap_bounds` for finiteness), for every quantity and
count. The count's value is Lean core's conversion `UInt64.toFloat`, which is the count itself
below `2 ^ 53` (`CurrentOrder.numerical64_ofUInt64`). The specification of `sum_admit` applies it
through the stored invariant of a total. The witnesses are the caps of the reward quantity, whose
bound is one, at the counts zero and one. -/
theorem maximum_sum : Regula.ExecutableContract maximumSum (fun cap =>
    (∀ (quantity : Quantity) (count : UInt64),
      (cap quantity count).Finite ∧
        ((CurrentArithmetic.numerical64 (cap quantity count) : ℚ) : ℝ) =
          FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt
            FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary64
            ((CurrentArithmetic.numerical64 (Binary64.ofUInt64 count) : ℝ) *
              (CurrentArithmetic.numerical32 quantity.bound : ℝ))) ∧
      cap .reward 0 = ⟨0⟩ ∧ cap .reward 1 = ⟨0x3ff0000000000000⟩) :=
  ⟨⟨fun quantity count => by
      have bound := CurrentLifetime.quantity_bound quantity
      have finite := (CurrentLifetime.cap_bounds quantity count).1
      refine ⟨finite, ?_⟩
      rw [← CurrentOrder.numerical_widen_exact quantity.bound bound.1]
      exact AcornVerif.FloatLibBridge.binary64_mul_roundAt _ _
        (CurrentLifetimeArithmetic.count_model count).1 (Conversion.widen_finite _ bound.1) finite,
    by decide, by decide⟩⟩

/-- A run of decimal digits spells the number that it writes by the place of each digit,
`Decimal.numberOf`, which reads each digit from a table of the ten digits
(`Decimal.spelled_numberOf`), for every run of decimal digits. The specifications of
`microduck_state`, `microduck_depth` and `microduck_line` in `Acorn.Decisions` apply it through
the relations `Host.Microduck.Counted` and `Host.Microduck.Signed`. The witness is the run `42`. -/
theorem digits_spelled : Regula.ExecutableContract Host.Microduck.spelled (fun spell =>
    (∀ digits : List Char, (∀ c ∈ digits, Json.Numeral.Digit c) →
      spell digits = Decimal.numberOf digits) ∧ spell ['4', '2'] = 42) :=
  ⟨⟨Decimal.spelled_numberOf, rfl⟩⟩

/-- The decimal of a formed numeral has the rational value that the numeral writes,
`Decimal.written`: the digits before the point, plus the digits after it over ten to their
count, times ten to the exponent, negated for a minus sign, each run read by the place of its
digits (`Decimal.ofNumeral_value`), for every formed numeral. The specifications of the
Microduck readers in `Acorn.Decisions` apply it through `Host.Microduck.Scale.Kept`. The witness
is the decimal of `-1.5`: the digits fifteen, a minus sign and the exponent minus one. -/
theorem decimal_of_numeral : Regula.ExecutableContract Host.Microduck.Decimal.ofNumeral
    (fun read =>
      (∀ numeral : Json.Numeral, numeral.Formed →
        Decimal.value (read numeral) = Decimal.written numeral) ∧
        read ⟨true, ['1'], some ['5'], none⟩ = ⟨true, 15, -1⟩) :=
  ⟨⟨Decimal.ofNumeral_value, rfl⟩⟩

/-- The scale of the whole numbers from minus ten to ten. -/
def tens : Host.Microduck.Scale := ⟨0, -10, 10, by decide⟩

/-- The conversion of a decimal to a scale is the integer nearest to its rational value times
ten to the places of the scale, a tie away from zero, saturated to the bounds of the scale
(`Decimal.fixed_nearest`), for every scale, decimal and nearest integer; at most one integer is
nearest (`Decimal.Nearest.unique`). The specifications of the Microduck readers in
`Acorn.Decisions` apply it through `Host.Microduck.Scale.Kept`. The witnesses are `-1.5`, which
`tens` keeps as minus two, and zero, which it keeps as zero. -/
theorem decimal_fixed : Regula.ExecutableContract @Host.Microduck.Decimal.fixed (fun fixed =>
    (∀ (scale : Host.Microduck.Scale) (decimal : Host.Microduck.Decimal) (nearest : Int),
      Decimal.Nearest (Decimal.value decimal * (10 : ℚ) ^ scale.places) nearest →
        (fixed scale decimal).val = max scale.low (min scale.high nearest)) ∧
      (fixed tens ⟨true, 15, -1⟩).val = -2 ∧ (fixed tens ⟨false, 0, 0⟩).val = 0) :=
  ⟨⟨Decimal.fixed_nearest, by decide +kernel, by decide +kernel⟩⟩

/-- The position that a body faces in a direction has the coordinates of the body moved by the
offset of the direction that `Offset` states by its constructors, for every configuration, body
and direction; every direction has an offset. The specifications of `stance_certified` and
`stance_check` reach it through the harvest of the world step. -/
theorem facing_position : Regula.ExecutableContract @Host.BoxPosition.facingPosition
    (fun facing =>
      (∀ (config : Host.WorldConfig) (body : Host.BoxPosition config)
        (direction : Host.Direction) (dx dy : Int), Offset direction dx dy →
          (facing body direction).x.val = body.x.val + dx ∧
            (facing body direction).y.val = body.y.val + dy) ∧
        ∀ direction, ∃ dx dy, Offset direction dx dy) :=
  ⟨⟨fun _ _ _ _ _ offset => by
      rcases offset with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        exact ⟨rfl, rfl⟩,
    fun direction => by
      cases direction
      · exact ⟨0, -1, .inl ⟨rfl, rfl, rfl⟩⟩
      · exact ⟨0, 1, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩
      · exact ⟨1, 0, .inr (.inr (.inl ⟨rfl, rfl, rfl⟩))⟩
      · exact ⟨-1, 0, .inr (.inr (.inr ⟨rfl, rfl, rfl⟩))⟩⟩⟩

/-- The offset table gives exactly the offset that `Offset` states by the constructors of a
direction, for every direction and pair of integers. The specifications of the blocked and
stance checks reach it through the world step. The statement has no hypothesis. -/
theorem direction_delta : Regula.ExecutableContract Host.Direction.delta (fun delta =>
    ∀ (direction : Host.Direction) (dx dy : Int), delta direction = (dx, dy) ↔
      Offset direction dx dy) :=
  ⟨fun direction dx dy => by
    cases direction <;> simp [Offset, Host.Direction.delta, Prod.ext_iff, eq_comm]⟩

/-- The decimal discount that the name of each discount declares. -/
def discountDecimal : Discount → ℚ
  | .g90 => 9 / 10
  | .g95 => 19 / 20
  | .g99 => 99 / 100

/-- The rational value of each discount word (`CurrentConstants.discount_values`). -/
private theorem gamma_word (discount : Discount) : CurrentArithmetic.numerical32 discount.gamma =
    match discount with
    | .g90 => ModelConstants.gammaG90
    | .g95 => ModelConstants.gammaG95
    | .g99 => ModelConstants.gammaG99 := by
  have values := congrArg Prod.fst (CurrentConstants.discount_values discount)
  cases discount <;> exact values

/-- The rational value of each horizon word (`CurrentConstants.discount_values`). -/
private theorem horizon_word (discount : Discount) :
    CurrentArithmetic.numerical32 discount.horizon =
      match discount with
      | .g90 => ModelConstants.horizonG90
      | .g95 => ModelConstants.horizonG95
      | .g99 => ModelConstants.horizonG99 := by
  have values := congrArg Prod.snd (CurrentConstants.discount_values discount)
  cases discount <;> exact values

/-- Each discount word is finite, lies in `[1/2, 1)`, and is within `2 ^ -25` of the decimal
that its name declares, for every discount. Neighbouring binary32 values in `[1/2, 1)` are
`2 ^ -24` apart, so the word is the binary32 value nearest to that decimal. The specification of
`precision_admit` applies it. The witness is the word of `g99`, `16609444 / 2 ^ 24`. -/
theorem discount_gamma : Regula.ExecutableContract Discount.gamma (fun gamma =>
    (∀ discount : Discount, (gamma discount).Finite ∧
      1 / 2 ≤ CurrentArithmetic.numerical32 (gamma discount) ∧
        CurrentArithmetic.numerical32 (gamma discount) < 1 ∧
          |CurrentArithmetic.numerical32 (gamma discount) - discountDecimal discount| ≤
            (2 : ℚ) ^ (-25 : Int)) ∧
      CurrentArithmetic.numerical32 (gamma .g99) = 16609444 / 16777216) :=
  ⟨⟨fun discount => by
      have value := gamma_word discount
      cases discount <;>
        refine ⟨by decide, ?_⟩ <;> rw [value] <;>
        norm_num [discountDecimal, ModelConstants.gammaG90, ModelConstants.gammaG95,
          ModelConstants.gammaG99, abs_le],
    by rw [gamma_word .g99]; rfl⟩⟩

/-- Each horizon word is finite and bounds the discounted return of a unit reward,
`1 / (1 - γ)` for the rational value `γ` of the discount word, from above by less than one
relative step of binary32: the word times `1 - 2 ^ -23` is at most that return, for every
discount. The specification of `precision_admit` applies it, and the domains of the weights and
the predictions apply it (`value_rule_domain`, `prediction_range`). The witness is the word of
`g99`, `13107213 / 2 ^ 17`. -/
theorem discount_horizon : Regula.ExecutableContract Discount.horizon (fun horizon =>
    (∀ discount : Discount, (horizon discount).Finite ∧
      1 / (1 - CurrentArithmetic.numerical32 discount.gamma) ≤
        CurrentArithmetic.numerical32 (horizon discount) ∧
      CurrentArithmetic.numerical32 (horizon discount) * (1 - (2 : ℚ) ^ (-23 : Int)) ≤
        1 / (1 - CurrentArithmetic.numerical32 discount.gamma)) ∧
      CurrentArithmetic.numerical32 (horizon .g99) = 13107213 / 131072) :=
  ⟨⟨fun discount => by
      have gamma := gamma_word discount
      have value := horizon_word discount
      cases discount <;>
        refine ⟨by decide, ?_⟩ <;> rw [gamma, value] <;>
        norm_num [ModelConstants.gammaG90, ModelConstants.gammaG95, ModelConstants.gammaG99,
          ModelConstants.horizonG90, ModelConstants.horizonG95, ModelConstants.horizonG99],
    by rw [horizon_word .g99]; rfl⟩⟩

/-- An interval with finite endpoints contains exactly the finite words whose rational value
lies between the rational values of its endpoints (`CurrentOrder.numerical32_order`). -/
private theorem contains_numerical (range : Interval32) (word : Binary32) :
    range.Contains word ↔ word.Finite ∧
      CurrentArithmetic.numerical32 range.lower ≤ CurrentArithmetic.numerical32 word ∧
        CurrentArithmetic.numerical32 word ≤ CurrentArithmetic.numerical32 range.upper := by
  constructor
  · rintro ⟨finite, low, high⟩
    exact ⟨finite, (CurrentOrder.numerical32_order _ _ range.lowerFinite finite).mpr low,
      (CurrentOrder.numerical32_order _ _ finite range.upperFinite).mpr high⟩
  · rintro ⟨finite, low, high⟩
    exact ⟨finite, (CurrentOrder.numerical32_order _ _ range.lowerFinite finite).mp low,
      (CurrentOrder.numerical32_order _ _ finite range.upperFinite).mp high⟩

/-- The weight domain of a discount contains exactly the finite words whose rational value is at
most the horizon in magnitude. -/
private theorem discount_domain (discount : Discount) (word : Binary32) :
    discount.domain.range.Contains word ↔
      word.Finite ∧ |CurrentArithmetic.numerical32 word| ≤
        CurrentArithmetic.numerical32 discount.horizon := by
  rw [contains_numerical]
  change word.Finite ∧ CurrentArithmetic.numerical32 discount.horizon.negate ≤
    CurrentArithmetic.numerical32 word ∧
      CurrentArithmetic.numerical32 word ≤ CurrentArithmetic.numerical32 discount.horizon ↔ _
  rw [(CurrentOffPolicy.horizon_facts discount).2.2.2.1, abs_le]

/-- The weight domain of a rule contains exactly the finite words whose rational value is at most
the horizon of its discount in magnitude, the horizon of `g99` for the differential rule, for
every rule and word. The specifications of `weight_admit` and `candidate_of_weight` in
`Acorn.Decisions` apply it. The witnesses are one, which the domain of `g90` contains, and
sixteen, which it does not. -/
theorem value_rule_domain : Regula.ExecutableContract ValueRule.domain (fun domain =>
    (∀ (discount : Discount) (word : Binary32),
      (domain (.discounted discount)).range.Contains word ↔
        word.Finite ∧ |CurrentArithmetic.numerical32 word| ≤
          CurrentArithmetic.numerical32 discount.horizon) ∧
      (∀ word : Binary32, (domain .differential).range.Contains word ↔
        word.Finite ∧ |CurrentArithmetic.numerical32 word| ≤
          CurrentArithmetic.numerical32 Discount.g99.horizon) ∧
      (domain (.discounted .g90)).range.Contains .one ∧
      ¬(domain (.discounted .g90)).range.Contains ⟨0x41800000⟩) :=
  ⟨⟨discount_domain, discount_domain .g99, by decide, by decide⟩⟩

/-- The prediction range of a discount contains exactly the finite words whose rational value
lies between zero and the horizon, for every discount and word. The specifications of the
assignment, retention, bonus and kept-slot contracts in `Acorn.Decisions` apply it. The
witnesses are one, which the range of `g90` contains, and minus one, which it does not. -/
theorem prediction_range : Regula.ExecutableContract Discount.predictionRange (fun range =>
    (∀ (discount : Discount) (word : Binary32), (range discount).Contains word ↔
      word.Finite ∧ 0 ≤ CurrentArithmetic.numerical32 word ∧
        CurrentArithmetic.numerical32 word ≤ CurrentArithmetic.numerical32 discount.horizon) ∧
      (range .g90).Contains .one ∧ ¬(range .g90).Contains ⟨0xbf800000⟩) :=
  ⟨⟨fun discount word => by
      rw [contains_numerical]
      change word.Finite ∧ CurrentArithmetic.numerical32 Binary32.zero ≤
        CurrentArithmetic.numerical32 word ∧
          CurrentArithmetic.numerical32 word ≤ CurrentArithmetic.numerical32 discount.horizon ↔ _
      have zero : CurrentArithmetic.numerical32 Binary32.zero = 0 := by decide
      rw [zero],
    by decide, by decide⟩⟩

/-- The bound of a reward is one, and the bound of a squared error under a discount is finite and
is the exact real square of twice the rational value of the horizon rounded once to nearest-even
in binary32 (`AcornVerif.FloatLibBridge.binary32_mul_roundAt`, with
`AgreementReturn.envelope_twice` for the envelope), for every discount. The specification of
`sum_admit` applies it through the stored invariant of a total, and the statement `maximum_sum`
names it. The statement has no hypothesis. -/
theorem quantity_limit : Regula.ExecutableContract Quantity.bound (fun bound =>
    CurrentArithmetic.numerical32 (bound .reward) = 1 ∧
      ∀ discount : Discount, (bound (.squaredError discount)).Finite ∧
        ((CurrentArithmetic.numerical32 (bound (.squaredError discount)) : ℚ) : ℝ) =
          FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt
            FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary32
            (((2 * CurrentArithmetic.numerical32 discount.horizon : ℚ) : ℝ) *
              ((2 * CurrentArithmetic.numerical32 discount.horizon : ℚ) : ℝ))) :=
  ⟨⟨by
      change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
      norm_num, fun discount => by
      have twice := AgreementReturn.envelope_twice discount
      have finite : (Quantity.squaredError discount).bound.Finite := by
        cases discount <;> decide
      refine ⟨finite, ?_⟩
      have exact := FloatLibBridge.binary32_mul_roundAt _ _ twice.1 twice.1 finite
      rw [twice.2] at exact
      exact exact⟩⟩

/-- The envelope of a discount, in units of the least binary32 subnormal `2 ^ -149`, is twice
the rational value of its horizon (`AgreementTelemetryPrecision.envelope_value` with
`AgreementReturn.envelope_twice`), for every discount. The specification of `channel_ratio` in
`Acorn.Decisions` applies it. The witness is the envelope of `g99`, `13107213 * 2 ^ 133`
units. -/
theorem envelope_units : Regula.ExecutableContract Agreement.envelopeUnits (fun units =>
    (∀ discount : Discount, (units discount : ℚ) * (2 : ℚ) ^ (-149 : Int) =
      2 * CurrentArithmetic.numerical32 discount.horizon) ∧
      units .g99 = 13107213 * 2 ^ 133) :=
  ⟨⟨fun discount => by
      have value := AgreementTelemetryPrecision.envelope_value discount
      have twice := (AgreementReturn.envelope_twice discount).2
      rw [← twice, ← value, Agreement.unitExponent, div_eq_mul_inv]
      norm_num,
    by decide⟩⟩

/-! ## Verdicts beside a state

Each function below returns its verdict as one component of a pair, and a component of that pair
has a type that depends on an earlier argument: the run that `Features.beginExploration` begins,
which is its verdict component, depends on the action count, and the state beside each other
verdict, the record, the statistics or the learner state, depends on the dimension, the discount
or the configuration. Regula reads a result whose type depends on the input only through
`Regula.Dependent.isSome` and `Regula.Dependent.isOk`, of an `Option` or an `Except`, so no kind
here is about such a component, and each statement is a requirement with no kind. Each states
the verdict for every input; `preceding_advance`, `slot_settles` and `first_loop_prune` also
state what the state keeps; and both verdicts occur at the inputs each names. -/

/-- An exploratory run begins exactly when the 53-bit fraction of the generator's next word is
below the exploration rate, compared as rational numbers (`TemporalSupport.branch_exact`), for
every action count, rate and generator state. The next word is the output of xoshiro256**
stated from the stored words with Lean core's operations on bit vectors: the second word times
five, rotated seven places to the left, times nine (David Blackman and Sebastiano Vigna,
xoshiro256** reference implementation, 2018, `next`:
https://prng.di.unimi.it/xoshiro256starstar.c), and the fraction is its top 53 bits over
`2 ^ 53`. The specification applies no definition of the generator; `Rng.rotateLeft_toBitVec`
connects the rotation that the generator runs. The function compares two binary64 words. Both
verdicts occur at the declared rate: a run begins from the generator state zero, whose
fraction is zero, and none from the state whose second word is `2 ^ 55`, whose fraction is one
quarter.

**Not claimed:** the run that begins and the generator state after its draws. -/
theorem exploration_begins : Regula.ExecutableContract beginExploration (fun begin =>
    (∀ (count : Word.Count) (rate : SwiftTd.ExploreRate) (rng : Rng.Xoshiro256),
      (begin count rate rng).1.isSome =
        decide (((((rng.s1.toBitVec * 5#64).rotateLeft 7 * 9#64) >>> 11).toNat : ℚ) *
          (2 : ℚ) ^ (-53 : Int) < CurrentArithmetic.numerical32 rate.value)) ∧
      (begin ⟨1, by decide⟩ Handcrafted.declaredRate ⟨0, 0, 0, 0⟩).1.isSome = true ∧
      (begin ⟨1, by decide⟩ Handcrafted.declaredRate ⟨0, 0x80000000000000, 0, 0⟩).1.isSome =
        false) :=
  ⟨⟨fun count rate rng => by
      have output : (rng.next.1 >>> 11).toNat =
          (((rng.s1.toBitVec * 5#64).rotateLeft 7 * 9#64) >>> 11).toNat := by
        change ((Rng.rotateLeft (rng.s1 * 5) 7 * 9) >>> 11).toBitVec.toNat = _
        rw [UInt64.toBitVec_shiftRight, UInt64.toBitVec_mul, Rng.rotateLeft_toBitVec,
          UInt64.toBitVec_mul, BitVec.ushiftRight_eq']
        rfl
      rw [← output, ← TemporalSupport.branch_exact]
      cases branch : rng.nextF64.1.less (Conversion.widen rate.value) <;>
        simp [beginExploration, branch],
    by decide, by decide⟩⟩

/-- An advance stores the current set when the frame is armed and the empty set otherwise, and
it records a passage exactly when the stored set is not empty and both sets fit `passageLimit`
(`CurrentOffPolicy.advance_stores`); a recorded passage runs from the stored set to the current
one (`CurrentOffPolicy.advance_passage`). This holds for every dimension, record, current set
and arming. Both verdicts occur over `narrow`: an armed advance from the record that holds
`onlyFirst` to `onlyFirst` records a passage, and one from the empty record records none.
`Features.Preceding.advanceCosted` is the costed definition whose value this function is, and
has no contract of its own: this statement is its evidence.

**Not claimed:** the classes of the passage's features and the flags that the record keeps,
which `Features.Preceding.advance_def` states. -/
theorem preceding_advance : Regula.ExecutableContract @Preceding.advance (fun advance =>
    (∀ {dimension} (preceding : Preceding dimension) (current : SwiftTd.ActiveSet dimension)
        (armed : Bool),
      (advance preceding current armed).2.features =
          (if armed then current else SwiftTd.ActiveSet.empty dimension) ∧
        (advance preceding current armed).1.isSome =
          (!preceding.features.indices.isEmpty &&
            decide (preceding.features.indices.length ≤ passageLimit ∧
              current.indices.length ≤ passageLimit)) ∧
        ∀ passage, (advance preceding current armed).1 = some passage →
          passage.source = preceding.features ∧ passage.target = current) ∧
      (advance ((Preceding.empty narrow).advance onlyFirst true).2 onlyFirst true).1.isSome =
        true ∧
      (advance (Preceding.empty narrow) onlyFirst true).1.isSome = false) :=
  ⟨⟨fun preceding current armed => ⟨(CurrentOffPolicy.advance_stores preceding current armed).1,
      (CurrentOffPolicy.advance_stores preceding current armed).2,
      CurrentOffPolicy.advance_passage preceding current armed⟩,
    by decide, by decide⟩⟩

/-- A slot settles exactly when it holds a sample whose advanced age, one observation older and
capped at `FeatureConstants.maxSettlement`, reaches the settlement horizon. -/
private theorem advanceSlot_capped {discount : Discount} (state : DemonStats discount)
    (slot : Fin FeatureConstants.pendingSamples) (cumulant : Binary32) (clock : UInt64) :
    (state.advanceSlot slot cumulant clock).2.isSome = true ↔
      ∃ sample, state.pending.get slot = some sample ∧
        state.settleAfter.val.val ≤ min (sample.age.val + 1) FeatureConstants.maxSettlement := by
  unfold DemonStats.advanceSlot
  cases state.pending.get slot with
  | none => simp
  | some sample =>
    by_cases due :
        state.settleAfter.val.val ≤ min (sample.age.val + 1) FeatureConstants.maxSettlement
    · simp [PendingPrediction.advance, due]
      omega
    · simp [PendingPrediction.advance, due]
      omega

/-- A slot settles exactly when it holds a sample whose age, one observation older, reaches
the settlement horizon: the horizon is at most `FeatureConstants.maxSettlement`, so the cap
changes no verdict. -/
private theorem advanceSlot_settles {discount : Discount} (state : DemonStats discount)
    (slot : Fin FeatureConstants.pendingSamples) (cumulant : Binary32) (clock : UInt64) :
    (state.advanceSlot slot cumulant clock).2.isSome = true ↔
      ∃ sample, state.pending.get slot = some sample ∧
        state.settleAfter.val.val ≤ sample.age.val + 1 := by
  rw [advanceSlot_capped]
  have bounded := Nat.lt_succ_iff.mp state.settleAfter.val.isLt
  exact ⟨fun ⟨sample, held, due⟩ => ⟨sample, held, (Nat.le_min.mp due).1⟩,
    fun ⟨sample, held, due⟩ => ⟨sample, held, Nat.le_min.mpr ⟨due, bounded⟩⟩⟩

/-- The settlement of one pending slot is reported exactly when the slot holds a sample whose
age, one observation older, reaches the settlement horizon of the statistics; the visit keeps
the horizon (`AgreementLifecycle.advanceSlot_horizon`) and every other slot
(`AgreementLifecycle.advanceSlot_other`). This holds for every discount, statistics, slot,
cumulant and clock. The function advances the sample, capping its age at
`FeatureConstants.maxSettlement`, and compares the advanced age with the horizon. Both verdicts
occur for the discount `Discount.g99`: the first slot settles when every slot holds
`oldestSample`, and the first slot of the initial statistics, which is empty, does not.

**Not claimed:** the settlement reported and what the slot holds afterwards, which
`AgreementLifecycle.advanceSlot_selected` states. -/
theorem slot_settles : Regula.ExecutableContract @DemonStats.advanceSlot (fun advanceSlot =>
    (∀ {discount} (state : DemonStats discount) (slot : Fin FeatureConstants.pendingSamples)
        (cumulant : Binary32) (clock : UInt64),
      ((advanceSlot state slot cumulant clock).2.isSome = true ↔
          ∃ sample, state.pending.get slot = some sample ∧
            state.settleAfter.val.val ≤ sample.age.val + 1) ∧
        (advanceSlot state slot cumulant clock).1.settleAfter = state.settleAfter ∧
        ∀ other, other ≠ slot →
          (advanceSlot state slot cumulant clock).1.pending.get other = state.pending.get other) ∧
      (advanceSlot { DemonStats.initial Discount.g99 with
          pending := Vector.replicate _ (some oldestSample) } ⟨0, by decide⟩ .zero 0).2.isSome =
        true ∧
      (advanceSlot (DemonStats.initial Discount.g99) ⟨0, by decide⟩ .zero 0).2.isSome = false) :=
  ⟨⟨fun state slot cumulant clock => ⟨advanceSlot_settles state slot cumulant clock,
      AgreementLifecycle.advanceSlot_horizon state slot cumulant clock,
      fun other distinct =>
        AgreementLifecycle.advanceSlot_other state slot other distinct cumulant clock⟩,
    (advanceSlot_settles _ _ _ _).mpr ⟨oldestSample, rfl,
      Nat.le_succ_of_le
        (Nat.lt_succ_iff.mp (DemonStats.initial Discount.g99).settleAfter.val.isLt)⟩,
    rfl⟩⟩

/-- The verdict of a first-loop element is its comparison of the decayed trace with the
reference. -/
private theorem first_element_verdict {config : Acorn.Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    (state.firstLoopElement idx delta vDelta decay).2 =
      ((state.transient.z.get idx).value.mul decay).lessOrEqual
        ((state.transient.lastAlpha.get idx).value.mul config.epsilon) := rfl

/-- A first-loop element prunes its index exactly when the trace it stores is at most the
pruning reference it keeps, scaled by the configuration's epsilon
(`CurrentLearner.first_element_prune`); the trace it stores is the trace decayed; it keeps the
pruning references (`CurrentLearner.first_element_reference`) and the eligible list
(`CurrentLearner.first_element_eligible`), and every other index's weight, log step size and
registers (`CurrentLearner.first_element_frame`). This holds for every configuration,
dimension, state, index and error words. At zero decay a managed learner prunes every index
with a finite trace (`CurrentControl.stop_prunes`). Both verdicts occur at the index `first`
of `control` over `narrow`: the fresh learner prunes it at zero decay, and `traced`, whose trace
is one, keeps it at decay one.

**Not claimed:** the values of the weight, the log step size and the registers that the
element writes at its index, which `NumericState.firstLoopElement_eq` states. -/
theorem first_loop_prune :
    Regula.ExecutableContract @NumericState.firstLoopElement (fun element =>
      (∀ {config dimension} (state : NumericState config dimension) (idx : FeatIdx dimension)
          (delta vDelta decay : Binary32),
        (element state idx delta vDelta decay).2 =
            ((element state idx delta vDelta decay).1.transient.z.get idx).value.lessOrEqual
              (((element state idx delta vDelta decay).1.transient.lastAlpha.get idx).value.mul
                config.epsilon) ∧
          ((element state idx delta vDelta decay).1.transient.z.get idx).value =
            (state.transient.z.get idx).value.mul decay ∧
          (element state idx delta vDelta decay).1.transient.lastAlpha =
            state.transient.lastAlpha ∧
          (element state idx delta vDelta decay).1.transient.eligible =
            state.transient.eligible ∧
          ∀ other, idx ≠ other →
            (element state idx delta vDelta decay).1.weights.get other =
                state.weights.get other ∧
              ((element state idx delta vDelta decay).1.beta.get other).value =
                (state.beta.get other).value ∧
              CurrentLearner.registers (element state idx delta vDelta decay).1 other =
                CurrentLearner.registers state other) ∧
        (∀ {config dimension} (learner : Managed config dimension) (idx : FeatIdx dimension)
            (delta vDelta : Binary32), (learner.state.transient.z.get idx).value.Finite →
          (element learner.state idx delta vDelta .zero).2 = true) ∧
        (element (NumericState.initial control narrow) first .zero .zero .zero).2 = true ∧
        (element traced first .zero .zero .one).2 = false) :=
  ⟨⟨fun state idx delta vDelta decay =>
      ⟨CurrentLearner.first_element_prune state idx delta vDelta decay,
        by simp only [NumericState.firstLoopElement, CurrentLearner.vector_get,
          Vector.getElem_set_self],
        CurrentLearner.first_element_reference state idx delta vDelta decay,
        CurrentLearner.first_element_eligible state idx delta vDelta decay,
        fun other distinct =>
          CurrentLearner.first_element_frame state idx other distinct delta vDelta decay⟩,
    fun learner idx delta vDelta finite =>
      CurrentControl.stop_prunes learner idx delta vDelta finite,
    by rw [first_element_verdict]; decide,
    by rw [first_element_verdict]; decide⟩⟩

end AcornVerif.Decisions
