/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Regula.Contract
import AcornVerif.AgreementTelemetryPrecision
import AcornVerif.CurrentCertificates
import AcornVerif.CurrentCheckpoint
import AcornVerif.CurrentExponential
import AcornVerif.CurrentTemporal
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
kind, under the name of the kind with `_refused` or as `interest_potential_declared`.

The round trips of the composed checkpoint admissions, the goal completion predicate, checked
translation and precision derivation are stated here because their theorems are in this
library. Each contract states only what its theorem proves.

## Statements that keep no kind

A requirement with no kind is a statement that the Regula audit does not examine: that audit
checks only that its theorem is proved about the executing definition. Such a statement can
fix one direction only, and it need not show that both outcomes occur for its function.
Each docstring says what its statement gives and what it does not claim.

Seven functions of this module have a contract and no kind. The reasons are three.

* The specification is a statement about runs of the executed world step, which the function
  runs: `Host.replayCertified`, `Host.ReplayCertificate.check` and
  `Host.World.advanceActions`. The step runs tests, and Regula's RG1009
  (https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/) refuses a kind whose
  specification reaches a test that its function runs. A kind needs the world step stated with
  propositions in the place of those tests.
* The input holds a state whose invariant names tests that the function runs, and Regula reads
  the type of the input of a specification (https://github.com/rbeauchamp/regula/issues/270):
  `Checkpoint.load`.
* No theorem states the set of the inputs that the function accepts. The statements of
  `Host.payAndAct` and `Host.performAction` are properties of the result of an accepted
  action, and the statement of `Host.terrain` is about what the readers of its result do with
  it.

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

Two kinds name a function that their functions call, as shared vocabulary. `world_enterable`
and `tile_kind` name the terrain generator `Host.terrain`: no theorem states its refusals in
other terms, and each kind states that its function adds no refusal to those of the generator.
The round trips of the checkpoint admissions name the writers of the forms that they read.

RG1009 does not examine a statement with no kind, and statements with no kind here do reach
tests that their functions run. `replay_certified`, `replay_check` and `advance_actions` reach
each test that the world step runs, through `CurrentStep.Trace`. `task_observed` names
`Host.Inventory.owns` in its craft clause.

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

/-- The position with the last horizontal coordinate. The terrain generator refuses it with a
coordinate overflow, and the kernel evaluates that refusal. -/
def last : Host.Position := ⟨⟨2 ^ 63 - 1, by decide⟩, ⟨0, by decide⟩⟩

/-- A complete decision about whether an optional result holds a value: the function accepts
every input with a written form, and it refuses one input. The kind is about
`Regula.Dependent.isSome` of the function. -/
private theorem reads.{u, v, w} {α : Sort u} {payload : α → Type v} {β : α → Sort w}
    {write : ∀ x, β x → Prop} {f : ∀ x, Option (payload x)}
    (complete : ∀ x (value : β x), write x value → (f x).isSome = true)
    (refused : ∃ x, (f x).isSome = false) :
    Regula.DecidesCompletely (· = true) (fun x => ∃ value : β x, write x value)
      (Regula.Dependent.isSome f) :=
  { complete := fun x ⟨value, written⟩ => complete x value written
    refused := refused.elim fun x none => ⟨x, fun some => by
      have some : (f x).isSome = true := some
      rw [none] at some
      exact Bool.false_ne_true some⟩ }

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

/-- A profile that is not resumable: primitive-only control. -/
def primitive : FeatureProfile := ⟨.primitiveOnly, .perStep, .declared, .learned⟩

/-- A construction of the given profile over `bank` and `narrow`. -/
def construction (profile : FeatureProfile) : AgentConstruction :=
  ⟨profile, .discounted, .none, .learnThenAct, bank, narrow⟩

/-- The feature words of an agent image of a construction: the raw image that the payload of
the image holds. -/
def featureWords (construction : AgentConstruction)
    (image : AgentImage Grid.interface construction.config construction.criterion
      construction.dimension) :
    RawFeatureImage Grid.actions construction.dimension demonLayout :=
  ⟨construction.config.seed, construction.config.tilings,
    construction.config.units.count.toUInt32.toUInt16,
    construction.dimension.capacity.toUInt32, construction.criterion.tag.toUInt32.toUInt8,
    image.features.progress.clock, (testerWords image.features.progress).progress,
    image.features.assignments.map (Assignment.words construction.dimension),
    image.features.primary⟩

/-- The feature words of the initial agent of the construction of a profile. -/
def initialWords (profile : FeatureProfile) : RawFeatureImage Grid.actions narrow demonLayout :=
  featureWords (construction profile)
    (snapshotImage (construction profile) (AgentConstruction.initial _)).image

/-- The payload of the initial agent of the resumable construction. -/
def initialPayload : Payload narrow :=
  imagePayload (construction resumable)
    (snapshotImage (construction resumable) (AgentConstruction.initial _))

/-- A tile of `wide` from which a tree to the west can be harvested. -/
def stand : Host.BoxPosition wide := ⟨⟨0, by decide⟩, ⟨6, by decide⟩⟩

/-- The stance checker accepts the wood stance on `stand`, facing west. The kernel evaluates
the terrain of its three tiles. -/
private theorem stood : Host.stanceCertified wide stand .west .wood = true := by
  decide +kernel

/-- The terrain generator returns a kind for the tile of `stand`: the stance checker accepts
only a stance on a walkable tile. -/
private theorem open_tile :
    (Host.terrain stand.position wide.raw.seed wide.raw.baseScale).isOk = true := by
  have accepted := stood
  unfold Host.stanceCertified at accepted
  have walkable := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp accepted).1).2
  unfold Host.walkableTile at walkable
  cases generated : Host.terrain stand.position wide.raw.seed wide.raw.baseScale with
  | ok kind => rfl
  | error refusal =>
    rw [generated] at walkable
    exact absurd walkable Bool.false_ne_true

/-- The terrain generator refuses the last coordinate. The kernel evaluates the refusal. -/
private theorem last_refused :
    (Host.terrain last wide.raw.seed wide.raw.baseScale).isOk = false := by
  decide +kernel

/-- A result is a success exactly when it is the success of some value. -/
private theorem ok_iff.{u, v} {ε : Type u} {α : Type v} (result : Except ε α) :
    result.isOk = true ↔ ∃ value, result = .ok value := by
  cases result with
  | error refusal => exact ⟨fun ok => (nomatch ok), fun ⟨_, same⟩ => (nomatch same)⟩
  | ok value => exact ⟨fun _ => ⟨value, rfl⟩, fun _ => rfl⟩

/-- Total admission accepts the words of every stored total of the receiving quantity
(`CurrentCheckpoint.sum_roundtrip`), and it refuses a reward total whose sum is a NaN word.
`sum_admit_value` states the total that it returns.

**Not claimed:** soundness. No theorem states that every accepted word pair is the word image
of a stored total. -/
theorem sum_admit : Regula.ExecutableContract admitSum (fun admit =>
    Regula.DecidesCompletely (· = true)
      (fun input : Quantity × SumWords => ∃ record : SumCount input.1, input.2 = sumWords record)
      (Regula.Dependent.isSome fun input : Quantity × SumWords => admit input.1 input.2)) :=
  ⟨reads
    (fun input record written => by
      rw [written, CurrentCheckpoint.sum_roundtrip]
      rfl)
    ⟨(.reward, (0, ⟨0x7ff8000000000000⟩)), by
      have illegal : ¬LegalSum .reward 0 ⟨0x7ff8000000000000⟩ := by decide
      simp [admitSum, SumCount.admit, illegal]⟩⟩

/-- Total admission returns the total whose words it reads (`CurrentCheckpoint.sum_roundtrip`).
A kind does not state the value of a result, so this statement is a requirement with no kind
beside the kind `sum_admit`. -/
theorem sum_admit_value : Regula.ExecutableContract admitSum (fun admit =>
    ∀ (quantity : Quantity) (record : SumCount quantity),
      admit quantity (sumWords record) = some record) :=
  ⟨fun _ => CurrentCheckpoint.sum_roundtrip⟩

/-- An image whose overall reward total is a NaN word, with every other field zero. -/
def refusedLifetime : LifetimeWords :=
  ⟨(0, ⟨0x7ff8000000000000⟩), .replicate _ (0, ⟨0⟩), .replicate _ (0, ⟨0⟩),
    .replicate _ (0, ⟨0⟩), .replicate _ .zero, .replicate _ .zero, .replicate _ (0, ⟨0⟩),
    .replicate _ .initial, .replicate _ (0, 0, 0), .replicate _ (.replicate _ (0, 0, 0))⟩

/-- Lifetime admission accepts every word image of a durable lifetime record whose option
counters are valid with no active option (`CurrentCheckpoint.lifetime_roundtrip`), and it
refuses an image whose overall reward total is a NaN word.

**Not claimed:** that every accepted image is the word image of such a record. -/
theorem lifetime_admit : Regula.ExecutableContract admitLifetime
    (Regula.DecidesCompletely (·.isSome = true) (fun raw =>
      ∃ record : Durable demonLayout, OptionsValid record.options none ∧
        raw = lifetimeWords record)) :=
  ⟨{ complete := fun raw ⟨record, valid, written⟩ => by
       rw [written, CurrentCheckpoint.lifetime_roundtrip record valid]
       rfl
     refused := ⟨refusedLifetime, by
       have illegal : ¬LegalSum .reward 0 ⟨0x7ff8000000000000⟩ := by decide
       simp [admitLifetime, admitSum, SumCount.admit, refusedLifetime, illegal]⟩ }⟩

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

/-- A position is determined by its two coordinates. -/
private theorem position_ext {first second : Host.Position}
    (column : first.x.val = second.x.val) (row : first.y.val = second.y.val) :
    first = second := by
  cases first with
  | mk firstX firstY =>
    cases second with
    | mk secondX secondY =>
      congr
      · exact Subtype.ext column
      · exact Subtype.ext row

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
      position_ext (by rw [column, ← first]; rfl) (by rw [row, ← second]; rfl)
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
    have same : tile = approach.position := position_ext tileColumn tileRow
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

Each admission below composes the admissions of its parts. Its round trip is proved in
`CurrentCheckpoint`, and its type depends on the receiving construction or on the discounts,
and the statement is a requirement with no kind. -/

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

/-- Demon admission accepts the columns of every durable demon list of the receiving discounts
(`CurrentCheckpoint.demons_roundtrip`), and it refuses empty columns for one discount.
`demons_admit_value` states the list that it returns.

**Not claimed:** soundness. No theorem states that every accepted column triple is the image of
a durable list. -/
theorem demons_admit : Regula.ExecutableContract admitDemons (fun admit =>
    Regula.DecidesCompletely (· = true)
      (fun input : DemonsAdmit => ∃ records : DurableDemons input.discounts,
        input.sums = (demonColumns records).sums.toList ∧
          input.returns = (demonColumns records).returns.toList ∧
          input.errors = (demonColumns records).errors.toList)
      (Regula.Dependent.isSome fun input : DemonsAdmit =>
        admit input.discounts input.sums input.returns input.errors)) :=
  ⟨reads
    (fun input records written => by
      rw [written.1, written.2.1, written.2.2, CurrentCheckpoint.demons_roundtrip]
      rfl)
    ⟨⟨[.g99], [], [], []⟩, rfl⟩⟩

/-- Demon admission returns the durable list whose columns it reads
(`CurrentCheckpoint.demons_roundtrip`). A kind does not state the value of a result, so this
statement is a requirement with no kind beside the kind `demons_admit`. -/
theorem demons_admit_value : Regula.ExecutableContract admitDemons (fun admit =>
    ∀ (discounts : List Discount) (records : DurableDemons discounts),
      admit discounts (demonColumns records).sums.toList (demonColumns records).returns.toList
        (demonColumns records).errors.toList = some records) :=
  ⟨fun _ => CurrentCheckpoint.demons_roundtrip⟩

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
seed. `feature_image_admit_value` states the features that it returns.

**Not claimed:** soundness. No theorem states that every accepted image is the word image of a
feature state. -/
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
       rw [featureWords, CurrentCheckpoint.feature_roundtrip construction image]
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

/-- Payload admission accepts the payload of every agent image of a resumable construction
(`CurrentCheckpoint.image_roundtrip`), and it refuses a payload under a construction that is
not resumable. `payload_admit_value` states the image that it returns.

**Not claimed:** soundness. No theorem states that every accepted payload is the payload of an
image. -/
theorem payload_admit : Regula.ExecutableContract admitPayload (fun admit =>
    Regula.DecidesCompletely (· = true)
      (fun input : (construction : AgentConstruction) × Payload construction.dimension =>
        ∃ image : input.1.Image, Resumable input.1.profile ∧
          input.2 = imagePayload input.1 image)
      (Regula.Dependent.isOk fun input :
          (construction : AgentConstruction) × Payload construction.dimension =>
        admit input.1 input.2)) :=
  ⟨{ complete := fun input ⟨image, supported, written⟩ => by
       change (admitPayload input.1 input.2).isOk = true
       rw [written, CurrentCheckpoint.image_roundtrip input.1 image
         ((FeatureProfile.checkpoint_iff _).mpr supported)]
       rfl
     refused := ⟨⟨construction primitive, initialPayload⟩, fun accepted => by
       have accepted : (admitPayload (construction primitive) initialPayload).isOk = true :=
         accepted
       cases admitted : admitPayload (construction primitive) initialPayload with
       | error refusal =>
         rw [admitted] at accepted
         exact Bool.false_ne_true accepted
       | ok image =>
         unfold admitPayload at admitted
         cases header : admitHeader (construction primitive) initialPayload.header with
         | error refusal =>
           rw [header] at admitted
           exact nomatch admitted
         | ok gain =>
           exact absurd ((admitHeader_iff _ _ _).mp header).supported.1 (by decide)⟩ }⟩

/-- Payload admission returns the image whose payload it reads
(`CurrentCheckpoint.image_roundtrip`). A kind does not state the value of a result, so this
statement is a requirement with no kind beside the kind `payload_admit`. -/
theorem payload_admit_value : Regula.ExecutableContract admitPayload (fun admit =>
    ∀ (construction : AgentConstruction) (image : construction.Image),
      construction.profile.checkpointSupported = true →
        admit construction (imagePayload construction image) = .ok image) :=
  ⟨CurrentCheckpoint.image_roundtrip⟩

/-- Candidate loading accepts the encoded payload of every agent image of a resumable
construction (`CurrentCheckpoint.candidate_roundtrip`), and it refuses the empty byte list.
`candidate_load_value` states the image that it returns.

**Not claimed:** soundness. No theorem states that every accepted byte list is such an
encoding. -/
theorem candidate_load : Regula.ExecutableContract loadCandidate (fun load =>
    Regula.DecidesCompletely (· = true)
      (fun input : AgentConstruction × List UInt8 => ∃ image : input.1.Image,
        Resumable input.1.profile ∧
          input.2 = encode input.1.dimension (imagePayload input.1 image))
      (Regula.Dependent.isOk fun input : AgentConstruction × List UInt8 =>
        load input.1 input.2)) :=
  ⟨{ complete := fun input ⟨image, supported, written⟩ => by
       change (loadCandidate input.1 input.2).isOk = true
       rw [written, CurrentCheckpoint.candidate_roundtrip input.1 image
         ((FeatureProfile.checkpoint_iff _).mpr supported)]
       rfl
     refused := ⟨(construction resumable, []), by decide⟩ }⟩

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

/-- The arguments of `Host.World.enterable` and of `Host.World.tileKind`, in order. -/
structure WorldTile where
  /-- The world configuration. -/
  config : Host.WorldConfig
  /-- The world. -/
  world : Host.World config
  /-- The tile. -/
  position : Host.Position

/-- The entry test returns a verdict exactly when the terrain generator returns a kind for the
tile (`CurrentStep.enterable_static`). `Host.terrain` is the generator, which the test also
calls. It is shared vocabulary: the generator is procedural noise with a checked coordinate
range, no theorem states its refusals in other terms, and the claim is that the test adds no
refusal to those of the generator. The two witnesses are the tile of `stand`, whose terrain the
kernel evaluates, and the last coordinate, which the generator refuses, so a generator with one
verdict for every tile fails one of them. `world_enterable_value` states the verdict. -/
theorem world_enterable : Regula.ExecutableContract @Host.World.enterable (fun enterable =>
    Regula.Decides (· = true)
      (fun input : WorldTile => ∃ base,
        Host.terrain input.position input.config.raw.seed input.config.raw.baseScale = .ok base)
      (Regula.Dependent.isOk fun input : WorldTile =>
        @enterable input.config input.world input.position)) :=
  ⟨decides
    (fun input => by
      change (input.world.enterable input.position).isOk = true ↔ _
      rw [CurrentStep.enterable_static]
      cases Host.terrain input.position input.config.raw.seed input.config.raw.baseScale with
      | error refusal => exact ⟨fun ok => (nomatch ok), fun ⟨_, same⟩ => (nomatch same)⟩
      | ok base => exact ⟨fun _ => ⟨base, rfl⟩, fun _ => rfl⟩)
    ⟨⟨wide, .empty wide, stand.position⟩, (ok_iff _).mp open_tile⟩
    ⟨⟨wide, .empty wide, last⟩, fun generated =>
      Bool.false_ne_true (last_refused.symm.trans ((ok_iff _).mpr generated))⟩⟩

/-- Whether the body may enter a tile is exactly the static passability of the tile's terrain
with the body's boat, and it refuses exactly when the terrain refuses
(`CurrentStep.enterable_static`). A kind does not state the value of a result, so this
statement is a requirement with no kind beside the kind `world_enterable`. -/
theorem world_enterable_value : Regula.ExecutableContract @Host.World.enterable
    (fun enterable =>
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
generator.

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

/-- The effective kind of a tile is returned exactly when the terrain generator returns a kind
for the tile. `Host.terrain` is the generator, which the function also calls: it is shared
vocabulary for the reason that `world_enterable` gives, and the witnesses are those of
`world_enterable`. `tile_kind_value` states the refusal.

**Not claimed:** the kind of an accepted tile. `CurrentStep.enterable_static` states what an
entry reads from it. -/
theorem tile_kind : Regula.ExecutableContract @Host.World.tileKind (fun tileKind =>
    Regula.Decides (· = true)
      (fun input : WorldTile => ∃ base,
        Host.terrain input.position input.config.raw.seed input.config.raw.baseScale = .ok base)
      (Regula.Dependent.isOk fun input : WorldTile =>
        @tileKind input.config input.world input.position)) :=
  ⟨decides
    (fun input => by
      change (input.world.tileKind input.position).isOk = true ↔ _
      unfold Host.World.tileKind
      cases Host.terrain input.position input.config.raw.seed input.config.raw.baseScale with
      | error refusal => exact ⟨fun ok => (nomatch ok), fun ⟨_, same⟩ => (nomatch same)⟩
      | ok base =>
        refine ⟨fun _ => ⟨base, rfl⟩, fun _ => ?_⟩
        simp only [bind, Except.bind, pure, Except.pure]
        repeat' split
        all_goals rfl)
    ⟨⟨wide, .empty wide, stand.position⟩, (ok_iff _).mp open_tile⟩
    ⟨⟨wide, .empty wide, last⟩, fun generated =>
      Bool.false_ne_true (last_refused.symm.trans ((ok_iff _).mpr generated))⟩⟩

/-- The effective kind of a tile is refused exactly when the terrain of the tile is refused,
with the same refusal. A kind does not state the value of a result, so this statement is a
requirement with no kind beside the kind `tile_kind`. -/
theorem tile_kind_value : Regula.ExecutableContract @Host.World.tileKind (fun tileKind =>
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

/-- A paid action that succeeds either found the energy short, rested and set the exhausted
flag, or spent the cost of the action with the exhausted flag clear
(`CurrentStep.payAndAct_outcome`). The world's type depends on the configuration, and the
statement has no kind.

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
hypotheses are the predicate `Moves`. The world's type depends on the configuration, and the
statement has no kind.

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

/-- A learned interest accepts every source of declared potentials
(`CurrentTemporal.learned_potential`). The refused input is a declared interest with a source
of another origin. `interest_potential_declared` states that class of refused inputs.

**Not claimed:** soundness. No theorem states the verdict of a declared interest on a source
of its own origin. -/
theorem interest_potential : Regula.ExecutableContract @Interest.potential (fun potential =>
    Regula.DecidesCompletely (·.isSome = true)
      (fun input : InterestPotential => ∃ assignment, input.interest = .learned assignment)
      (fun input : InterestPotential =>
        @potential input.config input.dimension input.interest input.features
          input.declared)) :=
  ⟨{ complete := fun input ⟨assignment, learned⟩ => by
       rw [learned]
       rfl
     refused := ⟨⟨bank, narrow, .declared .spatialPotentials ⟨0, by decide⟩, .empty narrow,
       ⟨.cumulants, .replicate _ false⟩⟩, fun accepted => by
         have accepted : ((Interest.declared (config := bank) .spatialPotentials
           ⟨0, by decide⟩).potential (SwiftTd.ActiveSet.empty narrow)
             ⟨.cumulants, .replicate _ false⟩).isSome = true := accepted
         rw [CurrentTemporal.declared_refusal _ _ _ _ (by decide)] at accepted
         exact absurd accepted (by decide)⟩ }⟩

/-- A declared interest refuses a source of declared potentials with another origin
(`CurrentTemporal.declared_refusal`). A complete kind does not state a set of refused inputs,
so this statement is a requirement with no kind beside the kind `interest_potential`. -/
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
`FeatureImage.admit` refuses; `profile_admit_accepts` states what it accepts. -/
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
construction (`CurrentCheckpoint.feature_roundtrip`), and it refuses the words of the initial
agent under a profile that is not resumable. `profile_admit_sound` states that it accepts
under no other profile, `profile_admit` in `Acorn.Decisions` states the refusal, and
`profile_admit_accepts_value` states the features that it returns. -/
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
       rw [featureWords, CurrentCheckpoint.feature_roundtrip construction image]
       rfl
     refused := ⟨⟨primitive, Grid.actions, bank, .discounted, narrow, demonLayout,
       initialWords primitive⟩, fun accepted => by
         have accepted : (FeatureProfile.admit primitive bank .discounted narrow
           (initialWords primitive)).isSome = true := accepted
         rw [FeatureProfile.unsupported_refuses primitive bank .discounted narrow
           (initialWords primitive) (by decide)] at accepted
         exact absurd accepted Bool.false_ne_true⟩ }⟩

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
