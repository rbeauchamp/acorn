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

No certificate checker is complete: each contract below states what an accepted certificate
establishes, and a refused certificate establishes nothing. The blocked checker is a function
between fixed types and carries the sound kind. The replay and stance checkers take an
argument whose type depends on the configuration, and their statements are requirements with
no kind. The walkable test is not a certificate checker, and it carries the two-way kind.

A requirement with no kind is a statement that the Regula audit does not examine: that audit
checks only that its theorem is proved about the executing definition. Such a statement can
fix one direction only, and it need not show that both outcomes occur for its function.
Each docstring says what its statement gives and what it does not claim.

The statements of this module with no kind about a function with a dependent type were stated
when Regula had no kind for such a function. Regula v0.10.0 reads a kind for them through the
fields of a structure and the erasures `Regula.Dependent.isSome` and `Regula.Dependent.isOk`,
as `Acorn.Decisions` states them for the functions whose proofs need no proof library. Those
kinds are remaining work of https://github.com/rbeauchamp/acorn/issues/105.

The round trips of the composed checkpoint admissions, the goal completion predicate, checked
translation and precision derivation are stated here for the same reason: their theorems are
in this library. Each contract states only what its theorem proves.

No specification of a contract with a kind here reaches a test that its function runs: Regula's
RG1009 refuses such a contract, and `Acorn.Decisions` states the rule and lists the propositions
that take the place of the tests. The specification of `exp_saturation` names the strict order
`Binary32.Less`.

RG1009 does not examine a statement with no kind, and statements with no kind here do reach
tests that their functions run. This module keeps no list of them, and the examples that follow
are not one. `goal_satisfied` names `Host.Inventory.owns` in its craft clause, and
`replay_certified` and `replay_check` reach it through `Reaches` and `Achieved`: the flag
`Host.World.goalSatisfied` runs that test through `Host.Goal.observe`, `Host.replayCertified`
applies that flag to the final world of its replay, and `Host.ReplayCertificate.check` runs
`Host.replayCertified`. `payload_admit` and `candidate_load` name
`FeatureProfile.checkpointSupported` in their hypothesis, and `admitHeader`, which both
functions run, runs that test. `world_enterable` names `CurrentStep.passable`, which calls
`Host.TileKind.walkable`, and `Host.World.enterable` decides `Host.TileKind.Walkable` through
the instance that runs that test. A statement about runs of the executed world step, such as
`advance_actions` through `CurrentStep.Trace`, reaches each test that the step runs.

Regula counts only a contract of the function's own library toward a decision registration,
so the functions below carry no registration. The ownership audit requires each contract by
name instead, with a statement that still refers to the executing definition.
-/

namespace AcornVerif.Decisions
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime

/-- A world configuration whose box reaches the last coordinate, with a noise scale of one.
The kernel evaluates the terrain of its tiles at that scale, so a tile of this configuration
is the accepted input of `terrain_walkable`. -/
def wide : Host.WorldConfig :=
  ⟨⟨0, ⟨2 ^ 63 - 1, by decide⟩, 1, 0, 0, 0, 0, ⟨0x3f800000⟩⟩, by decide, by decide⟩

/-- The position with the last horizontal coordinate. The terrain generator refuses it with a
coordinate overflow, and the kernel evaluates that refusal. -/
def last : Host.Position := ⟨⟨2 ^ 63 - 1, by decide⟩, ⟨0, by decide⟩⟩

/-- Total admission accepts the words of every stored total of the receiving quantity and
returns that total (`CurrentCheckpoint.sum_roundtrip`). The result type depends on the
quantity, and the contract is a requirement with no kind.

**Not claimed:** that every accepted word pair is the word image of a stored total. -/
theorem sum_admit : Regula.ExecutableContract admitSum (fun admit =>
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
longer than the cap. The world's type depends on the configuration, and the statement has no
kind.

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

/-- The stance checker accepts only a stance from which, in every world, a paid harvest
yields the item (`CurrentCertificates.stance_harvest`), which a paid move from the tile behind
it enters facing the resource (`stance_enter`), and whose tile behind is in the box and
enterable in every world (`stance_approach`, `walkable_enterable`). The tile behind and the
move are stated by coordinate equations and by the constructors of the action and the
direction, with no checked translation and no direction table. A wood stance needs its
tree standing. It refuses every stance of a box with one tile, because no tile of that box is
behind the stance. The stance's type depends on the configuration, and the statement has no
kind.

**Not claimed:** completeness, or that a step succeeds: a successful step is a hypothesis. -/
theorem stance_certified : Regula.ExecutableContract Host.stanceCertified (fun check =>
    ∀ (config : Host.WorldConfig) (stance : Host.BoxPosition config)
      (direction : Host.Direction) (item : Host.Item),
      (check config stance direction item = true →
        (∀ (world next : Host.World config) (events : Host.StepResult),
          world.body.position = stance → world.body.facing = direction →
          (item = .wood → world.tileKind (stance.facingPosition direction) = .ok .tree) →
          world.step .harvest = .ok (next, events) → events.exhausted = false →
            events.harvested = some item ∧
              next.body.inventory = world.body.inventory.add item
                (if item == .wood && world.body.inventory.axe then 3 else 1)) ∧
        (∀ (world next : Host.World config) (action : Host.Action) (events : Host.StepResult),
          Heads action direction →
          stance.position.x.val =
            world.body.position.position.x.val + direction.delta.1 →
          stance.position.y.val =
            world.body.position.position.y.val + direction.delta.2 →
          world.step action = .ok (next, events) → events.exhausted = false →
            next.body.position = stance ∧ next.body.facing = direction) ∧
        ∃ approach : Host.BoxPosition config,
          stance.position.x.val = approach.position.x.val + direction.delta.1 ∧
            stance.position.y.val = approach.position.y.val + direction.delta.2 ∧
            ∀ world : Host.World config, world.enterable approach.position = .ok true) ∧
        (config.side = 1 → check config stance direction item = false)) :=
  ⟨fun config stance direction item =>
    ⟨fun accepted =>
      ⟨CurrentCertificates.stance_harvest accepted,
        fun world next action events heads column row =>
          CurrentCertificates.stance_enter accepted world next action events
            (heads_direction heads)
            (CurrentCertificates.translate_of_eq _ _ _ _ column row), by
        obtain ⟨approach, moved, walkable⟩ := CurrentCertificates.stance_approach accepted
        obtain ⟨column, row⟩ := CurrentCertificates.translate_some _ _ _ _ moved
        exact ⟨approach, column, row, fun world =>
          CurrentCertificates.walkable_enterable world approach.position walkable⟩⟩,
      fun single => single_refused single stance direction item⟩⟩

/-- Replay checking returns a certificate only for an action list that shows its goal reached
(`replay_certified` states the relation), and it refuses the empty action list. The statement
names the relation and not the Boolean checker that the constructor calls. -/
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

/-- Blocked checking returns a certificate only for a region that shows the goal box
unreachable from the start tile (`CurrentCertificates.blocked_outside`), and it refuses the
region that holds only the start tile. The statement names the unreachability relation and
not the Boolean checker. -/
theorem blocked_check : Regula.ExecutableContract Host.BlockedCertificate.check (fun check =>
    ∀ (config : Host.WorldConfig) (boat : Bool) (target start : Host.Position)
      (cells : List Host.Position),
      ((check config boat target start cells).isSome = true →
        Unreachable config boat target start) ∧
        check config boat target start [start] = none) :=
  ⟨fun config boat target start cells =>
      ⟨fun present world final located later boatless => by
          obtain ⟨certificate, -⟩ := Option.isSome_iff_exists.mp present
          exact CurrentCertificates.blocked_outside (cells := certificate.cells)
            (by rw [located]; exact certificate.accepted) later boatless,
        by simp [Host.BlockedCertificate.check, Host.regionBlocked, Host.inRegion]⟩⟩

/-- Stance checking returns a certificate only for a stance from which, in every world, a
paid harvest yields the item (`CurrentCertificates.stance_harvest`), and it refuses every
stance of a box with one tile. The statement names the harvest relation and not the Boolean
checker. -/
theorem stance_check : Regula.ExecutableContract Host.StanceCertificate.check (fun check =>
    ∀ (config : Host.WorldConfig) (item : Host.Item) (stance : Host.BoxPosition config)
      (direction : Host.Direction),
      ((check config item stance direction).isSome = true →
        ∀ (world next : Host.World config) (events : Host.StepResult),
          world.body.position = stance → world.body.facing = direction →
          (item = .wood → world.tileKind (stance.facingPosition direction) = .ok .tree) →
          world.step .harvest = .ok (next, events) → events.exhausted = false →
            events.harvested = some item) ∧
        (config.side = 1 → check config item stance direction = none)) :=
  ⟨fun config item stance direction =>
    ⟨fun present world next events standing facing grown stepped paid => by
      obtain ⟨certificate, built⟩ := Option.isSome_iff_exists.mp present
      have accepted : Host.stanceCertified config stance direction item = true := by
        unfold Host.StanceCertificate.check at built
        split at built
        · assumption
        · exact absurd built (by simp)
      exact (CurrentCertificates.stance_harvest accepted world next events standing facing grown
        stepped paid).1,
    fun single => by
      simp [Host.StanceCertificate.check, single_refused single stance direction item]⟩⟩

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

/-- Demon admission accepts the columns of every durable demon list of the receiving discounts
and returns that list (`CurrentCheckpoint.demons_roundtrip`).

**Not claimed:** that every accepted column triple is the image of a durable list. -/
theorem demons_admit : Regula.ExecutableContract admitDemons (fun admit =>
    ∀ (discounts : List Discount) (records : DurableDemons discounts),
      admit discounts (demonColumns records).sums.toList (demonColumns records).returns.toList
        (demonColumns records).errors.toList = some records) :=
  ⟨fun _ => CurrentCheckpoint.demons_roundtrip⟩

/-- Feature-image admission accepts the feature words of every agent image of the receiving
construction and returns its features (`CurrentCheckpoint.feature_roundtrip`).

**Not claimed:** that every accepted image is the word image of a feature state. -/
theorem feature_image_admit : Regula.ExecutableContract @FeatureImage.admit (fun admit =>
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
and returns that image (`CurrentCheckpoint.image_roundtrip`).

**Not claimed:** that every accepted payload is the payload of an image. -/
theorem payload_admit : Regula.ExecutableContract admitPayload (fun admit =>
    ∀ (construction : AgentConstruction) (image : construction.Image),
      construction.profile.checkpointSupported = true →
        admit construction (imagePayload construction image) = .ok image) :=
  ⟨CurrentCheckpoint.image_roundtrip⟩

/-- Candidate loading accepts the encoded payload of every agent image of a resumable
construction and returns that image (`CurrentCheckpoint.candidate_roundtrip`).

**Not claimed:** that every accepted byte list is such an encoding. -/
theorem candidate_load : Regula.ExecutableContract loadCandidate (fun load =>
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

/-- Whether the body may enter a tile is exactly the static passability of the tile's terrain
with the body's boat, and it refuses exactly when the terrain refuses
(`CurrentStep.enterable_static`). The world's type depends on the configuration, and the
statement is a requirement with no kind. -/
theorem world_enterable : Regula.ExecutableContract @Host.World.enterable (fun enterable =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (position : Host.Position),
      @enterable config world position =
        (Host.terrain position config.raw.seed config.raw.baseScale).map
          (fun base => CurrentStep.passable base world.body.inventory.boat)) :=
  ⟨fun _ => CurrentStep.enterable_static⟩

/-- The world's completion flag, for each family of installed goal, is exactly: the body in
the goal box, the inventory holding the count, the time since installation reaching the
duration; for a craft goal it is the ownership of the tool (`CurrentGoals.goalSatisfied_eq`
with the four family theorems). The statement names neither the completion predicate
`Host.TaskObservation.satisfied` nor `Host.Goal.observe`, which the flag applies. Its craft
clause names the test `Host.Inventory.owns` and its collect clause names the count
`Host.Inventory.count`, and the flag applies both through `Host.Goal.observe`. Its survive
clause repeats the elapsed-time expression that `Host.World.taskObservation` computes. The
world's type depends on the configuration, and it is a requirement with no kind. -/
theorem goal_satisfied : Regula.ExecutableContract @Host.World.goalSatisfied (fun satisfied =>
    ∀ (config : Host.WorldConfig) (world : Host.World config),
      (∀ target, world.goal = some (.reach target) →
        (@satisfied config world = true ↔
          CurrentGoals.InGoalBox target world.body.position.position)) ∧
      (∀ item count, world.goal = some (.collect item count) →
        (@satisfied config world = true ↔
          count.toNat ≤ (world.body.inventory.count item).toNat)) ∧
      (∀ required, world.goal = some (.survive required) →
        (@satisfied config world = true ↔
          required.toNat ≤ ((world.time.toNat - world.goalStart.toNat).toUInt64).toNat)) ∧
      ∀ tool, world.goal = some (.craft tool) →
        @satisfied config world = world.body.inventory.owns tool) :=
  ⟨fun _ world =>
    ⟨fun target installed => by
        rw [CurrentGoals.goalSatisfied_eq world _ installed]
        exact CurrentGoals.reach_satisfied_iff _ _ _ _,
      fun item count installed => by
        rw [CurrentGoals.goalSatisfied_eq world _ installed]
        exact CurrentGoals.collect_satisfied_iff _ _ _ _ _,
      fun required installed => by
        rw [CurrentGoals.goalSatisfied_eq world _ installed]
        exact CurrentGoals.survive_satisfied_iff _ _ _ _,
      fun tool installed => by
        rw [CurrentGoals.goalSatisfied_eq world _ installed]
        exact CurrentGoals.craft_satisfied _ _ _ _⟩⟩

/-- An action replay returns a world exactly when a run of the executed world step over those
actions ends in that world (`CurrentStep.trace_actions`, `CurrentStep.actions_trace`). The
world step is the subject of the claim. The world's type depends on the configuration, and the
statement has no kind. -/
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

/-- The effective kind of a tile is refused exactly when the terrain of the tile is refused,
with the same refusal. The terrain generator is the subject of the claim. The world's type
depends on the configuration, and the statement has no kind.

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

/-- A declared interest refuses a source of declared potentials with another origin
(`CurrentTemporal.declared_refusal`), and a learned interest accepts every source
(`CurrentTemporal.learned_potential`). -/
theorem interest_potential : Regula.ExecutableContract @Interest.potential (fun potential =>
    ∀ {config : Features.Config} {dimension : Dimension},
      (∀ (origin : Departure) (tag : Fin Acorn.FeatureConstants.skillCount)
        (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials),
        origin ≠ declared.origin →
          potential (Interest.declared (config := config) origin tag) features declared =
            none) ∧
      ∀ (assignment : Assignment config) (features : SwiftTd.ActiveSet dimension)
        (declared : DeclaredPotentials),
        (potential (Interest.learned assignment) features declared).isSome = true) :=
  ⟨⟨CurrentTemporal.declared_refusal, fun _ _ _ => rfl⟩⟩

/-- Profile admission accepts the feature words of every agent image of a resumable
construction and returns its features (`CurrentCheckpoint.feature_roundtrip`). The refusal
under every other profile is `profile_admit` in `Acorn.Decisions`. -/
theorem profile_admit_accepts : Regula.ExecutableContract @FeatureProfile.admit (fun admit =>
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
profile is `checkpoint_load` in `Acorn.Decisions`. -/
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

/-- Squared-discrepancy admission accepts every pair of finite words whose exact
discrepancy is within the magnitude of a finite envelope word
(`CurrentAgreement.admitSquared_available`). `squared_admit` in `Acorn.Decisions` states the
kind against the exact squared discrepancy, and `squared_admit_value` the admitted sample. -/
theorem squared_admit_accepts : Regula.ExecutableContract Agreement.admitSquared (fun admit =>
    ∀ forecast outcome envelope : Binary32, forecast.Finite → outcome.Finite →
      envelope.Finite →
      |CurrentArithmetic.numerical32 forecast - CurrentArithmetic.numerical32 outcome| ≤
        |CurrentArithmetic.numerical32 envelope| →
      (admit (Agreement.magnitudeUnits envelope) forecast outcome).isSome = true) :=
  ⟨CurrentAgreement.admitSquared_available⟩

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
