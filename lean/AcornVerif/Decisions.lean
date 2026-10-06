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
argument whose type depends on the configuration, so their statements are requirements with
no kind. A requirement with no kind is weaker than a kind: the Regula audit checks that its
theorem is proved about the executing definition, and it does not check a witness of either
outcome or that the statement is independent of the implementation.

The round trips of the composed checkpoint admissions, the goal completion predicate, checked
translation and precision derivation are stated here for the same reason: their theorems are
in this library. Each contract states only what its theorem proves.

Regula counts only a contract of the function's own library toward a decision registration,
so the functions below carry no registration. The ownership audit requires each contract by
name instead, with a statement that still refers to the executing definition.
-/

namespace AcornVerif.Decisions
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime

/-- Total admission accepts the words of every stored total of the receiving quantity and
returns that total (`CurrentCheckpoint.sum_roundtrip`). The result type depends on the
quantity, so the contract is a requirement with no kind.

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

/-- The replay checker accepts only an action list that shows its goal feasible from its
world within its cap (`CurrentCertificates.replay_feasible`): some run of at least one and at
most `cap` executed steps, from the world with the goal installed, ends in a world that
satisfies the goal. It refuses the empty action list and every list longer than the cap. The
world's type depends on the configuration, so the statement has no kind.

**Not claimed:** completeness, or an accepted input. The checker refuses an action list that
does not itself reach the goal, whether or not the goal is feasible. An acceptance fact needs
an executed world step, whose value rests on the generated terrain; no theorem supplies one. -/
theorem replay_certified : Regula.ExecutableContract @Host.replayCertified (fun check =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (goal : Host.Goal) (cap : Nat),
      (∀ actions : List Host.Action, @check config world goal cap actions = true →
        CurrentCertificates.Feasible world goal cap) ∧
        @check config world goal cap [] = false ∧
        ∀ actions : List Host.Action, cap < actions.length →
          @check config world goal cap actions = false) :=
  ⟨fun _ _ _ cap =>
    ⟨fun _ => CurrentCertificates.replay_feasible, by simp [Host.replayCertified],
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

/-- The stance checker accepts only a stance from which, in every world, a paid harvest
yields the item (`CurrentCertificates.stance_harvest`), which a paid move from the tile behind
it enters facing the resource (`stance_enter`), and whose tile behind is in the box and
enterable in every world (`stance_approach`, `walkable_enterable`). A wood stance needs its
tree standing. It refuses every stance of a box with one tile, because no tile of that box is
behind the stance. The stance's type depends on the configuration, so the statement has no
kind.

**Not claimed:** completeness, an accepted input, or that a step succeeds: a successful step is
a hypothesis. An acceptance fact needs the generated terrain of the tiles at the stance; no
theorem supplies one. -/
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
          action.direction = some direction →
          world.body.position.position.translate direction.delta.1 direction.delta.2 =
            some stance.position →
          world.step action = .ok (next, events) → events.exhausted = false →
            next.body.position = stance ∧ next.body.facing = direction) ∧
        ∃ approach : Host.BoxPosition config,
          approach.position.translate direction.delta.1 direction.delta.2 =
            some stance.position ∧
            ∀ world : Host.World config, world.enterable approach.position = .ok true) ∧
        (config.side = 1 → check config stance direction item = false)) :=
  ⟨fun config stance direction item =>
    ⟨fun accepted =>
      ⟨CurrentCertificates.stance_harvest accepted, CurrentCertificates.stance_enter accepted, by
        obtain ⟨approach, moved, walkable⟩ := CurrentCertificates.stance_approach accepted
        exact ⟨approach, moved, fun world =>
          CurrentCertificates.walkable_enterable world approach.position walkable⟩⟩,
      fun single => by
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
          cases direction <;> simp only [Host.Direction.delta] at column row <;> omega⟩⟩

/-- Replay checking returns a certificate only for an action list that shows its goal
feasible (`CurrentCertificates.replay_feasible`), and it refuses the empty action list. The
statement names the feasibility relation and not the Boolean checker that it calls.

**Not claimed:** an accepted input. An acceptance fact needs an executed world step, whose
value rests on the generated terrain; no theorem supplies one. -/
theorem replay_check : Regula.ExecutableContract @Host.ReplayCertificate.check (fun check =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (goal : Host.Goal) (cap : Nat),
      (∀ actions : List Host.Action, (@check config world goal cap actions).isSome = true →
        CurrentCertificates.Feasible world goal cap) ∧
        @check config world goal cap [] = none) :=
  ⟨fun _ world goal cap =>
    ⟨fun actions present => by
        obtain ⟨certificate, -⟩ := Option.isSome_iff_exists.mp present
        exact CurrentCertificates.replay_feasible certificate.accepted,
      by simp [Host.ReplayCertificate.check, Host.replayCertified]⟩⟩

/-- Blocked checking returns a certificate only for a region that shows the goal box
unreachable from the start tile (`CurrentCertificates.blocked_outside`); it refuses a region
that holds the start tile; and it accepts the empty region for a goal box outside the box of
the world. The statement names the unreachability relation and not the Boolean checker. -/
theorem blocked_check : Regula.ExecutableContract Host.BlockedCertificate.check (fun check =>
    (∀ (config : Host.WorldConfig) (boat : Bool) (target start : Host.Position)
      (cells : List Host.Position),
      ((check config boat target start cells).isSome = true →
        Unreachable config boat target start) ∧
        check config boat target start [start] = none) ∧
      (check ⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩ true
        ⟨⟨100, by decide⟩, ⟨100, by decide⟩⟩ ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ []).isSome =
        true) :=
  ⟨⟨fun config boat target start cells =>
      ⟨fun present world final located later boatless => by
          obtain ⟨certificate, -⟩ := Option.isSome_iff_exists.mp present
          exact CurrentCertificates.blocked_outside (cells := certificate.cells)
            (by rw [located]; exact certificate.accepted) later boatless,
        by simp [Host.BlockedCertificate.check, Host.regionBlocked, Host.inRegion]⟩,
    by decide⟩⟩

/-- Stance checking returns a certificate only for a stance from which, in every world, a
paid harvest yields the item (`CurrentCertificates.stance_harvest`). The statement names the
harvest relation and not the Boolean checker.

**Not claimed:** an accepted or a refused input. Each needs the generated terrain of one
tile; no theorem supplies one. -/
theorem stance_check : Regula.ExecutableContract Host.StanceCertificate.check (fun check =>
    ∀ (config : Host.WorldConfig) (item : Host.Item) (stance : Host.BoxPosition config)
      (direction : Host.Direction),
      (check config item stance direction).isSome = true →
        ∀ (world next : Host.World config) (events : Host.StepResult),
          world.body.position = stance → world.body.facing = direction →
          (item = .wood → world.tileKind (stance.facingPosition direction) = .ok .tree) →
          world.step .harvest = .ok (next, events) → events.exhausted = false →
            events.harvested = some item) :=
  ⟨fun config item stance direction present world next events standing facing grown stepped
      paid => by
    obtain ⟨certificate, built⟩ := Option.isSome_iff_exists.mp present
    have accepted : Host.stanceCertified config stance direction item = true := by
      unfold Host.StanceCertificate.check at built
      split at built
      · assumption
      · exact absurd built (by simp)
    exact (CurrentCertificates.stance_harvest accepted world next events standing facing grown
      stepped paid).1⟩

/-- The walkable test accepts only a tile that is enterable in every world of the
configuration, with or without a boat (`CurrentCertificates.walkable_enterable`).

The function is between fixed types, but the sound kind carries an input the function
accepts, which is the generated terrain of one tile, and no theorem states the terrain of a
tile. The statement is therefore a requirement with no kind.

**Not claimed:** completeness. The test refuses water, which a body with a boat enters. -/
theorem terrain_walkable : Regula.ExecutableContract Host.walkableTile (fun test =>
    ∀ (config : Host.WorldConfig) (tile : Host.Position), test config tile = true →
      ∀ world : Host.World config, world.enterable tile = .ok true) :=
  ⟨fun _ tile accepted world => CurrentCertificates.walkable_enterable world tile accepted⟩

/-! ## Checkpoint admissions

Each admission below composes the admissions of its parts. Its round trip is proved in
`CurrentCheckpoint`, and its type depends on the receiving construction or on the discounts,
so the statement is a requirement with no kind. -/

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
    ∀ (construction : AgentConstruction)
      (image : AgentImage Grid.interface construction.config construction.criterion
        construction.dimension),
      construction.profile.checkpointSupported = true →
        admit construction (imagePayload construction image) = .ok image) :=
  ⟨CurrentCheckpoint.image_roundtrip⟩

/-- Candidate loading accepts the encoded payload of every agent image of a resumable
construction and returns that image (`CurrentCheckpoint.candidate_roundtrip`).

**Not claimed:** that every accepted byte list is such an encoding. -/
theorem candidate_load : Regula.ExecutableContract loadCandidate (fun load =>
    ∀ (construction : AgentConstruction)
      (image : AgentImage Grid.interface construction.config construction.criterion
        construction.dimension),
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
(`CurrentExponential.expSaturation_ends`). -/
theorem exp_saturation : Regula.ExecutableContract Portable.expSaturation
    (Regula.Decides (· = none)
      (fun value : Binary32 => value.Finite ∧
        (Binary32.mk Acorn.Constants.expUnderflowBits).less value = true ∧
          value.less ⟨Acorn.Constants.expOverflowBits⟩ = true)) :=
  ⟨{ sound := fun value admitted => by
       have ends := CurrentExponential.expSaturation_ends value
       rw [admitted] at ends
       exact ends
     accepted := ⟨.zero, by decide⟩
     complete := fun value ⟨finite, above, below⟩ => by
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
(`CurrentStep.enterable_static`). The world's type depends on the configuration, so the
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
with the four family theorems). The statement names no function that the flag applies. The
world's type depends on the configuration, so it is a requirement with no kind. -/
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
value of an accepted result. -/
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
