import Regula.Contract
import Acorn.Host.Attempt
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
import AcornVerif.CurrentRunner
import AcornVerif.CurrentSpawn
import AcornVerif.CurrentTemporal
import AcornVerif.CurrentTerrain
import AcornVerif.CurrentWorld
import AcornVerif.Decimal
import AcornVerif.Endurance
import AcornVerif.FloatLibBridge
import AcornVerif.TemporalSupport

namespace AcornVerif.Decisions
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime
open Acorn.Handcrafted.FeatureProfile (Resumable)

def wide : Host.WorldConfig :=
  ⟨⟨0, ⟨2 ^ 63 - 1, by decide⟩, 1, 0, 0, 0, 0, ⟨0x3f800000⟩⟩, by decide, by decide⟩

def last : Host.Position := ⟨⟨2 ^ 63 - 1, by decide⟩, ⟨0, by decide⟩⟩

def wideAt (scale : Binary32) : Host.WorldConfig :=
  ⟨{ wide.raw with baseScale := scale }, wide.positiveSide, wide.positiveDay⟩

private theorem decides.{u, v} {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
    {f : α → ρ} (iff : ∀ x, accepts (f x) ↔ spec x) (holds : ∃ x, spec x)
    (fails : ∃ x, ¬spec x) : Regula.Decides accepts spec f :=
  .of_iff iff (holds.elim fun x satisfied => ⟨x, (iff x).mpr satisfied⟩)
    (fails.elim fun x unsatisfied => ⟨x, fun accepted => unsatisfied ((iff x).mp accepted)⟩)

def bank : Features.Config :=
  ⟨0, 1, by decide, ⟨1, by decide, by decide⟩, ⟨1, by decide, by decide, 0, .zero, .zero⟩⟩

def narrow : Dimension := ⟨1, by decide, ⟨0, rfl⟩, by decide⟩

def resumable : FeatureProfile := ⟨.final, .perStep, .declared, .learned⟩

def construction (profile : FeatureProfile) : AgentConstruction :=
  ⟨profile, .discounted, .none, .learnThenAct, bank, narrow⟩

def control : Acorn.Config := ⟨.control, .differential⟩

def first : FeatIdx narrow := ⟨0, by decide⟩

def traced : NumericState control narrow :=
  let fresh := NumericState.initial control narrow
  { fresh with transient := { fresh.transient with z := #v[⟨⟨0x3f800000⟩⟩] } }

def oldestSample : PendingPrediction Discount.g99 :=
  ⟨⟨FeatureConstants.maxSettlement, by decide⟩, Prediction.project _ .zero, .zero, .one, 0⟩

def stand : Host.BoxPosition wide := ⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩

private theorem stood : Host.stanceCertified wide stand .west .wood = true := by
  decide +kernel

private theorem sum_written {quantity : Quantity} {words : SumWords}
    {record : SumCount quantity} (admitted : admitSum quantity words = some record) :
    words = sumWords record := by
  unfold admitSum SumCount.admit at admitted
  split at admitted
  · cases admitted
    rfl
  · exact nomatch admitted

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

theorem sum_admit_value : Regula.ExecutableContract admitSum (fun admit =>
    ∀ (quantity : Quantity) (record : SumCount quantity),
      admit quantity (sumWords record) = some record) :=
  ⟨fun _ => CurrentImage.sum_roundtrip⟩

def Achieved (goal : Host.Goal) (position : Host.Position) (inventory : Host.Inventory)
    (elapsed : UInt64) : Prop :=
  match goal with
  | .reach target => CurrentGoals.InGoalBox target position
  | .collect item count => count.toNat ≤ (inventory.count item).toNat
  | .craft tool => inventory.Owns tool
  | .survive required => required.toNat ≤ elapsed.toNat
  | .find target => CurrentGoals.InGoalBox target position

structure Replay where
  config : Host.WorldConfig
  world : Host.World config
  goal : Host.Goal
  cap : Nat
  actions : List Host.Action

def Replays {config : Host.WorldConfig} (world : Host.World config) (goal : Host.Goal) (cap : Nat)
    (actions : List Host.Action) : Prop :=
  0 < actions.length ∧ actions.length ≤ cap ∧
    ∃ (trace : List (Host.Action × Host.StepResult)) (final : Host.World config),
      CurrentStep.Trace (world.setGoal goal) trace final ∧ trace.map (·.1) = actions ∧
        final.Attained goal

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

def Unreachable (config : Host.WorldConfig) (boat : Bool) (target start : Host.Position) :
    Prop :=
  ∀ world final : Host.World config, world.body.position.position = start →
    CurrentGoals.Later world final → (boat = false → final.body.inventory.boat = false) →
      ¬CurrentGoals.InGoalBox target final.body.position.position

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

def Heads (action : Host.Action) (direction : Host.Direction) : Prop :=
  (action = .north ∧ direction = .north) ∨ (action = .south ∧ direction = .south) ∨
    (action = .east ∧ direction = .east) ∨ (action = .west ∧ direction = .west)

private theorem heads_direction {action : Host.Action} {direction : Host.Direction}
    (heads : Heads action direction) : action.direction = some direction := by
  rcases heads with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

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

def Offset (direction : Host.Direction) (dx dy : Int) : Prop :=
  (direction = .north ∧ dx = 0 ∧ dy = -1) ∨ (direction = .south ∧ dx = 0 ∧ dy = 1) ∨
    (direction = .east ∧ dx = 1 ∧ dy = 0) ∨ (direction = .west ∧ dx = -1 ∧ dy = 0)

private theorem offset_delta {direction : Host.Direction} {dx dy : Int}
    (offset : Offset direction dx dy) : direction.delta = (dx, dy) := by
  rcases offset with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rfl

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

structure StanceCertified where
  config : Host.WorldConfig
  stance : Host.BoxPosition config
  direction : Host.Direction
  item : Host.Item

theorem stance_certified : Regula.ExecutableContract Host.stanceCertified (fun check =>
    Regula.DecidesSoundly (· = true)
      (fun input : StanceCertified =>
        Harvests input.config input.stance input.direction input.item)
      (fun input : StanceCertified =>
        check input.config input.stance input.direction input.item)) :=
  ⟨{ sound := fun _ accepted => stance_sound accepted
     accepted := ⟨⟨wide, stand, .west, .wood⟩, stood⟩ }⟩

theorem stance_certified_refused : Regula.ExecutableContract Host.stanceCertified (fun check =>
    ∀ (config : Host.WorldConfig) (stance : Host.BoxPosition config)
      (direction : Host.Direction) (item : Host.Item),
      config.side = 1 → check config stance direction item = false) :=
  ⟨fun _ stance direction item single => single_refused single stance direction item⟩

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

structure BlockedCheck where
  config : Host.WorldConfig
  boat : Bool
  target : Host.Position
  start : Host.Position
  cells : List Host.Position

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

theorem blocked_check_refused : Regula.ExecutableContract Host.BlockedCertificate.check
    (fun check =>
      ∀ (config : Host.WorldConfig) (boat : Bool) (target start : Host.Position),
        check config boat target start [start] = none) :=
  ⟨fun _ _ _ _ => by simp [Host.BlockedCertificate.check, Host.regionBlocked, Host.inRegion]⟩

structure StanceCheck where
  config : Host.WorldConfig
  item : Host.Item
  stance : Host.BoxPosition config
  direction : Host.Direction

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

theorem stance_check_refused : Regula.ExecutableContract Host.StanceCertificate.check
    (fun check =>
      ∀ (config : Host.WorldConfig) (item : Host.Item) (stance : Host.BoxPosition config)
        (direction : Host.Direction),
        config.side = 1 → check config item stance direction = none) :=
  ⟨fun _ item stance direction single => by
    simp [Host.StanceCertificate.check, single_refused single stance direction item]⟩

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

theorem payload_admit : Regula.ExecutableContract admitPayload (fun admit =>
    ∀ (construction : AgentConstruction) (payload : Payload),
      (admit construction payload).isOk = true ↔
        ∃ image : construction.Image, Resumable construction.profile ∧
          payload = imagePayload construction image) :=
  ⟨payload_iff⟩

theorem payload_admit_value : Regula.ExecutableContract admitPayload (fun admit =>
    ∀ (construction : AgentConstruction) (image : construction.Image),
      construction.profile.checkpointSupported = true →
        admit construction (imagePayload construction image) = .ok image) :=
  ⟨CurrentCheckpoint.image_roundtrip⟩

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

theorem candidate_load : Regula.ExecutableContract loadCandidate (fun load =>
    ∀ (construction : AgentConstruction) (bytes : List UInt8),
      (load construction bytes).isOk = true ↔
        ∃ image : construction.Image, Resumable construction.profile ∧
          bytes = encode (imagePayload construction image)) :=
  ⟨candidate_iff⟩

theorem candidate_load_value : Regula.ExecutableContract loadCandidate (fun load =>
    ∀ (construction : AgentConstruction) (image : construction.Image),
      construction.profile.checkpointSupported = true →
        load construction (encode (imagePayload construction image)) = .ok image) :=
  ⟨CurrentCheckpoint.candidate_roundtrip⟩

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

theorem rank_index : Regula.ExecutableContract Host.Endurance.rankIndex (fun index =>
    Regula.DecidesSoundly (·.isSome = true)
      (fun input : ((Nat × Nat) × Nat) × List Nat =>
        ∃ i, input.1.1.1 ≤ input.1.1.2 * (input.1.2 + (input.2.take (i + 1)).sum))
      (Function.uncurry (Function.uncurry (Function.uncurry index)))) :=
  ⟨{ sound := fun input accepted => by
       obtain ⟨i, found⟩ := Option.isSome_iff_exists.mp accepted
       exact ⟨i, (Endurance.rankIndex_spec input.1.1.1 input.1.1.2 input.1.2 input.2 i found).1⟩
     accepted := ⟨(((0, 1), 0), [0]), by decide⟩ }⟩

theorem value_noise_lattice : Regula.ExecutableContract Host.valueNoise (fun valueNoise =>
    Regula.Decides (·.isOk = true)
      (fun input : (Host.Position × Binary32) × UInt64 =>
        ¬CurrentTerrain.PastLast ((Host.coordinateFloat input.1.1.x).div input.1.2) ∧
          ¬CurrentTerrain.PastLast ((Host.coordinateFloat input.1.1.y).div input.1.2))
      (Function.uncurry (Function.uncurry valueNoise))) :=
  ⟨decides (fun input => CurrentTerrain.valueNoise_isOk input.1.1 input.1.2 input.2)
    ⟨((last, ⟨0x40000000⟩), 0), by decide +kernel⟩
    ⟨((last, ⟨0x3f000000⟩), 0), by decide +kernel⟩⟩

structure OctaveLoop where
  count : Nat
  position : Host.Position
  seed : UInt64
  scale : Binary32
  amplitude : Binary32
  sum : Binary32

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

theorem fbm_lattice : Regula.ExecutableContract Host.fbm (fun fbm =>
    Regula.Decides (·.isOk = true)
      (fun input : (Host.Position × UInt64) × Binary32 =>
        CurrentTerrain.LatticeAdmits input.1.1 input.2)
      (Function.uncurry (Function.uncurry fbm))) :=
  ⟨decides (fun input => CurrentTerrain.fbm_isOk input.1.1 input.1.2 input.2)
    ⟨((last, 0), ⟨0x40000000⟩), by decide +kernel⟩
    ⟨((last, 0), ⟨0x3f000000⟩), by decide +kernel⟩⟩

structure WorldTile where
  config : Host.WorldConfig
  world : Host.World config
  position : Host.Position

theorem terrain_lattice : Regula.ExecutableContract Host.terrain (fun terrain =>
    Regula.Decides (·.isOk = true)
      (fun input : (Host.Position × UInt64) × Binary32 =>
        CurrentTerrain.LatticeAdmits input.1.1 input.2)
      (Function.uncurry (Function.uncurry terrain))) :=
  ⟨decides (fun input => CurrentTerrain.terrain_isOk input.1.1 input.1.2 input.2)
    ⟨((last, 0), ⟨0x40000000⟩), by decide +kernel⟩
    ⟨((last, 0), ⟨0x3f000000⟩), by decide +kernel⟩⟩

theorem tile_kind_lattice : Regula.ExecutableContract @Host.World.tileKind (fun tileKind =>
    Regula.Decides (·.isOk = true)
      (fun input : WorldTile =>
        CurrentTerrain.LatticeAdmits input.position input.config.raw.baseScale)
      (fun input : WorldTile => @tileKind input.config input.world input.position)) :=
  ⟨decides (fun input => CurrentTerrain.tileKind_isOk input.world input.position)
    ⟨⟨wideAt ⟨0x40000000⟩, Host.World.empty _, last⟩, by decide +kernel⟩
    ⟨⟨wideAt ⟨0x3f000000⟩, Host.World.empty _, last⟩, by decide +kernel⟩⟩

theorem world_enterable_lattice : Regula.ExecutableContract @Host.World.enterable
    (fun enterable =>
    Regula.Decides (·.isOk = true)
      (fun input : WorldTile =>
        CurrentTerrain.LatticeAdmits input.position input.config.raw.baseScale)
      (fun input : WorldTile => @enterable input.config input.world input.position)) :=
  ⟨decides (fun input => CurrentTerrain.enterable_isOk input.world input.position)
    ⟨⟨wideAt ⟨0x40000000⟩, Host.World.empty _, last⟩, by decide +kernel⟩
    ⟨⟨wideAt ⟨0x3f000000⟩, Host.World.empty _, last⟩, by decide +kernel⟩⟩

theorem world_enterable : Regula.ExecutableContract @Host.World.enterable (fun enterable =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (position : Host.Position),
      @enterable config world position =
        (Host.terrain position config.raw.seed config.raw.baseScale).map
          (fun base => CurrentStep.passable base world.body.inventory.boat)) :=
  ⟨fun _ => CurrentStep.enterable_static⟩

theorem goal_satisfied : Regula.ExecutableContract @Host.World.goalSatisfied (fun satisfied =>
    Regula.Decides (· = true)
      (fun input : (config : Host.WorldConfig) × Host.World config => ∃ goal,
        input.2.goal = some goal ∧ input.2.Attained goal)
      (fun input : (config : Host.WorldConfig) × Host.World config =>
        @satisfied input.1 input.2)) :=
  ⟨decides (fun input => Host.World.goalSatisfied_iff input.2)
    ⟨⟨wide, (Host.World.empty wide).setGoal (.survive 0)⟩, .survive 0, rfl, Nat.zero_le _⟩
    ⟨⟨wide, .empty wide⟩, fun ⟨_, installed, _⟩ => (nomatch installed)⟩⟩

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

structure WorldAction where
  config : Host.WorldConfig
  world : Host.World config
  action : Host.Action

def faced : Host.Position := ⟨⟨2 ^ 62 - 1, by decide⟩, ⟨2 ^ 62 - 2, by decide⟩⟩

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

private theorem harvest_paid :
    CurrentActions.Affords (Host.World.empty (wideAt ⟨0x3f000000⟩)) .harvest :=
  ⟨FeatureConstants.harvestCost * FeatureConstants.nightMultiplier,
    .inl ⟨rfl, by decide, rfl⟩, by decide⟩

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

def Moves {config : Host.WorldConfig} (world : Host.World config) (action : Host.Action)
    (direction : Host.Direction) (position : Host.BoxPosition config) : Prop :=
  Heads action direction ∧
    position.position.x.val = world.body.position.position.x.val + direction.delta.1 ∧
    position.position.y.val = world.body.position.position.y.val + direction.delta.2 ∧
    world.enterable position.position = .ok true

theorem perform_action : Regula.ExecutableContract @Host.performAction (fun perform =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (action : Host.Action)
      (direction : Host.Direction) (position : Host.BoxPosition config)
      (active : Host.ActionChange config), Moves world action direction position →
      @perform config world action = .ok active →
        active.body.position = position ∧ active.body.facing = direction) :=
  ⟨fun _ world action direction position active ⟨heads, column, row, enter⟩ performed =>
    CurrentCertificates.perform_move world action direction position (heads_direction heads)
      (CurrentCertificates.translate_of_eq _ _ _ _ column row) enter active performed⟩

structure AdvanceActions where
  config : Host.WorldConfig
  world : Host.World config
  actions : List Host.Action

theorem advance_actions_value : Regula.ExecutableContract @Host.World.advanceActions
    (fun advance =>
      ∀ (config : Host.WorldConfig) (world final : Host.World config)
        (actions : List Host.Action),
        @advance config world actions = .ok final ↔
          ∃ trace, CurrentStep.Trace world trace final ∧ trace.map (·.1) = actions) :=
  ⟨fun _ world final actions =>
    ⟨CurrentStep.actions_trace world final actions,
      fun ⟨_, run, same⟩ => same ▸ CurrentStep.trace_actions run⟩⟩

private theorem step_paid {config : Host.WorldConfig} {world middle : Host.World config}
    {action : Host.Action} {events : Host.StepResult}
    (stepped : world.step action = .ok (middle, events)) :
    (Host.payAndAct world action).isOk = true := by
  obtain ⟨active, paid, -⟩ := CurrentStep.step_active world middle action events stepped
  rw [paid]
  rfl

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

def fresh (cap : UInt64) : Host.Attempt wide Unit (.survive 0) cap :=
  ⟨⟨(Host.World.empty wide).setGoal (.survive 0), (), {}, 0⟩, rfl, 0, .zero, .wait⟩

private theorem ok_of_isOk {ε α : Type} {result : Except ε α} (accepted : result.isOk = true) :
    ∃ value, result = .ok value := by
  cases result with
  | error error => exact absurd accepted (by simp [Except.isOk, Except.toBool])
  | ok value => exact ⟨value, rfl⟩

private theorem ofFnM_isOk {ε α : Type} {n : Nat} (f : Fin n → Except ε α)
    (each : ∀ index, (f index).isOk = true) : (Vector.ofFnM f).isOk = true := by
  have values : f = fun index => pure (Classical.choose (ok_of_isOk (each index))) :=
    funext fun index => Classical.choose_spec (ok_of_isOk (each index))
  rw [values, Vector.ofFnM_pure]
  rfl

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

private theorem window_admits : ∀ offset : Fin Host.patchSide, ∀ octave : Fin 4,
    ¬CurrentTerrain.PastLast
      ((Host.coordinateFloatWord (Int64.ofInt (2 ^ 62 - 6 + offset.val))).div
        (CurrentTerrain.octaveScale ⟨0x3f800000⟩ octave.val)) := by
  decide +kernel

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

private theorem fresh_waits : ((fresh 1).run.world.step .wait).isOk = true := by
  decide +kernel

private theorem finish_isOk {order : StepOrder} {config : Host.WorldConfig} {α β : Type}
    {goal : Host.Goal} {cap : UInt64} (callbacks : Host.AgentCallbacks order α β)
    (context : Host.GoalContext) (attempt : Host.Attempt config α goal cap)
    (observed : attempt.run.world.observe.isOk = true) :
    (attempt.finish callbacks context).isOk = true := by
  obtain ⟨observation, observed⟩ := ok_of_isOk observed
  unfold Host.Attempt.finish
  simp only [observed, bind, Except.bind, pure, Except.pure]
  rfl

private theorem complete_isOk {order : StepOrder} {config : Host.WorldConfig} {α β : Type}
    {goal : Host.Goal} {cap : UInt64} (callbacks : Host.AgentCallbacks order α β)
    (context : Host.GoalContext) (attempt : Host.Attempt config α goal cap)
    (finished : (attempt.finish callbacks context).isOk = true) :
    (Host.Attempt.complete callbacks context 0 attempt).isOk = true := by
  obtain ⟨result, finished⟩ := ok_of_isOk finished
  simp only [Host.Attempt.complete, Host.Attempt.close, finished]
  rfl

theorem attempt_finish_accepts : Regula.ExecutableContract @Host.Attempt.finish (fun finish =>
    ∀ {order β} (callbacks : Host.AgentCallbacks order Unit β) (context : Host.GoalContext)
      (cap : UInt64), (finish callbacks context (fresh cap)).isOk = true) :=
  ⟨fun callbacks context cap => finish_isOk callbacks context (fresh cap) (fresh_observes cap)⟩

theorem attempt_complete_accepts : Regula.ExecutableContract @Host.Attempt.complete
    (fun complete =>
      ∀ {order β} (callbacks : Host.AgentCallbacks order Unit β) (context : Host.GoalContext)
        (cap : UInt64), (complete callbacks context 0 (fresh cap)).isOk = true) :=
  ⟨fun callbacks context cap => complete_isOk callbacks context (fresh cap)
    (finish_isOk callbacks context (fresh cap) (fresh_observes cap))⟩

structure ReleasedEnvironment where
  config : Host.WorldConfig
  agent : Type
  goal : Host.Goal
  cap : UInt64
  released : Host.Released config agent goal cap

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

private theorem bind_isOk {ε α β : Type} (first : Except ε α) (rest : α → Except ε β)
    (accepted : first.isOk = true) (each : ∀ value, (rest value).isOk = true) :
    (first >>= rest).isOk = true := by
  obtain ⟨value, same⟩ := ok_of_isOk accepted
  rw [same]
  exact each value

private theorem isOk_of_bind {ε α β : Type} {first : Except ε α} {rest : α → Except ε β}
    (accepted : (first >>= rest).isOk = true) : first.isOk = true := by
  cases first with
  | error refusal => exact accepted
  | ok value => rfl

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

def SquareAdmits (x y : Int) (radius : Nat) (scale : Binary32) : Prop :=
  ∀ row column, row < 2 * radius + 1 → column < 2 * radius + 1 → ∃ tile : Host.Position,
    tile.x.val = x + ((column : Int) - radius) ∧ tile.y.val = y + ((row : Int) - radius) ∧
      CurrentTerrain.LatticeAdmits tile scale

private theorem countKindNear_isOk {config : Host.WorldConfig} (world : Host.World config)
    (position : Host.Position) (radius : Nat) (kind : Host.TileKind)
    (admits : SquareAdmits position.x.val position.y.val radius config.raw.baseScale) :
    (Host.countKindNear world position radius kind).isOk = true := by
  unfold Host.countKindNear
  dsimp only
  refine bind_isOk _ _ ?_ fun _ => rfl
  refine CurrentWorld.forIn_range_isOk _ _ _ fun row state rowBound => ?_
  refine bind_isOk _ _ ?_ fun _ => rfl
  refine CurrentWorld.forIn_range_isOk _ _ _ fun column count columnBound => ?_
  obtain ⟨tile, tileColumn, tileRow, admitted⟩ := admits row column rowBound columnBound
  have translated := CurrentCertificates.translate_of_eq _ _ _ _ tileColumn tileRow
  obtain ⟨found, located⟩ := ok_of_isOk ((CurrentTerrain.tileKind_isOk world tile).mpr admitted)
  simp only [translated, located, bind, Except.bind]
  split <;> rfl

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

structure KindSquare where
  config : Host.WorldConfig
  world : Host.World config
  position : Host.Position
  radius : Nat
  kind : Host.TileKind

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

theorem spawn_count_value : Regula.ExecutableContract @Host.countKindNear (fun count =>
    ∀ {config} (world : Host.World config) (position : Host.Position) (radius found : Nat)
      (kind : Host.TileKind), count world position radius kind = .ok found →
        found = CurrentSpawn.squareCount world position radius kind (2 * radius + 1)) :=
  ⟨fun world position radius found kind counted =>
    CurrentSpawn.countKindNear_eq world position radius found kind counted⟩

structure SpawnCoordinate where
  config : Host.WorldConfig
  world : Host.World config
  x : Int
  y : Int
  best : Option (Host.SpawnCandidate config)

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

theorem spawn_consider_value : Regula.ExecutableContract @Host.considerSpawn (fun consider =>
    ∀ {config} (world : Host.World config) (x y : Int)
      (best selected : Option (Host.SpawnCandidate config)) (finished : Bool),
      consider world x y best = .ok (selected, finished) →
        CurrentSpawn.Considered world x y best selected finished) :=
  ⟨fun world x y best selected finished considered =>
    CurrentSpawn.considerSpawn_outcome world x y best selected finished considered⟩

def oneTile : Host.WorldConfig :=
  ⟨⟨0, ⟨1, by decide⟩, 8, 0, 0, 0, 0, ⟨0x3f800000⟩⟩, by decide, by decide⟩

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
    ⟨oneTile, Host.World.empty oneTile,
      CurrentWorld.admissible_selectSpawn_isOk (by decide) _⟩⟩⟩

theorem world_initial_accepts : Regula.ExecutableContract Host.World.initial (fun initial =>
    Regula.Decides (· = true)
      (fun config : Host.WorldConfig => config.raw.Admissible)
      (Regula.Dependent.isOk initial)) :=
  ⟨decides
    (fun config => (CurrentWorld.initial_isOk_iff config).trans
      (Host.RawWorldConfig.admissible_spec_iff config.raw))
    ⟨oneTile, (Host.RawWorldConfig.admissible_spec_iff oneTile.raw).mp (by decide)⟩
    ⟨wide, fun h => absurd
      ((Host.RawWorldConfig.admissible_spec_iff wide.raw).mpr h) (by decide)⟩⟩

theorem world_observe_accepts : Regula.ExecutableContract @Host.World.observe (fun observe =>
    Regula.DecidesCompletely (·.isOk = true)
      (fun input : (config : Host.WorldConfig) × Host.World config => input.1.raw.Admissible)
      (fun input : (config : Host.WorldConfig) × Host.World config =>
        @observe input.1 input.2)) :=
  ⟨{ complete := fun input hspec =>
       CurrentWorld.admissible_observe_isOk
         ((Host.RawWorldConfig.admissible_spec_iff input.1.raw).mpr hspec)
         input.2
     refused := by
       let base := Host.World.empty wide
       let edgePos : Host.BoxPosition wide := ⟨⟨2 ^ 63 - 2, by decide⟩, ⟨0, by decide⟩⟩
       let edgeWorld : Host.World wide :=
         { base with body := { base.body with position := edgePos } }
       refine ⟨⟨wide, edgeWorld⟩, ?_⟩
       have href : (edgeWorld.observe).isOk = false :=
         CurrentWorld.observe_refuses_exceeds_maxSide (by decide) edgeWorld (by decide)
       rw [href]
       exact Bool.false_ne_true }⟩

theorem world_step_accepts : Regula.ExecutableContract @Host.World.step (fun step =>
    Regula.DecidesCompletely (· = true)
      (fun input : WorldAction => input.config.raw.Admissible)
      (Regula.Dependent.isOk fun input : WorldAction =>
        @step input.config input.world input.action)) :=
  ⟨{ complete := fun input hspec =>
       CurrentWorld.admissible_step_isOk
         ((Host.RawWorldConfig.admissible_spec_iff input.config.raw).mpr hspec)
         input.world input.action
     refused :=
       ⟨⟨wideAt ⟨0x3f000000⟩, Host.World.empty _, .harvest⟩, fun accepted => by
         obtain ⟨⟨next, events⟩, stepped⟩ := (Regula.Dependent.isOk_eq_true_iff _ _).mp accepted
         exact absurd ((harvest_faced ⟨0x3f000000⟩).mp
           ((CurrentActions.payAndAct_isOk _ _).mp (step_paid stepped) harvest_paid))
           (by decide +kernel)⟩ }⟩

theorem spawn_select_accepts : Regula.ExecutableContract @Host.selectSpawn (fun select =>
    Regula.DecidesCompletely (· = true)
      (fun input : (config : Host.WorldConfig) × Host.World config => input.1.raw.Admissible)
      (Regula.Dependent.isOk fun input : (config : Host.WorldConfig) × Host.World config =>
        @select input.1 input.2)) :=
  ⟨{ complete := fun input hspec =>
       CurrentWorld.admissible_selectSpawn_isOk
         ((Host.RawWorldConfig.admissible_spec_iff input.1.raw).mpr hspec)
         input.2
     refused := by
       let zeroTile : Host.WorldConfig :=
         ⟨{ oneTile.raw with baseScale := ⟨0x00000000⟩ },
           oneTile.positiveSide, oneTile.positiveDay⟩
       refine ⟨⟨zeroTile, Host.World.empty zeroTile⟩, ?_⟩
       decide +kernel }⟩

structure WorldObserveTile where
  config : Host.WorldConfig
  world : Host.World config
  occupied : Host.Occupancy
  row : Fin Host.patchSide
  column : Fin Host.patchSide

theorem observe_tile_accepts : Regula.ExecutableContract @Host.World.observeTile
    (fun observeTile =>
      Regula.DecidesCompletely (·.isOk = true)
        (fun input : WorldObserveTile => input.config.raw.Admissible)
        (fun input : WorldObserveTile =>
          @observeTile input.config input.world input.occupied input.row input.column)) :=
  ⟨{ complete := fun input hspec =>
       CurrentWorld.admissible_observeTile_isOk
         ((Host.RawWorldConfig.admissible_spec_iff input.config.raw).mpr hspec)
         input.world input.occupied input.row input.column
     refused := by
       let base := Host.World.empty wide
       let edgePos : Host.BoxPosition wide := ⟨⟨2 ^ 63 - 2, by decide⟩, ⟨0, by decide⟩⟩
       let edgeWorld : Host.World wide :=
         { base with body := { base.body with position := edgePos } }
       refine ⟨⟨wide, edgeWorld, ∅, ⟨5, by decide⟩, ⟨10, by decide⟩⟩, ?_⟩
       have htr : edgeWorld.body.position.position.translate
           (10 - (Host.patchSide : Int) / 2) (5 - (Host.patchSide : Int) / 2) = none := by
         decide
       simp [Host.World.observeTile, htr, Except.isOk, Except.toBool] }⟩

theorem wander_population_accepts : Regula.ExecutableContract @Host.wanderPopulation
    (fun wander =>
      Regula.DecidesCompletely (· = true)
        (fun input : (config : Host.WorldConfig) × Host.World config => input.1.raw.Admissible)
        (Regula.Dependent.isOk fun input : (config : Host.WorldConfig) × Host.World config =>
          @wander input.1 input.2)) :=
  ⟨{ complete := fun input hspec =>
       CurrentWorld.admissible_wanderPopulation_isOk
         ((Host.RawWorldConfig.admissible_spec_iff input.1.raw).mpr hspec)
         input.2
     refused := by
       let deerCfg : Host.WorldConfig :=
         ⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 1, ⟨0x00000000⟩⟩, by decide, by decide⟩
       let deerPos : Host.Position := ⟨⟨10, by decide⟩, ⟨10, by decide⟩⟩
       let deerWorld : Host.World deerCfg :=
         { Host.World.empty deerCfg with
           deer := ⟨#[deerPos], by decide⟩
           rng := Rng.Xoshiro256.zero }
       refine ⟨⟨deerCfg, deerWorld⟩, ?_⟩
       decide +kernel }⟩

structure FoodTrialsInput where
  config : Host.WorldConfig
  world : Host.World config
  count : Nat
  rng : Rng.Xoshiro256

theorem food_trials_accepts : Regula.ExecutableContract @Host.foodTrials
    (fun trials =>
      Regula.DecidesCompletely (· = true)
        (fun input : FoodTrialsInput => input.config.raw.Admissible)
        (Regula.Dependent.isOk fun input : FoodTrialsInput =>
          @trials input.config input.world input.count input.rng)) :=
  ⟨{ complete := fun input hspec =>
       (Regula.Dependent.isOk_eq_true_iff _ input).mpr
         (CurrentWorld.admissible_foodTrials_isOk
           ((Host.RawWorldConfig.admissible_spec_iff input.config.raw).mpr hspec)
           input.world input.count input.rng)
     refused := by
       let twoZero : Host.WorldConfig :=
         ⟨⟨0, ⟨2, by decide⟩, 1, 0, 1, 1, 1, ⟨0x00000000⟩⟩, by decide, by decide⟩
       refine ⟨⟨twoZero, Host.World.empty twoZero, 8, Rng.Xoshiro256.seed 0⟩, ?_⟩
       decide +kernel }⟩

structure SpawnFoodInput where
  config : Host.WorldConfig
  world : Host.World config
  rng : Rng.Xoshiro256

theorem spawn_food_accepts : Regula.ExecutableContract @Host.spawnFood
    (fun spawn =>
      Regula.DecidesCompletely (· = true)
        (fun input : SpawnFoodInput => input.config.raw.Admissible)
        (Regula.Dependent.isOk fun input : SpawnFoodInput =>
          @spawn input.config input.world input.rng)) :=
  ⟨{ complete := fun input hspec =>
       CurrentWorld.admissible_spawnFood_isOk
         ((Host.RawWorldConfig.admissible_spec_iff input.config.raw).mpr hspec)
         input.world input.rng
     refused := by
       let twoZero : Host.WorldConfig :=
         ⟨⟨0, ⟨2, by decide⟩, 1, 0, 1, 1, 1, ⟨0x00000000⟩⟩, by decide, by decide⟩
       refine ⟨⟨twoZero, Host.World.empty twoZero, Rng.Xoshiro256.seed 0⟩, ?_⟩
       decide +kernel }⟩

theorem initialize_deer_accepts : Regula.ExecutableContract @Host.initializeDeer
    (fun init =>
      Regula.DecidesCompletely (· = true)
        (fun input : (config : Host.WorldConfig) × Host.World config => input.1.raw.Admissible)
        (Regula.Dependent.isOk fun input : (config : Host.WorldConfig) × Host.World config =>
          @init input.1 input.2)) :=
  ⟨{ complete := fun input hspec =>
       CurrentWorld.admissible_initializeDeer_isOk
         ((Host.RawWorldConfig.admissible_spec_iff input.1.raw).mpr hspec)
         input.2
     refused := by
       let twoZero : Host.WorldConfig :=
         ⟨⟨0, ⟨2, by decide⟩, 1, 0, 1, 1, 1, ⟨0x00000000⟩⟩, by decide, by decide⟩
       refine ⟨⟨twoZero, Host.World.empty twoZero⟩, ?_⟩
       decide +kernel }⟩

theorem world_admitted_nonrefusal {raw : Host.RawWorldConfig} {config : Host.WorldConfig}
    (hadmit : Host.WorldConfig.admit raw = .ok config) (initial world : Host.World config)
    (hinit : Host.World.initial config = .ok initial)
    (hreach : CurrentWorld.Reachable initial world) :
    (world.observe).isOk = true ∧
      (∀ action : Host.Action, (world.step action).isOk = true) ∧
      (∀ actions : List Host.Action, (world.advanceActions actions).isOk = true) :=
  CurrentWorld.admitted_config_reachable_nonrefusal hadmit initial world hinit hreach

structure ClearAt where
  config : Acorn.Config
  dimension : Dimension
  state : NumericState config dimension
  index : FeatIdx dimension

theorem learner_clear : Regula.ExecutableContract @NumericState.clearAt (fun clearAt =>
    Regula.Decides (· = true)
      (fun input : ClearAt =>
        CurrentLearner.registers input.state input.index = Vector.replicate 9 .zero)
      (fun input : ClearAt => @clearAt input.config input.dimension input.state input.index)) :=
  ⟨decides (fun input => CurrentLearnerCheck.clearAt_iff input.state input.index)
    ⟨⟨control, narrow, NumericState.initial _ _, first⟩, by decide⟩
    ⟨⟨control, narrow, traced, first⟩, by decide⟩⟩

theorem learner_resumable : Regula.ExecutableContract @NumericState.resumable (fun resumable =>
    ∀ {config : Acorn.Config} {dimension : Dimension} (state : NumericState config dimension)
      (phase : Bool),
      resumable state phase = true ↔ CurrentLearner.ScheduleInv state phase) :=
  ⟨CurrentLearnerCheck.resumable_iff⟩

structure InterestPotential where
  config : Features.Config
  dimension : Dimension
  interest : Interest config
  features : SwiftTd.ActiveSet dimension
  declared : DeclaredPotentials

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

theorem interest_potential_declared : Regula.ExecutableContract @Interest.potential
    (fun potential =>
    ∀ {config : Features.Config} {dimension : Dimension} (origin : Departure)
      (tag : Fin Acorn.FeatureConstants.skillCount) (features : SwiftTd.ActiveSet dimension)
      (declared : DeclaredPotentials), origin ≠ declared.origin →
        potential (Interest.declared (config := config) origin tag) features declared = none) :=
  ⟨CurrentTemporal.declared_refusal⟩

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

structure Load where
  construction : AgentConstruction
  receiver : construction.State
  bytes : List UInt8

theorem checkpoint_load : Regula.ExecutableContract Checkpoint.load (fun load =>
    Regula.DecidesSoundly (· = true)
      (fun input : Load => Resumable input.construction.profile)
      (Regula.Dependent.isOk fun input : Load =>
        load input.construction input.receiver input.bytes)) :=
  ⟨⟨fun input accepted => load_resumable input.construction input.receiver input.bytes accepted,
    ⟨⟨construction resumable, AgentConstruction.initial _,
        encode (snapshot (construction resumable) (AgentConstruction.initial _))⟩,
      (Regula.Dependent.isOk_eq_true_iff _ _).mpr ⟨_, CurrentCheckpoint.save_load _ _ _ rfl⟩⟩⟩⟩

theorem checkpoint_load_accepts : Regula.ExecutableContract Checkpoint.load (fun load =>
    ∀ (construction : AgentConstruction) (source receiver : construction.State),
      construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
        construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned →
      load construction receiver (encode (snapshot construction source)) = .ok source) :=
  ⟨fun construction source receiver resumable =>
    CurrentCheckpoint.save_load construction receiver source
      ((FeatureProfile.checkpoint_iff construction.profile).mpr resumable)⟩

private theorem loadKeeping_ok_snd {c : AgentConstruction} {r s : c.State} {b : List UInt8}
    (loaded : Checkpoint.load c r b = .ok s) :
    (Checkpoint.loadKeeping c r b).2 = none := by
  unfold Checkpoint.loadKeeping
  rw [loaded]

private theorem loadKeeping_not_resumable_snd {c : AgentConstruction} (r : c.State)
    (b : List UInt8) (unsupported : ¬Resumable c.profile) :
    (Checkpoint.loadKeeping c r b).2.isSome = true := by
  unfold Checkpoint.loadKeeping
  cases loading : Checkpoint.load c r b with
  | error _ => rfl
  | ok _ => exact absurd (load_resumable c r b (by rw [loading]; rfl)) unsupported

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
      fun restored loaded => by unfold Checkpoint.loadKeeping; rw [loaded]⟩,
    loadKeeping_ok_snd (CurrentCheckpoint.save_load (construction resumable)
      (AgentConstruction.initial _) (AgentConstruction.initial _) rfl),
    loadKeeping_not_resumable_snd (AgentConstruction.initial _)
      (encode (snapshot (construction ⟨.final, .perStep, .declared, .spatial⟩)
        (AgentConstruction.initial _)))
      (by decide)⟩⟩

private theorem resume_saved_state (construction : AgentConstruction)
    (receiver source : construction.State)
    (supported : construction.profile.checkpointSupported = true) :
    resume construction receiver (encode (snapshot construction source)) =
      .ok source.beginSession := by
  unfold resume
  rw [CurrentCheckpoint.save_load construction receiver source supported]
  rfl

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

theorem checkpoint_resume_accepts : Regula.ExecutableContract Checkpoint.resume (fun resume =>
    ∀ (construction : AgentConstruction) (source receiver : construction.State),
      construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
        construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned →
      resume construction receiver (encode (snapshot construction source)) =
        .ok source.beginSession) :=
  ⟨fun construction source receiver resumable =>
    resume_saved_state construction receiver source
      ((FeatureProfile.checkpoint_iff construction.profile).mpr resumable)⟩

theorem agent_input_edges : Regula.ExecutableContract @Agent.input (fun input =>
    ∀ {profile config criterion dimension planning}
      (before after : Agent Grid.interface profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (stopped : Bool),
      input before event = (after, stopped) → CurrentAgent.EdgeContract before event after) :=
  ⟨fun before after event stopped executed =>
    CurrentAgent.edge_contract before after event stopped executed⟩

theorem execute_prefix : Regula.ExecutableContract AgentConstruction.execute (fun execute =>
    ∀ (admitted : DefaultConstruction)
      (events : List (AgentInput admitted.construction.config admitted.construction.criterion
        admitted.construction.dimension)),
      CurrentAgent.SafePath admitted.construction.initial.agent events
        (execute admitted events).1.agent (execute admitted events).2) :=
  ⟨CurrentAgent.native_prefix⟩

structure SquaredAdmit where
  envelope : Nat
  forecast : Binary32
  outcome : Binary32

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

theorem managed_words : Regula.ExecutableContract @managedWords (fun words =>
    ∀ {config : Acorn.Config} {dimension : Dimension} (learner : Managed config dimension),
      managedState (words learner) = learner.state ∧ (words learner).2.2.2.2.2 = learner.phase) :=
  ⟨fun learner => ⟨CurrentImage.managedState_words learner, rfl⟩⟩

theorem squared_units : Regula.ExecutableContract Agreement.squaredUnits (fun squared =>
    (∀ forecast outcome : Binary32, forecast.Finite → outcome.Finite →
      (squared forecast outcome : ℚ) * ((2 : ℚ) ^ (-149 : Int)) ^ 2 =
        (CurrentArithmetic.numerical32 forecast - CurrentArithmetic.numerical32 outcome) ^ 2) ∧
      squared .zero .zero = 0 ∧ squared ⟨1⟩ .zero = 1) :=
  ⟨⟨CurrentAgreement.squaredUnits_numerical, by decide, by decide⟩⟩

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

theorem digits_spelled : Regula.ExecutableContract Host.Microduck.spelled (fun spell =>
    (∀ digits : List Char, (∀ c ∈ digits, Json.Numeral.Digit c) →
      spell digits = Decimal.numberOf digits) ∧ spell ['4', '2'] = 42) :=
  ⟨⟨Decimal.spelled_numberOf, rfl⟩⟩

theorem decimal_of_numeral : Regula.ExecutableContract Host.Microduck.Decimal.ofNumeral
    (fun read =>
      (∀ numeral : Json.Numeral, numeral.Formed →
        Decimal.value (read numeral) = Decimal.written numeral) ∧
        read ⟨true, ['1'], some ['5'], none⟩ = ⟨true, 15, -1⟩) :=
  ⟨⟨Decimal.ofNumeral_value, rfl⟩⟩

def tens : Host.Microduck.Scale := ⟨0, -10, 10, by decide⟩

theorem decimal_fixed : Regula.ExecutableContract @Host.Microduck.Decimal.fixed (fun fixed =>
    (∀ (scale : Host.Microduck.Scale) (decimal : Host.Microduck.Decimal) (nearest : Int),
      Decimal.Nearest (Decimal.value decimal * (10 : ℚ) ^ scale.places) nearest →
        (fixed scale decimal).val = max scale.low (min scale.high nearest)) ∧
      (fixed tens ⟨true, 15, -1⟩).val = -2 ∧ (fixed tens ⟨false, 0, 0⟩).val = 0) :=
  ⟨⟨Decimal.fixed_nearest, by decide +kernel, by decide +kernel⟩⟩

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

theorem direction_delta : Regula.ExecutableContract Host.Direction.delta (fun delta =>
    ∀ (direction : Host.Direction) (dx dy : Int), delta direction = (dx, dy) ↔
      Offset direction dx dy) :=
  ⟨fun direction dx dy => by
    cases direction <;> simp [Offset, Host.Direction.delta, Prod.ext_iff, eq_comm]⟩

def discountDecimal : Discount → ℚ
  | .g90 => 9 / 10
  | .g95 => 19 / 20
  | .g99 => 99 / 100

private theorem gamma_word (discount : Discount) : CurrentArithmetic.numerical32 discount.gamma =
    match discount with
    | .g90 => ModelConstants.gammaG90
    | .g95 => ModelConstants.gammaG95
    | .g99 => ModelConstants.gammaG99 := by
  have values := congrArg Prod.fst (CurrentConstants.discount_values discount)
  cases discount <;> exact values

private theorem horizon_word (discount : Discount) :
    CurrentArithmetic.numerical32 discount.horizon =
      match discount with
      | .g90 => ModelConstants.horizonG90
      | .g95 => ModelConstants.horizonG95
      | .g99 => ModelConstants.horizonG99 := by
  have values := congrArg Prod.snd (CurrentConstants.discount_values discount)
  cases discount <;> exact values

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

private theorem signedFieldUnits_neg (precision : Nat) (key : Int) :
    CurrentOrder.signedFieldUnits precision (-key) =
      -CurrentOrder.signedFieldUnits precision key := by
  unfold CurrentOrder.signedFieldUnits
  rcases lt_trichotomy key 0 with negative | zero | positive
  · have notNegative : ¬ (-key < 0) := by omega
    have magnitude : (-key).toNat = key.natAbs := by omega
    simp only [notNegative, negative, ↓reduceIte, neg_neg, magnitude]
  · subst zero
    simp [CurrentOrder.fieldUnits_zero]
  · have negated : -key < 0 := by omega
    have notNegative : ¬ (key < 0) := by omega
    have magnitude : (-key).natAbs = key.toNat := by omega
    simp only [negated, notNegative, ↓reduceIte, magnitude]

private theorem horizon_negate (discount : Discount) :
    CurrentArithmetic.numerical32 discount.horizon.negate =
      -CurrentArithmetic.numerical32 discount.horizon := by
  have finite : discount.horizon.Finite := by cases discount <;> decide
  have negFinite : discount.horizon.negate.Finite := by cases discount <;> decide
  have keys : discount.horizon.negate.key = -discount.horizon.key := by cases discount <;> decide
  rw [CurrentOrder.numerical32_key_units _ negFinite, CurrentOrder.numerical32_key_units _ finite,
    keys, signedFieldUnits_neg]
  push_cast
  ring

private theorem discount_domain (discount : Discount) (word : Binary32) :
    discount.domain.range.Contains word ↔
      word.Finite ∧ |CurrentArithmetic.numerical32 word| ≤
        CurrentArithmetic.numerical32 discount.horizon := by
  rw [contains_numerical]
  change word.Finite ∧ CurrentArithmetic.numerical32 discount.horizon.negate ≤
    CurrentArithmetic.numerical32 word ∧
      CurrentArithmetic.numerical32 word ≤ CurrentArithmetic.numerical32 discount.horizon ↔ _
  rw [horizon_negate discount, abs_le]

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

private theorem advanceSlot_settles {discount : Discount} (state : DemonStats discount)
    (slot : Fin FeatureConstants.pendingSamples) (cumulant : Binary32) (clock : UInt64) :
    (state.advanceSlot slot cumulant clock).2.isSome = true ↔
      ∃ sample, state.pending.get slot = some sample ∧
        state.settleAfter.val.val ≤ sample.age.val + 1 := by
  rw [advanceSlot_capped]
  have bounded := Nat.lt_succ_iff.mp state.settleAfter.val.isLt
  exact ⟨fun ⟨sample, held, due⟩ => ⟨sample, held, (Nat.le_min.mp due).1⟩,
    fun ⟨sample, held, due⟩ => ⟨sample, held, Nat.le_min.mpr ⟨due, bounded⟩⟩⟩

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

private theorem first_element_verdict {config : Acorn.Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    (state.firstLoopElement idx delta vDelta decay).2 =
      ((state.transient.z.get idx).value.mul decay).lessOrEqual
        ((state.transient.lastAlpha.get idx).value.mul config.epsilon) := rfl

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
