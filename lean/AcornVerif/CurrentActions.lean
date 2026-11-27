import Acorn.Host.WorldDynamics
import AcornVerif.CurrentTerrain

namespace AcornVerif.CurrentActions
open Acorn Acorn.Host

def Reads {config : WorldConfig} (world : World config) (dx dy : Int) : Prop :=
  ∀ tile : Position, tile.x.val = world.body.position.x.val + dx →
    tile.y.val = world.body.position.y.val + dy →
      CurrentTerrain.LatticeAdmits tile config.raw.baseScale

def Enters {config : WorldConfig} (world : World config) (dx dy : Int) : Prop :=
  ∀ tile : Position, tile.x.val = world.body.position.x.val + dx →
    tile.y.val = world.body.position.y.val + dy →
      0 ≤ tile.x.val → tile.x.val < config.side → 0 ≤ tile.y.val → tile.y.val < config.side →
        CurrentTerrain.LatticeAdmits tile config.raw.baseScale

def Faces {config : WorldConfig} (world : World config) : Prop :=
  match world.body.facing with
  | .north => Reads world 0 (-1)
  | .south => Reads world 0 1
  | .east => Reads world 1 0
  | .west => Reads world (-1) 0

def ActionAdmits {config : WorldConfig} (world : World config) : Action → Prop
  | .north => Enters world 0 (-1)
  | .south => Enters world 0 1
  | .east => Enters world 1 0
  | .west => Enters world (-1) 0
  | .harvest => Faces world
  | .wait | .craftAxe | .craftBoat | .eat => True

def Cost (action : Action) (phase cost : Nat) : Prop :=
  (action = .harvest ∧ 4 ≤ phase ∧
      cost = FeatureConstants.harvestCost * FeatureConstants.nightMultiplier) ∨
    (action = .harvest ∧ phase < 4 ∧
      cost = FeatureConstants.harvestCost * FeatureConstants.dayMultiplier) ∨
    (action ≠ .harvest ∧ 4 ≤ phase ∧ cost = FeatureConstants.nightMultiplier) ∨
    (action ≠ .harvest ∧ phase < 4 ∧ cost = FeatureConstants.dayMultiplier)

def Affords {config : WorldConfig} (world : World config) (action : Action) : Prop :=
  ∃ cost, Cost action world.dayPhase.val cost ∧ cost ≤ world.body.energy.val

theorem position_ext {first second : Position}
    (column : first.x.val = second.x.val) (row : first.y.val = second.y.val) :
    first = second := by
  cases first with
  | mk firstX firstY =>
    cases second with
    | mk secondX secondY =>
      congr
      · exact Subtype.ext column
      · exact Subtype.ext row

private theorem checked_val (coordinate : Coordinate) :
    Coordinate.checked coordinate.val = some coordinate := by
  unfold Coordinate.checked
  rw [dite_eq_left coordinate.property]

private theorem translate_facing {config : WorldConfig} (body : BoxPosition config)
    (direction : Direction) :
    body.position.translate direction.delta.1 direction.delta.2 =
      some (body.facingPosition direction) := by
  unfold Position.translate
  rw [show body.position.x.val + direction.delta.1 = (body.facingPosition direction).x.val from rfl,
    show body.position.y.val + direction.delta.2 = (body.facingPosition direction).y.val from rfl,
    checked_val, checked_val]
  rfl

private theorem admits_energy {config : WorldConfig} (world : World config) (energy : Energy)
    (action : Action) :
    ActionAdmits { world with body := { world.body with energy := energy } } action ↔
      ActionAdmits world action := by
  cases action <;> exact Iff.rfl

private theorem checked_isSome (config : WorldConfig) (x y : Int) :
    (BoxPosition.checked config x y).isSome = true ↔
      0 ≤ x ∧ x < config.side ∧ 0 ≤ y ∧ y < config.side := by
  unfold BoxPosition.checked
  by_cases column : 0 ≤ x ∧ x < config.side
  · by_cases row : 0 ≤ y ∧ y < config.side
    · rw [dite_eq_left column, dite_eq_left row]
      exact ⟨fun _ => ⟨column.1, column.2, row.1, row.2⟩, fun _ => rfl⟩
    · rw [dite_eq_left column, dite_eq_right row]
      exact ⟨fun refused => by simp at refused, fun ⟨_, _, low, high⟩ => absurd ⟨low, high⟩ row⟩
  · rw [dite_eq_right column]
    exact ⟨fun refused => by simp at refused,
      fun ⟨low, high, _, _⟩ => absurd ⟨low, high⟩ column⟩

private theorem move_isOk {config : WorldConfig} (world : World config) (action : Action)
    (direction : Direction) (heading : action.direction = some direction) :
    (performAction world action).isOk = true ↔
      ((BoxPosition.checked config (world.body.position.facingPosition direction).x.val
          (world.body.position.facingPosition direction).y.val).isSome = true →
        CurrentTerrain.LatticeAdmits (world.body.position.facingPosition direction)
          config.raw.baseScale) := by
  have ahead := translate_facing world.body.position direction
  rw [← CurrentTerrain.enterable_isOk world]
  unfold performAction
  simp only [heading, ahead]
  cases BoxPosition.checked config (world.body.position.facingPosition direction).x.val
      (world.body.position.facingPosition direction).y.val with
  | none => simp [pure, Except.pure, Except.isOk, Except.toBool]
  | some position =>
    cases world.enterable (world.body.position.facingPosition direction) with
    | error refusal => simp [bind, Except.bind, Except.isOk, Except.toBool]
    | ok enter =>
      cases enter <;> simp [bind, Except.bind, pure, Except.pure, Except.isOk, Except.toBool]

private theorem move_enters {config : WorldConfig} (world : World config) (action : Action)
    (direction : Direction) (heading : action.direction = some direction) :
    (performAction world action).isOk = true ↔
      Enters world direction.delta.1 direction.delta.2 := by
  rw [move_isOk world action direction heading, checked_isSome]
  constructor
  · intro admits tile column row low right high top
    have same : tile = world.body.position.facingPosition direction := position_ext column row
    subst same
    exact admits ⟨low, right, high, top⟩
  · intro enters ⟨low, right, high, top⟩
    exact enters (world.body.position.facingPosition direction) rfl rfl low right high top

private theorem harvest_reads {config : WorldConfig} (world : World config) :
    (performAction world .harvest).isOk = true ↔
      Reads world world.body.facing.delta.1 world.body.facing.delta.2 := by
  have faced : Reads world world.body.facing.delta.1 world.body.facing.delta.2 ↔
      CurrentTerrain.LatticeAdmits (world.body.position.facingPosition world.body.facing)
        config.raw.baseScale :=
    ⟨fun reads => reads (world.body.position.facingPosition world.body.facing) rfl rfl,
      fun admits tile column row => by
      have same : tile = world.body.position.facingPosition world.body.facing :=
        position_ext column row
      subst same
      exact admits⟩
  rw [faced, ← CurrentTerrain.tileKind_isOk world]
  unfold performAction
  simp only [Action.direction]
  cases world.tileKind (world.body.position.facingPosition world.body.facing) with
  | error refusal => simp [bind, Except.bind, Except.isOk, Except.toBool]
  | ok kind =>
    cases kind <;> simp [bind, Except.bind, pure, Except.pure, Except.isOk, Except.toBool,
      TileKind.harvestYield]

private theorem reads_faces {config : WorldConfig} (world : World config) :
    Reads world world.body.facing.delta.1 world.body.facing.delta.2 ↔ Faces world := by
  unfold Faces
  cases world.body.facing <;> rfl

private theorem idle_isOk {config : WorldConfig} (world : World config) (action : Action)
    (idle : action = .wait ∨ action = .craftAxe ∨ action = .craftBoat ∨ action = .eat) :
    (performAction world action).isOk = true := by
  rcases idle with rfl | rfl | rfl | rfl <;> unfold performAction <;>
    simp only [Action.direction] <;> (repeat' split) <;> rfl

theorem performAction_isOk {config : WorldConfig} (world : World config) (action : Action) :
    (performAction world action).isOk = true ↔ ActionAdmits world action := by
  cases action with
  | north => exact move_enters world .north .north rfl
  | south => exact move_enters world .south .south rfl
  | east => exact move_enters world .east .east rfl
  | west => exact move_enters world .west .west rfl
  | harvest => exact (harvest_reads world).trans (reads_faces world)
  | wait => exact iff_of_true (idle_isOk world .wait (.inl rfl)) trivial
  | craftAxe => exact iff_of_true (idle_isOk world .craftAxe (.inr (.inl rfl))) trivial
  | craftBoat => exact iff_of_true (idle_isOk world .craftBoat (.inr (.inr (.inl rfl)))) trivial
  | eat => exact iff_of_true (idle_isOk world .eat (.inr (.inr (.inr rfl)))) trivial

private theorem affords_iff {config : WorldConfig} (world : World config) (action : Action) :
    Affords world action ↔
      action.energyCost (decide (world.dayPhase.val ≥ 4)) ≤ world.body.energy.val := by
  unfold Affords Cost Action.energyCost
  rcases Nat.lt_or_ge world.dayPhase.val 4 with day | night
  · have night : ¬4 ≤ world.dayPhase.val := by omega
    by_cases harvest : action = .harvest <;> simp [harvest, night, day]
  · have night : 4 ≤ world.dayPhase.val := night
    have day : ¬world.dayPhase.val < 4 := by omega
    by_cases harvest : action = .harvest <;> simp [harvest, night, day]

theorem payAndAct_isOk {config : WorldConfig} (world : World config) (action : Action) :
    (payAndAct world action).isOk = true ↔ (Affords world action → ActionAdmits world action) := by
  rw [affords_iff]
  unfold payAndAct
  cases spent : world.body.energy.spend (action.energyCost (decide (world.dayPhase.val ≥ 4))) with
  | none =>
    have short := spent
    unfold Energy.spend at short
    split at short
    · exact nomatch short
    · exact iff_of_true rfl fun paid => absurd paid (by assumption)
  | some energy =>
    have paid : action.energyCost (decide (world.dayPhase.val ≥ 4)) ≤ world.body.energy.val := by
      unfold Energy.spend at spent
      split at spent
      · assumption
      · exact nomatch spent
    exact (performAction_isOk _ action).trans ((admits_energy world energy action).trans
      ⟨fun admits _ => admits, fun admits => admits paid⟩)

end AcornVerif.CurrentActions
