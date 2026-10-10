/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldDynamics
import AcornVerif.CurrentTerrain

/-!
# Refusals of the paid actions

`Host.performAction` reads the terrain of at most one tile. A movement action reads the tile one
step ahead of the body when that tile is in the box, and a harvest reads the tile that the body
faces, in the box or not. The other actions read no tile. The action is refused exactly when the
terrain refuses the tile that it reads, `CurrentTerrain.LatticeAdmits`. The checked translation of
a move never overflows: the body is in the box, and the side of the box is a signed coordinate.

`Host.payAndAct` performs the action when the energy pays its cost and rests otherwise. It is
refused exactly when the energy pays the cost and the action is refused.

`ActionAdmits` and `Affords` state the tiles and the cost by the constructors of the action and
of the direction, by equations on the coordinates and the box indices, and by the stored energy
and the phase of the day: no direction table, offset table, checked translation, box admission,
facing position or cost function. The phase of the day is `Host.World.dayPhase`, which the paid
action also reads.
-/

namespace AcornVerif.CurrentActions
open Acorn Acorn.Host

/-- The terrain admits every tile whose coordinates are those of the body plus the offset. -/
def Reads {config : WorldConfig} (world : World config) (dx dy : Int) : Prop :=
  ∀ tile : Position, tile.x.val = world.body.position.x.val + dx →
    tile.y.val = world.body.position.y.val + dy →
      CurrentTerrain.LatticeAdmits tile config.raw.baseScale

/-- The terrain admits every tile in the box whose coordinates are those of the body plus the
offset. -/
def Enters {config : WorldConfig} (world : World config) (dx dy : Int) : Prop :=
  ∀ tile : Position, tile.x.val = world.body.position.x.val + dx →
    tile.y.val = world.body.position.y.val + dy →
      0 ≤ tile.x.val → tile.x.val < config.side → 0 ≤ tile.y.val → tile.y.val < config.side →
        CurrentTerrain.LatticeAdmits tile config.raw.baseScale

/-- The terrain admits the tile that the body faces: north is one tile toward negative y, south
one toward positive y, east one toward positive x and west one toward negative x. -/
def Faces {config : WorldConfig} (world : World config) : Prop :=
  match world.body.facing with
  | .north => Reads world 0 (-1)
  | .south => Reads world 0 1
  | .east => Reads world 1 0
  | .west => Reads world (-1) 0

/-- The terrain admits the tile that an action reads: the tile one step ahead in the direction of
a movement action when that tile is in the box, and the tile that the body faces for a harvest.
The other actions read no tile. -/
def ActionAdmits {config : WorldConfig} (world : World config) : Action → Prop
  | .north => Enters world 0 (-1)
  | .south => Enters world 0 1
  | .east => Enters world 1 0
  | .west => Enters world (-1) 0
  | .harvest => Faces world
  | .wait | .craftAxe | .craftBoat | .eat => True

/-- The cost of an action at a phase of the day, in tenths of an energy unit: `harvestCost` for
a harvest and one for every other action, times `nightMultiplier` from the fifth of the eight
phases and `dayMultiplier` before it. -/
def Cost (action : Action) (phase cost : Nat) : Prop :=
  (action = .harvest ∧ 4 ≤ phase ∧
      cost = FeatureConstants.harvestCost * FeatureConstants.nightMultiplier) ∨
    (action = .harvest ∧ phase < 4 ∧
      cost = FeatureConstants.harvestCost * FeatureConstants.dayMultiplier) ∨
    (action ≠ .harvest ∧ 4 ≤ phase ∧ cost = FeatureConstants.nightMultiplier) ∨
    (action ≠ .harvest ∧ phase < 4 ∧ cost = FeatureConstants.dayMultiplier)

/-- The stored energy of the body pays the cost of the action at the phase of the day. -/
def Affords {config : WorldConfig} (world : World config) (action : Action) : Prop :=
  ∃ cost, Cost action world.dayPhase.val cost ∧ cost ≤ world.body.energy.val

/-- A position is determined by its two coordinates. -/
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

/-- Coordinate admission accepts a coordinate unchanged. -/
private theorem checked_val (coordinate : Coordinate) :
    Coordinate.checked coordinate.val = some coordinate := by
  unfold Coordinate.checked
  rw [dite_eq_left coordinate.property]

/-- The checked translation of an in-box body by the offset of a direction is the facing position
of the body: it never overflows. -/
private theorem translate_facing {config : WorldConfig} (body : BoxPosition config)
    (direction : Direction) :
    body.position.translate direction.delta.1 direction.delta.2 =
      some (body.facingPosition direction) := by
  unfold Position.translate
  rw [show body.position.x.val + direction.delta.1 = (body.facingPosition direction).x.val from rfl,
    show body.position.y.val + direction.delta.2 = (body.facingPosition direction).y.val from rfl,
    checked_val, checked_val]
  rfl

/-- The tile that an action reads does not depend on the stored energy. -/
private theorem admits_energy {config : WorldConfig} (world : World config) (energy : Energy)
    (action : Action) :
    ActionAdmits { world with body := { world.body with energy := energy } } action ↔
      ActionAdmits world action := by
  cases action <;> exact Iff.rfl

/-- Box admission accepts exactly a pair of coordinates that are both in the box. -/
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

/-- The tile ahead in the direction of a movement action is the facing position of the body, and
the move is refused exactly when that tile is in the box and the terrain refuses it. -/
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

/-- A move is refused exactly when the tile one offset ahead is in the box and the terrain refuses
it. -/
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

/-- A harvest is refused exactly when the terrain refuses the tile that the body faces. -/
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

/-- The tile that the body faces is the tile that `Faces` names. -/
private theorem reads_faces {config : WorldConfig} (world : World config) :
    Reads world world.body.facing.delta.1 world.body.facing.delta.2 ↔ Faces world := by
  unfold Faces
  cases world.body.facing <;> rfl

/-- An action that reads no tile is never refused. -/
private theorem idle_isOk {config : WorldConfig} (world : World config) (action : Action)
    (idle : action = .wait ∨ action = .craftAxe ∨ action = .craftBoat ∨ action = .eat) :
    (performAction world action).isOk = true := by
  rcases idle with rfl | rfl | rfl | rfl <;> unfold performAction <;>
    simp only [Action.direction] <;> (repeat' split) <;> rfl

/-- **A paid action's effect is refused exactly where the terrain refuses the tile that it
reads.** A movement action reads the tile one step ahead when that tile is in the box, a harvest
reads the tile that the body faces, and the other actions read no tile. -/
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

/-- The energy of the body pays the cost that the paid action computes exactly when it pays the
cost that `Cost` states. -/
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

/-- **A paid action is refused exactly when the energy pays its cost and the terrain refuses the
tile that the action reads.** An action that the energy does not pay for rests the body and is
accepted. -/
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
