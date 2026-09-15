/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Observation
import Acorn.Conversion

/-!
# World coordinate and configuration admission

Coordinates retain the complete signed 64-bit domain. Arithmetic is performed
exactly before admission, so overflowing movement is a refusal rather than a
wrapped position. The standard constructor keeps its supported side interval;
custom configuration has a separate boundary and retains raw noise words,
resource counts, regrowth intervals and the zero food-interval convention.
-/
namespace Acorn.Host

/-- Arithmetic cannot install a coordinate outside the signed machine domain. -/
def Coordinate.checked (value : Int) : Option Coordinate :=
  if h : -(2 ^ 63) ≤ value ∧ value < 2 ^ 63 then some ⟨value, h⟩ else none

/-- Successful coordinate admission preserves the exact input. -/
theorem Coordinate.checked_exact (value : Int) (position : Coordinate)
    (h : checked value = some position) : position.val = value := by
  unfold checked at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

/-- Coordinate rejection is exactly failure of signed representability. -/
theorem Coordinate.checked_none (value : Int) :
    checked value = none ↔ ¬ (-(2 ^ 63) ≤ value ∧ value < 2 ^ 63) := by
  simp [checked]

/-- Exact signed coordinates of one entity. -/
structure Position where
  /-- Horizontal coordinate. -/
  x : Coordinate
  /-- Vertical coordinate. -/
  y : Coordinate
  deriving DecidableEq, BEq

/-- Checked translation, atomic across both coordinates. -/
def Position.translate (position : Position) (dx dy : Int) : Option Position := do
  let x ← Coordinate.checked (position.x.val + dx)
  let y ← Coordinate.checked (position.y.val + dy)
  pure ⟨x, y⟩

/-- Public custom fields before configuration admission. -/
structure RawWorldConfig where
  /-- Seed of the environment stream and procedural terrain. -/
  seed : UInt64
  /-- Signed public side field. -/
  side : Coordinate
  /-- Day/night period; zero has no modulo interpretation. -/
  dayLength : UInt64
  /-- Harvest age required for tree regrowth. -/
  regrow : UInt64
  /-- Zero spawns only when the wrapping clock is zero. -/
  foodInterval : UInt64
  /-- Ground-food capacity. -/
  foodCap : UInt32
  /-- Number of initial deer placement draws. -/
  deerCap : UInt32
  /-- Raw binary32 noise scale, including exceptional words. -/
  baseScale : Binary32

/-- Configuration failures are explicit and precede world allocation. -/
inductive WorldConfigError where
  /-- The standard constructor requires at least 64 tiles per side. -/
  | sideTooSmall
  /-- The standard constructor's supported maximum is three billion. -/
  | sideTooLarge
  /-- A custom campaign box must have a positive side. -/
  | nonpositiveSide
  /-- Day-phase modulo requires a nonzero day length. -/
  | zeroDayLength
  deriving DecidableEq

/-- Immutable admitted configuration; custom fields cannot invalidate its geometry. -/
structure WorldConfig where
  /-- Original configuration words. -/
  raw : RawWorldConfig
  /-- The campaign box is inhabited. -/
  positiveSide : 0 < raw.side.val
  /-- The day-phase denominator is nonzero. -/
  positiveDay : 0 < raw.dayLength.toNat

/-- Custom admission seals only the geometry and denominator preconditions.
Terrain and entity arithmetic have their own per-operation refusal boundaries. -/
def WorldConfig.admit (raw : RawWorldConfig) : Except WorldConfigError WorldConfig :=
  if hs : 0 < raw.side.val then
    if hd : 0 < raw.dayLength.toNat then .ok ⟨raw, hs, hd⟩
    else .error .zeroDayLength
  else .error .nonpositiveSide

/-- Number of coordinates on one side of the campaign box. -/
def WorldConfig.side (config : WorldConfig) : Nat := config.raw.side.val.toNat

/-- Every admitted box has at least one position on each axis. -/
theorem WorldConfig.side_pos (config : WorldConfig) : 0 < config.side := by
  have := config.positiveSide
  simp only [side]
  omega

/-- Exact area is derived without a machine multiplication overflow. -/
def WorldConfig.area (config : WorldConfig) : Nat := config.side * config.side

/-- The raw public area API retains signed multiplication and explicitly refuses overflow. -/
def RawWorldConfig.area (raw : RawWorldConfig) : Option Coordinate :=
  Coordinate.checked (raw.side.val * raw.side.val)

/-- Successful public area multiplication never narrows or wraps its exact result. -/
theorem RawWorldConfig.area_exact (raw : RawWorldConfig) (result : Coordinate)
    (h : raw.area = some result) : result.val = raw.side.val * raw.side.val :=
  Coordinate.checked_exact _ _ h

/-- Standard configuration preserves the source's side admission and UInt32
deer-count narrowing; representability is not a feasibility promise. -/
def WorldConfig.standard (seed : UInt64) (side : Coordinate) : Except WorldConfigError WorldConfig :=
  if hs : side.val < FeatureConstants.worldMinSide then .error .sideTooSmall
  else if side.val > FeatureConstants.worldMaxSide then .error .sideTooLarge
  else .ok {
    raw := {
      seed := seed
      side := side
      dayLength := FeatureConstants.worldDayLength.toUInt64
      regrow := FeatureConstants.worldRegrow.toUInt64
      foodInterval := FeatureConstants.worldFoodInterval.toUInt64
      foodCap := FeatureConstants.worldFoodCap.toUInt32
      deerCap := (side.val.toNat * side.val.toNat / FeatureConstants.worldDeerArea).toUInt32
      baseScale := Binary32.ofUInt64 (max FeatureConstants.worldMinScale (side.val.toNat / FeatureConstants.worldScaleDivisor)).toUInt64 }
    positiveSide := by change 0 < side.val; change ¬ side.val < 64 at hs; omega
    positiveDay := by change 0 < (2048 : UInt64).toNat; decide }

/-- The standard constructor retains precisely its generated side interval on success. -/
theorem WorldConfig.standard_bounds (seed : UInt64) (side : Coordinate) (config : WorldConfig)
    (h : standard seed side = .ok config) :
    config.raw.side = side ∧ FeatureConstants.worldMinSide ≤ side.val ∧
      side.val ≤ FeatureConstants.worldMaxSide := by
  unfold standard at h
  split at h
  · contradiction
  · rename_i hlow
    split at h
    · contradiction
    · rename_i hhigh
      cases Except.ok.inj h
      exact ⟨rfl, by omega, by omega⟩

/-- A body or food position is always inside its receiving campaign box. -/
structure BoxPosition (config : WorldConfig) where
  /-- Horizontal in-box index. -/
  x : Fin config.side
  /-- Vertical in-box index. -/
  y : Fin config.side
  deriving DecidableEq, BEq

/-- Box indices embed exactly into signed coordinates. -/
def BoxPosition.position {config : WorldConfig} (position : BoxPosition config) : Position :=
  have hs := config.raw.side.property
  have hp := config.positiveSide
  ⟨⟨position.x.val, by have := position.x.isLt; dsimp [WorldConfig.side] at *; omega⟩,
    ⟨position.y.val, by have := position.y.isLt; dsimp [WorldConfig.side] at *; omega⟩⟩

/-- Box admission retains each exact candidate coordinate or refuses movement. -/
def BoxPosition.checked (config : WorldConfig) (x y : Int) : Option (BoxPosition config) :=
  if hx : 0 ≤ x ∧ x < config.side then
    if hy : 0 ≤ y ∧ y < config.side then
      some ⟨⟨x.toNat, by omega⟩, ⟨y.toNat, by omega⟩⟩
    else none
  else none

/-- Every point in the box is admitted, with no coordinate projection. -/
theorem BoxPosition.checked_position {config : WorldConfig} (position : BoxPosition config) :
    checked config position.position.x.val position.position.y.val = some position := by
  cases position with
  | mk x y => simp [checked, BoxPosition.position, x.isLt, y.isLt]

/-- The deterministic center is legal for every admitted side. -/
def BoxPosition.center (config : WorldConfig) : BoxPosition config :=
  let middle : Fin config.side := ⟨config.side / 2, Nat.div_lt_self config.side_pos (by decide)⟩
  ⟨middle, middle⟩

end Acorn.Host
