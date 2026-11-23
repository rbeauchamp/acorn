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
  deriving DecidableEq

/-- Checked translation, atomic across both coordinates. -/
def Position.translate (position : Position) (dx dy : Int) : Option Position := do
  let x ← Coordinate.checked (position.x.val + dx)
  let y ← Coordinate.checked (position.y.val + dy)
  pure ⟨x, y⟩

theorem coordinateIngress_exact (coordinate : Coordinate) :
    (Int64.ofInt coordinate.val).toInt = coordinate.val := by
  rw [Int64.toInt_ofInt, Int.bmod_eq_of_le coordinate.property.1 coordinate.property.2]

def coordinateFloatWord (value : Int64) : Binary32 :=
  let negative := value.toUInt64 ≥ (0x8000000000000000 : UInt64)
  let magnitude := Binary32.ofUInt64 (if negative then -value.toUInt64 else value.toUInt64)
  if negative then ⟨magnitude.bits ^^^ 0x80000000⟩ else magnitude

theorem coordinateFloatWord_eq (value : Int64) : coordinateFloatWord value =
    let magnitude := Binary32.ofUInt64 value.toInt.natAbs.toUInt64;
    if value.toInt < 0 then ⟨magnitude.bits ^^^ 0x80000000⟩ else magnitude := by
  have magnitude : (if value < 0 then -value.toUInt64 else value.toUInt64) =
      value.toInt.natAbs.toUInt64 := by
    apply UInt64.toNat.inj
    rw [Conversion.i64Magnitude_exact]
    have bound : value.toInt.natAbs < 2^64 := by
      rw [← Conversion.i64Magnitude_exact]
      exact UInt64.toNat_lt _
    exact (UInt64.toNat_ofNat_of_lt' bound).symm
  unfold coordinateFloatWord
  simp only [Conversion.i64Sign_eq]
  rw [magnitude]
  simp only [Int64.lt_iff_toInt_lt]
  rfl

def coordinateFloat (coordinate : Coordinate) : Binary32 :=
  coordinateFloatWord (Int64.ofInt coordinate.val)

theorem coordinateFloat_eq (coordinate : Coordinate) : coordinateFloat coordinate =
    let magnitude := Binary32.ofUInt64 coordinate.val.natAbs.toUInt64;
    if coordinate.val < 0 then ⟨magnitude.bits ^^^ 0x80000000⟩ else magnitude := by
  rw [coordinateFloat, coordinateFloatWord_eq, coordinateIngress_exact]

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
  | sideExceedsPatch
  | scaleOverflow
  deriving DecidableEq

/-- Immutable admitted configuration; custom fields cannot invalidate its geometry. -/
structure WorldConfig where
  /-- Original configuration words. -/
  raw : RawWorldConfig
  /-- The campaign box is inhabited. -/
  positiveSide : 0 < raw.side.val
  /-- The day-phase denominator is nonzero. -/
  positiveDay : 0 < raw.dayLength.toNat

def RawWorldConfig.maxSide : Int := 2 ^ 63 - 5

def isPastLast (quotient : Binary32) : Bool :=
  0x5f000000 ≤ quotient.bits.toNat && quotient.bits.toNat ≤ 0x7f800000

def octaveScale (scale : Binary32) : Nat → Binary32
  | 0 => scale
  | octave + 1 => octaveScale (scale.mul ⟨0x40000000⟩) octave

def scaleAdmitsOctave (lo hi : Coordinate) (scale : Binary32) : Bool :=
  !isPastLast ((coordinateFloat lo).div scale) &&
    !isPastLast ((coordinateFloat hi).div scale)

def scaleAdmitsRange (lo hi : Coordinate) (baseScale : Binary32) : Bool :=
  scaleAdmitsOctave lo hi (octaveScale baseScale 0) &&
    scaleAdmitsOctave lo hi (octaveScale baseScale 1) &&
    scaleAdmitsOctave lo hi (octaveScale baseScale 2) &&
    scaleAdmitsOctave lo hi (octaveScale baseScale 3)

def RawWorldConfig.admitLo (raw : RawWorldConfig) : Coordinate :=
  if raw.deerCap == 0 then ⟨-5, by decide⟩ else ⟨-(2 ^ 63), by decide⟩

def RawWorldConfig.admitHi (raw : RawWorldConfig) : Coordinate :=
  if raw.deerCap == 0 then
    if h : -(2 ^ 63) ≤ raw.side.val + 4 ∧ raw.side.val + 4 < 2 ^ 63 then ⟨raw.side.val + 4, h⟩
    else ⟨2 ^ 63 - 1, by decide⟩
  else ⟨2 ^ 63 - 1, by decide⟩

def RawWorldConfig.admissible (raw : RawWorldConfig) : Bool :=
  0 < raw.side.val && raw.side.val ≤ RawWorldConfig.maxSide && 0 < raw.dayLength.toNat &&
    scaleAdmitsRange raw.admitLo raw.admitHi raw.baseScale

def WorldConfig.admit (raw : RawWorldConfig) : Except WorldConfigError WorldConfig :=
  if hs : 0 < raw.side.val then
    if _hm : raw.side.val ≤ RawWorldConfig.maxSide then
      if hd : 0 < raw.dayLength.toNat then
        if _hsc : scaleAdmitsRange raw.admitLo raw.admitHi raw.baseScale then .ok ⟨raw, hs, hd⟩
        else .error .scaleOverflow
      else .error .zeroDayLength
    else .error .sideExceedsPatch
  else .error .nonpositiveSide

theorem RawWorldConfig.admitLo_val (raw : RawWorldConfig) :
    raw.admitLo.val = if raw.deerCap = 0 then -5 else -(2 ^ 63) := by
  unfold RawWorldConfig.admitLo
  by_cases h : raw.deerCap = 0 <;> simp [h]

theorem RawWorldConfig.admitHi_val (raw : RawWorldConfig) (hpos : 0 < raw.side.val)
    (hmax : raw.side.val ≤ RawWorldConfig.maxSide) :
    raw.admitHi.val = if raw.deerCap = 0 then raw.side.val + 4 else 2 ^ 63 - 1 := by
  unfold RawWorldConfig.admitHi RawWorldConfig.maxSide at *
  by_cases h : raw.deerCap = 0
  · simp [h]
    split
    · rfl
    · omega
  · simp [h]

theorem scaleAdmitsRange_iff (lo hi : Coordinate) (baseScale : Binary32) :
    scaleAdmitsRange lo hi baseScale = true ↔
      ∀ octave < 4,
        isPastLast ((coordinateFloat lo).div (octaveScale baseScale octave)) = false ∧
        isPastLast ((coordinateFloat hi).div (octaveScale baseScale octave)) = false := by
  unfold scaleAdmitsRange scaleAdmitsOctave
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · intro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ octave below
    rcases octave with _ | _ | _ | _ | _
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · omega
  · intro all
    exact ⟨⟨⟨all 0 (by decide), all 1 (by decide)⟩, all 2 (by decide)⟩, all 3 (by decide)⟩

theorem RawWorldConfig.admissible_iff (raw : RawWorldConfig) :
    raw.admissible = true ↔
      0 < raw.side.val ∧ raw.side.val ≤ RawWorldConfig.maxSide ∧ 0 < raw.dayLength.toNat ∧
        scaleAdmitsRange raw.admitLo raw.admitHi raw.baseScale = true := by
  unfold RawWorldConfig.admissible
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem WorldConfig.admit_isOk_iff (raw : RawWorldConfig) :
    (WorldConfig.admit raw).isOk = true ↔ raw.admissible = true := by
  unfold WorldConfig.admit RawWorldConfig.admissible
  by_cases hs : 0 < raw.side.val <;>
    by_cases hm : raw.side.val ≤ RawWorldConfig.maxSide <;>
    by_cases hd : 0 < raw.dayLength.toNat <;>
    by_cases hsc : scaleAdmitsRange raw.admitLo raw.admitHi raw.baseScale = true <;>
    simp [hs, hm, hd, hsc, Except.isOk, Except.toBool]

theorem WorldConfig.admit_admissible (raw : RawWorldConfig) (config : WorldConfig)
    (h : WorldConfig.admit raw = .ok config) : config.raw.admissible = true := by
  have ok : (WorldConfig.admit raw).isOk = true := by rw [h]; rfl
  have rawEq : config.raw = raw := by
    unfold WorldConfig.admit at h
    split at h
    · split at h
      · split at h
        · split at h
          · cases h; rfl
          · cases h
        · cases h
      · cases h
    · cases h
  rw [rawEq]
  exact (WorldConfig.admit_isOk_iff raw).mp ok

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
  deriving DecidableEq

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
