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

def QuotientPastLast (quotient : Binary32) : Prop :=
  quotient = ⟨0x7f800000⟩ ∨
    quotient.Finite ∧ ¬quotient.Negative ∧
      (2 ^ 63 - 1) * 2 ^ 1074 ≤ Conversion.magnitudeUnits32 quotient

private theorem exp190_helper (e f n c : Nat) (hn : 40 + n = 190 + c) (he : 190 ≤ e) :
    (2 ^ 63 - 1) * 2 ^ n ≤ (2 ^ 23 + f) * 2 ^ (e + c) := by
  have heq : e + c = (e - 150) + n := by omega
  rw [heq, Nat.pow_add]
  have h23 : 2 ^ 23 ≤ 2 ^ 23 + f := Nat.le_add_right _ _
  have hpow : 2 ^ 40 ≤ 2 ^ (e - 150) := Nat.pow_le_pow_right (by decide) (by omega)
  have hmul : 2 ^ 23 * 2 ^ 40 ≤ (2 ^ 23 + f) * 2 ^ (e - 150) := Nat.mul_le_mul h23 hpow
  have h63 : 2 ^ 63 - 1 ≤ (2 ^ 23 + f) * 2 ^ (e - 150) :=
    Nat.le_trans (by decide : 2 ^ 63 - 1 ≤ 2 ^ 23 * 2 ^ 40) hmul
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_right (2 ^ n) h63

private theorem exp0_helper (f n c : Nat) (hn : 23 + c ≤ n) (hf : f < 2 ^ 23) :
    f * 2 ^ c < (2 ^ 63 - 1) * 2 ^ n := by
  have hle : 2 ^ 23 * 2 ^ c ≤ 2 ^ n := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) hn
  have hlt1 : f * 2 ^ c < 2 ^ 23 * 2 ^ c :=
    Nat.mul_lt_mul_of_pos_right hf (Nat.two_pow_pos c)
  have hlt2 : 2 ^ n < (2 ^ 63 - 1) * 2 ^ n := by
    calc 2 ^ n = 1 * 2 ^ n := (Nat.one_mul _).symm
      _ < (2 ^ 63 - 1) * 2 ^ n :=
        Nat.mul_lt_mul_of_pos_right (by decide) (Nat.two_pow_pos n)
  exact Nat.lt_trans hlt1 (Nat.lt_of_le_of_lt hle hlt2)

private theorem exp189_helper (e f n c : Nat) (hn : 39 + n = 189 + c) (he : e ≤ 189)
    (hf : 2 ^ 23 + f ≤ 2 ^ 24 - 1) :
    (2 ^ 23 + f) * 2 ^ (e + c) < (2 ^ 63 - 1) * 2 ^ n := by
  have hpow : 2 ^ (e + c) ≤ 2 ^ (39 + n) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_add 2 39 n] at hpow
  have hmul : (2 ^ 23 + f) * 2 ^ (e + c) ≤ ((2 ^ 24 - 1) * 2 ^ 39) * 2 ^ n := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul hf hpow
  have hlt : ((2 ^ 24 - 1) * 2 ^ 39) * 2 ^ n < (2 ^ 63 - 1) * 2 ^ n :=
    Nat.mul_lt_mul_of_pos_right (by decide) (Nat.two_pow_pos n)
  exact Nat.lt_of_le_of_lt hmul hlt

theorem isPastLast_iff_units (q : Binary32) :
    isPastLast q = true ↔ QuotientPastLast q := by
  have hb := q.bits.toNat_lt
  have hmag : q.magnitude = q.bits.toNat % 2 ^ 31 := by
    unfold Binary32.magnitude
    rw [UInt32.toNat_and, show (0x7fffffff : UInt32).toNat = 2 ^ 31 - 1 by decide]
    exact Nat.and_two_pow_sub_one_eq_mod _ 31
  unfold QuotientPastLast
  constructor
  · intro hp
    unfold isPastLast at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    rcases hp with ⟨hlo, hhi⟩
    by_cases heq : q.bits.toNat = 0x7f800000
    · left
      cases q; congr 1; apply UInt32.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq; exact heq
    · right
      have hb_hi : q.bits.toNat < 2 ^ 31 := by omega
      have hnneg : ¬ q.Negative := by unfold Binary32.Negative; omega
      have hmag_eq : q.magnitude = q.bits.toNat := by
        rw [hmag]; exact Nat.mod_eq_of_lt hb_hi
      have hfin : q.Finite := by unfold Binary32.Finite; omega
      refine ⟨hfin, hnneg, ?_⟩
      have hexp : 190 ≤ q.magnitude / 2 ^ 23 := by omega
      unfold Conversion.magnitudeUnits32
      dsimp only
      rw [ite_eq_right (by omega : q.magnitude / 2 ^ 23 ≠ 0)]
      exact exp190_helper _ _ 1074 924 (by decide) hexp
  · intro h
    rcases h with rfl | ⟨hfin, hnneg, hunits⟩
    · decide
    · have hb_lo : q.bits.toNat < 2 ^ 31 := by unfold Binary32.Negative at hnneg; omega
      have hmag_eq : q.magnitude = q.bits.toNat := by
        rw [hmag]; exact Nat.mod_eq_of_lt hb_lo
      have hfin' : q.magnitude < 0x7f800000 := hfin
      have hpow_hi : 0x5f000000 ≤ q.bits.toNat := by
        apply Decidable.byContradiction
        intro hlt
        have hlt' : q.bits.toNat < 0x5f000000 := by omega
        have hexp_hi : q.magnitude / 2 ^ 23 ≤ 189 := by omega
        unfold Conversion.magnitudeUnits32 at hunits
        dsimp only at hunits
        by_cases h0 : q.magnitude / 2 ^ 23 = 0
        · rw [ite_eq_left h0] at hunits
          have hf : q.magnitude % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
          exact absurd (Nat.lt_of_le_of_lt hunits (exp0_helper _ 1074 925 (by decide) hf))
            (Nat.lt_irrefl _)
        · rw [ite_eq_right h0] at hunits
          have hfrac : 2 ^ 23 + q.magnitude % 2 ^ 23 ≤ 2 ^ 24 - 1 := by
            have := Nat.mod_lt q.magnitude (by decide : 0 < 2 ^ 23)
            have h24 : (2 ^ 24 : Nat) = 2 * 2 ^ 23 := by decide
            omega
          exact absurd
            (Nat.lt_of_le_of_lt hunits
              (exp189_helper _ _ 1074 924 (by decide) hexp_hi hfrac))
            (Nat.lt_irrefl _)
      unfold isPastLast
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hpow_hi, by omega⟩

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

def ScaleAdmitsRange (lo hi : Coordinate) (baseScale : Binary32) : Prop :=
  ∀ s0 s1 s2 s3 : Binary32,
    s0 = baseScale →
    s1 = s0.mul ⟨0x40000000⟩ →
    s2 = s1.mul ⟨0x40000000⟩ →
    s3 = s2.mul ⟨0x40000000⟩ →
    ∀ s ∈ [s0, s1, s2, s3],
      ¬QuotientPastLast ((coordinateFloat lo).div s) ∧
        ¬QuotientPastLast ((coordinateFloat hi).div s)

def RawWorldConfig.admitLo (raw : RawWorldConfig) : Coordinate :=
  if raw.deerCap == 0 then ⟨-5, by decide⟩ else ⟨-(2 ^ 63), by decide⟩

def RawWorldConfig.admitHi (raw : RawWorldConfig) (_hpos : 0 < raw.side.val)
    (hmax : raw.side.val ≤ RawWorldConfig.maxSide) : Coordinate :=
  if raw.deerCap == 0 then
    ⟨raw.side.val + 4, by unfold RawWorldConfig.maxSide at hmax; omega⟩
  else ⟨2 ^ 63 - 1, by decide⟩

def RawWorldConfig.admissible (raw : RawWorldConfig) : Bool :=
  if hpos : 0 < raw.side.val then
    if hmax : raw.side.val ≤ RawWorldConfig.maxSide then
      0 < raw.dayLength.toNat &&
        scaleAdmitsRange raw.admitLo (raw.admitHi hpos hmax) raw.baseScale
    else false
  else false

def RawWorldConfig.Admissible (raw : RawWorldConfig) : Prop :=
  0 < raw.side.val ∧ raw.side.val ≤ 2 ^ 63 - 5 ∧ 0 < raw.dayLength.toNat ∧
    ∀ lo hi : Coordinate,
      lo.val = (if raw.deerCap = 0 then -5 else -(2 ^ 63)) →
      hi.val = (if raw.deerCap = 0 then raw.side.val + 4 else 2 ^ 63 - 1) →
      ScaleAdmitsRange lo hi raw.baseScale

def WorldConfig.admit (raw : RawWorldConfig) : Except WorldConfigError WorldConfig :=
  if hs : 0 < raw.side.val then
    if hm : raw.side.val ≤ RawWorldConfig.maxSide then
      if hd : 0 < raw.dayLength.toNat then
        if _hsc : scaleAdmitsRange raw.admitLo (raw.admitHi hs hm) raw.baseScale then
          .ok ⟨raw, hs, hd⟩
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
    (raw.admitHi hpos hmax).val = if raw.deerCap = 0 then raw.side.val + 4 else 2 ^ 63 - 1 := by
  unfold RawWorldConfig.admitHi
  by_cases h : raw.deerCap = 0 <;> simp [h]

theorem scaleAdmitsOctave_spec_iff (lo hi : Coordinate) (scale : Binary32) :
    scaleAdmitsOctave lo hi scale = true ↔
      ¬QuotientPastLast ((coordinateFloat lo).div scale) ∧
        ¬QuotientPastLast ((coordinateFloat hi).div scale) := by
  unfold scaleAdmitsOctave
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, isPastLast_iff_units]

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

theorem scaleAdmitsRange_spec_iff (lo hi : Coordinate) (baseScale : Binary32) :
    scaleAdmitsRange lo hi baseScale = true ↔ ScaleAdmitsRange lo hi baseScale := by
  rw [scaleAdmitsRange_iff]
  unfold ScaleAdmitsRange
  constructor
  · intro hsc s0 s1 s2 s3 hs0 hs1 hs2 hs3 s hmem
    have hnot : ∀ octave < 4,
        ¬QuotientPastLast ((coordinateFloat lo).div (octaveScale baseScale octave)) ∧
        ¬QuotientPastLast ((coordinateFloat hi).div (octaveScale baseScale octave)) := by
      intro octave hlt
      obtain ⟨hl, hr⟩ := hsc octave hlt
      exact ⟨fun hp => Bool.noConfusion (hl.symm.trans ((isPastLast_iff_units _).mpr hp)),
        fun hp => Bool.noConfusion (hr.symm.trans ((isPastLast_iff_units _).mpr hp))⟩
    have h0 := hnot 0 (by decide)
    have h1 := hnot 1 (by decide)
    have h2 := hnot 2 (by decide)
    have h3 := hnot 3 (by decide)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · simpa [hs0, octaveScale] using h0
    · simpa [hs1, hs0, octaveScale] using h1
    · simpa [hs2, hs1, hs0, octaveScale] using h2
    · simpa [hs3, hs2, hs1, hs0, octaveScale] using h3
  · intro hforall octave hlt
    have hspec := hforall
      (octaveScale baseScale 0)
      (octaveScale baseScale 1)
      (octaveScale baseScale 2)
      (octaveScale baseScale 3)
      rfl rfl rfl rfl
    have hmem : octaveScale baseScale octave ∈
        [octaveScale baseScale 0, octaveScale baseScale 1,
          octaveScale baseScale 2, octaveScale baseScale 3] := by
      match octave, hlt with
      | 0, _ => simp
      | 1, _ => simp
      | 2, _ => simp
      | 3, _ => simp
    obtain ⟨hl, hr⟩ := hspec _ hmem
    constructor
    · cases h : isPastLast ((coordinateFloat lo).div (octaveScale baseScale octave))
      · rfl
      · exact absurd ((isPastLast_iff_units _).mp h) hl
    · cases h : isPastLast ((coordinateFloat hi).div (octaveScale baseScale octave))
      · rfl
      · exact absurd ((isPastLast_iff_units _).mp h) hr

theorem RawWorldConfig.admissible_iff (raw : RawWorldConfig) :
    raw.admissible = true ↔
      ∃ (hpos : 0 < raw.side.val) (hmax : raw.side.val ≤ RawWorldConfig.maxSide),
        0 < raw.dayLength.toNat ∧
          scaleAdmitsRange raw.admitLo (raw.admitHi hpos hmax) raw.baseScale = true := by
  unfold RawWorldConfig.admissible
  by_cases hpos : 0 < raw.side.val <;> by_cases hmax : raw.side.val ≤ RawWorldConfig.maxSide <;>
    simp [hpos, hmax, Bool.and_eq_true, decide_eq_true_eq]

theorem RawWorldConfig.admissible_spec_iff (raw : RawWorldConfig) :
    raw.admissible = true ↔ raw.Admissible := by
  rw [RawWorldConfig.admissible_iff]
  unfold RawWorldConfig.Admissible
  have hmax : RawWorldConfig.maxSide = 2 ^ 63 - 5 := rfl
  have hlo_val : raw.admitLo.val = if raw.deerCap = 0 then -5 else -(2 ^ 63) :=
    RawWorldConfig.admitLo_val raw
  constructor
  · intro ⟨hpos, hmx, hday, hsc⟩
    have hmx' : raw.side.val ≤ 2 ^ 63 - 5 := by rw [← hmax]; exact hmx
    refine ⟨hpos, hmx', hday, ?_⟩
    intro lo hi hlo hhi
    have hhi_val := RawWorldConfig.admitHi_val raw hpos hmx
    have hlo_eq : lo = raw.admitLo := Subtype.ext (hlo.trans hlo_val.symm)
    have hhi_eq : hi = raw.admitHi hpos hmx := Subtype.ext (hhi.trans hhi_val.symm)
    rw [hlo_eq, hhi_eq]
    exact (scaleAdmitsRange_spec_iff _ _ _).mp hsc
  · intro ⟨hpos, hmx, hday, hforall⟩
    have hmx' : raw.side.val ≤ RawWorldConfig.maxSide := by rw [hmax]; exact hmx
    refine ⟨hpos, hmx', hday, ?_⟩
    have hhi_val := RawWorldConfig.admitHi_val raw hpos hmx'
    exact (scaleAdmitsRange_spec_iff _ _ _).mpr
      (hforall raw.admitLo (raw.admitHi hpos hmx') hlo_val hhi_val)

theorem WorldConfig.admit_isOk_iff (raw : RawWorldConfig) :
    (WorldConfig.admit raw).isOk = true ↔ raw.admissible = true := by
  unfold WorldConfig.admit RawWorldConfig.admissible
  by_cases hs : 0 < raw.side.val
  · by_cases hm : raw.side.val ≤ RawWorldConfig.maxSide
    · by_cases hd : 0 < raw.dayLength.toNat
      · by_cases hsc : scaleAdmitsRange raw.admitLo (raw.admitHi hs hm) raw.baseScale = true <;>
          simp [hs, hm, hd, hsc, Except.isOk, Except.toBool]
      · simp [hs, hm, hd, Except.isOk, Except.toBool]
    · simp [hs, hm, Except.isOk, Except.toBool]
  · simp [hs, Except.isOk, Except.toBool]

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
