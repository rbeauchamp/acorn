import Acorn.Host.Observation
import Acorn.Conversion

namespace Acorn.Host

def Coordinate.checked (value : Int) : Option Coordinate :=
  if h : -(2 ^ 63) ≤ value ∧ value < 2 ^ 63 then some ⟨value, h⟩ else none

theorem Coordinate.checked_exact (value : Int) (position : Coordinate)
    (h : checked value = some position) : position.val = value := by
  unfold checked at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

theorem Coordinate.checked_none (value : Int) :
    checked value = none ↔ ¬ (-(2 ^ 63) ≤ value ∧ value < 2 ^ 63) := by
  simp [checked]

structure Position where
  x : Coordinate
  y : Coordinate
  deriving DecidableEq

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

structure RawWorldConfig where
  seed : UInt64
  side : Coordinate
  dayLength : UInt64
  regrow : UInt64
  foodInterval : UInt64
  foodCap : UInt32
  deerCap : UInt32
  baseScale : Binary32

inductive WorldConfigError where
  | sideTooSmall
  | sideTooLarge
  | nonpositiveSide
  | zeroDayLength
  | invalidDayLength
  | sideExceedsPatch
  | scaleOverflow
  deriving DecidableEq

structure WorldConfig where
  raw : RawWorldConfig
  positiveSide : 0 < raw.side.val
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

def RawWorldConfig.admitHi (raw : RawWorldConfig)
    (hmax : raw.side.val ≤ RawWorldConfig.maxSide) : Coordinate :=
  if raw.deerCap == 0 then
    ⟨raw.side.val + 4, by
      have := raw.side.property
      unfold RawWorldConfig.maxSide at hmax
      omega⟩
  else ⟨2 ^ 63 - 1, by decide⟩

def WorldConfig.admit (raw : RawWorldConfig) : Except WorldConfigError WorldConfig :=
  if hs : 0 < raw.side.val then
    if hm : raw.side.val ≤ RawWorldConfig.maxSide then
      if hd : 0 < raw.dayLength.toNat then
        if raw.dayLength.toNat % 8 == 0 && 2 ^ 64 % raw.dayLength.toNat == 0 then
          if scaleAdmitsRange raw.admitLo (raw.admitHi hm) raw.baseScale then
            .ok ⟨raw, hs, hd⟩
          else .error .scaleOverflow
        else .error .invalidDayLength
      else .error .zeroDayLength
    else .error .sideExceedsPatch
  else .error .nonpositiveSide

def RawWorldConfig.admissible (raw : RawWorldConfig) : Bool :=
  (WorldConfig.admit raw).isOk

def RawWorldConfig.Admissible (raw : RawWorldConfig) : Prop :=
  0 < raw.side.val ∧ raw.side.val ≤ 2 ^ 63 - 5 ∧
    0 < raw.dayLength.toNat ∧ 8 ∣ raw.dayLength.toNat ∧ raw.dayLength.toNat ∣ 2 ^ 64 ∧
    ∀ lo hi : Coordinate,
      lo.val = (if raw.deerCap = 0 then -5 else -(2 ^ 63)) →
      hi.val = (if raw.deerCap = 0 then raw.side.val + 4 else 2 ^ 63 - 1) →
      ScaleAdmitsRange lo hi raw.baseScale

theorem RawWorldConfig.admitLo_val (raw : RawWorldConfig) :
    raw.admitLo.val = if raw.deerCap = 0 then -5 else -(2 ^ 63) := by
  unfold RawWorldConfig.admitLo
  by_cases h : raw.deerCap = 0 <;> simp [h]

theorem RawWorldConfig.admitHi_val (raw : RawWorldConfig)
    (hmax : raw.side.val ≤ RawWorldConfig.maxSide) :
    (raw.admitHi hmax).val = if raw.deerCap = 0 then raw.side.val + 4 else 2 ^ 63 - 1 := by
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
      0 < raw.side.val ∧ ∃ (hmax : raw.side.val ≤ RawWorldConfig.maxSide),
        0 < raw.dayLength.toNat ∧ 8 ∣ raw.dayLength.toNat ∧ raw.dayLength.toNat ∣ 2 ^ 64 ∧
          scaleAdmitsRange raw.admitLo (raw.admitHi hmax) raw.baseScale = true := by
  unfold RawWorldConfig.admissible WorldConfig.admit
  by_cases hs : 0 < raw.side.val
  · by_cases hm : raw.side.val ≤ RawWorldConfig.maxSide
    · by_cases hd : 0 < raw.dayLength.toNat
      · by_cases hdiv :
            (raw.dayLength.toNat % 8 == 0 && 2 ^ 64 % raw.dayLength.toNat == 0) = true
        · by_cases hsc : scaleAdmitsRange raw.admitLo (raw.admitHi hm) raw.baseScale = true
          · rw [dite_eq_left hs, dite_eq_left hm, dite_eq_left hd, ite_eq_left hdiv,
              ite_eq_left hsc]
            simp only [Bool.and_eq_true, beq_iff_eq] at hdiv
            exact ⟨fun _ => ⟨hs, hm, hd, Nat.dvd_of_mod_eq_zero hdiv.1,
                Nat.dvd_of_mod_eq_zero hdiv.2, hsc⟩,
              fun _ => rfl⟩
          · rw [dite_eq_left hs, dite_eq_left hm, dite_eq_left hd, ite_eq_left hdiv,
              ite_eq_right hsc]
            exact ⟨fun h => Bool.noConfusion h, fun ⟨_, _, _, _, _, hsc'⟩ => False.elim (hsc hsc')⟩
        · rw [dite_eq_left hs, dite_eq_left hm, dite_eq_left hd, ite_eq_right hdiv]
          refine ⟨fun h => Bool.noConfusion h,
            fun ⟨_, _, _, h8, hdvd, _⟩ => False.elim (hdiv ?_)⟩
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨Nat.mod_eq_zero_of_dvd h8, Nat.mod_eq_zero_of_dvd hdvd⟩
      · rw [dite_eq_left hs, dite_eq_left hm, dite_eq_right hd]
        exact ⟨fun h => Bool.noConfusion h, fun ⟨_, _, hd', _⟩ => False.elim (hd hd')⟩
    · rw [dite_eq_left hs, dite_eq_right hm]
      exact ⟨fun h => Bool.noConfusion h, fun ⟨_, hm', _⟩ => False.elim (hm hm')⟩
  · rw [dite_eq_right hs]
    exact ⟨fun h => Bool.noConfusion h, fun ⟨hs', _⟩ => False.elim (hs hs')⟩

theorem RawWorldConfig.admissible_spec_iff (raw : RawWorldConfig) :
    raw.admissible = true ↔ raw.Admissible := by
  rw [RawWorldConfig.admissible_iff]
  unfold RawWorldConfig.Admissible
  have hmax : RawWorldConfig.maxSide = 2 ^ 63 - 5 := rfl
  have hlo_val : raw.admitLo.val = if raw.deerCap = 0 then -5 else -(2 ^ 63) :=
    RawWorldConfig.admitLo_val raw
  constructor
  · intro ⟨hpos, hmx, hday, h8, hdvd, hsc⟩
    have hmx' : raw.side.val ≤ 2 ^ 63 - 5 := by rw [← hmax]; exact hmx
    refine ⟨hpos, hmx', hday, h8, hdvd, ?_⟩
    intro lo hi hlo hhi
    have hhi_val := RawWorldConfig.admitHi_val raw hmx
    have hlo_eq : lo = raw.admitLo := Subtype.ext (hlo.trans hlo_val.symm)
    have hhi_eq : hi = raw.admitHi hmx := Subtype.ext (hhi.trans hhi_val.symm)
    rw [hlo_eq, hhi_eq]
    exact (scaleAdmitsRange_spec_iff _ _ _).mp hsc
  · intro ⟨hpos, hmx, hday, h8, hdvd, hforall⟩
    have hmx' : raw.side.val ≤ RawWorldConfig.maxSide := by rw [hmax]; exact hmx
    refine ⟨hpos, hmx', hday, h8, hdvd, ?_⟩
    have hhi_val := RawWorldConfig.admitHi_val raw hmx'
    exact (scaleAdmitsRange_spec_iff _ _ _).mpr
      (hforall raw.admitLo (raw.admitHi hmx') hlo_val hhi_val)

theorem WorldConfig.admit_isOk_iff (raw : RawWorldConfig) :
    (WorldConfig.admit raw).isOk = true ↔ raw.admissible = true :=
  Iff.rfl

private theorem WorldConfig.admit_raw (raw : RawWorldConfig) (config : WorldConfig)
    (h : WorldConfig.admit raw = .ok config) : config.raw = raw := by
  unfold WorldConfig.admit at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · cases h; rfl
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem WorldConfig.admit_admissible (raw : RawWorldConfig) (config : WorldConfig)
    (h : WorldConfig.admit raw = .ok config) : config.raw.admissible = true := by
  rw [WorldConfig.admit_raw raw config h, RawWorldConfig.admissible, h]
  rfl

theorem WorldConfig.admit_of_admissible (config : WorldConfig)
    (hadm : config.raw.admissible = true) : WorldConfig.admit config.raw = .ok config := by
  have hok : (WorldConfig.admit config.raw).isOk = true := hadm
  cases hres : WorldConfig.admit config.raw with
  | error e => rw [hres] at hok; cases hok
  | ok admitted =>
    have hraw := WorldConfig.admit_raw config.raw admitted hres
    cases config
    cases admitted
    simp only at hraw
    subst hraw
    rfl

theorem WorldConfig.admit_isOk_dayLength {raw : RawWorldConfig}
    (h : (WorldConfig.admit raw).isOk = true) :
    0 < raw.dayLength.toNat ∧
      8 ∣ raw.dayLength.toNat ∧ raw.dayLength.toNat ∣ 2 ^ 64 := by
  obtain ⟨_, _, hd, h8, hdvd, _⟩ :=
    (RawWorldConfig.admissible_iff raw).mp ((WorldConfig.admit_isOk_iff raw).mp h)
  exact ⟨hd, h8, hdvd⟩

theorem WorldConfig.admit_dayLength {raw : RawWorldConfig} {config : WorldConfig}
    (h : WorldConfig.admit raw = .ok config) :
    0 < config.raw.dayLength.toNat ∧
      8 ∣ config.raw.dayLength.toNat ∧ config.raw.dayLength.toNat ∣ 2 ^ 64 := by
  obtain ⟨_, _, hd, h8, hdvd, _⟩ :=
    (RawWorldConfig.admissible_iff config.raw).mp (WorldConfig.admit_admissible raw config h)
  exact ⟨hd, h8, hdvd⟩

def WorldConfig.side (config : WorldConfig) : Nat := config.raw.side.val.toNat

theorem WorldConfig.side_pos (config : WorldConfig) : 0 < config.side := by
  have := config.positiveSide
  simp only [side]
  omega

def WorldConfig.area (config : WorldConfig) : Nat := config.side * config.side

def RawWorldConfig.area (raw : RawWorldConfig) : Option Coordinate :=
  Coordinate.checked (raw.side.val * raw.side.val)

theorem RawWorldConfig.area_exact (raw : RawWorldConfig) (result : Coordinate)
    (h : raw.area = some result) : result.val = raw.side.val * raw.side.val :=
  Coordinate.checked_exact _ _ h

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

structure BoxPosition (config : WorldConfig) where
  x : Fin config.side
  y : Fin config.side
  deriving DecidableEq

def BoxPosition.position {config : WorldConfig} (position : BoxPosition config) : Position :=
  have hs := config.raw.side.property
  have hp := config.positiveSide
  ⟨⟨position.x.val, by have := position.x.isLt; dsimp [WorldConfig.side] at *; omega⟩,
    ⟨position.y.val, by have := position.y.isLt; dsimp [WorldConfig.side] at *; omega⟩⟩

def BoxPosition.checked (config : WorldConfig) (x y : Int) : Option (BoxPosition config) :=
  if hx : 0 ≤ x ∧ x < config.side then
    if hy : 0 ≤ y ∧ y < config.side then
      some ⟨⟨x.toNat, by omega⟩, ⟨y.toNat, by omega⟩⟩
    else none
  else none

theorem BoxPosition.checked_position {config : WorldConfig} (position : BoxPosition config) :
    checked config position.position.x.val position.position.y.val = some position := by
  cases position with
  | mk x y => simp [checked, BoxPosition.position, x.isLt, y.isLt]

def BoxPosition.center (config : WorldConfig) : BoxPosition config :=
  let middle : Fin config.side := ⟨config.side / 2, Nat.div_lt_self config.side_pos (by decide)⟩
  ⟨middle, middle⟩

end Acorn.Host
