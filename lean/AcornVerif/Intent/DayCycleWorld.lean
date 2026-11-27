import AcornVerif.Intent.DayCycle
import Acorn.Host.WorldDynamics
import Acorn.Host.WorldObservation

namespace AcornVerif.Intent.DayCycle

open Acorn Acorn.Host LeanIntent

def acornDay (config : WorldConfig) (base : World config) (phase : World config → Fin 8) :
    DayWorld (World config) Action UInt8 Nat where
  length := config.raw.dayLength.toNat
  night t := decide (4 ≤ (phase { base with time := t.toUInt64 }).val)
  cost t c a := a.energyCost (decide (4 ≤ (phase { c with time := t.toUInt64 }).val))
  sees t c := (phase { c with time := t.toUInt64 }).val.toUInt8

theorem payAndAct_spends {config : WorldConfig} (base world : World config) (action : Action) :
    payAndAct world action =
      match world.body.energy.spend
          ((acornDay config base World.dayPhase).cost world.time.toNat world action) with
      | none => .ok { ActionChange.unchanged world with
          body := { world.body with energy := world.body.energy.gain .rest }
          events := { exhausted := true } }
      | some energy => performAction { world with body := { world.body with energy := energy } }
          action := by
  simp only [acornDay, Nat.toUInt64_eq, UInt64.ofNat_toNat]
  rfl

theorem observe_day {config : WorldConfig} (base world : World config)
    (observation : Observation) (h : world.observe = .ok observation) :
    observation.day = (acornDay config base World.dayPhase).sees world.time.toNat world := by
  unfold World.observe at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · cases h
    simp [acornDay]

theorem dayPhase_clock {config : WorldConfig} (c base : World config) (time : UInt64) :
    World.dayPhase { c with time } = World.dayPhase { base with time } := rfl

theorem slot_of_dvd {length : Nat} (hwrap : 2 ^ 64 % length = 0) (t : Nat) :
    t.toUInt64.toNat % length = t % length := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_mod_of_dvd t (Nat.dvd_of_mod_eq_zero hwrap)

theorem dayPhase_val {config : WorldConfig} (w : World config) {m : Nat} (hm : 0 < m)
    (hL : config.raw.dayLength.toNat = 8 * m) :
    (World.dayPhase w).val =
      if w.time.toNat % (8 * m) < 4 * m then w.time.toNat % (8 * m) / m
      else 4 + (w.time.toNat % (8 * m) - 4 * m) / m := by
  have hs := Nat.mod_lt w.time.toNat (show 0 < 8 * m by omega)
  have he : max 1 (8 * m / 8) = m := by omega
  have hh : 8 * m / 2 = 4 * m := by omega
  unfold World.dayPhase
  dsimp only
  by_cases first :
      w.time.toNat % config.raw.dayLength.toNat < config.raw.dayLength.toNat / 2
  · rw [ite_eq_left first]
    show min _ _ = _
    simp only [hL, FeatureConstants.dayPhases, he, hh] at first ⊢
    rw [ite_eq_left first]
    have : w.time.toNat % (8 * m) / m < 4 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
    omega
  · rw [ite_eq_right first]
    show _ + min _ _ = _
    simp only [hL, FeatureConstants.dayPhases, he, hh] at first ⊢
    rw [ite_eq_right first]
    have : (w.time.toNat % (8 * m) - 4 * m) / m < 4 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
    omega

theorem half_shift {length : Nat} (hpos : 0 < length) (heven : length % 2 = 0) (t : Nat) :
    (t + length / 2) % length < length / 2 ↔ length / 2 ≤ t % length := by
  have hr := Nat.mod_lt t hpos
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show length / 2 < length by omega)]
  by_cases h : t % length < length / 2
  · rw [Nat.mod_eq_of_lt (show t % length + length / 2 < length by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (show length ≤ t % length + length / 2 by omega),
      Nat.mod_eq_of_lt (show t % length + length / 2 - length < length by omega)]
    omega

theorem quarter_of_phase {m : Nat} (hm : 0 < m) (t : Nat) :
    quarter (8 * m) (8 * m / 2) t =
      if t % (8 * m) < 4 * m then t % (8 * m) / m / 2 + 2 else (t % (8 * m) - 4 * m) / m / 2 := by
  have hs := Nat.mod_lt t (show 0 < 8 * m by omega)
  unfold quarter
  rw [show 8 * m / 2 = 4 * m by omega, Nat.add_mod,
    Nat.mod_eq_of_lt (show 4 * m < 8 * m by omega), Nat.div_div_eq_div_mul,
    Nat.div_div_eq_div_mul]
  rw [show 8 * m = m * 2 * 4 by omega] at hs ⊢
  split
  · next first =>
    rw [Nat.mod_eq_of_lt (show t % (m * 2 * 4) + 4 * m < m * 2 * 4 by omega),
      Nat.mul_div_mul_right _ _ (by decide : 0 < 4),
      show t % (m * 2 * 4) + 4 * m = t % (m * 2 * 4) + 2 * (m * 2) by omega,
      Nat.add_mul_div_right _ _ (by omega : 0 < m * 2)]
  · next second =>
    rw [Nat.mod_eq_sub_mod (show m * 2 * 4 ≤ t % (m * 2 * 4) + 4 * m by omega),
      Nat.mod_eq_of_lt (show t % (m * 2 * 4) + 4 * m - m * 2 * 4 < m * 2 * 4 by omega),
      Nat.mul_div_mul_right _ _ (by decide : 0 < 4),
      show t % (m * 2 * 4) + 4 * m - m * 2 * 4 = t % (m * 2 * 4) - 4 * m by omega]

def IsDayPhase {config : WorldConfig} (phase : World config → Fin 8) : Prop :=
  phase = World.dayPhase

theorem dayPhase_refines {config : WorldConfig} (base : World config) {m : Nat}
    (hL : config.raw.dayLength.toNat = 8 * m) (hwrap : 2 ^ 64 % (8 * m) = 0) :
    Refines (dayCycleFor (World config) Action UInt8 Nat) (acornDay config base) IsDayPhase := by
  intro phase hphase _
  subst hphase
  have hpos : 0 < 8 * m := hL ▸ config.positiveDay
  have hm : 0 < m := by omega
  have hnight : ∀ (c : World config) (t : Nat),
      4 ≤ (World.dayPhase { c with time := t.toUInt64 }).val ↔ 8 * m / 2 ≤ t % (8 * m) := by
    intro c t
    rw [World.dayPhase_night_iff]
    simp only [hL, slot_of_dvd hwrap]
  have hval : ∀ (c : World config) (t : Nat),
      (World.dayPhase { c with time := t.toUInt64 }).val =
        if t % (8 * m) < 4 * m then t % (8 * m) / m else 4 + (t % (8 * m) - 4 * m) / m := by
    intro c t
    rw [dayPhase_val _ hm hL]
    simp only [slot_of_dvd hwrap]
  have hbyte : ∀ (p q : Fin 8), p.val.toUInt8 = q.val.toUInt8 → p.val = q.val := by
    intro p q h
    have h' := congrArg UInt8.toNat h
    rw [Nat.toUInt8_eq, Nat.toUInt8_eq, UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at h'
    have := p.isLt
    have := q.isLt
    omega
  refine ((dayCycle_meets (w := acornDay config base World.dayPhase)).mpr ⟨⟨?_, ?_, 8 * m / 2,
    fun t => ?_⟩, fun c a t t' ht ht' => ?_, fun t t' c c' h => ?_, 8 * m / 2,
    fun t t' c c' h => ?_⟩).2
  · show 0 < config.raw.dayLength.toNat
    omega
  · show config.raw.dayLength.toNat % 2 = 0
    omega
  · show decide (4 ≤ _) = true ↔ NightHalf config.raw.dayLength.toNat _ t
    rw [decide_eq_true_iff, hnight, hL, NightHalf, half_shift hpos (by omega)]
  · have hn : 4 ≤ (World.dayPhase { base with time := t.toUInt64 }).val :=
      of_decide_eq_true ht
    have hd : ¬ 4 ≤ (World.dayPhase { base with time := t'.toUInt64 }).val :=
      of_decide_eq_false ht'
    show a.energyCost (decide (4 ≤ (World.dayPhase { c with time := t'.toUInt64 }).val)) <
      a.energyCost (decide (4 ≤ (World.dayPhase { c with time := t.toUInt64 }).val))
    rw [dayPhase_clock c base, dayPhase_clock c base, decide_eq_true hn, decide_eq_false hd]
    cases a <;> decide
  · have hp := hbyte _ _ h
    show decide (4 ≤ _) = decide (4 ≤ _)
    rw [← dayPhase_clock c base, ← dayPhase_clock c' base, hp]
  · have hp := hbyte _ _ h
    rw [hval, hval] at hp
    show quarter config.raw.dayLength.toNat _ t = quarter config.raw.dayLength.toNat _ t'
    rw [hL, quarter_of_phase hm, quarter_of_phase hm]
    have fa : t % (8 * m) < 4 * m → t % (8 * m) / m < 4 :=
      fun h => (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
    have fb : t' % (8 * m) < 4 * m → t' % (8 * m) / m < 4 :=
      fun h => (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
    by_cases h1 : t % (8 * m) < 4 * m <;> by_cases h2 : t' % (8 * m) < 4 * m <;>
      simp only [h1, h2, ↓reduceIte] at hp ⊢
    · omega
    · have := fa h1
      rw [hp] at this
      exact absurd this (Nat.not_lt.mpr (Nat.le_add_right 4 _))
    · have := fb h2
      rw [← hp] at this
      exact absurd this (Nat.not_lt.mpr (Nat.le_add_right 4 _))
    · omega

theorem acornDay_fulfils {config : WorldConfig} (base : World config) {m : Nat}
    (hL : config.raw.dayLength.toNat = 8 * m) (hwrap : 2 ^ 64 % (8 * m) = 0) :
    (dayCycleFor (World config) Action UInt8 Nat).Fulfilled
      (acornDay config base World.dayPhase) :=
  fulfils (dayPhase_refines base hL hwrap) rfl

theorem admissible_fulfils {config : WorldConfig} (hadm : config.raw.admissible = true)
    (base : World config) :
    (dayCycleFor (World config) Action UInt8 Nat).Fulfilled
      (acornDay config base World.dayPhase) := by
  obtain ⟨_, _, _, h8, hdvd, _⟩ := (RawWorldConfig.admissible_iff config.raw).mp hadm
  obtain ⟨m, hm⟩ := h8
  exact acornDay_fulfils base hm (hm ▸ Nat.mod_eq_zero_of_dvd hdvd)

theorem admissible_spec_fulfils {config : WorldConfig} (hspec : config.raw.Admissible)
    (base : World config) :
    (dayCycleFor (World config) Action UInt8 Nat).Fulfilled
      (acornDay config base World.dayPhase) :=
  admissible_fulfils ((RawWorldConfig.admissible_spec_iff config.raw).mpr hspec) base

theorem admitted_fulfils {raw : RawWorldConfig} {config : WorldConfig}
    (hadmit : WorldConfig.admit raw = .ok config) (base : World config) :
    (dayCycleFor (World config) Action UInt8 Nat).Fulfilled
      (acornDay config base World.dayPhase) :=
  admissible_fulfils (WorldConfig.admit_admissible raw config hadmit) base

theorem standard_fulfils {seed : UInt64} {side : Coordinate} {config : WorldConfig}
    (h : WorldConfig.standard seed side = .ok config) (base : World config) :
    (dayCycleFor (World config) Action UInt8 Nat).Fulfilled
      (acornDay config base World.dayPhase) := by
  have hL : config.raw.dayLength.toNat = 8 * 256 := by
    unfold WorldConfig.standard at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases h
        rfl
  exact acornDay_fulfils base hL (by decide)

theorem acornDay_odd_unfulfilled {config : WorldConfig} (base : World config)
    (phase : World config → Fin 8) (hodd : config.raw.dayLength.toNat % 2 = 1) :
    ¬ (dayCycleFor (World config) Action UInt8 Nat).Fulfilled (acornDay config base phase) :=
  fun h => by
    have := (dayCycle_meets.mp ⟨(fun _ hd => nomatch hd), h (fun _ hd => nomatch hd)⟩).1.2.1
    simp only [acornDay] at this
    omega

theorem acornDay_not_dvd_unfulfilled {config : WorldConfig} (base : World config)
    (phase : World config → Fin 8) (hwrap : ¬ config.raw.dayLength.toNat ∣ 2 ^ 64) :
    ¬ (dayCycleFor (World config) Action UInt8 Nat).Fulfilled (acornDay config base phase) := by
  intro h
  obtain ⟨⟨hpos, heven, s, hs⟩, -⟩ :=
    dayCycle_meets.mp ⟨(fun _ hd => nomatch hd), h (fun _ hd => nomatch hd)⟩
  simp only [acornDay, NightHalf] at hpos heven hs
  obtain ⟨L, hL⟩ : ∃ L, config.raw.dayLength.toNat = L := ⟨_, rfl⟩
  rw [hL] at hpos heven hs hwrap
  have hper : ∀ t : Nat,
      (t + 2 ^ 64).toUInt64 = t.toUInt64 := fun t => by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    simp [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have hshift : ∀ t : Nat,
      (t + s) % L < L / 2 ↔ (t + 2 ^ 64 + s) % L < L / 2 := fun t => by
    rw [← hs t, ← hs (t + 2 ^ 64), hper t]
  have hr_pos : 0 < 2 ^ 64 % L :=
    Nat.pos_of_ne_zero fun h0 => hwrap (Nat.dvd_of_mod_eq_zero h0)
  have hr_lt : 2 ^ 64 % L < L := Nat.mod_lt _ hpos
  have hzero : (L - s % L + s) % L = 0 := by
    have hs_lt : s % L < L := Nat.mod_lt s hpos
    have hs_le : s % L ≤ s := Nat.mod_le s L
    have h1 : L - s % L + s = L + (s - s % L) := by omega
    have h2 : s - s % L = L * (s / L) := by
      have := Nat.mod_add_div s L
      omega
    rw [h1, h2, Nat.add_mod, Nat.mod_self, Nat.mul_mod_right, Nat.zero_add, Nat.zero_mod]
  by_cases hhalf : 2 ^ 64 % L ≤ L / 2
  · have h1 := hshift (L - s % L + (L / 2 - 1))
    have ha : (L - s % L + (L / 2 - 1) + s) % L = L / 2 - 1 := by
      rw [show L - s % L + (L / 2 - 1) + s = (L - s % L + s) + (L / 2 - 1) by omega,
        Nat.add_mod, hzero, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    have hb : (L - s % L + (L / 2 - 1) + 2 ^ 64 + s) % L = L / 2 - 1 + 2 ^ 64 % L := by
      rw [show L - s % L + (L / 2 - 1) + 2 ^ 64 + s =
          (L - s % L + (L / 2 - 1) + s) + 2 ^ 64 by omega,
        Nat.add_mod, ha, Nat.mod_eq_of_lt (by omega)]
    rw [ha, hb] at h1
    omega
  · have h1 := hshift (L - s % L + L / 2)
    have ha : (L - s % L + L / 2 + s) % L = L / 2 := by
      rw [show L - s % L + L / 2 + s = (L - s % L + s) + L / 2 by omega,
        Nat.add_mod, hzero, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    have hb : (L - s % L + L / 2 + 2 ^ 64 + s) % L = L / 2 + 2 ^ 64 % L - L := by
      rw [show L - s % L + L / 2 + 2 ^ 64 + s = (L - s % L + L / 2 + s) + 2 ^ 64 by omega,
        Nat.add_mod, ha, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [ha, hb] at h1
    omega

theorem admit_refuses_non_eight_dvd {raw : RawWorldConfig}
    (hbad : ¬ (0 < raw.dayLength.toNat ∧ 8 ∣ raw.dayLength.toNat ∧ raw.dayLength.toNat ∣ 2 ^ 64)) :
    (WorldConfig.admit raw).isOk = false :=
  Bool.eq_false_iff.mpr fun h => hbad (WorldConfig.admit_isOk_dayLength h)

theorem admit_refuses_odd {raw : RawWorldConfig}
    (hodd : raw.dayLength.toNat % 2 = 1) : (WorldConfig.admit raw).isOk = false :=
  admit_refuses_non_eight_dvd fun ⟨_, h8, _⟩ => by omega

theorem admit_refuses_not_dvd {raw : RawWorldConfig}
    (hwrap : ¬ raw.dayLength.toNat ∣ 2 ^ 64) : (WorldConfig.admit raw).isOk = false :=
  admit_refuses_non_eight_dvd fun ⟨_, _, hdvd⟩ => hwrap hdvd

theorem admit_refuses_short {raw : RawWorldConfig}
    (hpos : 0 < raw.dayLength.toNat) (hshort : raw.dayLength.toNat < 8) :
    (WorldConfig.admit raw).isOk = false :=
  admit_refuses_non_eight_dvd fun ⟨_, ⟨m, hm⟩, _⟩ => by omega

section

variable {Ctx Act Obs E : Type}

def DayWorld.at (w : DayWorld Ctx Act Obs E) (c : Ctx) : DayWorld Unit Act Obs E where
  length := w.length
  night := w.night
  cost t _ a := w.cost t c a
  sees t _ := w.sees t c

theorem fulfilled_at [LT E] {w : DayWorld Ctx Act Obs E}
    (h : (dayCycleFor Ctx Act Obs E).Fulfilled w) (c : Ctx) :
    (dayCycleFor Unit Act Obs E).Fulfilled (w.at c) := fun _ => by
  obtain ⟨h1, h2, h3, ⟨start, h4⟩⟩ :=
    dayCycle_meets.mp ⟨(fun _ hd => nomatch hd), h (fun _ hd => nomatch hd)⟩
  exact ((dayCycle_meets (w := w.at c)).mpr ⟨h1, fun _ a t t' => h2 c a t t',
    fun t t' _ _ => h3 t t' c c, start, fun t t' _ _ => h4 t t' c c⟩).2

end

def standardSide : Coordinate := ⟨FeatureConstants.worldMinSide, by decide⟩

theorem standard_isOk : (WorldConfig.standard 0 standardSide).isOk = true := by decide

def standardConfig : WorldConfig :=
  match h : WorldConfig.standard 0 standardSide with
  | .ok config => config
  | .error _ => absurd (h ▸ standard_isOk) (by simp [Except.isOk, Except.toBool])

theorem standardConfig_ok : WorldConfig.standard 0 standardSide = .ok standardConfig := by
  unfold standardConfig
  split
  · next h => exact h
  · next h => exact absurd (h ▸ standard_isOk) (by simp [Except.isOk, Except.toBool])

theorem standard_dayLength {seed : UInt64} {side : Coordinate} {config : WorldConfig}
    (h : WorldConfig.standard seed side = .ok config) :
    config.raw.dayLength = FeatureConstants.worldDayLength.toUInt64 := by
  unfold WorldConfig.standard at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · cases h
      rfl

theorem dayPhase_of_dayLength {config config' : WorldConfig} (w : World config)
    (w' : World config') (hlen : config.raw.dayLength = config'.raw.dayLength) (time : UInt64) :
    (World.dayPhase { w with time }).val = (World.dayPhase { w' with time }).val := by
  simp only [World.dayPhase, hlen]

def acornStandardDay : DayWorld Unit Action UInt8 Nat :=
  (acornDay standardConfig (World.empty standardConfig) World.dayPhase).at
    (World.empty standardConfig)

theorem acornStandardDay_fulfils :
    (dayCycleFor Unit Action UInt8 Nat).Fulfilled acornStandardDay :=
  fulfilled_at (standard_fulfils standardConfig_ok _) _

theorem acornStandardDay_eq {seed : UInt64} {side : Coordinate} {config : WorldConfig}
    (h : WorldConfig.standard seed side = .ok config) (base c : World config) :
    acornStandardDay = (acornDay config base World.dayPhase).at c := by
  have hlen : standardConfig.raw.dayLength = config.raw.dayLength := by
    rw [standard_dayLength standardConfig_ok, standard_dayLength h]
  have hphase : ∀ (w : World config) (time : UInt64), (World.dayPhase { w with time }).val =
      (World.dayPhase { World.empty standardConfig with time }).val :=
    fun w time => (dayPhase_of_dayLength _ w hlen time).symm
  simp only [acornStandardDay, acornDay, DayWorld.at, hlen, hphase]

end AcornVerif.Intent.DayCycle
