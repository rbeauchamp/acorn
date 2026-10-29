/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.DayCycle
import Acorn.Host.WorldDynamics
import Acorn.Host.WorldObservation

/-!
# Acorn's world against the day record

`acornDay` reads Acorn's world as the day record's subject, for one configuration and one way of
reading the day phase: tick `t` is the world whose clock reads `t`, wrapped to 64 bits as the
clock wraps; night is a phase of four or more, the condition under which `payAndAct` charges the
night multiplier; an action costs `Action.energyCost` at that night flag; and the agent sees the
day-phase byte. Two theorems tie the subject to the executing code: `payAndAct_spends` (the step
spends the subject's cost) and `observe_day` (a successful observation reports the subject's
sight).

`acornDay_fulfils` proves that `World.dayPhase` fulfils the record, through the refinement link,
for every day of `8 * m` ticks that divides 2^64, the standard day of 2048 ticks among them
(`standard_fulfils`). Two kinds of day length fall outside it:

* an odd length, which `WorldConfig.admit` accepts and the record rules out, since its halves
  cannot be equal (`acornDay_odd_unfulfilled`);
* a length that does not divide 2^64, for which the 64-bit clock's wrap, after 2^64 ticks, breaks
  one day; and a length of 2, 4 or 6 ticks, below eight, whose phases the proof does not cover.
-/

namespace AcornVerif.Intent.DayCycle

open Acorn Acorn.Host LeanIntent

/-- Acorn's world read as the record's subject, for the configuration `config`, the day-phase
reader `phase` and a world `base` that supplies the rest of the state where the record's night
reads no situation. -/
def acornDay (config : WorldConfig) (base : World config) (phase : World config → Fin 8) :
    DayWorld (World config) Action UInt8 Nat where
  length := config.raw.dayLength.toNat
  night t := decide (4 ≤ (phase { base with time := t.toUInt64 }).val)
  cost t c a := a.energyCost (decide (4 ≤ (phase { c with time := t.toUInt64 }).val))
  sees t c := (phase { c with time := t.toUInt64 }).val.toUInt8

/-- `payAndAct` spends the cost the subject gives the action at the world's own clock. -/
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

/-- A successful observation reports the day-phase byte the subject says the agent sees. -/
theorem observe_day {config : WorldConfig} (base world : World config)
    (observation : Observation) (h : world.observe = .ok observation) :
    observation.day = (acornDay config base World.dayPhase).sees world.time.toNat world := by
  unfold World.observe at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · cases h
    simp [acornDay]

/-- `World.dayPhase` reads only the clock of the world. -/
theorem dayPhase_clock {config : WorldConfig} (c base : World config) (time : UInt64) :
    World.dayPhase { c with time } = World.dayPhase { base with time } := rfl

/-- The clock reading of tick `t`, modulo a day whose length divides 2^64, is the tick's slot. -/
theorem slot_of_dvd {length : Nat} (hwrap : 2 ^ 64 % length = 0) (t : Nat) :
    t.toUInt64.toNat % length = t % length := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_mod_of_dvd t (Nat.dvd_of_mod_eq_zero hwrap)

/-- In a day of `8 * m` ticks, the phase of a slot in the first half is the eighths it has passed,
and in the second half four more than the eighths it has passed since the half. -/
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

/-- Shifting a day of even length by half of it exchanges its halves. -/
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

/-- In a day of `8 * m` ticks counted from its half, the quarter of a tick is a function of its
phase. -/
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

/-- The day phase is exactly `World.dayPhase`: the specification the implementation meets. -/
def IsDayPhase {config : WorldConfig} (phase : World config → Fin 8) : Prop :=
  phase = World.dayPhase

/-- `World.dayPhase` refines the day record, for every day of `8 * m` ticks dividing 2^64. -/
theorem dayPhase_refines {config : WorldConfig} (base : World config) {m : Nat}
    (hL : config.raw.dayLength.toNat = 8 * m) (hwrap : 2 ^ 64 % (8 * m) = 0) :
    Refines (dayCycle (World config) Action UInt8 Nat) (acornDay config base) IsDayPhase := by
  intro phase hphase _
  subst hphase
  have hpos : 0 < 8 * m := hL ▸ config.positiveDay
  have hm : 0 < m := by omega
  -- night is the second half of the day, slot by slot
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

/-- `World.dayPhase` fulfils the day record, for every day of `8 * m` ticks dividing 2^64. -/
theorem acornDay_fulfils {config : WorldConfig} (base : World config) {m : Nat}
    (hL : config.raw.dayLength.toNat = 8 * m) (hwrap : 2 ^ 64 % (8 * m) = 0) :
    (dayCycle (World config) Action UInt8 Nat).Fulfilled (acornDay config base World.dayPhase) :=
  fulfils (dayPhase_refines base hL hwrap) rfl

/-- The standard world, whose day lasts 2048 ticks, fulfils the day record. -/
theorem standard_fulfils {seed : UInt64} {side : Coordinate} {config : WorldConfig}
    (h : WorldConfig.standard seed side = .ok config) (base : World config) :
    (dayCycle (World config) Action UInt8 Nat).Fulfilled (acornDay config base World.dayPhase) := by
  have hL : config.raw.dayLength.toNat = 8 * 256 := by
    unfold WorldConfig.standard at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases h
        rfl
  exact acornDay_fulfils base hL (by decide)

/-- A day of an odd number of ticks, which `WorldConfig.admit` accepts, does not fulfil the record,
whatever the phase reader: its halves cannot be equal. -/
theorem acornDay_odd_unfulfilled {config : WorldConfig} (base : World config)
    (phase : World config → Fin 8) (hodd : config.raw.dayLength.toNat % 2 = 1) :
    ¬ (dayCycle (World config) Action UInt8 Nat).Fulfilled (acornDay config base phase) :=
  fun h => by
    have := (dayCycle_meets.mp ⟨(fun _ hd => nomatch hd), h (fun _ hd => nomatch hd)⟩).1.2.1
    simp only [acornDay] at this
    omega

end AcornVerif.Intent.DayCycle
