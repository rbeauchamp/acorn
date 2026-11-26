import AcornVerif.Intent.DayCycleWorld
import AcornVerif.Intent.Hash
import Acorn.Rng

namespace AcornVerif.Intent.BeforeFixes

open Acorn Acorn.Host AcornVerif.Intent.DayCycle AcornVerif.Intent.Hash LeanIntent

def dayPhaseBefore {config : WorldConfig} (world : World config) : Fin FeatureConstants.dayPhases :=
  let slot := world.time.toNat % config.raw.dayLength.toNat
  let half := config.raw.dayLength.toNat / 2
  let eighth := max 1 (config.raw.dayLength.toNat / FeatureConstants.dayPhases)
  let phase := if slot < half then slot / eighth
    else FeatureConstants.dayPhases / 2 + (slot - half) / eighth
  ⟨min phase (FeatureConstants.dayPhases - 1), by change min phase 7 < 8; omega⟩

theorem dayPhaseBefore_night {config : WorldConfig} (base : World config)
    (hL : config.raw.dayLength.toNat = 20) (t : Nat) (ht : t < 20) :
    (acornDay config base dayPhaseBefore).night t = true ↔ 8 ≤ t := by
  have hm : t % 2 ^ 64 = t := Nat.mod_eq_of_lt (by omega)
  have he : max 1 (20 / 8) = 2 := by decide
  have hh : (20 : Nat) / 2 = 10 := by decide
  have hp : (8 : Nat) / 2 = 4 := by decide
  have hl : (8 : Nat) - 1 = 7 := by decide
  simp only [acornDay, dayPhaseBefore, hL, decide_eq_true_iff, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', hm, FeatureConstants.dayPhases, he, hh, hp, hl]
  split <;> omega

theorem dayPhaseBefore_unfulfilled {config : WorldConfig} (base : World config)
    (hL : config.raw.dayLength.toNat = 20) :
    ¬ (dayCycleFor (World config) Action UInt8 Nat).Fulfilled
      (acornDay config base dayPhaseBefore) := by
  intro h
  obtain ⟨⟨-, -, s, hs⟩, -⟩ :=
    dayCycle_meets.mp ⟨(fun _ hd => nomatch hd), h (fun _ hd => nomatch hd)⟩
  have key : ∀ t, t < 20 → (8 ≤ t ↔ (t + s) % 20 < 10) := fun t ht => by
    rw [← dayPhaseBefore_night base hL t ht, hs t]
    show (t + s) % config.raw.dayLength.toNat < config.raw.dayLength.toNat / 2 ↔ _
    rw [hL]
  have k0 := key 0 (by decide)
  have k1 := key 1 (by decide)
  have k2 := key 2 (by decide)
  have k3 := key 3 (by decide)
  have k4 := key 4 (by decide)
  have k5 := key 5 (by decide)
  have k6 := key 6 (by decide)
  have k7 := key 7 (by decide)
  have k8 := key 8 (by decide)
  have k9 := key 9 (by decide)
  have k10 := key 10 (by decide)
  have k11 := key 11 (by decide)
  have k12 := key 12 (by decide)
  have k13 := key 13 (by decide)
  have k14 := key 14 (by decide)
  have k15 := key 15 (by decide)
  have k16 := key 16 (by decide)
  have k17 := key 17 (by decide)
  have k18 := key 18 (by decide)
  have k19 := key 19 (by decide)
  omega

theorem twentyTickDay_admitted :
    ∃ raw config, WorldConfig.admit raw = .ok config ∧
      config.raw.dayLength.toNat = 20 := by
  let raw : RawWorldConfig :=
    { seed := 0, side := ⟨1, by decide⟩, dayLength := 20, regrow := 0,
      foodInterval := 0, foodCap := 0, deerCap := 0, baseScale := ⟨0x3f800000⟩ }
  have hside : 0 < raw.side.val := by decide
  have hmax : raw.side.val ≤ RawWorldConfig.maxSide := by decide
  have hd : 0 < raw.dayLength.toNat := by decide
  have hsc : scaleAdmitsRange raw.admitLo (raw.admitHi hmax) raw.baseScale = true := by
    have hhi : raw.admitHi hmax = ⟨5, by decide⟩ :=
      Subtype.ext (by rw [raw.admitHi_val hmax]; decide)
    rw [hhi]
    decide
  refine ⟨raw, ⟨raw, hside, hd⟩, ?_, rfl⟩
  unfold WorldConfig.admit
  simp [hside, hmax, hd, hsc]

def hash2Before (x y seed : UInt64) : UInt64 :=
  let first := Acorn.Rng.mix64 ((seed ^^^ Acorn.Rng.increment) ^^^ x)
  Acorn.Rng.mix64 (Acorn.Rng.mix64 (first ^^^ Acorn.Rng.rotateLeft y 32))

def hash3Before (a b c : UInt64) : UInt64 :=
  Acorn.Rng.mix64 (Acorn.Rng.mix64 ((a ^^^ Acorn.Rng.increment) ^^^ b) ^^^ Acorn.Rng.rotateLeft c 17)

def hashesBefore : Hashes :=
  ⟨fun x => hash2Before x.1 x.2.1 x.2.2, fun x => hash3Before x.1 x.2.1 x.2.2⟩

theorem flip_cancel (a b k i : UInt64) : ((a ^^^ k) ^^^ i) ^^^ (b ^^^ k) = (a ^^^ i) ^^^ b :=
  calc ((a ^^^ k) ^^^ i) ^^^ (b ^^^ k) = (a ^^^ i) ^^^ (k ^^^ (b ^^^ k)) := by
        rw [UInt64.xor_assoc a k i, UInt64.xor_comm k i, ← UInt64.xor_assoc a i k,
          UInt64.xor_assoc (a ^^^ i) k (b ^^^ k)]
    _ = (a ^^^ i) ^^^ b := by
        rw [UInt64.xor_comm b k, ← UInt64.xor_assoc k k b, UInt64.xor_self, UInt64.zero_xor]

theorem hash3Before_flip (a b c k : UInt64) :
    hash3Before (a ^^^ k) (b ^^^ k) (c ^^^ 0) = hash3Before a b c := by
  unfold hash3Before
  rw [UInt64.xor_zero, flip_cancel]

theorem hash2Before_flip (x y s k : UInt64) :
    hash2Before (x ^^^ k) (y ^^^ 0) (s ^^^ k) = hash2Before x y s := by
  unfold hash2Before
  rw [UInt64.xor_zero, flip_cancel]

theorem hashes_refuses_before : ¬ hashes.Meets hashesBefore := fun h => by
  obtain ⟨-, ⟨-, h3⟩⟩ := hashes_meets.mp h
  obtain ⟨⟨a, b, c⟩, hx⟩ := h3 ⟨.abc, .flip, (1, 1, 0)⟩
    (fun h => absurd (congrArg (·.1) h.2) (by decide))
  exact hx (hash3Before_flip a b c 1)

theorem hash2Before_keeps : ¬ NoRuleKeepsSpots hashesBefore.hash2 := fun h => by
  obtain ⟨⟨x, y, s⟩, hx⟩ := h ⟨.abc, .flip, (1, 0, 1)⟩
    (fun h => absurd (congrArg (·.1) h.2) (by decide))
  exact hx (hash2Before_flip x y s 1)

end AcornVerif.Intent.BeforeFixes
