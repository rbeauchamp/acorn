/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.DayCycleWorld
import AcornVerif.Intent.Hash
import Acorn.Rng

/-!
# The records refuse the definitions as they were before #154 and #155 were fixed

The pilot asks whether the intent records, written from the owner's world-level statements, would
have refused the definitions that #154 and #155 found defective. This module copies those
definitions, as they stood before #159 and #161 fixed them, and proves that each record refuses
them.

* `dayPhaseBefore_unfulfilled`: `World.dayPhase` before #159 put the last two slots of the first
  half of a 20-tick day in the night phases, so 12 of its 20 ticks were night; the day record's
  `halves` asks for half of them, so the record refuses it for every world of that configuration.
* `hashes_refuses_before` and `hash2Before_keeps`: `Rng.hash3` before #161 read its first two
  inputs only through their exclusive or, and `Rng.hash2` its first and last inputs, so flipping
  the same bits of both keeps every spot; the hash record's `noRuleKeepsSpots` refuses both.
-/

namespace AcornVerif.Intent.BeforeFixes

open Acorn Acorn.Host AcornVerif.Intent.DayCycle AcornVerif.Intent.Hash LeanIntent

/-- `World.dayPhase` as it was before #159: the first half is not clamped to its four phases. -/
def dayPhaseBefore {config : WorldConfig} (world : World config) : Fin FeatureConstants.dayPhases :=
  let slot := world.time.toNat % config.raw.dayLength.toNat
  let half := config.raw.dayLength.toNat / 2
  let eighth := max 1 (config.raw.dayLength.toNat / FeatureConstants.dayPhases)
  let phase := if slot < half then slot / eighth
    else FeatureConstants.dayPhases / 2 + (slot - half) / eighth
  ⟨min phase (FeatureConstants.dayPhases - 1), by change min phase 7 < 8; omega⟩

/-- In a day of 20 ticks, `dayPhaseBefore` puts tick `t` of the first day in the night exactly
from tick 8 on. -/
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

/-- The day record refuses `dayPhaseBefore` in every world whose day lasts 20 ticks: 12 of its 20
ticks are night, where the record asks for one unbroken half. -/
theorem dayPhaseBefore_unfulfilled {config : WorldConfig} (base : World config)
    (hL : config.raw.dayLength.toNat = 20) :
    ¬ (dayCycle (World config) Action UInt8 Nat).Fulfilled
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

/-- A configuration whose day lasts 20 ticks exists: `WorldConfig.admit` accepts it, so the
refusal above is about a world Acorn can build. -/
theorem twentyTickDay_admitted (raw : RawWorldConfig) (hside : 0 < raw.side.val)
    (hday : raw.dayLength = 20) : ∃ config, WorldConfig.admit raw = .ok config ∧
      config.raw.dayLength.toNat = 20 := by
  have hd : 0 < raw.dayLength.toNat := by rw [hday]; decide
  refine ⟨⟨raw, hside, hd⟩, ?_, by rw [hday]; decide⟩
  unfold WorldConfig.admit
  split
  · rfl
  · contradiction

/-- `Acorn.Rng.hash2` as it was before #161. -/
def hash2Before (x y seed : UInt64) : UInt64 :=
  let first := Acorn.Rng.mix64 ((seed ^^^ Acorn.Rng.increment) ^^^ x)
  Acorn.Rng.mix64 (Acorn.Rng.mix64 (first ^^^ Acorn.Rng.rotateLeft y 32))

/-- `Acorn.Rng.hash3` as it was before #161. -/
def hash3Before (a b c : UInt64) : UInt64 :=
  Acorn.Rng.mix64 (Acorn.Rng.mix64 ((a ^^^ Acorn.Rng.increment) ^^^ b) ^^^ Acorn.Rng.rotateLeft c 17)

/-- The pair before #161, read as the record's subject. -/
def hashesBefore : Hashes :=
  ⟨fun x => hash2Before x.1 x.2.1 x.2.2, fun x => hash3Before x.1 x.2.1 x.2.2⟩

/-- Flipping the same bits `k` of two words cancels between them. -/
theorem flip_cancel (a b k i : UInt64) : ((a ^^^ k) ^^^ i) ^^^ (b ^^^ k) = (a ^^^ i) ^^^ b :=
  calc ((a ^^^ k) ^^^ i) ^^^ (b ^^^ k) = (a ^^^ i) ^^^ (k ^^^ (b ^^^ k)) := by
        rw [UInt64.xor_assoc a k i, UInt64.xor_comm k i, ← UInt64.xor_assoc a i k,
          UInt64.xor_assoc (a ^^^ i) k (b ^^^ k)]
    _ = (a ^^^ i) ^^^ b := by
        rw [UInt64.xor_comm b k, ← UInt64.xor_assoc k k b, UInt64.xor_self, UInt64.zero_xor]

/-- Flipping the same bits of the first two inputs keeps every spot of `hash3` before #161. -/
theorem hash3Before_flip (a b c k : UInt64) :
    hash3Before (a ^^^ k) (b ^^^ k) (c ^^^ 0) = hash3Before a b c := by
  unfold hash3Before
  rw [UInt64.xor_zero, flip_cancel]

/-- Flipping the same bits of the first and last inputs keeps every spot of `hash2` before
#161. -/
theorem hash2Before_flip (x y s k : UInt64) :
    hash2Before (x ^^^ k) (y ^^^ 0) (s ^^^ k) = hash2Before x y s := by
  unfold hash2Before
  rw [UInt64.xor_zero, flip_cancel]

/-- The record refuses the pair as it was before #161: the rule that flips the lowest bit of
the first two inputs moves inputs and keeps every spot of `hash3`. -/
theorem hashes_refuses_before : ¬ hashes.Meets hashesBefore := fun h => by
  obtain ⟨-, ⟨-, h3⟩⟩ := hashes_meets.mp h
  obtain ⟨⟨a, b, c⟩, hx⟩ := h3 ⟨.abc, .flip, (1, 1, 0)⟩
    (fun h => absurd (congrArg (·.1) h.2) (by decide))
  exact hx (hash3Before_flip a b c 1)

/-- The same holds of `hash2` alone: flipping the lowest bit of its first and last inputs keeps
every spot. -/
theorem hash2Before_keeps : ¬ NoRuleKeepsSpots hashesBefore.hash2 := fun h => by
  obtain ⟨⟨x, y, s⟩, hx⟩ := h ⟨.abc, .flip, (1, 0, 1)⟩
    (fun h => absurd (congrArg (·.1) h.2) (by decide))
  exact hx (hash2Before_flip x y s 1)

end AcornVerif.Intent.BeforeFixes
