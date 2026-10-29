/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.Hash
import Acorn.Rng

/-!
# Acorn's hash functions against their intent record

`acornHashes` reads Acorn's executing `Acorn.Rng.hash2` and `Acorn.Rng.hash3` as the record's
subject, each with its three inputs in the order it takes them. `acornHashes_oneInputMoves`
proves the record's first property of both: changing any one input moves the spot. Each step is a
bijection of the words (`Acorn.Rng.mix64_injective`, exclusive or with a fixed word, and the fixed
rotations `rotateLeft_injective`), so no 64-bit domain is enumerated.

The record's second property, that no fixed rule of reordering and shifting keeps every spot, is
not proved of these functions here. For a rule that shifts two or more inputs, it comes down to
`Acorn.Rng.mix64` having no fixed difference: for each nonzero word `d`, some word `u` with
`mix64 (u ^^^ d) ^^^ mix64 u` unlike its value at another word, and likewise for differences by
addition. SplitMix64's finalizer is a nonlinear bijection, so this is expected, but it is a
statement about all 2^64 differences that no proof in this repository yet establishes.
`acornHashes_reorder` proves the part that needs no such statement: no reordering of the inputs
alone keeps every spot.
-/

namespace AcornVerif.Intent.Hash

open Acorn

/-- Acorn's hash functions as the record's subject. -/
def acornHashes : Hashes :=
  ⟨fun x => Rng.hash2 x.1 x.2.1 x.2.2, fun x => Rng.hash3 x.1 x.2.1 x.2.2⟩

/-- A rotation by a count below the width is injective: bit `j` of the word is bit
`(j + r) % 64` of the rotated word. -/
theorem rotateLeft_injective {count : UInt64} {r : Nat} (hc : count.toNat % 64 = r)
    (hr : r < 64) (x y : UInt64) (h : Rng.rotateLeft x count = Rng.rotateLeft y count) :
    x = y := by
  have hb := congrArg UInt64.toBitVec h
  rw [Rng.rotateLeft_toBitVec, Rng.rotateLeft_toBitVec, hc] at hb
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hbit := congrArg (fun v : BitVec 64 => v.getLsbD ((j + r) % 64)) hb
  simp only [BitVec.getLsbD_rotateLeft_of_le hr] at hbit
  by_cases hjr : j + r < 64
  · rw [Nat.mod_eq_of_lt hjr] at hbit
    have h1 : ¬ (j + r < r) := by omega
    have h2 : j + r - r = j := by omega
    simp only [h1, ↓reduceIte, hjr, decide_true, Bool.true_and, h2] at hbit
    exact hbit
  · have hm : (j + r) % 64 = j + r - 64 := by omega
    rw [hm] at hbit
    have h1 : j + r - 64 < r := by omega
    have h2 : 64 - r + (j + r - 64) = j := by omega
    simp only [h1, ↓reduceIte, h2] at hbit
    exact hbit

/-- Exclusive or with a fixed word on the left is injective. -/
theorem xor_left_injective (mask left right : UInt64) (h : mask ^^^ left = mask ^^^ right) :
    left = right :=
  Word.xor_word_injective _ _ mask (by rw [UInt64.xor_comm left, UInt64.xor_comm right]; exact h)

/-- Changing any one input of either function, the others kept, moves the spot. -/
theorem acornHashes_oneInputMoves :
    OneInputMoves acornHashes.hash2 ∧ OneInputMoves acornHashes.hash3 := by
  refine ⟨⟨fun x x' y s h => ?_, fun x y y' s h => ?_, fun x y s s' h => ?_⟩,
    ⟨fun a a' b c h => ?_, fun a b b' c h => ?_, fun a b c c' h => ?_⟩⟩
  · exact xor_left_injective _ _ _ ((Rng.hash2_eq_iff x y s x' s).mp h)
  · have h' := Rng.mix64_injective _ _ (Rng.mix64_injective _ _ h)
    exact rotateLeft_injective (r := 32) (by decide) (by decide) _ _ (xor_left_injective _ _ _ h')
  · have h' := Word.xor_word_injective _ _ _ ((Rng.hash2_eq_iff x y s x s').mp h)
    exact Word.xor_word_injective _ _ _ (Rng.mix64_injective _ _ h')
  · have h' := Word.xor_word_injective _ _ _ ((Rng.hash3_eq_iff a b a' b c).mp h)
    exact Word.xor_word_injective _ _ _ (Rng.mix64_injective _ _ h')
  · exact xor_left_injective _ _ _ ((Rng.hash3_eq_iff a b a b' c).mp h)
  · have h' := Rng.mix64_injective _ _ h
    exact rotateLeft_injective (r := 17) (by decide) (by decide) _ _ (xor_left_injective _ _ _ h')

/-- No reordering of the inputs alone keeps every spot of either function: for each of the five
orders other than the given one, the inputs (1, 2, 3) land elsewhere. -/
theorem acornHashes_reorder (o : Order) (s : Shift) (ho : o ≠ .abc) :
    (∃ x, acornHashes.hash2 ((⟨o, s, (0, 0, 0)⟩ : Rule).apply x) ≠ acornHashes.hash2 x) ∧
      ∃ x, acornHashes.hash3 ((⟨o, s, (0, 0, 0)⟩ : Rule).apply x) ≠ acornHashes.hash3 x := by
  cases o <;> cases s <;> first
    | exact absurd rfl ho
    | exact ⟨⟨(1, 2, 3), by decide⟩, ⟨(1, 2, 3), by decide⟩⟩

end AcornVerif.Intent.Hash
