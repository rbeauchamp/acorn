/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Rng
import AcornVerif.Rng

/-!
# Current executable range selection

The executable multiply-high definition proves its full-product quotient in
`Acorn.Word`. These results connect that definition to the existing counting
theorems. Counting preimages establishes a distribution only under a uniform
source-word hypothesis. A deterministic xoshiro prefix does not supply that
hypothesis, nor independence between successive outputs.
-/

namespace AcornVerif

/-- Membership in a bin of the actual machine-word range map, for every word. -/
theorem current_range_bin (word : UInt64) (count : Acorn.Word.Count) (bin : ℕ) :
    (Acorn.Word.below word count).val.toNat = bin ↔
      natCeilDiv (bin * 2 ^ 64) count.word.toNat ≤ word.toNat ∧
      word.toNat < natCeilDiv ((bin + 1) * 2 ^ 64) count.word.toNat := by
  simp only [Acorn.Word.below]
  rw [Acorn.Word.multiplyHigh_exact]
  exact next_below_bin_iff (by positivity) count.positive

/-- Every bounded natural source word is represented without wrapping before
the compiled range operation. This is the bridge to the finite preimage set. -/
theorem current_range_word (word : ℕ) (h : word < 2 ^ 64) (count : Acorn.Word.Count) :
    (Acorn.Word.below word.toUInt64 count).val.toNat =
      word * count.word.toNat / 2 ^ 64 := by
  simp only [Acorn.Word.below]
  rw [Acorn.Word.multiplyHigh_exact]
  change (word % (2 ^ 64)) * count.word.toNat / 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt h]

/-- Exact preimage count for the current executable function. The finite set is
a mathematical specification, not an enumeration performed by the executable. -/
theorem current_range_card (count : Acorn.Word.Count) (bin : ℕ)
    (hbin : bin < count.word.toNat) :
    ((Finset.range (2 ^ 64)).filter (fun word =>
      (Acorn.Word.below word.toUInt64 count).val.toNat = bin)).card =
      natCeilDiv ((bin + 1) * 2 ^ 64) count.word.toNat -
        natCeilDiv (bin * 2 ^ 64) count.word.toNat := by
  have heq : (Finset.range (2 ^ 64)).filter (fun word =>
      (Acorn.Word.below word.toUInt64 count).val.toNat = bin) =
      binPreimage (2 ^ 64) count.word.toNat bin := by
    ext word
    simp only [Finset.mem_filter, Finset.mem_range, binPreimage]
    constructor
    · rintro ⟨hword, hresult⟩
      exact ⟨hword, (current_range_word word hword count) ▸ hresult⟩
    · rintro ⟨hword, hresult⟩
      exact ⟨hword, (current_range_word word hword count).symm ▸ hresult⟩
  rw [heq]
  exact next_below_bin_card (by positivity) count.positive hbin

end AcornVerif
