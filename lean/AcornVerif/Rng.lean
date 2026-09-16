/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# RNG range and distribution contracts

Arithmetic contracts for multiply-shift selection: the high 64 bits of `x·n`
for a 64-bit word `x`, that is `⌊x·n / 2^64⌋`. The proofs use integer arithmetic
and interval cardinalities.

Two contracts, both over the *shipped* map rather than an ideal-uniform
model of it, and both generalized over the word size `W` so nothing here
computes with `2^64`:

- `next_below_in_range`: the result is below `n`.
- `next_below_bin_card` and `next_below_bins_within_one`: bin `k` of the map
  has exactly `⌈(k+1)·W/n⌉ − ⌈k·W/n⌉` preimages in `[0, W)`, and so every
  bin has `⌊W/n⌋` or `⌊W/n⌋ + 1` of them. That is the exact finite bias of
  multiply-high without rejection: for `n = 3` at `W = 2^64`, bin 0 has
  `(2^64 + 2) / 3` preimages against `(2^64 − 1) / 3` for the others, not one
  third of the word. `next_below_word_bins_within_one` restates the bound at
  the shipped word. The runtime branches that select through this map —
  `SwiftSarsa::uniform` and the reservoir tie-break in `SwiftSarsa::greedy`,
  each `next_below` call with a count that need not divide `2^64` — are
  near-uniform in exactly this sense, and no more.
-/

namespace AcornVerif

/-- Lemire's method never returns a value `≥ n`: for every 64-bit word
`x` and every `n ≥ 1`, the high 64 bits of `x·n` are `< n`.
`(x * n) / 2^64` is exactly `Xoshiro256::next_below`'s computation. -/
theorem next_below_in_range (x n : ℕ) (hn : 0 < n) (hx : x < 2 ^ 64) :
    x * n / 2 ^ 64 < n := by
  have hpos64 : 0 < (2 : ℕ) ^ 64 := pow_pos (by norm_num : 0 < (2 : ℕ)) 64
  have hxle : x ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt hx
  have hmul : x * n ≤ (2 ^ 64 - 1) * n := Nat.mul_le_mul_right n hxle
  have hlt : (2 ^ 64 - 1) * n < 2 ^ 64 * n := by
    rw [Nat.sub_mul (2 ^ 64) 1 n]
    rw [one_mul]
    exact Nat.sub_lt (Nat.mul_pos hpos64 hn) hn
  have hdiv :
      (2 ^ 64 - 1) * n / 2 ^ 64 < n := by
    rw [Nat.div_lt_iff_lt_mul hpos64]
    calc
      (2 ^ 64 - 1) * n < 2 ^ 64 * n := hlt
      _ = n * 2 ^ 64 := by rw [mul_comm]
  calc
    x * n / 2 ^ 64 ≤ (2 ^ 64 - 1) * n / 2 ^ 64 := Nat.div_le_div_right hmul
    _ < n := hdiv

/-- `⌈a / n⌉` over `ℕ`, spelled as the integer division `(a + n − 1) / n`. -/
def natCeilDiv (a n : ℕ) : ℕ := (a + n - 1) / n

/-- The ceiling is the least integer whose multiple of `n` reaches `a`. -/
theorem natCeilDiv_le_iff {a n x : ℕ} (hn : 0 < n) :
    natCeilDiv a n ≤ x ↔ a ≤ x * n := by
  unfold natCeilDiv
  have key : (a + n - 1) / n < x + 1 ↔ a + n - 1 < (x + 1) * n :=
    Nat.div_lt_iff_lt_mul hn
  rw [Nat.add_mul, Nat.one_mul] at key
  constructor
  · intro h
    have := key.1 (Nat.lt_succ_of_le h)
    omega
  · intro h
    have := key.2 (by omega)
    omega

/-- Strictly below the ceiling exactly when the multiple stays below `a`. -/
theorem lt_natCeilDiv_iff {a n x : ℕ} (hn : 0 < n) :
    x < natCeilDiv a n ↔ x * n < a := by
  rw [← Nat.not_le, natCeilDiv_le_iff hn, Nat.not_le]

/-- Bin membership of the multiply-high map: `x` lands in bin `k` exactly
when `⌈k·W/n⌉ ≤ x < ⌈(k+1)·W/n⌉`. -/
theorem next_below_bin_iff {W n k x : ℕ} (hW : 0 < W) (hn : 0 < n) :
    x * n / W = k ↔ natCeilDiv (k * W) n ≤ x ∧ x < natCeilDiv ((k + 1) * W) n := by
  rw [natCeilDiv_le_iff hn, lt_natCeilDiv_iff hn]
  have lo : k ≤ x * n / W ↔ k * W ≤ x * n := Nat.le_div_iff_mul_le hW
  have hi : x * n / W < k + 1 ↔ x * n < (k + 1) * W := Nat.div_lt_iff_lt_mul hW
  constructor
  · rintro rfl
    exact ⟨lo.1 le_rfl, hi.1 (Nat.lt_succ_self _)⟩
  · rintro ⟨hlo, hhi⟩
    exact Nat.le_antisymm (Nat.lt_succ_iff.1 (hi.2 hhi)) (lo.2 hlo)

/-- The preimage of bin `k` under the multiply-high map, inside the word
`[0, W)`. -/
def binPreimage (W n k : ℕ) : Finset ℕ :=
  (Finset.range W).filter (fun x => x * n / W = k)

/-- For `k < n` the preimage of bin `k` is the interval
`[⌈k·W/n⌉, ⌈(k+1)·W/n⌉)`, which lies inside the word. -/
theorem next_below_bin_eq_Ico {W n k : ℕ} (hW : 0 < W) (hn : 0 < n) (hk : k < n) :
    binPreimage W n k =
      Finset.Ico (natCeilDiv (k * W) n) (natCeilDiv ((k + 1) * W) n) := by
  ext x
  simp only [binPreimage, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  rw [next_below_bin_iff hW hn]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, hlo, hhi⟩
    have hle : natCeilDiv ((k + 1) * W) n ≤ W := by
      rw [natCeilDiv_le_iff hn, Nat.mul_comm W n]
      exact Nat.mul_le_mul_right W hk
    exact Nat.lt_of_lt_of_le hhi hle

/-- **The exact preimage count.** For `k < n`, bin `k` of the multiply-high
map over word size `W` has exactly `⌈(k+1)·W/n⌉ − ⌈k·W/n⌉` preimages. -/
theorem next_below_bin_card {W n k : ℕ} (hW : 0 < W) (hn : 0 < n) (hk : k < n) :
    (binPreimage W n k).card = natCeilDiv ((k + 1) * W) n - natCeilDiv (k * W) n := by
  rw [next_below_bin_eq_Ico hW hn hk, Nat.card_Ico]

/-- Consecutive ceilings `⌈(a + W)/n⌉ − ⌈a/n⌉` are `⌊W/n⌋` or one more: write
`W = q·n + r` with `r < n`; the `q·n` shifts the ceiling by exactly `q`, and
the `r` shifts it by at most one. -/
theorem natCeilDiv_add_sub {a W n : ℕ} (hn : 0 < n) :
    W / n ≤ natCeilDiv (a + W) n - natCeilDiv a n ∧
      natCeilDiv (a + W) n - natCeilDiv a n ≤ W / n + 1 := by
  have hmod : W / n * n + W % n = W := Nat.div_add_mod' W n
  have hr : W % n < n := Nat.mod_lt _ hn
  -- Name the quotient and remainder, so the arithmetic below is over plain
  -- naturals rather than over a division by a variable.
  generalize hq : W / n = q at hmod ⊢
  generalize hrem : W % n = r at hmod hr ⊢
  have shift : natCeilDiv (a + W) n = natCeilDiv (a + r) n + q := by
    unfold natCeilDiv
    have split : a + W + n - 1 = (a + r + n - 1) + q * n := by omega
    rw [split, Nat.add_mul_div_right _ _ hn]
  have mono : natCeilDiv a n ≤ natCeilDiv (a + r) n :=
    Nat.div_le_div_right (by omega)
  have step : natCeilDiv (a + r) n ≤ natCeilDiv a n + 1 := by
    unfold natCeilDiv
    rw [Nat.div_le_iff_le_mul_add_pred hn]
    have := Nat.lt_mul_div_succ (a + n - 1) hn
    rw [Nat.mul_add, Nat.mul_one] at this ⊢
    omega
  omega

/-- **The shipped bound.** For `k < n`, every bin of the multiply-high map
over word size `W` has `⌊W/n⌋` or `⌊W/n⌋ + 1` preimages — the "bin counts
differ by at most one" that `Xoshiro256::next_below` documents, as a theorem
about the map it computes. -/
theorem next_below_bins_within_one {W n k : ℕ} (hW : 0 < W) (hn : 0 < n) (hk : k < n) :
    W / n ≤ (binPreimage W n k).card ∧ (binPreimage W n k).card ≤ W / n + 1 := by
  rw [next_below_bin_card hW hn hk, show (k + 1) * W = k * W + W by ring]
  exact natCeilDiv_add_sub hn

/-- The bound at the shipped word size, `W = 2^64` — an instance of the
general theorem, so no arithmetic over `2^64` is evaluated. -/
theorem next_below_word_bins_within_one {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    2 ^ 64 / n ≤ (binPreimage (2 ^ 64) n k).card ∧
      (binPreimage (2 ^ 64) n k).card ≤ 2 ^ 64 / n + 1 :=
  next_below_bins_within_one (by positivity) hn hk

end AcornVerif
