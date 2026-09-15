/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Rng
import Init.Data.Vector.Perm

/-!
# Bounded descending shuffle

The current descending swap sequence consumes one multiply-high draw per
position above zero. The length must fit the native 64-bit slice domain;
zero and one length consume no draws. Indices carry proofs at the actual
Vector swap, and the vector's type preserves length for every element type.
The near-uniform range map is not an exact-uniform shuffle law.
-/

namespace Acorn.Rng

/-- An exact count formed from a positive natural already in word range. -/
def countOfNat (count : Nat) (positive : 0 < count) (fits : count < 2 ^ 64) : Word.Count :=
  ⟨count.toUInt64, by
    change 0 < count % (2 ^ 64)
    rwa [Nat.mod_eq_of_lt fits]⟩

/-- Admitted natural counts retain their exact value at the range boundary. -/
theorem countOfNat_exact (count : Nat) (positive : 0 < count) (fits : count < 2 ^ 64) :
    (countOfNat count positive fits).word.toNat = count := Nat.mod_eq_of_lt fits

/-- Descending swaps with one actual RNG transition for each remaining
position above zero. Every array access is proved against its own dimension. -/
def shuffleLoop {α : Type} {size : Nat} (fits : size < 2 ^ 64) :
    (remaining : Nat) → Vector α size → Xoshiro256 → remaining ≤ size →
      Vector α size × Xoshiro256
  | 0, items, stream, _ => (items, stream)
  | 1, items, stream, _ => (items, stream)
  | remaining + 2, items, stream, bounded =>
    let count := countOfNat (remaining + 2) (by omega) (Nat.lt_of_le_of_lt bounded fits)
    let (selected, next) := stream.nextBelow count
    let hi : remaining + 1 < size := by omega
    let hj : selected.val.toNat < size := by
      have hb := selected.property
      have hc := countOfNat_exact (remaining + 2) (by omega) (Nat.lt_of_le_of_lt bounded fits)
      change count.word.toNat = remaining + 2 at hc
      omega
    shuffleLoop fits (remaining + 1)
      (items.swap (remaining + 1) selected.val.toNat hi hj) next (by omega)

/-- Shuffle the complete admitted vector without changing its dimension. -/
def Xoshiro256.shuffle {α : Type} {size : Nat} (stream : Xoshiro256)
    (items : Vector α size) (fits : size < 2 ^ 64) : Vector α size × Xoshiro256 :=
  shuffleLoop fits size items stream (Nat.le_refl size)

/-- A shuffle consumes exactly `remaining - 1` draws; zero and singleton
vectors consume none. The statement quantifies over all states and elements. -/
theorem shuffleLoop_state {α : Type} {size : Nat} (fits : size < 2 ^ 64)
    (remaining : Nat) (items : Vector α size) (stream : Xoshiro256) (bounded : remaining ≤ size) :
    (shuffleLoop fits remaining items stream bounded).2 = advance (remaining - 1) stream := by
  induction remaining generalizing items stream with
  | zero => rfl
  | succ remaining ih =>
    cases remaining with
    | zero => rfl
    | succ remaining =>
      simp only [shuffleLoop]
      rw [ih]
      rfl

/-- Each executing swap preserves the complete multiset, for every vector
and RNG state. This is a permutation guarantee, not a distribution claim. -/
theorem shuffleLoop_permutation {α : Type} {size : Nat} (fits : size < 2 ^ 64)
    (remaining : Nat) (items : Vector α size) (stream : Xoshiro256) (bounded : remaining ≤ size) :
    Vector.Perm (shuffleLoop fits remaining items stream bounded).1 items := by
  induction remaining generalizing items stream with
  | zero => exact .rfl
  | succ remaining ih =>
    cases remaining with
    | zero => exact .rfl
    | succ remaining =>
      simp only [shuffleLoop]
      exact (ih _ _ _).trans (Vector.swap_perm _ _)

end Acorn.Rng
