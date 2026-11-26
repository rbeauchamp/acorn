import Acorn.Rng
import Init.Data.Vector.Perm

namespace Acorn.Rng

def countOfNat (count : Nat) (positive : 0 < count) (fits : count < 2 ^ 64) : Word.Count :=
  ⟨count.toUInt64, by
    change 0 < count % (2 ^ 64)
    rwa [Nat.mod_eq_of_lt fits]⟩

theorem countOfNat_exact (count : Nat) (positive : 0 < count) (fits : count < 2 ^ 64) :
    (countOfNat count positive fits).word.toNat = count := Nat.mod_eq_of_lt fits

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

def Xoshiro256.shuffle {α : Type} {size : Nat} (stream : Xoshiro256)
    (items : Vector α size) (fits : size < 2 ^ 64) : Vector α size × Xoshiro256 :=
  shuffleLoop fits size items stream (Nat.le_refl size)

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
