/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Regula.Contract
import AcornVerif.CurrentCheckpoint

/-!
# Decision contracts proved in the proof library

`Acorn.Decisions` registers the decisions of the executing library whose kinds follow from
Lean core alone. A contract here states a direction whose proof needs this library: the
legality of every stored lifetime total rests on the real-valued bounds of
`CurrentLifetime.stored_sum_legal`.

Regula counts only a contract of the function's own library toward a decision registration,
so the function below carries no registration. The ownership audit requires this contract by
name instead, with a statement that still refers to the executing definition.
-/

namespace AcornVerif.Decisions
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime

/-- An image whose overall reward total is a NaN word, with every other field zero. -/
def refusedLifetime : LifetimeWords :=
  ⟨(0, ⟨0x7ff8000000000000⟩), .replicate _ (0, ⟨0⟩), .replicate _ (0, ⟨0⟩),
    .replicate _ (0, ⟨0⟩), .replicate _ .zero, .replicate _ .zero, .replicate _ (0, ⟨0⟩),
    .replicate _ .initial, .replicate _ (0, 0, 0), .replicate _ (.replicate _ (0, 0, 0))⟩

/-- Lifetime admission accepts every word image of a durable lifetime record whose option
counters are valid with no active option (`CurrentCheckpoint.lifetime_roundtrip`), and it
refuses an image whose overall reward total is a NaN word.

**Not claimed:** that every accepted image is the word image of such a record. -/
theorem lifetime_admit : Regula.ExecutableContract admitLifetime
    (Regula.DecidesCompletely (·.isSome = true) (fun raw =>
      ∃ record : Durable demonLayout, OptionsValid record.options none ∧
        raw = lifetimeWords record)) :=
  ⟨{ complete := fun raw ⟨record, valid, written⟩ => by
       rw [written, CurrentCheckpoint.lifetime_roundtrip record valid]
       rfl
     refused := ⟨refusedLifetime, by
       have illegal : ¬LegalSum .reward 0 ⟨0x7ff8000000000000⟩ := by decide
       simp [admitLifetime, admitSum, SumCount.admit, refusedLifetime, illegal]⟩ }⟩

end AcornVerif.Decisions
