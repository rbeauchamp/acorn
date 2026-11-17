/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Targets.ColumnLatch
import AcornVerif.Targets.Json
import AcornVerif.Targets.StateEntry

/-! # The registry of targets

A *target* is an open statement held as a definition of type `Prop` in a module of this directory,
`lean/AcornVerif/Targets/`. The build elaborates every target against the current definitions, and
`.github/CODEOWNERS` gives this directory to the repository's owner, so a target changes only at
the owner's hand. A mission that has targets is finished by proving each of them.

`registry` lists every target with the issue number of its mission. Each entry repeats one
identifier, as in `⟨200, ``StateEntry.arm_letter, StateEntry.arm_letter⟩`: Lean resolves the
doubled backquote to the name of a declaration, and the last field is that declaration, which
Lean requires to be a proposition. A target's name is its module's name followed by the name its
contract gave the theorem, so `AcornVerif.Targets.StateEntry.arm_letter` is in
`lean/AcornVerif/Targets/StateEntry.lean`.

`Landing` is the record that a target is proved: the target's name, the name of the theorem that
proves it, and a proof of `statementOf` that name, which Lean's kernel checks. The record itself,
`AcornVerif.landings`, is outside this directory, so that a mission's pull request adds to it and
changes nothing here.

What the proofs below establish: the statement registered under each target's name is that
target's statement (`statementOf_name`), so no entry hides another, and a proof of what is
registered under any name is a proof of a registered target's statement (`statementOf_registered`,
`Landing.proves`).

What they do not establish: that an entry's name and its statement are one declaration, since no
theorem relates a name to the declaration it names; the entry's form above and the owner's review
of this directory keep that. Nor that a target states what its mission means: review reads each
statement.
-/

namespace AcornVerif.Targets

/-- One open statement on record. -/
structure Target where
  /-- The issue number of the mission the statement belongs to. -/
  mission : Nat
  /-- The name of the definition of type `Prop` that holds the statement. -/
  name : Lean.Name
  /-- The statement. -/
  statement : Prop

/-- Every target, each with its mission, in the order of the contracts. -/
def registry : List Target := [
  ⟨163, ``Json.parse_complete, Json.parse_complete⟩,
  ⟨200, ``StateEntry.arm_letter, StateEntry.arm_letter⟩,
  ⟨200, ``StateEntry.fold_arm, StateEntry.fold_arm⟩,
  ⟨200, ``StateEntry.near_threshold, StateEntry.near_threshold⟩,
  ⟨200, ``StateEntry.clear_threshold, StateEntry.clear_threshold⟩,
  ⟨200, ``StateEntry.latches_mono, StateEntry.latches_mono⟩,
  ⟨200, ``StateEntry.memoryless_refused, StateEntry.memoryless_refused⟩,
  ⟨200, ``StateEntry.frozen_refused, StateEntry.frozen_refused⟩,
  ⟨200, ``StateEntry.fading_margin, StateEntry.fading_margin⟩,
  ⟨200, ``StateEntry.fading_no_uniform, StateEntry.fading_no_uniform⟩,
  ⟨200, ``StateEntry.additive_margin, StateEntry.additive_margin⟩,
  ⟨200, ``StateEntry.rows_accept, StateEntry.rows_accept⟩,
  ⟨200, ``StateEntry.rows_clamped, StateEntry.rows_clamped⟩,
  ⟨200, ``StateEntry.linearTrace_additive, StateEntry.linearTrace_additive⟩,
  ⟨200, ``StateEntry.linearTrace_margin, StateEntry.linearTrace_margin⟩,
  ⟨200, ``StateEntry.linearTrace_refused, StateEntry.linearTrace_refused⟩,
  ⟨200, ``StateEntry.column_accepts, StateEntry.column_accepts⟩,
  ⟨200, ``StateEntry.tracks_decide, StateEntry.tracks_decide⟩,
  ⟨200, ``StateEntry.column_tracks, StateEntry.column_tracks⟩,
  ⟨200, ``StateEntry.bucket_refuses, StateEntry.bucket_refuses⟩,
  ⟨200, ``StateEntry.level_carries, StateEntry.level_carries⟩,
  ⟨200, ``StateEntry.two_values_levels, StateEntry.two_values_levels⟩,
  ⟨200, ``StateEntry.values_bellman, StateEntry.values_bellman⟩,
  ⟨200, ``StateEntry.values_first_bucket, StateEntry.values_first_bucket⟩,
  ⟨201, ``ColumnLatch.cell_accepts, ColumnLatch.cell_accepts⟩,
  ⟨201, ``ColumnLatch.cell_bands, ColumnLatch.cell_bands⟩,
  ⟨201, ``ColumnLatch.read_lipschitz, ColumnLatch.read_lipschitz⟩,
  ⟨201, ``ColumnLatch.threshold_trap, ColumnLatch.threshold_trap⟩,
  ⟨201, ``ColumnLatch.front_accepts, ColumnLatch.front_accepts⟩,
  ⟨201, ``ColumnLatch.tied_bounded, ColumnLatch.tied_bounded⟩,
  ⟨201, ``ColumnLatch.tied_fixed, ColumnLatch.tied_fixed⟩,
  ⟨201, ``ColumnLatch.tied_drift, ColumnLatch.tied_drift⟩,
  ⟨201, ``ColumnLatch.tied_fades, ColumnLatch.tied_fades⟩,
  ⟨201, ``ColumnLatch.tied_accepts, ColumnLatch.tied_accepts⟩,
  ⟨201, ``ColumnLatch.tiedFront_accepts, ColumnLatch.tiedFront_accepts⟩,
  ⟨201, ``ColumnLatch.tied_slope, ColumnLatch.tied_slope⟩,
  ⟨201, ``ColumnLatch.state_bound, ColumnLatch.state_bound⟩,
  ⟨201, ``ColumnLatch.standardized_fades, ColumnLatch.standardized_fades⟩,
  ⟨201, ``ColumnLatch.grid_carries, ColumnLatch.grid_carries⟩,
  ⟨201, ``ColumnLatch.envelope_decides, ColumnLatch.envelope_decides⟩,
  ⟨201, ``ColumnLatch.swing_bound, ColumnLatch.swing_bound⟩,
  ⟨201, ``ColumnLatch.cell_word_decides, ColumnLatch.cell_word_decides⟩,
  ⟨201, ``ColumnLatch.counts_separated, ColumnLatch.counts_separated⟩]

/-- The statement registered under a name: that of the first entry of `registry` with the name,
and `False` for a name the registry does not hold. -/
def statementOf (name : Lean.Name) : Prop :=
  match registry.find? (·.name == name) with
  | some target => target.statement
  | none => False

/-- The statement registered under each target's name is that target's statement. So an entry is
never hidden by an earlier one of the same name, and a proof of a target is a proof of
`statementOf` its name as it stands. -/
theorem statementOf_name : ∀ target ∈ registry, statementOf target.name = target.statement := by
  simp only [registry, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  and_intros <;> rfl

/-- A proof of what is registered under a name is a proof of a registered target's statement. -/
theorem statementOf_registered {name : Lean.Name} (holds : statementOf name) :
    ∃ target ∈ registry, target.name = name ∧ target.statement := by
  unfold statementOf at holds
  split at holds
  · rename_i target found
    have named : (target.name == name) = true :=
      List.find?_some (p := fun entry : Target => entry.name == name) found
    exact ⟨target, List.mem_of_find?_eq_some found, eq_of_beq named, holds⟩
  · exact holds.elim

/-- The record that a target is proved. -/
structure Landing where
  /-- The name of the target. -/
  target : Lean.Name
  /-- The name of the theorem that proves it. -/
  provedBy : Lean.Name
  /-- A proof of the statement registered under `target`. -/
  proof : statementOf target

/-- A landing proves the statement of a registered target of the name it gives. -/
theorem Landing.proves (landing : Landing) :
    ∃ target ∈ registry, target.name = landing.target ∧ target.statement :=
  statementOf_registered landing.proof

end AcornVerif.Targets
