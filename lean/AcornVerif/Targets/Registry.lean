/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Targets.ColumnLatch
import AcornVerif.Targets.Json
import AcornVerif.Targets.StateEntry

/-! # The registry of targets

A *target* is a statement that a mission is to prove, held as a definition of type `Prop` in a
module of this directory, `lean/AcornVerif/Targets/`. It is open until `AcornVerif.landings`
records a proof of it. The build elaborates every target against the current definitions, so a
target that no longer type-checks fails the build. `.github/CODEOWNERS` names this directory, so
GitHub asks the repository's owner to review any pull request that changes it, and only the owner
merges. A mission establishes its statements by proving each of its targets; a part of its
contract that is not a statement to prove stays in its issue.

`registry` lists the targets by mission: `ofMission 200 [...]` holds one pair for each target of
mission #200. Each pair repeats one identifier, as in
`(``StateEntry.arm_letter, StateEntry.arm_letter)`: Lean resolves the doubled backquote to the
name of a declaration, and the second component is that declaration, which Lean requires to be a
proposition. A target's name is its module's name followed by one more component, the name of the
theorem that is to prove it, so `AcornVerif.Targets.StateEntry.arm_letter` is in
`lean/AcornVerif/Targets/StateEntry.lean`.

`Landing` is the record that a target is proved: the target's name, the name of the theorem that
proves it, and a proof of `statementOf` that name, which Lean's kernel checks. The record itself,
`AcornVerif.landings`, is outside this directory, so that a mission's pull request adds to it and
changes nothing here.

What the proofs below establish: no two targets have one name (`registry_distinct`), so the
statement registered under each target's name is that target's statement (`statementOf_name`), and
a proof of what is registered under any name is a proof of a registered target's statement
(`statementOf_registered`, `Landing.proves`).

What they do not establish:

* That a pair's name and its statement are one declaration, since no theorem relates a name to the
  declaration it names. The pair's form above and the owner's review of this directory keep that.
* That the registry holds every definition of a statement in this directory. One left out is
  elaborated by the build and is no target.
* That a mission's number is the right issue. Nothing joins it to GitHub's record.
* That a target keeps its meaning. A target fixes its own text, and the definitions it names are
  outside this directory: a change to one of them changes what the target says.
* That a target states what its mission means. Review reads each statement.
-/

namespace AcornVerif.Targets

/-- One statement on record. -/
structure Target where
  /-- The issue number of the mission the statement belongs to. -/
  mission : Nat
  /-- The name of the definition of type `Prop` that holds the statement. -/
  name : Lean.Name
  /-- The statement. -/
  statement : Prop

/-- The targets of one mission, from the name and the statement of each. -/
def ofMission (mission : Nat) (statements : List (Lean.Name × Prop)) : List Target :=
  statements.map fun entry => ⟨mission, entry.1, entry.2⟩

/-- Every target, by mission, each mission's in the order of its contract. -/
def registry : List Target :=
  ofMission 163 [
    (``Json.parse_complete, Json.parse_complete)] ++
  ofMission 200 [
    (``StateEntry.arm_letter, StateEntry.arm_letter),
    (``StateEntry.fold_arm, StateEntry.fold_arm),
    (``StateEntry.near_threshold, StateEntry.near_threshold),
    (``StateEntry.clear_threshold, StateEntry.clear_threshold),
    (``StateEntry.latches_mono, StateEntry.latches_mono),
    (``StateEntry.memoryless_refused, StateEntry.memoryless_refused),
    (``StateEntry.frozen_refused, StateEntry.frozen_refused),
    (``StateEntry.fading_margin, StateEntry.fading_margin),
    (``StateEntry.fading_no_uniform, StateEntry.fading_no_uniform),
    (``StateEntry.additive_margin, StateEntry.additive_margin),
    (``StateEntry.rows_accept, StateEntry.rows_accept),
    (``StateEntry.rows_clamped, StateEntry.rows_clamped),
    (``StateEntry.linearTrace_additive, StateEntry.linearTrace_additive),
    (``StateEntry.linearTrace_margin, StateEntry.linearTrace_margin),
    (``StateEntry.linearTrace_refused, StateEntry.linearTrace_refused),
    (``StateEntry.column_accepts, StateEntry.column_accepts),
    (``StateEntry.tracks_decide, StateEntry.tracks_decide),
    (``StateEntry.column_tracks, StateEntry.column_tracks),
    (``StateEntry.bucket_refuses, StateEntry.bucket_refuses),
    (``StateEntry.level_carries, StateEntry.level_carries),
    (``StateEntry.two_values_levels, StateEntry.two_values_levels),
    (``StateEntry.values_bellman, StateEntry.values_bellman),
    (``StateEntry.values_first_bucket, StateEntry.values_first_bucket)] ++
  ofMission 201 [
    (``ColumnLatch.cell_accepts, ColumnLatch.cell_accepts),
    (``ColumnLatch.cell_bands, ColumnLatch.cell_bands),
    (``ColumnLatch.read_lipschitz, ColumnLatch.read_lipschitz),
    (``ColumnLatch.threshold_trap, ColumnLatch.threshold_trap),
    (``ColumnLatch.front_accepts, ColumnLatch.front_accepts),
    (``ColumnLatch.tied_bounded, ColumnLatch.tied_bounded),
    (``ColumnLatch.tied_fixed, ColumnLatch.tied_fixed),
    (``ColumnLatch.tied_drift, ColumnLatch.tied_drift),
    (``ColumnLatch.tied_fades, ColumnLatch.tied_fades),
    (``ColumnLatch.tied_accepts, ColumnLatch.tied_accepts),
    (``ColumnLatch.tiedFront_accepts, ColumnLatch.tiedFront_accepts),
    (``ColumnLatch.tied_slope, ColumnLatch.tied_slope),
    (``ColumnLatch.state_bound, ColumnLatch.state_bound),
    (``ColumnLatch.standardized_fades, ColumnLatch.standardized_fades),
    (``ColumnLatch.grid_carries, ColumnLatch.grid_carries),
    (``ColumnLatch.envelope_decides, ColumnLatch.envelope_decides),
    (``ColumnLatch.swing_bound, ColumnLatch.swing_bound),
    (``ColumnLatch.cell_word_decides, ColumnLatch.cell_word_decides),
    (``ColumnLatch.counts_separated, ColumnLatch.counts_separated)]

/-- The statement registered under a name: that of the first target of `registry` with the name,
and `False` for a name the registry does not hold. -/
def statementOf (name : Lean.Name) : Prop :=
  match registry.find? (·.name == name) with
  | some target => target.statement
  | none => False

/-- In a list of targets with distinct names, the first target with a member's name is that
member. -/
theorem find_named {targets : List Target} (distinct : (targets.map (·.name)).Nodup)
    {target : Target} (member : target ∈ targets) :
    targets.find? (·.name == target.name) = some target := by
  induction targets with
  | nil => cases member
  | cons head tail step =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with same | later
    · subst same
      simp
    · have differs : head.name ≠ target.name := fun same =>
        fresh (List.mem_map.mpr ⟨target, later, same.symm⟩)
      simp [differs, step rest later]

/-- No two targets of the registry have one name. -/
theorem registry_distinct : (registry.map (·.name)).Nodup := by decide +kernel

/-- The statement registered under each target's name is that target's statement. So no target is
hidden by an earlier one, and a proof of a target is a proof of `statementOf` its name. -/
theorem statementOf_name : ∀ target ∈ registry, statementOf target.name = target.statement := by
  intro target member
  simp only [statementOf, find_named registry_distinct member]

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
