import AcornVerif.Targets.ColumnLatch
import AcornVerif.Targets.CurrentConcealedTargetRung
import AcornVerif.Targets.Json
import AcornVerif.Targets.StateEntry

namespace AcornVerif.Targets

structure Target where
  mission : Nat
  name : Lean.Name
  statement : Prop

def ofMission (mission : Nat) (statements : List (Lean.Name × Prop)) : List Target :=
  statements.map fun entry => ⟨mission, entry.1, entry.2⟩

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
    (``ColumnLatch.counts_separated, ColumnLatch.counts_separated)] ++
  ofMission 283 [
    (``CurrentConcealedTargetRung.rung_learns, CurrentConcealedTargetRung.rung_learns)]

def statementOf (name : Lean.Name) : Prop :=
  match registry.find? (·.name == name) with
  | some target => target.statement
  | none => False

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

theorem registry_distinct : (registry.map (·.name)).Nodup := by decide +kernel

theorem statementOf_name : ∀ target ∈ registry, statementOf target.name = target.statement := by
  intro target member
  simp only [statementOf, find_named registry_distinct member]

theorem statementOf_registered {name : Lean.Name} (holds : statementOf name) :
    ∃ target ∈ registry, target.name = name ∧ target.statement := by
  unfold statementOf at holds
  split at holds
  · rename_i target found
    have named : (target.name == name) = true :=
      List.find?_some (p := fun entry : Target => entry.name == name) found
    exact ⟨target, List.mem_of_find?_eq_some found, eq_of_beq named, holds⟩
  · exact holds.elim

structure Landing where
  target : Lean.Name
  provedBy : Lean.Name
  proof : statementOf target

theorem Landing.proves (landing : Landing) :
    ∃ target ∈ registry, target.name = landing.target ∧ target.statement :=
  statementOf_registered landing.proof

end AcornVerif.Targets
