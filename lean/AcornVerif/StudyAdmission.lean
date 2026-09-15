/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Dossier

/-! # Executed dossier admission contracts

These universals use the same constructors as the native dossier loader. The
compiler refusal contracts quantify over arbitrary admitted values: they prevent
ordinary callers from rewriting evidence-bearing state or forging cache entries.
Cryptographic truth, filesystem stability and subprocess behavior remain host
assumptions; private constructors do not prove those external systems correct.
-/
namespace AcornVerif.StudyAdmission
open AcornStudy

/-- Every stored path satisfies the actual portable-path admission predicate. -/
theorem stored_path (p : LocalPath) : pathLegal p.val = true := p.property

/-- An admitted string cannot be silently normalized into another path. -/
theorem admitted_path_exact (s : String) (p : LocalPath) (h : localPath s = .ok p) :
    p.val = s := localPath_exact s p h

/-- Every stored digest has the algorithm's exact canonical spelling. -/
theorem stored_digest (width : Nat) (h : Hex width) : hexLegal width h.val = true := h.property

/-- Direct ancestry is strictly decreasing for every admitted protocol. -/
theorem parent_earlier (p : Protocol) (parent : Revision) (h : p.parent = some parent) :
    parent.val < p.id.val := by
  have ancestry := p.ancestry
  rw [h] at ancestry
  exact ancestry

/-- No admitted protocol can name itself as parent. -/
theorem no_self_parent (p : Protocol) : p.parent ≠ some p.id := by
  intro h
  exact Nat.lt_irrefl _ (parent_earlier p p.id h)

/-- Kind/format admission preserves the supplied scientific state universally. -/
theorem format_preserves_state (s : State) (format : String) (r : RunState)
    (h : runState s format = .ok r) : r.state = s := runState_preserves s format r h

/-- Non-completed state cannot acquire an outcome through its presentation. -/
theorem unassessed {α : Type} (s : Lifecycle α) (label : α → String)
    (h : ∀ value, s ≠ .completed value) : s.outcome label = "not-assessed" := by
  cases s with
  | completed value => exact False.elim (h value rfl)
  | _ => rfl

/-- error: invalid {...} notation, constructor for `Run` is marked as private -/
#guard_msgs in
example (r : Run) : Run := { r with comparisons := [] }

/-- error: Field `entries` from structure `AcornStudy.Integrity` is private -/
#guard_msgs in
example (r : Integrity) : IO Unit := r.entries.set #[]

/-- error: Field `entries` from structure `AcornStudy.ArchiveCache` is private -/
#guard_msgs in
example (r : ArchiveCache) : IO Unit := r.entries.set #[]

/-- error: invalid {...} notation, constructor for `TimestampEvidence` is marked as private -/
#guard_msgs in
example (t : TimestampEvidence) (p : LocalPath) : TimestampEvidence := { t with reply := p }

/-- error: invalid {...} notation, constructor for `GitObject` is marked as private -/
#guard_msgs in
example (o : GitObject) : GitObject := { o with bytes := ByteArray.empty }

/-- error: invalid {...} notation, constructor for `Registry` is marked as private -/
#guard_msgs in
example (r : Registry) : Registry := { r with studies := [] }

end AcornVerif.StudyAdmission
