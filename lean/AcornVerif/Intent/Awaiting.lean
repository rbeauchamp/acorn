/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LeanIntentBridge

/-!
# Deliverables awaiting an implementation

lean-intent's implementation check (`LeanIntent.Implementation.findings`) finds nothing only when
every declared deliverable has exactly one `LeanIntent.Implementation` value recording its
implementation. The intent-first method confirms a record before its implementation exists, so a
declared deliverable is unimplemented for a while by design. Acorn's merge gate therefore accepts
from that check exactly the unimplemented findings of the deliverables it lists as awaiting an
implementation, in one closed list kept in the gate's code (`AcornIntentCheck.awaiting`), and
nothing else. This module states that acceptance and proves what it decides.

`onlyAwaiting awaiting fs` holds exactly when the findings `fs` are, as a set, the unimplemented
findings of the deliverables listed (`onlyAwaiting_iff`): another finding of any kind refuses, and
so does a listed name with no unimplemented finding, which is a name that is no declared
deliverable or a deliverable the check finds implemented. Applied to lean-intent's decision, it
gives `implemented_of_onlyAwaiting`: there is a declared deliverable; each listed name is a declared
deliverable that no value implements; each declared deliverable not listed has exactly one value
recording its implementation; and each value names a declared deliverable and records a constant.

The acceptance was decided on the owner's behalf by the agent supervising Acorn's research, on
2026-11-03. lean-intent#52 proposes a first-class declaration of a deliverable awaiting its
implementation; once it lands, the list and this acceptance are retired for it.
-/

namespace AcornVerif.Intent

open LeanIntent LeanIntent.Implementation

/-- The implementation check's findings `fs` are exactly the unimplemented findings of the
deliverables `awaiting`: each finding is one of them, and each of them is found. -/
def onlyAwaiting (awaiting : List Lean.Name) (fs : List Finding) : Bool :=
  fs.all (fun f => awaiting.any fun d => f == .unimplemented d) &&
    awaiting.all fun d => fs.contains (.unimplemented d)

/-- **What the acceptance decides**: the findings, as a set, are the unimplemented findings of the
deliverables listed. -/
theorem onlyAwaiting_iff {awaiting : List Lean.Name} {fs : List Finding} :
    onlyAwaiting awaiting fs = true ↔
      (∀ f ∈ fs, ∃ d ∈ awaiting, f = .unimplemented d) ∧
        ∀ d ∈ awaiting, Finding.unimplemented d ∈ fs := by
  simp [onlyAwaiting]

/-- **What it establishes of lean-intent's decision.** When the acceptance holds of the findings of
the deliverables `ds` and the entries `vs`: there is a deliverable; each listed name is one of them
that no entry implements; each deliverable not listed has exactly one entry recording its
implementation; and each entry names one of the deliverables and records a constant. -/
theorem implemented_of_onlyAwaiting {awaiting ds : List Lean.Name} {vs : List Entry}
    (h : onlyAwaiting awaiting (findings ds vs) = true) :
    ds ≠ [] ∧ (∀ d ∈ awaiting, d ∈ ds ∧ ∀ v ∈ vs, v.deliverable ≠ some d) ∧
      (∀ d ∈ ds, d ∉ awaiting → ∃ v, implementing vs d = [v]) ∧
      ∀ v ∈ vs, (∃ d ∈ ds, v.deliverable = some d) ∧ v.subject.isSome = true := by
  obtain ⟨hall, hlisted⟩ := onlyAwaiting_iff.mp h
  have mem_of_deliverable {d : Lean.Name} (hd : d ∈ ds) {f : Finding}
      (hf : f ∈ deliverableFindings vs d) : f ∈ findings ds vs := by
    unfold findings
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨d, hd, hf⟩))
  have mem_of_entry {v : Entry} (hv : v ∈ vs) {f : Finding} (hf : f ∈ entryFindings ds v) :
      f ∈ findings ds vs := by
    unfold findings
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨v, hv, hf⟩)
  refine ⟨fun hnil => ?_, fun d hd => ?_, fun d hd hna => ?_, fun v hv => ?_⟩
  · have hf : Finding.noDeliverable ∈ findings ds vs := by
      unfold findings
      simp [hnil]
    obtain ⟨_, _, heq⟩ := hall _ hf
    exact Finding.noConfusion heq
  · exact findings_sound (hlisted d hd)
  · refine deliverableFindings_eq_nil_iff.mp (List.eq_nil_iff_forall_not_mem.mpr fun f hf => ?_)
    obtain ⟨d', hd', heq⟩ := hall f (mem_of_deliverable hd hf)
    subst heq
    unfold deliverableFindings at hf
    split at hf
    · rw [List.mem_singleton] at hf
      cases hf
      exact hna hd'
    · exact List.not_mem_nil hf
    · exact Finding.noConfusion (List.mem_singleton.mp hf)
  · refine entryFindings_eq_nil_iff.mp (List.eq_nil_iff_forall_not_mem.mpr fun f hf => ?_)
    obtain ⟨_, _, heq⟩ := hall f (mem_of_entry hv hf)
    subst heq
    unfold entryFindings at hf
    split at hf <;> split at hf <;> simp at hf

end AcornVerif.Intent
