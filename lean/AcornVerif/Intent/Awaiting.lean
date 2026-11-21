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
implementation or one `LeanIntent.AwaitingImplementation` value declaring it awaiting one. The
intent-first method confirms a record before its implementation exists, so a declared deliverable
is unimplemented for a while by design. Acorn's merge gate therefore accepts from that check
exactly the unimplemented findings of the deliverables it lists as awaiting an implementation, in
one closed list kept in the gate's code (`AcornIntentCheck.awaiting`), requires the check's
reported `awaiting` list to be empty (refusing `LeanIntent.AwaitingImplementation` declarations
while the closed list governs), and accepts nothing else. This module states that acceptance and
proves what it decides.

`onlyAwaiting awaiting fs` holds exactly when the findings `fs` are, as a set, the unimplemented
findings of the deliverables listed (`onlyAwaiting_iff`): another finding of any kind refuses, and
so does a listed name with no unimplemented finding, which is a name that is no declared
deliverable or a deliverable the check finds implemented or declared awaiting. Together with
`(report ds vs as).awaiting = []`, applied to lean-intent's decision, it gives
`implemented_of_onlyAwaiting`: no `LeanIntent.AwaitingImplementation` value exists (`as = []`);
there is a declared deliverable; each listed name is a declared deliverable that no value
implements; each declared deliverable not listed has exactly one value recording its
implementation; and each value names a declared deliverable and records a constant.

The acceptance was decided on the owner's behalf by the agent supervising Acorn's research, on
2026-11-03. The closed list remains until the listed deliverables migrate to lean-intent's
`LeanIntent.AwaitingImplementation` declaration (rbeauchamp/lean-intent#52).
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
the deliverables `ds`, the implementation entries `vs` and the awaiting entries `as`, and the
report lists no awaiting entry: no awaiting entry exists (`as = []`); there is a deliverable; each
listed name is one of them that no entry implements; each deliverable not listed has exactly one
entry recording its implementation; and each entry names one of the deliverables and records a
constant. -/
theorem implemented_of_onlyAwaiting {awaiting ds : List Lean.Name} {vs : List Entry}
    {as : List AwaitingEntry} (h : onlyAwaiting awaiting (findings ds vs as) = true)
    (hno : (report ds vs as).awaiting = []) :
    as = [] ∧ ds ≠ [] ∧ (∀ d ∈ awaiting, d ∈ ds ∧ ∀ v ∈ vs, v.deliverable ≠ some d) ∧
      (∀ d ∈ ds, d ∉ awaiting → ∃ v, implementing vs d = [v]) ∧
      ∀ v ∈ vs, (∃ d ∈ ds, v.deliverable = some d) ∧ v.subject.isSome = true := by
  obtain ⟨hall, hlisted⟩ := onlyAwaiting_iff.mp h
  have mem_of_deliverable {d : Lean.Name} (hd : d ∈ ds) {f : Finding}
      (hf : f ∈ deliverableFindings vs as d) : f ∈ findings ds vs as := by
    unfold findings
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨d, hd, hf⟩)))
  have mem_of_entry {v : Entry} (hv : v ∈ vs) {f : Finding} (hf : f ∈ entryFindings ds v) :
      f ∈ findings ds vs as := by
    unfold findings
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨v, hv, hf⟩))
  have mem_of_awaiting {a : AwaitingEntry} (ha : a ∈ as) {f : Finding}
      (hf : f ∈ awaitingFindings ds a) : f ∈ findings ds vs as := by
    unfold findings
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hf⟩)
  have deliverable_nil {d : Lean.Name} (hd : d ∈ ds) (hna : d ∉ awaiting) :
      deliverableFindings vs as d = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun f hf => by
      obtain ⟨d', hd', heq⟩ := hall f (mem_of_deliverable hd hf)
      subst heq
      unfold deliverableFindings at hf
      simp only [List.mem_append] at hf
      rcases hf with ((hf | hf) | hf) | hf <;> split at hf
      · rw [List.mem_singleton] at hf
        cases hf
        exact hna hd'
      · exact List.not_mem_nil hf
      · exact Finding.noConfusion (List.mem_singleton.mp hf)
      · exact List.not_mem_nil hf
      · exact Finding.noConfusion (List.mem_singleton.mp hf)
      · exact List.not_mem_nil hf
      · exact Finding.noConfusion (List.mem_singleton.mp hf)
      · exact List.not_mem_nil hf
  have has : as = [] := List.eq_nil_iff_forall_not_mem.mpr fun a ha => by
    have ha_nil : awaitingFindings ds a = [] := List.eq_nil_iff_forall_not_mem.mpr fun f hf => by
      obtain ⟨_, _, heq⟩ := hall f (mem_of_awaiting ha hf)
      subst heq
      unfold awaitingFindings at hf
      split at hf <;> simp at hf
    obtain ⟨d, hd, had⟩ := awaitingFindings_eq_nil_iff.mp ha_nil
    have hna : d ∉ awaiting := fun hda => (findings_sound (hlisted d hda)).2.2 a ha had
    have hone := deliverableFindings_eq_nil_iff.mp (deliverable_nil hd hna)
    have hpos : 0 < (awaitingFor as d).length :=
      List.length_pos_of_mem (mem_awaitingFor.mpr ⟨ha, had⟩)
    obtain ⟨a', ha'⟩ := List.length_eq_one_iff.mp (by omega : (awaitingFor as d).length = 1)
    have hrep : (d, a'.name, a'.reason) ∈ (report ds vs as).awaiting :=
      mem_awaiting.mpr ⟨hd, a', ha', rfl, rfl⟩
    rw [hno] at hrep
    exact List.not_mem_nil hrep
  refine ⟨has, fun hnil => ?_, fun d hd => ?_, fun d hd hna => ?_, fun v hv => ?_⟩
  · have hf : Finding.noDeliverable ∈ findings ds vs as := by
      unfold findings
      simp [hnil]
    obtain ⟨_, _, heq⟩ := hall _ hf
    exact Finding.noConfusion heq
  · have hs := findings_sound (hlisted d hd)
    exact ⟨hs.1, hs.2.1⟩
  · have hone := deliverableFindings_eq_nil_iff.mp (deliverable_nil hd hna)
    subst has
    simp only [awaitingFor, List.filter_nil, List.length_nil, Nat.add_zero] at hone
    exact List.length_eq_one_iff.mp hone
  · refine entryFindings_eq_nil_iff.mp (List.eq_nil_iff_forall_not_mem.mpr fun f hf => ?_)
    obtain ⟨_, _, heq⟩ := hall f (mem_of_entry hv hf)
    subst heq
    unfold entryFindings at hf
    split at hf <;> split at hf <;> simp at hf

end AcornVerif.Intent
