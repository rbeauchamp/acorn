/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-! # Study identity and lifecycle admission

These predicates govern stored identities, including identities decoded from
untrusted manifests. Filesystem and digest agreement are separate host checks;
no content identity implies authenticity or timing.
-/
namespace AcornStudy

/-- Portable manifest paths exclude traversal, absolute paths and empty components. -/
def pathLegal (s : String) : Bool :=
  !s.isEmpty && (s.splitOn "/").all (fun p =>
    !p.isEmpty && p != "." && p != ".." &&
    p.toList.all (fun c => c.isAlphanum && c.toNat < 128 || "._-".contains c))

/-- A stored path carries its admission invariant at every construction boundary. -/
abbrev LocalPath := {s : String // pathLegal s = true}

/-- Exact admission, with no normalization that could alias two spellings. -/
def localPath (s : String) : Except String LocalPath :=
  if h : pathLegal s = true then .ok ⟨s, h⟩
  else .error s!"not a normalized repository-relative path: {s}"

/-- Every admitted path retains precisely the supplied spelling. -/
theorem localPath_exact (s : String) (p : LocalPath) (h : localPath s = .ok p) :
    p.val = s := by
  unfold localPath at h
  split at h
  · cases h; rfl
  · contradiction

/-- Portable semantic identity, also suitable as a bare executable name. -/
def slugLegal (s : String) : Bool :=
  !s.isEmpty && !s.startsWith "-" && !s.endsWith "-" &&
  s.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'z') || c == '-')

/-- Slugs cannot be replaced by arbitrary command or citation text. -/
abbrev Slug := {s : String // slugLegal s = true}

/-- Admit a semantic identity without changing its spelling. -/
def slug (s : String) : Except String Slug :=
  if h : slugLegal s = true then .ok ⟨s, h⟩ else .error s!"invalid semantic slug: {s}"

/-- Fixed-width lowercase digest spelling. -/
def hexLegal (width : Nat) (s : String) : Bool :=
  s.length == width && s.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- Digest spelling carries the algorithm's width; cryptographic truth is external. -/
abbrev Hex (width : Nat) := {s : String // hexLegal width s = true}

/-- Admit only canonical lowercase hexadecimal identifiers. -/
def hex (width : Nat) (s : String) : Except String (Hex width) :=
  if h : hexLegal width s = true then .ok ⟨s, h⟩
  else .error s!"expected {width} lowercase hexadecimal digits"

/-- Performance assessment has precisely the three declared scientific outcomes. -/
inductive Effect where
  /-- The declared criterion supports the claim. -/
  | supported
  /-- The declared criterion refutes the claim. -/
  | refuted
  /-- The declared criterion is inconclusive. -/
  | inconclusive

/-- Only completion can contain an assessment. -/
inductive Lifecycle (assessment : Type) where
  /-- A protocol or run is being prepared. -/
  | draft
  /-- The protocol is registered without execution. -/
  | registered
  /-- Execution is in progress. -/
  | running
  /-- Execution completed with an assessment appropriate to its kind. -/
  | completed (result : assessment)
  /-- Execution was aborted, without a scientific verdict. -/
  | aborted

/-- Kind and assessment cannot disagree in stored state. -/
inductive State where
  /-- Performance comparisons carry an effect verdict only at completion. -/
  | performance (state : Lifecycle Effect)
  /-- Probes are descriptive. -/
  | probe (state : Lifecycle Unit)
  /-- Diagnostics are descriptive. -/
  | diagnostic (state : Lifecycle Unit)

/-- Parse lifecycle using its kind-specific assessment constructor. -/
def lifecycle {α : Type} (assessment : String → Except String α)
    (phase outcome : String) : Except String (Lifecycle α) := do
  if phase == "completed" then return .completed (← assessment outcome)
  unless outcome == "not-assessed" do throw "non-completed lifecycle must be not-assessed"
  match phase with
  | "draft" => return .draft
  | "registered" => return .registered
  | "running" => return .running
  | "aborted" => return .aborted
  | _ => throw "unknown lifecycle"

/-- Admit a kind/lifecycle/outcome triple into its dependent scientific state. -/
def state (kind phase outcome : String) : Except String State := do
  let descriptive := fun s => if s == "descriptive" then Except.ok ()
    else Except.error "completed probes and diagnostics require descriptive outcome"
  match kind with
  | "performance-comparison" =>
    let effect := fun s => match s with
      | "supported" => Except.ok Effect.supported
      | "refuted" => Except.ok Effect.refuted
      | "inconclusive" => Except.ok Effect.inconclusive
      | _ => Except.error "completed performance comparison requires an effect verdict"
    return .performance (← lifecycle effect phase outcome)
  | "observational-probe" => return .probe (← lifecycle descriptive phase outcome)
  | "operational-diagnostic" => return .diagnostic (← lifecycle descriptive phase outcome)
  | _ => throw "unknown study kind"

end AcornStudy
