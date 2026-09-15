/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Lifecycle
import Acorn.Host.Viewer.ClockProgram

/-!
# Observer identity and ordering admission

Durable identity, capture ordering and frame ordering are independent checks.
The current browser contract admits one repeated lifetime clock only for the
terminal capture following its nonterminal predecessor. A newer timestamp on
an older lifetime clock is an explicit rewind, not fresh learning. No rejected
record mutates the retained-frame watermark. The maximum valid-frame timestamp
is independent and may advance when a newer capture reports a rewind.
-/
namespace Acorn.Host.Viewer

/-- Exact source counters, before any browser number conversion. -/
structure Capture where
  /-- Durable run identifier. -/
  run : UInt64
  /-- Durable logical agent epoch. -/
  epoch : UInt64
  /-- Capture time in milliseconds. -/
  timestamp : UInt64
  /-- Checkpoint-persistent agent clock. -/
  lifetime : UInt64
  /-- Process/world clock. -/
  world : UInt64
  /-- A final capture after the environment committed the last action. -/
  terminal : Bool
  deriving DecidableEq, BEq

/-- A record must name the identity currently published by the supervisor. -/
def Capture.matches (capture : Capture) (identity : Identity) : Bool :=
  capture.run == identity.run && capture.epoch == identity.agentEpoch

/-- Strict lexicographic capture order, without arithmetic overflow. -/
def Capture.after (next previous : Capture) : Bool :=
  ClockProgram.after.eval fun i =>
    match i.val with
    | 0 => next.timestamp.toNat | 1 => next.lifetime.toNat | 2 => next.world.toNat
    | 3 => previous.timestamp.toNat | 4 => previous.lifetime.toNat | _ => previous.world.toNat

/-- The one legal repeated lifetime clock derives from the terminal capture schedule. -/
def Capture.follows (next previous : Capture) : Bool :=
  ClockProgram.follows.eval fun i =>
    match i.val with
    | 0 => next.lifetime.toNat | 1 => next.world.toNat | 2 => if next.terminal then 1 else 0
    | 3 => previous.lifetime.toNat | 4 => previous.world.toNat | _ => if previous.terminal then 1 else 0

/-- No capture can refresh health by repeating itself. -/
theorem Capture.after_irreflexive (capture : Capture) : capture.after capture = false := by
  change (decide (capture.timestamp.toNat < capture.timestamp.toNat) ||
    ((capture.timestamp.toNat == capture.timestamp.toNat) &&
      (decide (capture.lifetime.toNat < capture.lifetime.toNat) ||
        ((capture.lifetime.toNat == capture.lifetime.toNat) &&
          decide (capture.world.toNat < capture.world.toNat))))) = false
  simp

/-- Equal lifetime clocks require precisely the terminal successor-world capture. -/
theorem Capture.follows_equal_lifetime (next previous : Capture)
    (same : next.lifetime = previous.lifetime) :
    next.follows previous =
      (next.terminal && !previous.terminal && next.world.toNat == previous.world.toNat + 1) := by
  change (decide (previous.lifetime.toNat < next.lifetime.toNat) ||
    ((next.lifetime.toNat == previous.lifetime.toNat) &&
      (((if next.terminal then 1 else 0 : Nat) == 1) &&
        (((if previous.terminal then 1 else 0 : Nat) == 0) &&
          (next.world.toNat == previous.world.toNat + 1))))) = _
  cases hn : next.terminal <;> cases hp : previous.terminal <;>
    simp_all

/-- Every outcome states whether a complete frame entered retained history. -/
inductive Intake where
  /-- A complete current record was retained. -/
  | stored
  /-- Wrong identity or duplicate/older capture. -/
  | skipped
  /-- Newer physical capture with a backwards or repeated agent clock. -/
  | rewound
  deriving DecidableEq, BEq

/-- A retained watermark names the same durable identity as its containing state. -/
structure Admission (identity : Identity) where
  /-- Last accepted capture, absent before the first frame. -/
  previous : Option Capture
  /-- Neither restore nor direct construction can mix agent identities. -/
  identityBound : ∀ capture, previous = some capture → capture.matches identity = true
  /-- Maximum timestamp of a schema-valid current-identity frame, including rewinds. -/
  newestTimestamp : Option UInt64 := none

/-- A new durable identity begins without an inherited watermark. -/
def Admission.empty (identity : Identity) : Admission identity := ⟨none, by simp, none⟩

/-- Timestamp health is independent of whether a frame enters retained history. -/
def Admission.noteTimestamp {identity : Identity} (state : Admission identity) (timestamp : UInt64) :
    Admission identity :=
  { state with newestTimestamp := some (match state.newestTimestamp with
      | none => timestamp
      | some previous => max previous timestamp) }

/-- Whole-record admission preserves the browser's distinct history and timestamp rules. -/
def Admission.receive {identity : Identity} (state : Admission identity) (capture : Capture) :
    Intake × Admission identity :=
  if same : capture.matches identity = true then
    let fresh := state.newestTimestamp.all (capture.timestamp > ·)
    let stamped := state.noteTimestamp capture.timestamp
    let install : Admission identity :=
      ⟨some capture, by intro other h; cases h; exact same, stamped.newestTimestamp⟩
    match state.previous with
    | none => (.stored, install)
    | some previous =>
      if capture.follows previous then (.stored, install)
      else if fresh then (.rewound, stamped) else (.skipped, stamped)
  else (.skipped, state)

/-- Wrong-identity input preserves both retained-frame and timestamp state. -/
theorem Admission.wrong_identity {identity : Identity} (state : Admission identity) (capture : Capture)
    (wrong : capture.matches identity = false) :
    state.receive capture = (.skipped, state) := by simp [receive, wrong]

/-- Refused or skipped frames cannot move the retained-frame watermark. -/
theorem Admission.rejected_preserves_history {identity : Identity} (state : Admission identity)
    (capture : Capture) (rejected : (state.receive capture).1 ≠ .stored) :
    (state.receive capture).2.previous = state.previous := by
  by_cases same : capture.matches identity = true
  · cases previous : state.previous with
    | none => simp [receive, same, previous] at rejected
    | some old =>
      by_cases follows : capture.follows old = true
      · simp [receive, same, previous, follows] at rejected
      · simp [receive, same, previous, follows]
        split <;> simp [noteTimestamp, previous]
  · simp [receive, same]

/-- A stored frame installs exactly its own complete capture as the history watermark. -/
theorem Admission.stored_capture {identity : Identity} (state : Admission identity) (capture : Capture)
    (stored : (state.receive capture).1 = .stored) :
    (state.receive capture).2.previous = some capture := by
  by_cases same : capture.matches identity = true
  · cases previous : state.previous with
    | none => simp [receive, same, previous]
    | some old =>
      by_cases follows : capture.follows old = true
      · simp [receive, same, previous, follows]
      · simp [receive, same, previous, follows] at stored
        split at stored <;> contradiction
  · simp [receive, same] at stored

/-- Envelope freshness is checked before full schema/ring admission, independently. -/
structure HealthAdmission (identity : Identity) where
  /-- Last current-identity envelope that advanced the capture order. -/
  previous : Option Capture
  /-- An envelope watermark cannot belong to another logical agent. -/
  identityBound : ∀ capture, previous = some capture → capture.matches identity = true

/-- A new identity starts with no asserted stream progress. -/
def HealthAdmission.empty (identity : Identity) : HealthAdmission identity := ⟨none, by simp⟩

/-- Even a frame with a refused scientific field can report fresh capture activity. -/
def HealthAdmission.receive {identity : Identity} (state : HealthAdmission identity) (capture : Capture) :
    Bool × HealthAdmission identity :=
  if same : capture.matches identity = true then
    if state.previous.all (capture.after ·) then
      (true, ⟨some capture, by intro other h; cases h; exact same⟩)
    else (false, state)
  else (false, state)

/-- Stale or wrong-identity envelopes cannot assert stream freshness. -/
theorem HealthAdmission.rejected_preserves {identity : Identity} (state : HealthAdmission identity)
    (capture : Capture) (rejected : (state.receive capture).1 = false) :
    (state.receive capture).2 = state := by
  by_cases same : capture.matches identity = true
  · by_cases later : state.previous.all (capture.after ·) = true
    · simp [receive, same, later] at rejected
    · simp [receive, same, later]
  · simp [receive, same]

end Acorn.Host.Viewer
