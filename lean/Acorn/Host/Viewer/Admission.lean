import Acorn.Host.Viewer.Lifecycle
import Acorn.Host.Viewer.ClockProgram

namespace Acorn.Host.Viewer

structure Capture where
  run : UInt64
  epoch : UInt64
  timestamp : UInt64
  lifetime : UInt64
  world : UInt64
  terminal : Bool
  deriving DecidableEq, BEq

def Capture.matches (capture : Capture) (identity : Identity) : Bool :=
  capture.run == identity.run && capture.epoch == identity.agentEpoch

def Capture.after (next previous : Capture) : Bool :=
  ClockProgram.after.eval fun i =>
    match i.val with
    | 0 => next.timestamp.toNat | 1 => next.lifetime.toNat | 2 => next.world.toNat
    | 3 => previous.timestamp.toNat | 4 => previous.lifetime.toNat | _ => previous.world.toNat

def Capture.follows (next previous : Capture) : Bool :=
  ClockProgram.follows.eval fun i =>
    match i.val with
    | 0 => next.lifetime.toNat | 1 => next.world.toNat | 2 => if next.terminal then 1 else 0
    | 3 => previous.lifetime.toNat | 4 => previous.world.toNat | _ => if previous.terminal then 1 else 0

theorem Capture.after_irreflexive (capture : Capture) : capture.after capture = false := by
  change (decide (capture.timestamp.toNat < capture.timestamp.toNat) ||
    ((capture.timestamp.toNat == capture.timestamp.toNat) &&
      (decide (capture.lifetime.toNat < capture.lifetime.toNat) ||
        ((capture.lifetime.toNat == capture.lifetime.toNat) &&
          decide (capture.world.toNat < capture.world.toNat))))) = false
  simp

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

inductive Intake where
  | stored
  | skipped
  | rewound
  deriving DecidableEq, BEq

structure Admission (identity : Identity) where
  previous : Option Capture
  identityBound : ∀ capture, previous = some capture → capture.matches identity = true
  newestTimestamp : Option UInt64 := none

def Admission.empty (identity : Identity) : Admission identity := ⟨none, by simp, none⟩

def Admission.noteTimestamp {identity : Identity} (state : Admission identity) (timestamp : UInt64) :
    Admission identity :=
  { state with newestTimestamp := some (match state.newestTimestamp with
      | none => timestamp
      | some previous => max previous timestamp) }

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

theorem Admission.wrong_identity {identity : Identity} (state : Admission identity) (capture : Capture)
    (wrong : capture.matches identity = false) :
    state.receive capture = (.skipped, state) := by simp [receive, wrong]

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

structure HealthAdmission (identity : Identity) where
  previous : Option Capture
  identityBound : ∀ capture, previous = some capture → capture.matches identity = true

def HealthAdmission.empty (identity : Identity) : HealthAdmission identity := ⟨none, by simp⟩

def HealthAdmission.receive {identity : Identity} (state : HealthAdmission identity) (capture : Capture) :
    Bool × HealthAdmission identity :=
  if same : capture.matches identity = true then
    if state.previous.all (capture.after ·) then
      (true, ⟨some capture, by intro other h; cases h; exact same⟩)
    else (false, state)
  else (false, state)

theorem HealthAdmission.rejected_preserves {identity : Identity} (state : HealthAdmission identity)
    (capture : Capture) (rejected : (state.receive capture).1 = false) :
    (state.receive capture).2 = state := by
  by_cases same : capture.matches identity = true
  · by_cases later : state.previous.all (capture.after ·) = true
    · simp [receive, same, later] at rejected
    · simp [receive, same, later]
  · simp [receive, same]

end Acorn.Host.Viewer
