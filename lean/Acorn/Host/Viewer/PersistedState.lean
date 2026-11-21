/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.RunDirectory
import Acorn.Host.Viewer.Wire

/-!
# Durable viewer-state admission

The current state file has seven fields: its schema version and six of state. Strict
JSON syntax and exact integer admission precede identity construction. Missing files
and refused files have different result constructors; a caller cannot mistake parse
failure for a successful restore. Publication uses an exclusively created temporary
file and rename after a complete write and flush. Filesystem stability and POSIX
rename remain the RunDirectory trust boundary; no power-loss durability is claimed.

**A running intent in a file of this schema follows a Start.** A viewer that finds no
state file builds a state that intends to stay stopped (`PersistedState.unstarted`), and
a supervisor started from a stopped intent waits on no write of a running intent while
no operator's Start is handed to its step (`Acorn.Host.Viewer.ExplicitStart`). That a
running intent on disk therefore follows a Start in some viewer that owned the run
directory is argued from that theorem by induction over those viewers, and is not
proved. Before schema version 2 the viewer wrote `running` when it found no file, with
no Start, and its files name no schema. So a file that names none is decoded with its
other fields as written and with intent stopped: the intent is the one field whose
value an operator may never have chosen. `PersistedState.decode_unversioned` proves the
stopped intent.
-/
namespace Acorn.Host.Viewer

/-- Origin of an agent constructed without restoring a checkpoint. -/
inductive NewAgentOrigin where
  /-- Initial run construction. -/
  | fresh
  /-- Construction after explicit Clear. -/
  | cleared
  deriving DecidableEq, BEq

/-- Exact persisted spelling of the closed origin domain. -/
def NewAgentOrigin.tag : NewAgentOrigin → String
  | .fresh => "fresh"
  | .cleared => "cleared"

/-- Durable identity, user intent and prior-process fact owned by state.json. -/
structure PersistedState where
  /-- Run, terrain seed and logical agent identity. -/
  identity : Identity
  /-- Operator's persisted intent. -/
  desired : Desired
  /-- Origin of a newly constructed agent. -/
  origin : NewAgentOrigin
  /-- Whether this run previously launched a process. -/
  processStarted : Bool
  deriving DecidableEq, BEq

/-- Closed operator-intent spellings. -/
def Desired.tag : Desired → String
  | .running => "running"
  | .stopped => "stopped"

/-- Fixed-width lowercase hexadecimal representation of a full-width run ID. -/
def runHex (word : UInt64) : String :=
  String.ofList ((List.range 16).reverse.map fun index =>
    let digit := word.toNat / 16 ^ index % 16
    Char.ofNat (if digit < 10 then 48 + digit else 87 + digit))

/-- The schema version the viewer writes. From this version on, a viewer that finds no state
file writes a stopped intent. -/
def stateSchema : Nat := 2

/-- The state a viewer builds when its run directory holds no state file: a new run of a fresh
agent that intends to stay stopped, so the absence of a file gives the supervisor no running
intent. `migrated`
records that a stray checkpoint of an earlier layout was adopted into the run. -/
def PersistedState.unstarted (seed : UInt64) (migrated : Bool) : PersistedState :=
  ⟨⟨seed, seed, 0⟩, .stopped, .fresh, migrated⟩

/-- Serialization contains only closed spellings and numeric digits, with no caller text. -/
def PersistedState.encode (state : PersistedState) : String :=
  "{\"schema_version\":" ++ toString stateSchema ++
  ",\"seed\":" ++ toString state.identity.seed ++
  ",\"desired\":\"" ++ state.desired.tag ++
  "\",\"run_id\":\"" ++ runHex state.identity.run ++
  "\",\"agent_epoch\":" ++ toString state.identity.agentEpoch ++
  ",\"origin\":\"" ++ state.origin.tag ++
  "\",\"process_started\":" ++ (if state.processStarted then "true" else "false") ++ "}\n"

/-- Whether a state file names its schema. Before schema version 2 the viewer wrote files that
name none. -/
def stateVersioned (value : Json.Value) : Bool := (value.member "schema_version").isSome

/-- The fields of a state file: the schema version when the file names one, which must be
`stateSchema`, and the six fields of state. -/
def PersistedState.fields (versioned : Bool) : Json.Decoder PersistedState := do
  if versioned then
    unless (← (← Json.take "schema_version").natural) == stateSchema do
      throw (s!"schema_version is not {stateSchema}; a state file another version wrote is " ++
        "neither guessed at nor overwritten")
  let seed ← jsonWord (← Json.take "seed")
  let desired ← match ← Json.text "desired" with
    | "running" => pure Desired.running
    | "stopped" => pure Desired.stopped
    | _ => throw "unknown desired state"
  let run ← runWord (← Json.take "run_id")
  let epoch ← jsonWord (← Json.take "agent_epoch")
  let origin ← match ← Json.text "origin" with
    | "fresh" => pure NewAgentOrigin.fresh
    | "cleared" => pure NewAgentOrigin.cleared
    | _ => throw "unknown new-agent origin"
  let processStarted ← jsonBool (← Json.take "process_started")
  return ⟨⟨run, seed, epoch⟩, desired, origin, processStarted⟩

/-- The complete state schema refuses unknown fields, partial identity and any schema version
but `stateSchema`. A file that names no schema keeps every field but its intent, which is
admitted as stopped. -/
def PersistedState.decode (value : Json.Value) : Except String PersistedState := do
  let state ← Json.decode value (PersistedState.fields (stateVersioned value))
  return if stateVersioned value then state else { state with desired := .stopped }

/-- **A state file that names no schema is admitted with intent stopped.** For every JSON
value with no member named `schema_version` and every state the decoder returns for it. -/
theorem PersistedState.decode_unversioned (value : Json.Value) (state : PersistedState)
    (unversioned : stateVersioned value = false)
    (decoded : PersistedState.decode value = .ok state) : state.desired = .stopped := by
  unfold PersistedState.decode at decoded
  obtain ⟨read, -, returned⟩ := Json.except_bind_ok decoded
  simp only [unversioned, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
    Except.ok.injEq] at returned
  rw [← returned]

/-- Where the state a viewer starts from came from. -/
inductive StartSource where
  /-- The run directory held no state file. -/
  | absent
  /-- The state file names no schema version, so its intent was read as stopped. -/
  | unversioned
  /-- The state file names the schema this viewer writes; its intent is the one it records. -/
  | saved
  deriving DecidableEq

/-- One line that says why the run a viewer starts with is stopped, or that it resumes. The
viewer prints it at start-up and publishes it as the reason of its first control record, so a
person who finds the run stopped is told why and what starts it. -/
def startAccount (source : StartSource) (desired : Desired) : String :=
  match desired, source with
  | .running, _ => "the saved state intends to run, so the run resumes"
  | .stopped, .absent =>
    "stopped because the run directory holds no saved state; " ++
      "press Start in the page or launch with --start"
  | .stopped, .unversioned =>
    "stopped because the saved state was written before state.json recorded a schema " ++
      "version, so its intent is not taken as a Start; " ++
      "press Start in the page or launch with --start"
  | .stopped, .saved =>
    "stopped because the saved state says stopped; " ++
      "press Start in the page or launch with --start"

/-- Absence, refusal and successful restore require distinct caller branches. -/
inductive StateRead where
  /-- No prior state file exists. -/
  | missing
  /-- IO, syntax or schema refused the prior file. -/
  | refused (reason : String)
  /-- The complete state was admitted, from a file that names its schema or from one that
  names none. -/
  | restored (state : PersistedState) (versioned : Bool)

private def stateBytes (handle : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  let chunk ← handle.read (min (remaining + 1) 4096).toUSize
  if _empty : chunk.size = 0 then return bytes
  else if _fits : chunk.size ≤ remaining then
    stateBytes handle (remaining - chunk.size) (bytes ++ chunk)
  else throw (IO.userError "viewer state exceeds 4096 bytes")
termination_by remaining

/-- A bounded read preserves the distinction between missing and malformed state. -/
def RunDirectory.readState (directory : RunDirectory) : IO StateRead := do
  let handle ← try directory.openRead .state
    catch error =>
      match error with
      | .noFileOrDirectory _ _ _ => return .missing
      | _ => return .refused error.toString
  try
    let bytes ← stateBytes handle 4096 ByteArray.empty
    let some text := String.fromUTF8? bytes | return .refused "invalid state UTF-8"
    match Json.parse text with
    | .error reason => return .refused reason
    | .ok value =>
      match PersistedState.decode value with
      | .error reason => return .refused reason
      | .ok state => return .restored state (stateVersioned value)
  catch error => return .refused error.toString

/-- Exclusive temporary creation prevents truncating a file owned by another pending writer.
Only successful complete writing and flushing can reach the rename publication. -/
def RunDirectory.writeState (directory : RunDirectory) (state : PersistedState) : IO Unit :=
  directory.publishBytes .state state.encode.toUTF8

end Acorn.Host.Viewer
