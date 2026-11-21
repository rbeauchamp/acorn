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
failure for a successful restore.

**A running intent on disk records a Start.** A viewer that finds no state file builds
a state that intends to stay stopped (`PersistedState.unstarted`), and the supervisor
writes a running intent only after an operator's Start or from a state that already
held one (`Acorn.Host.Viewer.ExplicitStart`). Viewers before schema version 2 wrote
`running` when they found no file, with no Start, and their files name no schema. So a
file that names none is admitted with its identity, its origin and its process fact,
and with intent stopped (`PersistedState.decode_unversioned`): the intent is the one
field whose value an operator may never have chosen. Publication uses an exclusively created temporary file and
rename after a complete write and flush. Filesystem stability and POSIX rename
remain the RunDirectory trust boundary; no power-loss durability is claimed.
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

/-- The schema version the viewer writes. From this version on, a state file holds a running
intent only after an operator's Start. -/
def stateSchema : Nat := 2

/-- The state a viewer builds when its run directory holds no state file: a new run of a fresh
agent that intends to stay stopped, so the absence of a file starts no process. `migrated`
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

/-- Whether a state file names its schema. A file that names none is from a viewer before
schema version 2. -/
def stateVersioned (value : Json.Value) : Bool := (value.member "schema_version").isSome

/-- The fields of a state file: the schema version when the file names one, which must be
`stateSchema`, and the six fields of state. -/
def PersistedState.fields (versioned : Bool) : Json.Decoder PersistedState := do
  if versioned then Json.version stateSchema
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

/-- Absence, refusal and successful restore require distinct caller branches. -/
inductive StateRead where
  /-- No prior state file exists. -/
  | missing
  /-- IO, syntax or schema refused the prior file. -/
  | refused (reason : String)
  /-- The complete current state was admitted. -/
  | restored (state : PersistedState)

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
    match Json.parse text >>= PersistedState.decode with
    | .error reason => return .refused reason
    | .ok state => return .restored state
  catch error => return .refused error.toString

/-- Exclusive temporary creation prevents truncating a file owned by another pending writer.
Only successful complete writing and flushing can reach the rename publication. -/
def RunDirectory.writeState (directory : RunDirectory) (state : PersistedState) : IO Unit :=
  directory.publishBytes .state state.encode.toUTF8

end Acorn.Host.Viewer
