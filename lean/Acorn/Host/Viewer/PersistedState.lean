/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.RunDirectory
import Acorn.Host.Viewer.Wire

/-!
# Durable viewer-state admission

The current state file has six fields. Strict JSON syntax and exact integer
admission precede identity construction. Missing files and refused files have
different result constructors; a caller cannot mistake parse failure for a
successful restore. Publication uses an exclusively created temporary file and
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

/-- Serialization contains only closed spellings and numeric digits, with no caller text. -/
def PersistedState.encode (state : PersistedState) : String :=
  "{\"seed\":" ++ toString state.identity.seed ++
  ",\"desired\":\"" ++ state.desired.tag ++
  "\",\"run_id\":\"" ++ runHex state.identity.run ++
  "\",\"agent_epoch\":" ++ toString state.identity.agentEpoch ++
  ",\"origin\":\"" ++ state.origin.tag ++
  "\",\"process_started\":" ++ (if state.processStarted then "true" else "false") ++ "}\n"

/-- The complete current state schema refuses unknown fields and partial identity. -/
def PersistedState.decode (value : Json.Value) : Except String PersistedState :=
  Json.decode value do
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
