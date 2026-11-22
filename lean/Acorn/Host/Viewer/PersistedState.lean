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
no Start, and its files name no schema. So a file whose version does not read as the
current one is decoded with its other fields as written and with intent stopped: the
intent is the one field whose value an operator may never have chosen.
`PersistedState.decode_earlier` proves the stopped intent, and
`PersistedState.decode_running` that the decoder returns a running intent only under the
current version. A file that names another natural number is refused
(`PersistedState.decode_other`).
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

/-- The schema version a state file names: the natural number its `schema_version` member
spells, and nothing when the member is absent or is not a natural number. Before schema
version 2 the viewer wrote files with no such member. -/
def stateVersion (value : Json.Value) : Option Nat :=
  (value.member "schema_version").bind fun mark => mark.natural.toOption

/-- Admission of the version a state file names, decided once: a natural number other than
`stateSchema` is refused, so that a file another version wrote is neither guessed at nor
overwritten; `stateSchema` and no readable version are admitted. -/
def admitVersion : Option Nat → Except String Unit
  | some version =>
    if version = stateSchema then .ok ()
    else .error (s!"schema_version {version} is not {stateSchema}; a state file another " ++
      "version wrote is neither guessed at nor overwritten")
  | none => .ok ()

/-- The fields of a state file: its `schema_version` member when it has one, whose value
`admitVersion` has already judged, and the six fields of state. -/
def PersistedState.fields (marked : Bool) : Json.Decoder PersistedState := do
  if marked then discard (Json.take "schema_version")
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

/-- The complete state schema refuses unknown fields, partial identity and a schema version
that is a natural number other than `stateSchema`. A file whose version does not read as
`stateSchema`, because it has no `schema_version` member or one that is not a natural number,
is read as an earlier version's file: it keeps every field but its intent, which is admitted
as stopped. -/
def PersistedState.decode (value : Json.Value) : Except String PersistedState := do
  admitVersion (stateVersion value)
  let state ← Json.decode value (PersistedState.fields (value.member "schema_version").isSome)
  return if stateVersion value = some stateSchema then state else { state with desired := .stopped }

/-- **A state file whose version does not read as the current one is admitted with intent
stopped.** For every JSON value whose `schema_version` member is absent, is not a natural
number or spells another number, and every state the decoder returns for it. -/
theorem PersistedState.decode_earlier (value : Json.Value) (state : PersistedState)
    (earlier : stateVersion value ≠ some stateSchema)
    (decoded : PersistedState.decode value = .ok state) : state.desired = .stopped := by
  unfold PersistedState.decode at decoded
  obtain ⟨-, -, rest⟩ := Json.except_bind_ok decoded
  obtain ⟨read, -, returned⟩ := Json.except_bind_ok rest
  simp only [earlier, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at returned
  rw [← returned]

/-- **The decoder returns a running intent only under the current schema version.** For
every JSON value and every state the decoder returns for it that intends to run, the value's
`schema_version` member spells `stateSchema`. -/
theorem PersistedState.decode_running (value : Json.Value) (state : PersistedState)
    (decoded : PersistedState.decode value = .ok state) (running : state.desired = .running) :
    stateVersion value = some stateSchema := by
  refine Decidable.byContradiction fun earlier => ?_
  have stopped := PersistedState.decode_earlier value state earlier decoded
  rw [stopped] at running
  cases running

/-- **A state file that names another schema version is refused.** For every JSON value
whose `schema_version` member spells a natural number other than `stateSchema`. -/
theorem PersistedState.decode_other (value : Json.Value) (version : Nat)
    (named : stateVersion value = some version) (other : version ≠ stateSchema) :
    ∃ reason, PersistedState.decode value = .error reason := by
  unfold PersistedState.decode
  rw [named]
  simp only [admitVersion, other, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- Where the state a viewer starts from came from. -/
inductive StartSource where
  /-- The run directory held no state file. -/
  | absent
  /-- The state file's version does not read as `stateSchema`: an earlier version's file,
  whose intent was read as stopped. -/
  | earlier
  /-- The state file names the schema this viewer writes; its intent is the one it records. -/
  | saved
  deriving DecidableEq

/-- One line that says why the run a viewer starts with is shown stopped, and nothing when it
is not. The viewer prints it before it publishes its start state and gives it as the reason of
its first control record, so a person who finds the run stopped is told why and what starts
it. -/
def startAccount (source : StartSource) (desired : Desired) : Option String :=
  match desired, source with
  | .running, _ => none
  | .stopped, .absent =>
    some ("stopped because the run directory holds no saved state; " ++
      "it starts only on Start in the page or the --start flag")
  | .stopped, .earlier =>
    some ("stopped because the saved state was written before state.json recorded a schema " ++
      "version, so its intent is not taken as a Start; " ++
      "it starts only on Start in the page or the --start flag")
  | .stopped, .saved =>
    some ("stopped because the saved state says stopped; " ++
      "it starts only on Start in the page or the --start flag")

/-- Absence, refusal and successful restore require distinct caller branches. -/
inductive StateRead where
  /-- No prior state file exists. -/
  | missing
  /-- IO, syntax or schema refused the prior file. -/
  | refused (reason : String)
  /-- The complete state was admitted, with whether the file's version reads as the current
  one; when it does not, the file was read as an earlier version's. -/
  | restored (state : PersistedState) (current : Bool)

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
      | .ok state => return .restored state (stateVersion value == some stateSchema)
  catch error => return .refused error.toString

/-- Exclusive temporary creation prevents truncating a file owned by another pending writer.
Only successful complete writing and flushing can reach the rename publication. -/
def RunDirectory.writeState (directory : RunDirectory) (state : PersistedState) : IO Unit :=
  directory.publishBytes .state state.encode.toUTF8

end Acorn.Host.Viewer
