/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.RunDirectory
import Acorn.Host.Viewer.Wire
import Acorn.Rng

/-!
# Durable viewer-state admission

The current state file has eight members: its schema version, six of state and the record of
the child of the viewer that wrote it. Strict JSON syntax and exact integer admission precede
identity construction. Missing files and refused files have different result constructors; a
caller cannot mistake parse failure for a successful restore. Only a run directory with no
entry named state.json reads as a missing file. An entry that exists and is not a regular
file, or a link to one, is refused without being opened: a symbolic link whose target is gone,
a directory, a pipe, a device. Publication uses an exclusively created temporary file and
rename after a complete write and flush. Filesystem stability and POSIX rename remain the
RunDirectory trust boundary; no power-loss durability is claimed.

**A running intent in a file of this schema follows a Start given for the child the file
names.** A viewer that finds no state file builds a state that intends to stay stopped
(`PersistedState.unstarted`), and a supervisor started from a stopped intent waits on no write
of a running intent while no operator's Start is handed to its step
(`Acorn.Host.Viewer.ExplicitStart`). Every state a viewer writes carries the record of the
child its own supervisor would start (`childRecord`, `PersistedState.encode`): the
executable's path, its length in bytes, the 64-bit FNV-1a digest of every byte of the file
(`fileDigest`), and the argument vector at the reference launch. That a running intent on disk
therefore follows a Start given, in some viewer that owned the run directory, while that
viewer's child had the record the file names is argued from that theorem by induction over
those viewers, and is not proved. Two files of equal length and equal digest are taken as one:
the digest suffices against accident, a rebuilt file that agrees in length and in a 64-bit
digest by chance, and forging it needs no more power than writing the state file by hand.

Two things decide whether a decoded file's intent is kept; a file is decoded only when its six
members of state are all admitted. Before schema version 2 the viewer wrote `running` when it
found no file, with no Start, and its files name no schema and no child. So for a file whose
version does not read as the current one, every state the decoder returns intends to stay
stopped (`PersistedState.decode_earlier`): the intent is the one field whose value an operator
may never have chosen, and the other fields are kept as written. The version a file names is
the natural number its `schema_version` member spells in decimal digits alone, of any size
(`stateVersion`); a member spelled any other way, `3e0` for example, is no readable version.
For a file that names another natural number the decoder returns an error
(`PersistedState.decode_other`), and so it does for one whose digits spell a number of
`2 ^ 64` or more (`PersistedState.decode_wide`). And for a file that does not name the child
record of the launch that reads it, or that is read by a launch with no record, every state
the decoder returns intends to stay stopped (`PersistedState.decode_unbound`). The decoder
returns a running intent only under the current version and for this launch's child
(`PersistedState.decode_running`).
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

/-- A word of a child record that the state file can hold as written: printable ASCII with no
quotation mark and no backslash, so its JSON spelling is the word between quotation marks. -/
def childWordAdmitted (word : String) : Bool :=
  word.toList.all fun c => ' ' ≤ c && c ≤ '~' && c != '"' && c != '\\'

/-- The room a child record may take in the state file, which a viewer reads within 4096 bytes:
the lengths of its words, with three more for each word's quotation marks and comma. -/
def childBudget : Nat := 2048

/-- A child record the state file can hold: at least one word, every word admitted, within the
budget. -/
def childAdmitted (words : List String) : Bool :=
  !words.isEmpty && words.all childWordAdmitted &&
    words.foldl (fun total word => total + word.length + 3) 0 ≤ childBudget

/-- The digest of a file's content: 64-bit FNV-1a over every byte, in order, a function of
the bytes alone. Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake 3rd and Tony Hansen, The FNV
Non-Cryptographic Hash Algorithm, RFC 9923 (2026), sections 2 and 5; the step and the offset
basis are those of `Acorn.Rng`. It tells two files apart against accident and not against
forgery. -/
def fileDigest (content : ByteArray) : UInt64 :=
  content.foldl Rng.fnvStep Rng.fnvOffset

/-- The record of the child a viewer's supervisor would start, as far as the viewer can read
it before it starts it: the executable's path, the length in bytes and the digest
(`fileDigest`) of the content read from the file at that path, and the argument vector at a
fixed reference launch (`referenceLaunch`). Two launches have the same child, for the purpose
of a saved running intent, exactly when both have a record and the records are equal word for
word, so two files of equal length and equal digest are taken as one. A launch has no record
when sameness cannot be established: a command given to a shell, whose process depends on the
working directory, the environment and the files the command names; an executable whose file
cannot be read whole; or words the state file cannot hold. -/
def childRecord (executable : String) (content : ByteArray) (arguments : List String) :
    Option (List String) :=
  let words := executable :: toString content.size :: toString (fileDigest content) :: arguments
  if childAdmitted words then some words else none

/-- The `child` member of a state file: the record's words as a JSON array of strings, and
`null` when the launch has no record or its record cannot be held. -/
def childText : Option (List String) → String
  | some words =>
    if childAdmitted words then
      "[" ++ ",".intercalate (words.map fun word => "\"" ++ word ++ "\"") ++ "]"
    else "null"
  | none => "null"

/-- Serialization contains only closed spellings, numeric digits and the admitted words of the
child record of the viewer that writes it. -/
def PersistedState.encode (child : Option (List String)) (state : PersistedState) : String :=
  "{\"schema_version\":" ++ toString stateSchema ++
  ",\"seed\":" ++ toString state.identity.seed ++
  ",\"desired\":\"" ++ state.desired.tag ++
  "\",\"run_id\":\"" ++ runHex state.identity.run ++
  "\",\"agent_epoch\":" ++ toString state.identity.agentEpoch ++
  ",\"origin\":\"" ++ state.origin.tag ++
  "\",\"process_started\":" ++ (if state.processStarted then "true" else "false") ++
  ",\"child\":" ++ childText child ++ "}\n"

/-- The schema version a state file names: the natural number, of any size, that its
`schema_version` member spells in decimal digits alone (`Digits.read`), and nothing when the
member is absent or is not a number so spelled. Before schema version 2 the viewer wrote files
with no such member. -/
def stateVersion (value : Json.Value) : Option Nat :=
  (value.member "schema_version").bind fun mark =>
    match mark with
    | .number spelling => Digits.read spelling
    | _ => none

/-- The child record a state file names: the words of its `child` member when that is a JSON
array of strings, and nothing when the member is absent or has any other form. -/
def stateChild (value : Json.Value) : Option (List String) :=
  (value.member "child").bind fun mark =>
    match mark with
    | .array words =>
      words.mapM fun word =>
        match word with
        | .string text => some text
        | _ => none
    | _ => none

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
`admitVersion` has already judged, its `child` member when it has one, which `stateChild`
reads, and the six fields of state. -/
def PersistedState.fields (marked recorded : Bool) : Json.Decoder PersistedState := do
  if marked then discard (Json.take "schema_version")
  if recorded then discard (Json.take "child")
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

/-- Where the state a viewer starts from came from. -/
inductive StartSource where
  /-- The run directory held no state file. -/
  | absent
  /-- The state file's version does not read as `stateSchema`: an earlier version's file,
  whose intent was read as stopped. -/
  | earlier
  /-- The state file names the schema this viewer writes and this launch's child, or records
  a stopped intent; its intent is the one it records. -/
  | saved
  /-- The state file names the schema this viewer writes and a running intent that was not
  given for this launch's child: the file names another child record or none, or this launch
  has none. Its intent was read as stopped. -/
  | other
  deriving DecidableEq

/-- The complete state schema refuses unknown fields, partial identity and a schema version
that is a natural number other than `stateSchema`. For a file that is decoded, one decision
gives both the state admitted and where its intent came from. The intent the file records is
kept only when the file names `stateSchema` and names the child record of this launch, which
must have one: the saved intent was then written by a viewer whose supervisor would start the
same child. In every other case the state keeps every field but its intent, which is admitted
as stopped: a file whose version does not read as `stateSchema`, because it has no
`schema_version` member or one that is not a number spelled in decimal digits alone, which is
an earlier version's file and carries no record of its child; a file whose `child` member is
absent, is not an array of strings or names another record; and any file read by a launch
that has no record. -/
def PersistedState.admit (child : Option (List String)) (value : Json.Value) :
    Except String (PersistedState × StartSource) := do
  admitVersion (stateVersion value)
  let state ← Json.decode value
    (PersistedState.fields (value.member "schema_version").isSome (value.member "child").isSome)
  return if stateVersion value = some stateSchema then
      if child.isSome ∧ stateChild value = child then (state, .saved)
      else match state.desired with
        | .running => ({ state with desired := .stopped }, .other)
        | .stopped => (state, .saved)
    else ({ state with desired := .stopped }, .earlier)

/-- The state admitted from a state file: the first component of `PersistedState.admit`, so
the state and the account of where its intent came from are one decision. -/
def PersistedState.decode (child : Option (List String)) (value : Json.Value) :
    Except String PersistedState :=
  (PersistedState.admit child value).map Prod.fst

/-- A state the decoder returns intends to stay stopped unless the file names the current
schema and the child record of this launch. -/
private theorem PersistedState.decode_stopped (child : Option (List String))
    (value : Json.Value) (state : PersistedState)
    (unbound : ¬(stateVersion value = some stateSchema ∧ child.isSome ∧
      stateChild value = child))
    (decoded : PersistedState.decode child value = .ok state) : state.desired = .stopped := by
  unfold PersistedState.decode at decoded
  cases admitted : PersistedState.admit child value with
  | error reason =>
    rw [admitted] at decoded
    exact nomatch decoded
  | ok pair =>
    rw [admitted] at decoded
    have first : pair.1 = state := Except.ok.inj decoded
    unfold PersistedState.admit at admitted
    obtain ⟨-, -, rest⟩ := Json.except_bind_ok admitted
    obtain ⟨read, -, returned⟩ := Json.except_bind_ok rest
    have result := Except.ok.inj returned
    rw [← first, ← result]
    by_cases current : stateVersion value = some stateSchema
    · by_cases same : child.isSome ∧ stateChild value = child
      · exact absurd ⟨current, same⟩ unbound
      · rw [ite_eq_left current, ite_eq_right same]
        split
        · rfl
        · assumption
    · rw [ite_eq_right current]

/-- **A state the decoder returns for a file whose version does not read as the current one
intends to stay stopped.** For every child record a launch may have, or none, every JSON value
whose `schema_version` member is absent, is not a number spelled in decimal digits alone or
spells another number, and every state the decoder returns for it. -/
theorem PersistedState.decode_earlier (child : Option (List String)) (value : Json.Value)
    (state : PersistedState) (earlier : stateVersion value ≠ some stateSchema)
    (decoded : PersistedState.decode child value = .ok state) : state.desired = .stopped :=
  PersistedState.decode_stopped child value state (fun bound => earlier bound.1) decoded

/-- **A state the decoder returns for a file that does not name this launch's child record
intends to stay stopped.** For every launch that has no child record, and every launch whose
record differs from the one the JSON value's `child` member names, or that reads a value with
no such record: every state the decoder returns for the value. -/
theorem PersistedState.decode_unbound (child : Option (List String)) (value : Json.Value)
    (state : PersistedState) (unbound : child = none ∨ stateChild value ≠ child)
    (decoded : PersistedState.decode child value = .ok state) : state.desired = .stopped := by
  refine PersistedState.decode_stopped child value state (fun bound => ?_) decoded
  rcases unbound with none | other
  · rw [none] at bound
    exact absurd bound.2.1 (by decide)
  · exact other bound.2.2

/-- **The decoder returns a running intent only under the current schema version and for this
launch's child.** For every child record a launch may have, or none, every JSON value and
every state the decoder returns for it that intends to run: the value's `schema_version`
member spells `stateSchema`, the launch has a child record, and the value's `child` member
names that record. -/
theorem PersistedState.decode_running (child : Option (List String)) (value : Json.Value)
    (state : PersistedState) (decoded : PersistedState.decode child value = .ok state)
    (running : state.desired = .running) :
    stateVersion value = some stateSchema ∧
      ∃ words, child = some words ∧ stateChild value = some words := by
  have bound :
      stateVersion value = some stateSchema ∧ child.isSome ∧ stateChild value = child :=
    Decidable.byContradiction fun unbound => by
      have stopped := PersistedState.decode_stopped child value state unbound decoded
      rw [stopped] at running
      cases running
  obtain ⟨current, recorded, same⟩ := bound
  obtain ⟨words, named⟩ := Option.isSome_iff_exists.mp recorded
  exact ⟨current, words, named, by rw [same, named]⟩

/-- **The decoder returns an error for a state file that names another schema version.** For
every child record a launch may have, or none, and every JSON value whose `schema_version`
member spells a natural number other than `stateSchema`. -/
theorem PersistedState.decode_other (child : Option (List String)) (value : Json.Value)
    (version : Nat) (named : stateVersion value = some version) (other : version ≠ stateSchema) :
    ∃ reason, PersistedState.decode child value = .error reason := by
  unfold PersistedState.decode PersistedState.admit
  rw [named]
  simp only [admitVersion, other, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- **The decoder returns an error for a state file whose schema version spells a number of
`2 ^ 64` or more.** For every child record a launch may have, or none, and every JSON value
whose `schema_version` member is a number whose spelling `Digits.read` reads as a natural
number of `2 ^ 64` or more. -/
theorem PersistedState.decode_wide (child : Option (List String)) (value : Json.Value)
    (spelling : String) (version : Nat)
    (mark : value.member "schema_version" = some (.number spelling))
    (spelled : Digits.read spelling = some version) (wide : 2 ^ 64 ≤ version) :
    ∃ reason, PersistedState.decode child value = .error reason := by
  refine PersistedState.decode_other child value version ?_ ?_
  · unfold stateVersion
    rw [mark]
    exact spelled
  · intro same
    rw [same, stateSchema] at wide
    omega

/-- Whether the viewer leaves the state file as it is until its listener is bound: a file
whose running intent was set aside, an earlier version's or one given for another child. Once
the listener is bound the bootstrap publishes the stopped state it started from, in the
current schema with this launch's record, so a start-up that fails before then leaves the next
viewer the same file and the same reason, and the file is read that way once, in the first
launch whose start-up succeeds. -/
def StartSource.kept : StartSource → Bool
  | .earlier | .other => true
  | .absent | .saved => false

/-- One line that says why the run a viewer starts with is shown stopped, and nothing when it
is not. The viewer gives it as the reason of its first control record and, when it was not
launched with `--start`, prints it once it serves its page, so a person who finds the run
stopped is told why and what starts it. -/
def startAccount (source : StartSource) (desired : Desired) : Option String :=
  match desired, source with
  | .running, _ => none
  | .stopped, .absent =>
    some ("stopped because the run directory holds no saved state; " ++
      "it starts only on a Start on the viewer's control endpoint, " ++
      "which the page's Start button sends, or the --start flag")
  | .stopped, .earlier =>
    some ("stopped because the saved state names no readable schema version, " ++
      "so its intent is not taken as a Start; " ++
      "it starts only on a Start on the viewer's control endpoint, " ++
      "which the page's Start button sends, or the --start flag")
  | .stopped, .saved =>
    some ("stopped because the saved state says stopped; " ++
      "it starts only on a Start on the viewer's control endpoint, " ++
      "which the page's Start button sends, or the --start flag")
  | .stopped, .other =>
    some ("stopped because the saved running intent was given for another child than this " ++
      "launch starts, or for one that cannot be shown to be the same, " ++
      "so it is not taken as a Start; " ++
      "it starts only on a Start on the viewer's control endpoint, " ++
      "which the page's Start button sends, or the --start flag")

/-- Absence, refusal and successful restore require distinct caller branches. -/
inductive StateRead where
  /-- The run directory holds no entry named state.json. -/
  | missing
  /-- IO, syntax or schema refused the prior file, an entry that cannot be opened included. -/
  | refused (reason : String)
  /-- The complete state was admitted, with where its intent came from
  (`PersistedState.admit`). -/
  | restored (state : PersistedState) (source : StartSource)

private def stateBytes (handle : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  let chunk ← handle.read (min (remaining + 1) 4096).toUSize
  if _empty : chunk.size = 0 then return bytes
  else if _fits : chunk.size ≤ remaining then
    stateBytes handle (remaining - chunk.size) (bytes ++ chunk)
  else throw (IO.userError "viewer state exceeds 4096 bytes")
termination_by remaining

/-- A bounded read preserves the distinction between missing and malformed state. Only the
absence of the directory entry, which `System.FilePath.symlinkMetadata` reads without
following a symbolic link, is a missing state. An entry that exists is opened only when it is
a regular file, or a symbolic link that leads to one (`System.FilePath.metadata` follows
links): anything else, such as a link whose target is gone, a directory, a pipe or a device,
is refused before it is opened, so the read never waits on an entry that cannot supply a
finite document. The two looks and the open are separate calls, so this rests on the run
directory's stable-path assumption like the rest of the reader. -/
def RunDirectory.readState (directory : RunDirectory) (child : Option (List String)) :
    IO StateRead := do
  try discard (directory.path .state).symlinkMetadata
  catch error =>
    match error with
    | .noFileOrDirectory _ _ _ => return .missing
    | _ => return .refused error.toString
  let kind ← try pure (← (directory.path .state).metadata).type
    catch error => return .refused error.toString
  unless kind == .file do return .refused "state.json is not a regular file"
  let handle ← try directory.openRead .state
    catch error => return .refused error.toString
  try
    let bytes ← stateBytes handle 4096 ByteArray.empty
    let some text := String.fromUTF8? bytes | return .refused "invalid state UTF-8"
    match Json.parse text with
    | .error reason => return .refused reason
    | .ok value =>
      match PersistedState.admit child value with
      | .error reason => return .refused reason
      | .ok (state, source) => return .restored state source
  catch error => return .refused error.toString

/-- Exclusive temporary creation prevents truncating a file owned by another pending writer.
Only successful complete writing and flushing can reach the rename publication. -/
def RunDirectory.writeState (directory : RunDirectory) (child : Option (List String))
    (state : PersistedState) : IO Unit :=
  directory.publishBytes .state (state.encode child).toUTF8

end Acorn.Host.Viewer
