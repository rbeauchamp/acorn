import Acorn.Host.Viewer.RunDirectory
import Acorn.Host.Viewer.Wire
import Acorn.Rng

namespace Acorn.Host.Viewer

inductive NewAgentOrigin where
  | fresh
  | cleared
  deriving DecidableEq, BEq

def NewAgentOrigin.tag : NewAgentOrigin → String
  | .fresh => "fresh"
  | .cleared => "cleared"

structure PersistedState where
  identity : Identity
  desired : Desired
  origin : NewAgentOrigin
  processStarted : Bool
  deriving DecidableEq, BEq

def Desired.tag : Desired → String
  | .running => "running"
  | .stopped => "stopped"

def runHex (word : UInt64) : String :=
  String.ofList ((List.range 16).reverse.map fun index =>
    let digit := word.toNat / 16 ^ index % 16
    Char.ofNat (if digit < 10 then 48 + digit else 87 + digit))

def stateSchema : Nat := 2

def PersistedState.unstarted (seed : UInt64) (migrated : Bool) : PersistedState :=
  ⟨⟨seed, seed, 0⟩, .stopped, .fresh, migrated⟩

def childWordAdmitted (word : String) : Bool :=
  word.toList.all fun c => ' ' ≤ c && c ≤ '~' && c != '"' && c != '\\'

def childBudget : Nat := 2048

def childAdmitted (words : List String) : Bool :=
  !words.isEmpty && words.all childWordAdmitted &&
    words.foldl (fun total word => total + word.length + 3) 0 ≤ childBudget

def fileDigest (content : ByteArray) : UInt64 :=
  content.foldl Rng.fnvStep Rng.fnvOffset

structure ProgramReading where
  length : Nat
  digest : UInt64
  deriving DecidableEq, BEq

def ProgramReading.of (content : ByteArray) : ProgramReading :=
  ⟨content.size, fileDigest content⟩

def childRecord (executable : String) (reading : ProgramReading) (arguments : List String) :
    Option (List String) :=
  let words := executable :: toString reading.length :: toString reading.digest :: arguments
  if childAdmitted words then some words else none

def childText : Option (List String) → String
  | some words =>
    if childAdmitted words then
      "[" ++ ",".intercalate (words.map fun word => "\"" ++ word ++ "\"") ++ "]"
    else "null"
  | none => "null"

def PersistedState.encode (child : Option (List String)) (state : PersistedState) : String :=
  "{\"schema_version\":" ++ toString stateSchema ++
  ",\"seed\":" ++ toString state.identity.seed ++
  ",\"desired\":\"" ++ state.desired.tag ++
  "\",\"run_id\":\"" ++ runHex state.identity.run ++
  "\",\"agent_epoch\":" ++ toString state.identity.agentEpoch ++
  ",\"origin\":\"" ++ state.origin.tag ++
  "\",\"process_started\":" ++ (if state.processStarted then "true" else "false") ++
  ",\"child\":" ++ childText child ++ "}\n"

def stateVersion (value : Json.Value) : Option Nat :=
  (value.member "schema_version").bind fun mark =>
    match mark with
    | .number spelling => Digits.read spelling
    | _ => none

def stateChild (value : Json.Value) : Option (List String) :=
  (value.member "child").bind fun mark =>
    match mark with
    | .array words =>
      words.mapM fun word =>
        match word with
        | .string text => some text
        | _ => none
    | _ => none

def admitVersion : Option Nat → Except String Unit
  | some version =>
    if version = stateSchema then .ok ()
    else .error (s!"schema_version {version} is not {stateSchema}; a state file another " ++
      "version wrote is neither guessed at nor overwritten")
  | none => .ok ()

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

inductive StartSource where
  | absent
  | earlier
  | saved
  | other
  deriving DecidableEq

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

def PersistedState.decode (child : Option (List String)) (value : Json.Value) :
    Except String PersistedState :=
  (PersistedState.admit child value).map Prod.fst

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

theorem PersistedState.decode_earlier (child : Option (List String)) (value : Json.Value)
    (state : PersistedState) (earlier : stateVersion value ≠ some stateSchema)
    (decoded : PersistedState.decode child value = .ok state) : state.desired = .stopped :=
  PersistedState.decode_stopped child value state (fun bound => earlier bound.1) decoded

theorem PersistedState.decode_unbound (child : Option (List String)) (value : Json.Value)
    (state : PersistedState) (unbound : child = none ∨ stateChild value ≠ child)
    (decoded : PersistedState.decode child value = .ok state) : state.desired = .stopped := by
  refine PersistedState.decode_stopped child value state (fun bound => ?_) decoded
  rcases unbound with none | other
  · rw [none] at bound
    exact absurd bound.2.1 (by decide)
  · exact other bound.2.2

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

theorem PersistedState.decode_other (child : Option (List String)) (value : Json.Value)
    (version : Nat) (named : stateVersion value = some version) (other : version ≠ stateSchema) :
    ∃ reason, PersistedState.decode child value = .error reason := by
  unfold PersistedState.decode PersistedState.admit
  rw [named]
  simp only [admitVersion, other, ↓reduceIte]
  exact ⟨_, rfl⟩

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

def StartSource.kept : StartSource → Bool
  | .earlier | .other => true
  | .absent | .saved => false

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

inductive StateRead where
  | missing
  | refused (reason : String)
  | restored (state : PersistedState) (source : StartSource)

private def stateBytes (handle : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  let chunk ← handle.read (min (remaining + 1) 4096).toUSize
  if _empty : chunk.size = 0 then return bytes
  else if _fits : chunk.size ≤ remaining then
    stateBytes handle (remaining - chunk.size) (bytes ++ chunk)
  else throw (IO.userError "viewer state exceeds 4096 bytes")
termination_by remaining

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

def RunDirectory.writeState (directory : RunDirectory) (child : Option (List String))
    (state : PersistedState) : IO Unit :=
  directory.publishBytes .state (state.encode child).toUTF8

end Acorn.Host.Viewer
