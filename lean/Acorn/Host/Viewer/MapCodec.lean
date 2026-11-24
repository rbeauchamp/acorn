import Acorn.Host.Viewer.WorldMemory
import Acorn.Host.Viewer.PersistedState

namespace Acorn.Host.Viewer

def mapHeaderCapacity : Nat := 1024

def mapFileCapacity : Nat := mapHeaderCapacity + 1 + 3 * mapSideCapacity * mapSideCapacity

structure MapRun (bytes : ByteArray) (start : Nat) (inside : start < bytes.size) where
  count : Nat
  positive : 0 < count
  countBound : count ≤ 65535
  fits : start + count ≤ bytes.size
  same : ∀ offset, (bound : offset < count) →
    bytes[start + offset]'(by omega) = bytes[start]

private def extendRun (bytes : ByteArray) (start : Nat) (inside : start < bytes.size)
    (run : MapRun bytes start inside) : MapRun bytes start inside :=
  if room : run.count < 65535 ∧ start + run.count < bytes.size then
    if same : bytes[start + run.count] = bytes[start] then
      extendRun bytes start inside ⟨run.count + 1, by have := run.positive; omega,
        by omega, by omega, by
          intro offset bound
          by_cases last : offset = run.count
          · subst offset; exact same
          · exact run.same offset (by omega)⟩
    else run
  else run
termination_by 65535 - run.count

def mapRunAt (bytes : ByteArray) (start : Nat) (inside : start < bytes.size) :
    MapRun bytes start inside :=
  extendRun bytes start inside ⟨1, by decide, by decide, by omega, by
    intro offset bound
    have : offset = 0 := by omega
    subst offset
    rfl⟩

private def encodeRuns (bytes : ByteArray) (start : Nat) (out : ByteArray) : ByteArray :=
  if h : start < bytes.size then
    let value := bytes[start]
    let run := mapRunAt bytes start h
    have positive := run.positive
    encodeRuns bytes (start + run.count)
      (((out.push value).push (run.count % 256).toUInt8).push (run.count / 256).toUInt8)
  else out
termination_by bytes.size - start
decreasing_by
  have := (mapRunAt bytes start h).positive
  omega

def encodeMapRuns (bytes : ByteArray) : ByteArray := encodeRuns bytes 0 ByteArray.empty

private theorem encodeRuns_size (bytes : ByteArray) (start : Nat) (out : ByteArray) :
    (encodeRuns bytes start out).size ≤ out.size + 3 * (bytes.size - start) ∧
    (encodeRuns bytes start out).size % 3 = out.size % 3 := by
  unfold encodeRuns
  split
  · rename_i inside
    dsimp only
    have positive := (mapRunAt bytes start inside).positive
    have fits := (mapRunAt bytes start inside).fits
    have next := encodeRuns_size bytes (start + (mapRunAt bytes start inside).count)
      (((out.push bytes[start]).push ((mapRunAt bytes start inside).count % 256).toUInt8).push
        ((mapRunAt bytes start inside).count / 256).toUInt8)
    simp only [ByteArray.size_push] at next
    constructor <;> omega
  · constructor <;> omega
termination_by bytes.size - start

theorem encodeMapRuns_shape (bytes : ByteArray) :
    (encodeMapRuns bytes).size ≤ 3 * bytes.size ∧ (encodeMapRuns bytes).size % 3 = 0 := by
  simpa only [encodeMapRuns, ByteArray.size_empty, Nat.zero_add, Nat.sub_zero, Nat.zero_mod]
    using encodeRuns_size bytes 0 ByteArray.empty

theorem map_run_count_roundtrip (count : Nat) (bound : count < 65536) :
    (count % 256).toUInt8.toNat + 256 * (count / 256).toUInt8.toNat = count := by
  change count % 256 % 256 + 256 * (count / 256 % 256) = count
  omega

private def decodeRuns (bytes : ByteArray) (expected start : Nat)
    (out : {bytes : ByteArray // bytes.size ≤ expected}) : Except String ByteArray :=
  if finished : start = bytes.size then
    if out.val.size = expected then .ok out.val else .error "short retained map"
  else if triple : start + 2 < bytes.size then do
    let value := bytes[start]
    unless value.toNat < 8 || value == 255 do throw "invalid retained terrain byte"
    let count := bytes[start + 1].toNat + 256 * bytes[start + 2].toNat
    if fits : out.val.size + count ≤ expected then
      let expanded := out.val ++ ⟨Array.replicate count value⟩
      have bounded : expanded.size ≤ expected := by
        change (out.val ++ (⟨Array.replicate count value⟩ : ByteArray)).size ≤ expected
        rw [ByteArray.size_append]
        change out.val.size + (Array.replicate count value).size ≤ expected
        simpa only [Array.size_replicate] using fits
      decodeRuns bytes expected (start + 3) ⟨expanded, bounded⟩
    else throw "retained map run exceeds world size"
  else .error "truncated retained map triple"
termination_by bytes.size - start

def decodeMapRuns (key : MapKey) (bytes : ByteArray) : Except String (MapBytes key) := do
  let decoded ← decodeRuns bytes (key.side.val * key.side.val) 0 ⟨ByteArray.empty, by simp⟩
  MapBytes.admit key decoded

private def base64Digit (digit : Nat) : UInt8 :=
  (if digit < 26 then 65 + digit else if digit < 52 then 97 + digit - 26
    else if digit < 62 then 48 + digit - 52 else if digit = 62 then 43 else 47).toUInt8

def mapRunsBase64 (runs : ByteArray) : Except String String := do
  unless runs.size % 3 == 0 do throw "incomplete RLE base64 group"
  let mut out := ByteArray.empty
  for start in [0:runs.size:3] do
    if h : start + 2 < runs.size then
      let a := runs[start].toNat
      let b := runs[start + 1].toNat
      let c := runs[start + 2].toNat
      out := (((out.push (base64Digit (a / 4))).push (base64Digit (a % 4 * 16 + b / 16))).push
        (base64Digit (b % 16 * 4 + c / 64))).push (base64Digit (c % 64))
  let some text := String.fromUTF8? out | throw "invalid base64 alphabet"
  return text

private def mapHeader (key : MapKey) (memory : WorldMemory key) (wire : Bool) : String :=
  (if wire then "{\"map\":true,\"runId\":\"" else "{\"run_id\":\"") ++ runHex key.run ++
  "\",\"side\":" ++ toString key.side.val ++ ",\"seed\":" ++ toString key.seed ++
  ",\"seen\":" ++ toString memory.seen ++ ",\"partial\":" ++
  (if memory.isIncomplete then "true" else "false")

def WorldMemory.encode {key : MapKey} (memory : WorldMemory key) : ByteArray :=
  (mapHeader key memory false ++ "}\n").toUTF8 ++ encodeMapRuns memory.observations.bytes

def WorldMemory.frame {key : MapKey} (memory : WorldMemory key) : Except String
    (SseLine (4 * mapSideCapacity * mapSideCapacity + 1024)) := do
  let kinds ← mapRunsBase64 (encodeMapRuns memory.observations.bytes)
  let some frame := sseLine _ (mapHeader key memory true ++ ",\"kinds\":\"" ++ kinds ++ "\"}")
    | throw "retained map exceeds wire limit"
  return frame

private def decodeHeader (value : Json.Value) (identity : Identity) : Except String MapKey :=
  Json.decode value do
    let run ← runWord (← Json.take "run_id")
    let side ← (← Json.take "side").natural
    let seed ← jsonWord (← Json.take "seed")
    let _seen ← (← Json.take "seen").natural
    let _partial ← jsonBool (← Json.take "partial")
    unless run == identity.run && seed == identity.seed do throw "foreign retained map"
    if bound : 0 < side ∧ side ≤ mapSideCapacity then
      return ⟨run, seed, ⟨side, bound⟩⟩
    else throw "retained map side exceeds admission range"

def decodeMap (identity : Identity) (bytes : ByteArray) : Except String
    ((key : MapKey) × WorldMemory key) := do
  unless bytes.size ≤ mapFileCapacity do throw "retained map file exceeds byte limit"
  let mut delimiter := none
  for index in [:min bytes.size (mapHeaderCapacity + 1)] do
    if h : index < bytes.size then
      if bytes[index] == 10 then
        delimiter := some index
        break
  let some splitAt := delimiter | throw "missing or oversized retained map header"
  let some header := String.fromUTF8? (bytes.extract 0 splitAt) | throw "invalid map header UTF-8"
  let key ← Json.parse header >>= (decodeHeader · identity)
  let cells ← decodeMapRuns key (bytes.extract (splitAt + 1) bytes.size)
  return ⟨key, WorldMemory.restore key cells⟩

inductive MapRead where
  | missing
  | refused (reason : String)
  | restored (key : MapKey) (memory : WorldMemory key)

private def readMapBytes (handle : IO.FS.Handle) (remaining : Nat)
    (bytes : ByteArray) : IO ByteArray := do
  let chunk ← handle.read (min (remaining + 1) 65536).toUSize
  if _empty : chunk.size = 0 then return bytes
  else if _fits : chunk.size ≤ remaining then
    readMapBytes handle (remaining - chunk.size) (bytes ++ chunk)
  else throw (IO.userError "retained map exceeds file byte limit")
termination_by remaining

def RunDirectory.readMap (directory : RunDirectory) (identity : Identity) : IO MapRead := do
  let handle ← try directory.openRead .explored
    catch error =>
      match error with
      | .noFileOrDirectory _ _ _ => return .missing
      | _ => return .refused error.toString
  try
    match decodeMap identity (← readMapBytes handle mapFileCapacity ByteArray.empty) with
    | .error reason => return .refused reason
    | .ok ⟨key, memory⟩ => return .restored key memory
  catch error => return .refused error.toString

def RunDirectory.writeMap (directory : RunDirectory) {key : MapKey}
    (memory : WorldMemory key) : IO Unit :=
  directory.publishBytes .explored memory.encode

end Acorn.Host.Viewer
