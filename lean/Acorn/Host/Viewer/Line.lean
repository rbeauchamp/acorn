import Init
import Acorn.Host.Forever

namespace Acorn.Host.Viewer

def lineCapacity : Nat := 1048576

structure LineBytes where
  bytes : ByteArray
  bounded : bytes.size ≤ lineCapacity

def LineBytes.empty : LineBytes := ⟨ByteArray.empty, by decide⟩

inductive LineDecoder where
  | reading (line : LineBytes)
  | discarding

inductive LineResult where
  | line (value : LineBytes)
  | oversized

def LineBytes.append (line : LineBytes) (byte : UInt8) : Option LineBytes :=
  if h : line.bytes.size < lineCapacity then
    some ⟨line.bytes.push byte, by simp only [ByteArray.size_push]; omega⟩
  else none

def LineDecoder.step (decoder : LineDecoder) (byte : UInt8) : LineDecoder × Option LineResult :=
  match decoder with
  | .discarding =>
    if byte == 10 then (.reading .empty, some .oversized) else (.discarding, none)
  | .reading line =>
    if byte == 10 then (.reading .empty, some (.line line))
    else match line.append byte with
      | some next => (.reading next, none)
      | none => (.discarding, none)

def LineDecoder.finish : LineDecoder → Option LineResult
  | .discarding => some .oversized
  | .reading line => if line.bytes.isEmpty then none else some (.line line)

theorem LineDecoder.discard_suffix (byte : UInt8) (notDelimiter : byte ≠ 10) :
    LineDecoder.discarding.step byte = (.discarding, none) := by
  simp [step, notDelimiter]

theorem LineDecoder.delimiter_resets (decoder : LineDecoder) :
    (decoder.step 10).1 = .reading .empty := by cases decoder <;> rfl

theorem LineBytes.append_exact (line next : LineBytes) (byte : UInt8)
    (accepted : line.append byte = some next) : next.bytes = line.bytes.push byte := by
  unfold append at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

def readLines (input : IO.FS.Stream) (consume : LineResult → IO Unit) : IO Unit := do
  let mut decoder := LineDecoder.reading .empty
  for _ in forever do
    let chunk ← input.read 1
    if chunk.isEmpty then
      if let some result := decoder.finish then consume result
      return
    for byte in chunk do
      let (next, result) := decoder.step byte
      decoder := next
      if let some result := result then consume result

end Acorn.Host.Viewer
