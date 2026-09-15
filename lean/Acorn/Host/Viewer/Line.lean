/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# Bounded incremental pipe admission

Input is bounded while bytes arrive, before UTF-8 or JSON decoding. An oversized
line is discarded through its newline, so a suffix cannot be mistaken for a new
record. EOF does not publish an incomplete oversized record. Native readers must
use bounded chunks rather than an unbounded `getLine` allocation.
-/
namespace Acorn.Host.Viewer

/-- Maximum admitted telemetry line, excluding its delimiter, in bytes. -/
def lineCapacity : Nat := 1048576

/-- The retained input byte length is bounded at every constructor and byte write. -/
structure LineBytes where
  /-- Exact input bytes; strict UTF-8 admission is a separate operation. -/
  bytes : ByteArray
  /-- Storage cannot exceed the fixed pipe protocol limit. -/
  bounded : bytes.size ≤ lineCapacity

/-- Empty input owns no decoded or partially decoded record. -/
def LineBytes.empty : LineBytes := ⟨ByteArray.empty, by decide⟩

/-- Oversized input has no retained payload while its suffix is discarded. -/
inductive LineDecoder where
  /-- Bounded bytes of the current line. -/
  | reading (line : LineBytes)
  /-- Ignore bytes until the next delimiter. -/
  | discarding

/-- A completed delimiter reports either a whole bounded line or an oversize refusal. -/
inductive LineResult where
  /-- Complete input, still requiring strict UTF-8 and schema admission. -/
  | line (value : LineBytes)
  /-- Exactly one refusal for an oversized line. -/
  | oversized

/-- Append only with a proof that the new byte fits. -/
def LineBytes.append (line : LineBytes) (byte : UInt8) : Option LineBytes :=
  if h : line.bytes.size < lineCapacity then
    some ⟨line.bytes.push byte, by simp only [ByteArray.size_push]; omega⟩
  else none

/-- One byte either extends the bounded line, terminates it, or discards an oversize suffix. -/
def LineDecoder.step (decoder : LineDecoder) (byte : UInt8) : LineDecoder × Option LineResult :=
  match decoder with
  | .discarding =>
    if byte == 10 then (.reading .empty, some .oversized) else (.discarding, none)
  | .reading line =>
    if byte == 10 then (.reading .empty, some (.line line))
    else match line.append byte with
      | some next => (.reading next, none)
      | none => (.discarding, none)

/-- EOF may finish a nonempty final line; empty input creates no extra record. -/
def LineDecoder.finish : LineDecoder → Option LineResult
  | .discarding => some .oversized
  | .reading line => if line.bytes.isEmpty then none else some (.line line)

/-- Discarded suffixes cannot be promoted into records before their delimiter. -/
theorem LineDecoder.discard_suffix (byte : UInt8) (notDelimiter : byte ≠ 10) :
    LineDecoder.discarding.step byte = (.discarding, none) := by
  simp [step, notDelimiter]

/-- Every delimiter restores a fresh bounded input state. -/
theorem LineDecoder.delimiter_resets (decoder : LineDecoder) :
    (decoder.step 10).1 = .reading .empty := by cases decoder <;> rfl

/-- Every successful byte write preserves the exact input prefix. -/
theorem LineBytes.append_exact (line next : LineBytes) (byte : UInt8)
    (accepted : line.append byte = some next) : next.bytes = line.bytes.push byte := by
  unfold append at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

/-- The native pipe reader retains one bounded line and one input byte.
Lean 4.33.0's Handle.read uses buffered C fread (runtime/io.cpp, lines 555–577);
a multi-byte request can wait past a newline for a full request or EOF. Reading
one byte makes a delivered output delimiter sufficient for dispatch. C stdio still owns its internal input buffering.
The callback must enqueue locally; network delivery belongs to a separate task.
IO failure propagates to the owning process pump instead of manufacturing EOF. -/
def readLines (input : IO.FS.Stream) (consume : LineResult → IO Unit) : IO Unit := do
  let mut decoder := LineDecoder.reading .empty
  repeat
    let chunk ← input.read 1
    if chunk.isEmpty then
      if let some result := decoder.finish then consume result
      return
    for byte in chunk do
      let (next, result) := decoder.step byte
      decoder := next
      if let some result := result then consume result

end Acorn.Host.Viewer
