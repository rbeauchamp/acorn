/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentArguments
import Acorn.Host.Checkpoint.IO

/-!
# Native checkpoint consumer

The diagnostic entry exercises the actual current agent, file writer, receiver
admission and restoration. It admits every current construction through the
shared native parser. It creates no study or scientific execution receipt;
application CLI integration remains the final program's owner.
-/
namespace Acorn.Host.CheckpointDriver
open Features Handcrafted Checkpoint

/-- The complete native persistence command domain. -/
inductive Command where
  /-- Save the supplied finite prefix from cold initialization. -/
  | save
  /-- Load and report the durable projection without advancing the learner. -/
  | load
  /-- Load, consume the supplied prefix and atomically save its next durable image. -/
  | resume

/-- Unknown operations cannot reach file IO. -/
def command : String → Option Command
  | "save" => some .save
  | "load" => some .load
  | "resume" => some .resume
  | _ => none

/-- Refusals remain explicit at the native process boundary. -/
def checked {α : Type} (result : Except Checkpoint.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"checkpoint refused: {repr error}")

/-- Every diagnostic input reaches the existing finite-prefix transition, with no alternate
evaluator. That transition is the step of the default order, and the type of the
construction says so. -/
def advance (admitted : DefaultConstruction) (state : admitted.construction.State)
    (words : List UInt64) : IO admitted.construction.State := do
  match admitted.runPrefix state (words.map (AgentArguments.input admitted.construction)) with
  | .ok (next, _) => return next
  | .error .unsupportedProfile => throw (IO.userError "agent prefix refused unsupported restoration")

/-- The invoked process owns the writer; load always binds to the admitted receiver.
The receiver is a construction of the default step order: `advance` runs that order's
step, so every image this entry saves holds the order of the steps that produced it,
and every image it loads was saved under that order. -/
@[noinline] def execute (operation : Command) (path : System.FilePath)
    (admitted : DefaultConstruction) (words : List UInt64) : IO String := do
  let store ← Store.new ((← IO.appDir) / "checkpoint-sync")
  let initial := admitted.construction.initial
  let state ← match operation with
    | .save =>
      let state ← advance admitted initial words
      let _ ← checked (← store.save admitted.construction state path)
      pure state
    | .load =>
      unless words.isEmpty do throw (IO.userError "load accepts no transition words; use resume")
      checked (← loadFile admitted.construction initial path)
    | .resume =>
      let restored ← checked (← loadFile admitted.construction initial path)
      let state ← advance admitted restored words
      let _ ← checked (← store.save admitted.construction state path)
      pure state
  return s!"checkpoint format={formatVersion} process={store.processId} clock={state.agent.clock} gain={state.agent.control.average.rate.value.bits}"

/-- All native arguments are admitted before file allocation or replacement. -/
def dispatch (arguments : List String) : IO UInt32 := do
  match arguments with
  | operation :: path :: arguments =>
    let some operation := command operation | throw (IO.userError "unknown checkpoint operation")
    let some (admitted, words) := AgentArguments.admit arguments
      | throw (IO.userError "invalid checkpoint construction or input word")
    IO.println (← execute operation path admitted words)
    return 0
  | _ => throw (IO.userError
      "usage: checkpoint-native (save|load|resume) FILE SEED EXPONENT TILINGS UNITS MODE CREDIT RATE SUBTASKS CRITERION PLANNING [RAW_WORD ...]")

end Acorn.Host.CheckpointDriver

/-- Native IO or admission failure produces a failing exit status. -/
def main (arguments : List String) : IO UInt32 := do
  try Acorn.Host.CheckpointDriver.dispatch arguments
  catch error =>
    try IO.eprintln s!"checkpoint-native: {error}" catch _ => pure ()
    return 1
