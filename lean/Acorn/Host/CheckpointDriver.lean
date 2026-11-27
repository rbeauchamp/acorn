import Acorn.Host.AgentArguments
import Acorn.Host.Checkpoint.IO

namespace Acorn.Host.CheckpointDriver
open Features Handcrafted Checkpoint

inductive Command where
  | save
  | load
  | resume

def command : String → Option Command
  | "save" => some .save
  | "load" => some .load
  | "resume" => some .resume
  | _ => none

def checked {α : Type} (result : Except Checkpoint.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"checkpoint refused: {repr error}")

def advance (admitted : DefaultConstruction) (state : admitted.construction.State)
    (words : List UInt64) : admitted.construction.State :=
  (admitted.runPrefix state (words.map (AgentArguments.input admitted.construction))).1

@[noinline] def execute (operation : Command) (path : System.FilePath)
    (admitted : DefaultConstruction) (words : List UInt64) : IO String := do
  let store ← Store.new ((← IO.appDir) / "checkpoint-sync")
  let initial := admitted.construction.initial
  let state ← match operation with
    | .save =>
      let state := advance admitted initial words
      let _ ← checked (← store.save admitted.construction state path)
      pure state
    | .load =>
      unless words.isEmpty do throw (IO.userError "load accepts no transition words; resume takes them")
      checked (← loadFile admitted.construction initial path)
    | .resume =>
      let restored ← checked (← loadFile admitted.construction initial path)
      let state := advance admitted restored words
      let _ ← checked (← store.save admitted.construction state path)
      pure state
  return s!"checkpoint format={formatVersion} process={store.processId} clock={state.agent.clock} gain={state.agent.control.average.rate.value.bits}"

def dispatch (arguments : List String) : IO UInt32 := do
  match arguments with
  | operation :: path :: arguments =>
    let some operation := command operation | throw (IO.userError "unknown checkpoint operation")
    let some (admitted, words) := AgentArguments.admit arguments
      | throw (IO.userError "invalid checkpoint construction or input word")
    IO.println (← execute operation path admitted words)
    return 0
  | _ => throw (IO.userError ("usage: checkpoint-native (save|load|resume) FILE SEED EXPONENT " ++
      "TILINGS UNITS MODE CREDIT RATE SUBTASKS CRITERION PLANNING [RAW_WORD ...]\n" ++
      Digits.usage))

end Acorn.Host.CheckpointDriver

def _root_.Acorn.Host.CheckpointDriver.main (arguments : List String) : IO UInt32 := do
  try Acorn.Host.CheckpointDriver.dispatch arguments
  catch error =>
    try IO.eprintln s!"checkpoint-native: {error}" catch _ => pure ()
    return 1
