import Acorn.Host.AgentArguments

namespace Acorn.AgentDriver
open Features Handcrafted

@[noinline] def execute (admitted : DefaultConstruction) (words : List UInt64) : String :=
  let (state, stopped) := AgentConstruction.execute admitted
    (words.map (Host.AgentArguments.input admitted.construction))
  let observed := state.agent.observe
  let action := observed.decision.map (·.action.val)
  s!"clock={observed.clock} action={action} gain={observed.gain.value.bits} stopped={stopped}"

def dispatch (arguments : List String) : Option String := do
  let (construction, words) ← Host.AgentArguments.admit arguments
  return execute construction words

end Acorn.AgentDriver

def _root_.Acorn.AgentDriver.main (arguments : List String) : IO UInt32 := do
  try
    match Acorn.AgentDriver.dispatch arguments with
    | some output => IO.println output; return 0
    | none =>
      IO.eprintln ("usage: agent-native SEED EXPONENT TILINGS UNITS MODE CREDIT RATE " ++
        s!"SUBTASKS CRITERION PLANNING [RAW_WORD ...]\n{Acorn.Digits.usage}")
      return 2
  catch error =>
    try IO.eprintln s!"agent-native: {error}" catch _ => pure ()
    return 1
