/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentArguments

/-!
# Native full-agent consumer

This diagnostic entry admits the full feature-size domain and calls the actual
initialization, finite-prefix transition and current observation definitions.
Caller-supplied words provide raw sensory and feedback inputs; output records
execution. The application CLI and delivered IO have separate owners.
-/
namespace Acorn.AgentDriver
open Features Handcrafted

/-- Native execution consumes the exact proved prefix and observation owners. -/
@[noinline] def execute (construction : AgentConstruction) (words : List UInt64) : String :=
  match construction.execute (words.map (Host.AgentArguments.input construction)) with
  | .error .unsupportedProfile => "refused unsupported restore profile"
  | .ok (state, stopped) =>
    let observed := state.observe
    let action := observed.decision.map (·.action.val)
    s!"clock={observed.clock} action={action} gain={observed.gain.value.bits} stopped={stopped}"

/-- Complete immutable native configuration is checked before allocating learner storage. -/
def dispatch (arguments : List String) : Option String := do
  let (construction, words) ← Host.AgentArguments.admit arguments
  return execute construction words

end Acorn.AgentDriver

/-- Native admission/output failures cannot produce a false success status. -/
def main (arguments : List String) : IO UInt32 := do
  try
    match Acorn.AgentDriver.dispatch arguments with
    | some output => IO.println output; return 0
    | none =>
      IO.eprintln "usage: agent-native SEED EXPONENT TILINGS UNITS MODE CREDIT RATE SUBTASKS CRITERION PLANNING [RAW_WORD ...]"
      return 2
  catch error =>
    try IO.eprintln s!"agent-native: {error}" catch _ => pure ()
    return 1
