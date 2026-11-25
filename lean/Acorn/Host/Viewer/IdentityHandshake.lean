import Acorn.Host.Viewer.PersistedState

namespace Acorn.Host.Viewer

structure CoreIdentity where
  identity : Identity
  newOrigin : Option NewAgentOrigin
  deriving DecidableEq, BEq

def coreIdentityFromJson (value : Acorn.Json.Value) : Except String CoreIdentity := do
  let run ← runWord (← jsonField value "run_id")
  let seed ← jsonWord (← jsonField value "seed")
  let epoch ← jsonWord (← jsonField value "agent_epoch")
  let origin ← (← jsonField value "origin").text
  let newOrigin ← match origin with
    | "resumed" => pure none
    | "fresh" => pure (some NewAgentOrigin.fresh)
    | "cleared" => pure (some NewAgentOrigin.cleared)
    | _ => throw "unknown core identity origin"
  return ⟨⟨run, seed, epoch⟩, newOrigin⟩

def coreIdentity (text : WireText) : Except String CoreIdentity :=
  Acorn.Json.parse text.val >>= coreIdentityFromJson

def PersistedState.adopt (state : PersistedState) (actual : CoreIdentity) : PersistedState :=
  { state with identity := actual.identity, origin := actual.newOrigin.getD state.origin }

theorem PersistedState.adopt_desired (state : PersistedState) (actual : CoreIdentity) :
    (state.adopt actual).desired = state.desired := rfl

end Acorn.Host.Viewer
