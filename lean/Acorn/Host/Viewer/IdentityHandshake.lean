/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.PersistedState

/-!
# Checkpoint-selected process identity

A process's first identity-bearing telemetry record supplies the checkpoint
outcome selected by the actual core. The supervisor persists that identity
before releasing its bounded pending observation suffix. Once admitted, the
same process cannot switch identity. Syntax and exact numeric decoding precede
this handshake; native core authenticity remains the owned-child boundary.
-/
namespace Acorn.Host.Viewer

/-- Identity facts supplied by one parsed core record. -/
structure CoreIdentity where
  /-- Run, world and logical agent identity. -/
  identity : Identity
  /-- Resumed construction preserves the saved fresh-origin provenance. -/
  newOrigin : Option NewAgentOrigin
  deriving DecidableEq, BEq

/-- Exact required fields identify the actual construction outcome. -/
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

/-- Identity comes from the exact bounded record whose publication is pending. -/
def coreIdentity (text : WireText) : Except String CoreIdentity :=
  Acorn.Json.parse text.val >>= coreIdentityFromJson

/-- Installing the actual core outcome changes no durable operator intent. -/
def PersistedState.adopt (state : PersistedState) (actual : CoreIdentity) : PersistedState :=
  { state with identity := actual.identity, origin := actual.newOrigin.getD state.origin }

/-- A checkpoint identity handshake cannot start or stop a process. -/
theorem PersistedState.adopt_desired (state : PersistedState) (actual : CoreIdentity) :
    (state.adopt actual).desired = state.desired := rfl

end Acorn.Host.Viewer
