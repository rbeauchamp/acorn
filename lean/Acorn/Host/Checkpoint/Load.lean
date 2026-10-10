/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission

/-!
# Loading a state of a construction

The loader admits a candidate image from the bytes and installs it with the receiver's own
restore, which replaces every field of the agent. The state it returns holds the proof that
the construction's loader admitted its image, so a loaded state is a state the
construction reaches (`AgentConstruction.Reached.loaded`). A refusal returns no state.
-/
namespace Acorn.Checkpoint
open Features Handcrafted

/-- Only the successful candidate branch invokes the receiver's restore. -/
@[noinline] def load (construction : AgentConstruction) (receiver : construction.State)
    (bytes : List UInt8) : Except Error construction.State :=
  match admitted : loadCandidate construction bytes with
  | .error error => .error error
  | .ok image =>
    match receiver.restore image ⟨bytes, admitted⟩ with
    | none => .error .unsupportedPolicy
    | some restored => .ok restored

/-- **A loaded state is the receiver restored from an admitted candidate.** For every
construction, receiver, byte list and state: when `load` returns the state, the loader
admitted an image of the construction from those bytes, and the state is the receiver's
own restore of that image. -/
theorem load_candidate (construction : AgentConstruction) (receiver restored : construction.State)
    (bytes : List UInt8) (loaded : load construction receiver bytes = .ok restored) :
    ∃ (image : construction.Image) (admitted : loadCandidate construction bytes = .ok image),
      receiver.restore image ⟨bytes, admitted⟩ = some restored := by
  unfold load at loaded
  split at loaded
  · cases loaded
  · rename_i image admitted
    split at loaded
    · cases loaded
    · rename_i state installed
      cases loaded
      exact ⟨image, admitted, installed⟩

/-- An explicit return of the unchanged state on refusal, with the error preserved. -/
def loadKeeping (construction : AgentConstruction) (receiver : construction.State) (bytes : List UInt8) :
    construction.State × Option Error :=
  match load construction receiver bytes with
  | .error error => (receiver, some error)
  | .ok restored => (restored, none)

/-- Arbitrary rejected byte streams cannot return a partially changed receiver. -/
theorem load_nonmutation (construction : AgentConstruction) (receiver : construction.State)
    (bytes : List UInt8) (error : Error) (rejected : load construction receiver bytes = .error error) :
    loadKeeping construction receiver bytes = (receiver, some error) := by
  simp [loadKeeping, rejected]

end Acorn.Checkpoint
