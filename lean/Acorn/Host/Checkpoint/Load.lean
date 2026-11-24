import Acorn.Host.AgentAdmission

namespace Acorn.Checkpoint
open Features Handcrafted

@[noinline] def load (construction : AgentConstruction) (receiver : construction.State)
    (bytes : List UInt8) : Except Error construction.State :=
  match admitted : loadCandidate construction bytes with
  | .error error => .error error
  | .ok image =>
    match receiver.restore image ⟨bytes, admitted⟩ with
    | none => .error .unsupportedPolicy
    | some restored => .ok restored

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

def resume (construction : AgentConstruction) (receiver : construction.State)
    (bytes : List UInt8) : Except Error construction.State :=
  (load construction receiver bytes).map (·.beginSession)

def loadKeeping (construction : AgentConstruction) (receiver : construction.State) (bytes : List UInt8) :
    construction.State × Option Error :=
  match load construction receiver bytes with
  | .error error => (receiver, some error)
  | .ok restored => (restored, none)

theorem load_nonmutation (construction : AgentConstruction) (receiver : construction.State)
    (bytes : List UInt8) (error : Error) (rejected : load construction receiver bytes = .error error) :
    loadKeeping construction receiver bytes = (receiver, some error) := by
  simp [loadKeeping, rejected]

end Acorn.Checkpoint
