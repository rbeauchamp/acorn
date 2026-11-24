import Init

namespace Acorn.Host

def checkpointRefusalNotice : String := "writing disabled for this run"

def checkpointRefusalMessage (reason : String) : String :=
  "checkpoint: " ++ reason ++ "; " ++ checkpointRefusalNotice

inductive CheckpointStatus where
  | disabled
  | refused
  | pending
  | saved
  | failed
  deriving DecidableEq, BEq

def CheckpointStatus.line : CheckpointStatus → String
  | .disabled => "checkpoint final: saving disabled"
  | .refused => "checkpoint final: load refused; saving disarmed"
  | .pending => "checkpoint final: no completed attempt saved"
  | .saved => "checkpoint final: saved successfully"
  | .failed => "checkpoint final: SAVE FAILED; durability unconfirmed"

def CheckpointStatus.parse : String → Option CheckpointStatus
  | "checkpoint final: saving disabled" => some .disabled
  | "checkpoint final: load refused; saving disarmed" => some .refused
  | "checkpoint final: no completed attempt saved" => some .pending
  | "checkpoint final: saved successfully" => some .saved
  | "checkpoint final: SAVE FAILED; durability unconfirmed" => some .failed
  | _ => none

theorem CheckpointStatus.roundtrip (status : CheckpointStatus) : parse status.line = some status := by
  cases status <;> rfl

end Acorn.Host
