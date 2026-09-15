/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# Shared native checkpoint-refusal diagnostic

The runner owns checkpoint admission. The observer recognizes its shared
diagnostic spelling without inferring refusal from arbitrary IO errors.
Stderr provenance remains the native child-generation boundary.
-/
namespace Acorn.Host

/-- Exact shared suffix emitted when checkpoint admission disarms writes for the run. -/
def checkpointRefusalNotice : String := "writing disabled for this run"

/-- Runner diagnostic constructed from the same notice the observer recognizes. -/
def checkpointRefusalMessage (reason : String) : String :=
  "checkpoint: " ++ reason ++ "; " ++ checkpointRefusalNotice

/-- Final write disposition is distinct from process exit and image admission. -/
inductive CheckpointStatus where
  /-- No admitted write capability exists, including a load-only schedule. -/
  | disabled
  /-- An existing image was refused and writes were disarmed. -/
  | refused
  /-- Saving is armed but no completed attempt has attempted a write. -/
  | pending
  /-- The latest boundary write returned successfully. -/
  | saved
  /-- The latest boundary write failed; older knowledge may still exist. -/
  | failed
  deriving DecidableEq, BEq

/-- Fixed bounded diagnostic spelling shared by native reporting and pipe admission. -/
def CheckpointStatus.line : CheckpointStatus → String
  | .disabled => "checkpoint final: saving disabled"
  | .refused => "checkpoint final: load refused; saving disarmed"
  | .pending => "checkpoint final: no completed attempt saved"
  | .saved => "checkpoint final: saved successfully"
  | .failed => "checkpoint final: SAVE FAILED; durability unconfirmed"

/-- Only complete canonical status lines establish a terminal save observation. -/
def CheckpointStatus.parse : String → Option CheckpointStatus
  | "checkpoint final: saving disabled" => some .disabled
  | "checkpoint final: load refused; saving disarmed" => some .refused
  | "checkpoint final: no completed attempt saved" => some .pending
  | "checkpoint final: saved successfully" => some .saved
  | "checkpoint final: SAVE FAILED; durability unconfirmed" => some .failed
  | _ => none

/-- Every emitted disposition is recognized without changing its meaning. -/
theorem CheckpointStatus.roundtrip (status : CheckpointStatus) : parse status.line = some status := by
  cases status <;> rfl

end Acorn.Host
