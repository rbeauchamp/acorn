/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.BrowserStore
import Acorn.Host.Viewer.BrowserMath
import Acorn.Host.Viewer.ClockProgram
import Acorn.Host.Viewer.BrowserNat

/-!
# Generated browser kernel

One generated resource carries everything the page takes from Lean: its named
dimensions, refusal vocabulary and lifecycle labels, the frame store, admission,
the record conversion and the numeric programs. The `browser-kernel` executable
prints it and verification compares the maintained file with it byte for byte.
Nothing here relates the emitted JavaScript to the Lean semantics of the
definitions it is printed from; the browser's JavaScript engine and these
structural emitters remain trusted.
-/
namespace Acorn.Host.Viewer

/-- How the run control presents one actual phase. -/
structure RunLabel where
  /-- The action the run button offers. -/
  action : String
  /-- The state word beside it. -/
  state : String
  /-- The style class of the state word. -/
  style : String
  /-- The phase is in transit: the button waits for the server to move. -/
  busy : Bool

/-- The three transient phases are shown, not skipped: a Clear lasts as long as the
core needs to finish its attempt, and a control that sat unchanged for that time
would read as a click that did nothing. -/
def Phase.runLabel : Phase → RunLabel
  | .starting _ => ⟨"Stop", "starting…", "busy", true⟩
  | .running _ => ⟨"Stop", "running", "on", false⟩
  | .stopping _ => ⟨"Stop", "stopping…", "busy", true⟩
  | .archiving => ⟨"Stop", "clearing…", "busy", true⟩
  | .idle => ⟨"Start", "stopped", "off", false⟩

/-- Each actual-phase tag with its run-control label. -/
def browserRunLabels : List (String × RunLabel) :=
  Phase.representatives.map fun phase => (phase.controlTag, phase.runLabel)

/-- Every phase the supervisor can report has its own label in the emitted table. -/
theorem browserRunLabels_complete (phase : Phase) :
    (phase.controlTag, phase.runLabel) ∈ browserRunLabels := by
  cases phase <;>
    simp [browserRunLabels, Phase.representatives, Phase.controlTag, Phase.runLabel]

/-- The emitted table has one entry per tag, so a lookup by tag finds that label. -/
theorem browserRunLabels_distinct : (browserRunLabels.map Prod.fst).Nodup := by
  decide +kernel

/-- Stops the operator did not ask for. Their reason stays on the connection label:
it is the one line that says what happened. -/
def unaskedStops : List ControlTransition := [.failed, .restartScheduled]

/-- Run-control labels and unasked-stop transitions, from the lifecycle owners. -/
def browserLifecycleJavascript : String :=
  "const RUN_LABEL={" ++ String.intercalate "," (browserRunLabels.map fun (tag, label) =>
    telemetryString tag ++ ":[" ++ telemetryString label.action ++ "," ++
      telemetryString label.state ++ "," ++ telemetryString label.style ++ "," ++
      toString label.busy ++ "]") ++ "};\n" ++
  "const UNASKED_STOPS=[" ++ String.intercalate "," (unaskedStops.map fun transition =>
    telemetryString transition.tag) ++ "];\n"

/-- One generated resource owns the page's constants, storage, admission, conversion
and observer calculations together. -/
def browserKernelJavascript : String :=
  browserConstantsJavascript ++ browserRefusalJavascript ++ browserLifecycleJavascript ++
    browserStoreJavascript ++ BrowserMath.javascript ++ browserGoalLabelsJavascript ++
    browserGoalTextJavascript ++ browserAdmissionJavascript ++ browserRecordJavascript ++
    ClockProgram.javascript ++ BrowserNat.javascript ++ browserRulesJavascript

end Acorn.Host.Viewer
