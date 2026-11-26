import Acorn.Host.Viewer.BrowserStore
import Acorn.Host.Viewer.BrowserMath
import Acorn.Host.Viewer.ClockProgram
import Acorn.Host.Viewer.BrowserNat

namespace Acorn.Host.Viewer

structure RunLabel where
  action : String
  state : String
  style : String
  busy : Bool

def Phase.runLabel : Phase → RunLabel
  | .starting _ => ⟨"Stop", "starting…", "busy", true⟩
  | .running _ => ⟨"Stop", "running", "on", false⟩
  | .stopping _ => ⟨"Stop", "stopping…", "busy", true⟩
  | .archiving => ⟨"Stop", "clearing…", "busy", true⟩
  | .idle => ⟨"Start", "stopped", "off", false⟩

def browserRunLabels : List (String × RunLabel) :=
  Phase.representatives.map fun phase => (phase.controlTag, phase.runLabel)

theorem browserRunLabels_complete (phase : Phase) :
    (phase.controlTag, phase.runLabel) ∈ browserRunLabels := by
  cases phase <;>
    simp [browserRunLabels, Phase.representatives, Phase.controlTag, Phase.runLabel]

theorem browserRunLabels_distinct : (browserRunLabels.map Prod.fst).Nodup := by
  decide +kernel

def unaskedStops : List ControlTransition := [.failed, .restartScheduled]

def browserLifecycleJavascript : String :=
  "const RUN_LABEL={" ++ String.intercalate "," (browserRunLabels.map fun (tag, label) =>
    telemetryString tag ++ ":[" ++ telemetryString label.action ++ "," ++
      telemetryString label.state ++ "," ++ telemetryString label.style ++ "," ++
      toString label.busy ++ "]") ++ "};\n" ++
  "const UNASKED_STOPS=[" ++ String.intercalate "," (unaskedStops.map fun transition =>
    telemetryString transition.tag) ++ "];\n"

def browserKernelJavascript : String :=
  browserConstantsJavascript ++ browserRefusalJavascript ++ browserLifecycleJavascript ++
    browserStoreJavascript ++ BrowserMath.javascript ++ browserGoalLabelsJavascript ++
    browserGoalTextJavascript ++ browserAdmissionJavascript ++ browserRecordJavascript ++
    ClockProgram.javascript ++ BrowserNat.javascript ++ browserRulesJavascript

end Acorn.Host.Viewer
