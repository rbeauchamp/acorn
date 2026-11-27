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

def goalItemLabel (code : Nat) (count : Nat := 1) : String :=
  match decodeGoalItem code with
  | none => "—"
  | some item =>
    let labels := item.labels
    if count == 1 then labels.1 else labels.2

theorem goalItemLabel_roundtrip (item : GoalItem) :
    goalItemLabel item.code 1 = item.labels.1 ∧ goalItemLabel item.code 2 = item.labels.2 := by
  simp [goalItemLabel, goalItem_roundtrip]

def goalText (gkind gitem : Nat) (gx gy : Int) (gn : Nat) : String :=
  match decodeGoalKind gkind with
  | some (some .reach) => s!"Go to the gold target ({gx}, {gy})"
  | some (some .collect) => s!"Hold at least {gn} {(goalItemLabel gitem gn).toLower}"
  | some (some .craft) => s!"Own {goalItemLabel gitem 1}"
  | some (some .survive) => s!"Continue for {gn} world steps in this attempt"
  | _ => "—"

end Acorn.Host.Viewer
