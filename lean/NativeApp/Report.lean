import Acorn.Host.AgentAudit
import Acorn.Host.Baseline
import Acorn.Host.Viewer.NativeCore

namespace NativeApp
open Acorn Acorn.Host Acorn.Host.Viewer Acorn.Features Acorn.Handcrafted

def hexWord (word : UInt64) : String :=
  String.ofList ((List.range 16).reverse.map fun index =>
    let digit := ((word >>> (4 * index).toUInt64) &&& 15).toNat
    Char.ofNat (if digit < 10 then 48 + digit else 87 + digit))

def numberText (value : Binary32) : String :=
  if value.Finite then binary32Text value
  else if value.magnitude = 0x7f800000 then (if value.negative then "-inf" else "inf")
  else "NaN"

def planningProvenance (construction : AgentConstruction) : String :=
  s!"planning={construction.planning.name}"

def orderProvenance (order : StepOrder) : String :=
  s!"step-order={order.name}"

def outcomeCsv (outcome : GoalOutcome) : String :=
  s!"{outcome.index},{outcome.attempt},{outcome.tier},{outcome.steps},{if outcome.achieved then 1 else 0},{numberText outcome.reward},{numberText outcome.learner.demonError},{numberText outcome.learner.epsilon},{numberText outcome.learner.meanAlpha},{outcome.position.x.val},{outcome.position.y.val}\n"

def baselineCsv (outcome : BaselineOutcome) : String :=
  s!"# baseline cycle={outcome.context.cycle} index={outcome.context.index} attempt={outcome.context.attempt} steps={outcome.steps} achieved={if outcome.achieved then 1 else 0} x={outcome.position.x.val} y={outcome.position.y.val}\n"

def baselineDistinct (goals : Nat) (outcomes : Array BaselineOutcome) : Nat :=
  ((List.range goals).filter fun index =>
    outcomes.any fun outcome => outcome.achieved && outcome.context.index.toNat == index).length

def outcomeText (outcome : GoalOutcome) : String :=
  s!"  goal {outcome.index} (tier {outcome.tier}, attempt {outcome.attempt}): {if outcome.achieved then "achieved" else "timed out"} in {outcome.steps} steps{if outcome.achieved then "" else " (cap)"}\n"

def attemptText {α : Type} (frame : StepFrame α) : String :=
  s!"goal {frame.goal.index} (tier {frame.goal.tier}, attempt {frame.goal.attempt}) {if frame.result.events.done then "achieved" else "timed out"} at t={frame.worldTime}  energy={frame.energy.val} wood={frame.inventory.wood} stone={frame.inventory.stone} gold={frame.inventory.gold}\n"

structure OutcomeReport (goals : Nat) where
  recent : Buffer GoalOutcome goals := .empty
  attempts : UInt64 := 0
  achieved : UInt64 := 0
  saturated : Bool := false
  goalsAchieved : Vector Bool goals := Vector.replicate goals false

def OutcomeReport.push {goals : Nat} (report : OutcomeReport goals) (outcome : GoalOutcome) :
    OutcomeReport goals :=
  { recent := report.recent.retain outcome
    attempts := saturatingIncrement64 report.attempts
    achieved := if outcome.achieved then saturatingIncrement64 report.achieved else report.achieved
    saturated := report.saturated || report.attempts == 18446744073709551615
    goalsAchieved := if h : outcome.index.toNat < goals then
      report.goalsAchieved.set outcome.index.toNat
        (report.goalsAchieved[outcome.index.toNat] || outcome.achieved) h
      else report.goalsAchieved }

theorem OutcomeReport.recent_suffix {goals : Nat} (report : OutcomeReport goals)
    (outcome : GoalOutcome) : (report.push outcome).recent.values =
      (report.recent.values ++ [outcome]).drop (report.recent.values.length + 1 - goals) :=
  Buffer.retain_values _ _

def OutcomeReport.distinct {goals : Nat} (report : OutcomeReport goals) : Nat :=
  report.goalsAchieved.toList.count true

def csvHeader : String := "index,attempt,tier,steps,achieved,reward,demon_error,epsilon,mean_alpha,x,y\n"

private def destinationIdentity (path : System.FilePath) : IO System.FilePath := do
  let some name := path.fileName | throw (IO.userError "report destination has no file name")
  return (← IO.FS.realPath (path.parent.getD ".")) / name

def openCsv (path : System.FilePath) (checkpoint : Option System.FilePath)
    (construction : AgentConstruction) : IO IO.FS.Handle := do
  let destination ← destinationIdentity path
  if let some image := checkpoint then
    if destination == (← destinationIdentity image) then
      throw (IO.userError "CSV destination aliases the checkpoint")
  let handle ← IO.FS.Handle.mk destination .writeNew
  handle.putStr csvHeader
  handle.putStr s!"# {planningProvenance construction}\n"
  handle.putStr s!"# {orderProvenance construction.order}\n"
  return handle

def reportText (options : Cli.Streaming) {construction : AgentConstruction}
    (result : CampaignResult options.common.world construction.State)
    (outcomes : OutcomeReport (standardCurriculum options.common.world options.common.world.raw.seed).size) (elapsedMs : Nat) : String × String := Id.run do
  let agent := result.run.agent.agent
  let progress := agent.control.runtime.lifecycle.representation.progress
  let checksum := hexWord (agentChecksum agent)
  let last := match progress.last with
    | none => "none"
    | some event => s!"{event.step}:{event.unit.val}"
  let census := (imprintCensus (config := construction.config)
    agent.control.runtime.lifecycle.consumers.demons).toList.map toString
  let ranked := agent.control.runtime.lifecycle.consumers.skills.toList.map fun skill =>
    toString skill.model.transition.ranked.occupied.length
  let common := options.common
  let rate := if elapsedMs == 0 then 0 else result.totalSteps.toNat * 1000 / elapsedMs
  let mut summary := s!"campaign seed={common.world.raw.seed} world={common.world.raw.side.val}x{common.world.raw.side.val} {planningProvenance construction} {orderProvenance construction.order} weights={construction.dimension.capacity} achieved {outcomes.achieved}/{outcomes.attempts}{if outcomes.saturated then " (counts saturated; lower bounds)" else ""} attempts over {result.totalSteps} steps in {elapsedMs}ms ({rate} steps/s)\n"
  summary := summary ++ s!"  recent attempt detail (last {outcomes.recent.values.length} retained):\n"
  for outcome in outcomes.recent.values do summary := summary ++ outcomeText outcome
  summary := summary ++ s!"  audit checksum: {checksum}\n  retire_count: {progress.replaced}\n  retire_last: {last}\n  imprint_distinct_abs: {String.intercalate " " census}\n  ranked_slots: {String.intercalate " " ranked}\n"
  let csv := s!"# seed={common.world.raw.seed} side={common.world.raw.side.val} weights={construction.dimension.capacity} total_steps={result.totalSteps} behavior={hexWord result.run.behavior} checksum={checksum} wall_ms={elapsedMs} steps_per_sec={rate} retire_count={progress.replaced} retire_last={last} imprint_distinct_abs={String.intercalate ";" census}\n"
  return (summary, csv)

end NativeApp
