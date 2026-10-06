/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAudit
import Acorn.Host.Baseline
import Acorn.Host.Viewer.NativeCore

/-!
# One-way campaign reports

The report observes completed outcomes and the returned agent. Numeric fields
use the exact dyadic spelling shared with telemetry. A bounded recent suffix and fixed-size goal bitmap belong to this report
consumer; explicitly requested CSV rows stream to an exclusively created file.
A requested comparator's attempts enter that file as comment lines before the footer.
Wall time is an observed native clock interval, not a performance guarantee.
-/
namespace NativeApp
open Acorn Acorn.Host Acorn.Host.Viewer Acorn.Features Acorn.Handcrafted

/-- Fixed-width lowercase hexadecimal spelling of a complete machine word. -/
def hexWord (word : UInt64) : String :=
  String.ofList ((List.range 16).reverse.map fun index =>
    let digit := ((word >>> (4 * index).toUInt64) &&& 15).toNat
    Char.ofNat (if digit < 10 then 48 + digit else 87 + digit))

/-- Non-JSON diagnostics retain NaN and signed infinity as distinct observations. -/
def numberText (value : Binary32) : String :=
  if value.Finite then binary32Text value
  else if value.magnitude = 0x7f800000 then (if value.negative then "-inf" else "inf")
  else "NaN"

/-- Run provenance renders the effective constructor choice, not raw argument text. -/
def planningProvenance (construction : AgentConstruction) : String :=
  s!"planning={construction.planning.name}"

/-- Run provenance renders the effective step order in the spelling command admission
accepts. -/
def orderProvenance (order : StepOrder) : String :=
  s!"step-order={order.name}"

/-- One agent outcome: the first nine fields keep their order, and the body
position at the end of the attempt follows them. -/
def outcomeCsv (outcome : GoalOutcome) : String :=
  s!"{outcome.index},{outcome.attempt},{outcome.tier},{outcome.steps},{if outcome.achieved then 1 else 0},{numberText outcome.reward},{numberText outcome.learner.demonError},{numberText outcome.learner.epsilon},{numberText outcome.learner.meanAlpha},{outcome.position.x.val},{outcome.position.y.val}\n"

/-- One comparator attempt, as a comment line so that a reader of the agent's
rows skips it. It names the cycle the attempt was made in, which an agent row
does not hold, and omits the tier, which the agent's rows give at the same
index. The comparator's row has no reward total and no learner observation. -/
def baselineCsv (outcome : BaselineOutcome) : String :=
  s!"# baseline cycle={outcome.context.cycle} index={outcome.context.index} attempt={outcome.context.attempt} steps={outcome.steps} achieved={if outcome.achieved then 1 else 0} x={outcome.position.x.val} y={outcome.position.y.val}\n"

/-- Distinct goals the comparator achieved among the first `goals` curriculum
entries: one for each index with an achieved attempt, in any cycle. -/
def baselineDistinct (goals : Nat) (outcomes : Array BaselineOutcome) : Nat :=
  ((List.range goals).filter fun index =>
    outcomes.any fun outcome => outcome.achieved && outcome.context.index.toNat == index).length

/-- Human-readable attempt outcome; it reads only the completed row. -/
def outcomeText (outcome : GoalOutcome) : String :=
  s!"  goal {outcome.index} (tier {outcome.tier}, attempt {outcome.attempt}): {if outcome.achieved then "achieved" else "timed out"} in {outcome.steps} steps{if outcome.achieved then "" else " (cap)"}\n"

/-- Attempt progress reads the fresh terminal frame, including its actual inventory. -/
def attemptText {α : Type} (frame : StepFrame α) : String :=
  s!"goal {frame.goal.index} (tier {frame.goal.tier}, attempt {frame.goal.attempt}) {if frame.result.events.done then "achieved" else "timed out"} at t={frame.worldTime}  energy={frame.energy.val} wood={frame.inventory.wood} stone={frame.inventory.stone} gold={frame.inventory.gold}\n"

/-- Reporting retains one bounded recent suffix and one bit per admitted goal.
Counters saturate with an explicit lower-bound marker instead of wrapping. -/
structure OutcomeReport (goals : Nat) where
  /-- At most one curriculum's worth of recent attempt detail. -/
  recent : Buffer GoalOutcome goals := .empty
  /-- Attempt count, saturated at the word boundary. -/
  attempts : UInt64 := 0
  /-- Successful attempt count, saturated at the word boundary. -/
  achieved : UInt64 := 0
  /-- A saturated count must be rendered as a lower bound. -/
  saturated : Bool := false
  /-- Distinct achievements share the actual curriculum's fixed size. -/
  goalsAchieved : Vector Bool goals := Vector.replicate goals false

/-- One row updates only fixed-size report state and the newest bounded suffix. -/
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

/-- Every report write retains exactly the declared bounded suffix of actual outcomes. -/
theorem OutcomeReport.recent_suffix {goals : Nat} (report : OutcomeReport goals)
    (outcome : GoalOutcome) : (report.push outcome).recent.values =
      (report.recent.values ++ [outcome]).drop (report.recent.values.length + 1 - goals) :=
  Buffer.retain_values _ _

/-- Distinct goal reporting counts the fixed goal bitmap, never retained-row frequency. -/
def OutcomeReport.distinct {goals : Nat} (report : OutcomeReport goals) : Nat :=
  report.goalsAchieved.toList.count true

/-- Streaming CSV schema, emitted before the first outcome without retaining rows. -/
def csvHeader : String := "index,attempt,tier,steps,achieved,reward,demon_error,epsilon,mean_alpha,x,y\n"

private def destinationIdentity (path : System.FilePath) : IO System.FilePath := do
  let some name := path.fileName | throw (IO.userError "report destination has no file name")
  return (← IO.FS.realPath (path.parent.getD ".")) / name

/-- CSV owns a new file after campaign admission. Canonical parent/name separation
protects even a not-yet-created checkpoint; exclusive creation also rejects
existing files, symlinks and hard-link aliases without truncating them.
Parent-directory stability and concurrent external renames remain OS assumptions. -/
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

/-- All campaign reporting inputs are derived from the actual execution result. The
planning selection, the step order and the weight capacity, in the summary and in the
CSV footer, are those of the construction whose state the result holds. -/
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
