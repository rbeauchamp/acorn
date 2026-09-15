/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.Build
import Acorn.Host.Viewer.NativeCore
import Acorn.Host.Ansi
import Acorn.Host.AgentAudit
import Acorn.Host.Baseline
import NativeApp.Report
import NativeApp.MutationAudit

/-!
# Native core entry

The viewer launches the streaming process; ANSI uses its separate admitted loop.
Unsupported output modes are refused before execution.
The stdin reader owns only the monotone attempt-boundary stop capability.
-/
namespace NativeApp
open Acorn.Host Acorn.Host.Viewer

private def runnerError : RunnerError → String
  | .campaign _ => "campaign configuration refused"
  | .world _ => "world transition refused"
  | .metric _ => "campaign metric overflow"
  | .io message => message

private def actionText : Action → String
  | .north => "Move(North)" | .south => "Move(South)"
  | .east => "Move(East)" | .west => "Move(West)"
  | .wait => "Wait" | .harvest => "Harvest" | .craftAxe => "Craft(Axe)"
  | .craftBoat => "Craft(Boat)" | .eat => "Eat"

private def tileText (tile : TileObservation) : Char :=
  if tile.deer != 0 then 'd' else if tile.food != 0 then 'f' else
    match tile.kind.toNat with
    | 0 => '~' | 1 => '.' | 2 => ' ' | 3 => '"' | 4 => 'T'
    | 5 => '^' | 6 => '#' | _ => '$'

private def renderAnsi {config : WorldConfig} (frame : AnsiFrame config) : IO Unit := do
  IO.print "\x1b[H"
  for row in List.finRange patchShape.side do
    let line := (List.finRange patchShape.side).foldl (fun text col =>
      text ++ String.singleton (if row.val == 5 && col.val == 5 then '@'
        else tileText ((frame.observation.tiles.get row).get col)) ++ " ") ""
    IO.println line
  let body := frame.world.body
  let position := body.position.position
  let inventory := body.inventory
  IO.println s!"t={frame.steps} goal={frame.goalIndex} @({position.x.val},{position.y.val}) energy={body.energy.val / 10}% inv w{inventory.wood} s{inventory.stone} f{inventory.food} g{inventory.gold} axe{if inventory.axe then 1 else 0} boat{if inventory.boat then 1 else 0}"
  IO.println s!"action={actionText frame.action} reward={binary32Text frame.result.reward}"

/-- ANSI uses the same full-agent constructor as streaming with its admitted
discounted criterion, and the distinct observation schedule owned by `runAnsi`. -/
def runAnsiDemo (common : Cli.Common) (period : Acorn.Word.Count) : IO UInt32 := do
  let construction := Acorn.Handcrafted.AgentConstruction.standard common.world.raw.seed
    ⟨common.profile, .discounted⟩ .scalar
  IO.print "\x1b[2J\x1b[H"
  let result ← runAnsi common period (fun _ => IO.lazyPure fun _ => construction.initial)
    Acorn.Handcrafted.Agent.callbacks renderAnsi (fun index tier achieved steps =>
      IO.println s!"goal {index} (tier {tier}) {if achieved then "achieved" else "timed out"} in {steps} steps")
  match result with
  | .ok state =>
    IO.println s!"agent state checksum: {hexWord (agentChecksum state.agent)}"
    return 0
  | .error error => throw (IO.userError (runnerError error))

/-- Admit the streaming demo command before spawning a control reader or constructing an agent. -/
def streamingOptions (arguments : List String) : IO Cli.Streaming := do
  unless (← match Cli.command arguments with
      | .ok .demo => pure true
      | _ => pure false) do
    throw (IO.userError "streaming demo admission requires the demo command")
  match Cli.demo arguments with
  | .error error => throw (IO.userError error.message)
  | .ok (.ansi _ _) => throw (IO.userError "ANSI presentation requires the separate ANSI runner")
  | .ok (.streaming options) =>
    return options

/-- Run the actual full-agent stream with compiled provenance and receiver-bound persistence. -/
def runCore (arguments : List String) : IO UInt32 := do
  match Cli.dispatch arguments with
  | .error error => throw (IO.userError error.message)
  | .ok (.demo (.ansi common period)) => return ← runAnsiDemo common period
  | .ok (.external ⟨.audit, _⟩ _) => return ← runMutationAudit arguments
  | .ok (.external ⟨.executionIdentity, _⟩ _)
  | .ok (.external ⟨.agentBaseline, _⟩ _)
  | .ok (.external ⟨.intraOptionCredit, _⟩ _)
  | .ok (.external ⟨.derivedExplorationRate, _⟩ _)
  | .ok (.external ⟨.stompPlanning, _⟩ _)
  | .ok (.external ⟨.enduranceStability, _⟩ _)
  | .ok (.external ⟨.averageRewardControl, _⟩ _)
  | .ok (.external ⟨.averageRewardControlArm, _⟩ _) =>
    throw (IO.userError "scientific commands require the private acorn-research executable")
  | .ok (.external ⟨.emitLean, _⟩ _) =>
    throw (IO.userError "emit-lean is retired: native constants and their proofs share maintained Lean owners")
  | .ok (.demo (.streaming _)) => pure ()
  let options ← streamingOptions arguments
  let some build := buildIdentity | throw (IO.userError "embedded native build identity is invalid")
  let stop ← StopFlag.new
  stop.withCommands options.controlStdin do
    let outcomes ← IO.mkRef ({} : OutcomeReport
      (standardCurriculum options.common.world options.common.world.raw.seed).size)
    let csv ← IO.mkRef (none : Option IO.FS.Handle)
    let csvFailed ← IO.mkRef false
    let refuseCsv (error : IO.Error) : IO Unit := do
      let failed ← csvFailed.get
      csvFailed.set true
      unless failed do
        try IO.eprintln s!"csv: report is incomplete: {error}"
        catch _ => pure ()
    let ensureCsv : IO (Option IO.FS.Handle) := do
      if ← csvFailed.get then return none
      if let some handle ← csv.get then return some handle
      let some path := options.csv | return none
      try
        let handle ← openCsv path options.checkpoint
        csv.set (some handle)
        return some handle
      catch error =>
        refuseCsv error
        return none
    let started ← IO.monoMsNow
    let result ← runNativeCampaign options build ((← IO.appDir) / "checkpoint-sync")
      (← IO.getStdout) (fun outcome => do
        outcomes.modify (·.push outcome)
        if let some handle ← ensureCsv then
          try handle.putStr (outcomeCsv outcome)
          catch error => refuseCsv error) stop
      (fun frame => if options.telemetry then IO.eprint (attemptText frame) else pure ())
    match result with
    | .ok result =>
      let elapsed := (← IO.monoMsNow) - started
      let rows ← outcomes.get
      let (summary, footer) := reportText options result rows elapsed
      if options.telemetry then IO.eprint summary else IO.print summary
      if result.ending == .stopped then
        IO.eprintln s!"control: stopped on request after {result.totalSteps} steps"
      if let some handle ← ensureCsv then
        try
          handle.putStr footer
          handle.flush
        catch error => refuseCsv error
      if options.csv.isSome then
        if ← csvFailed.get then IO.eprintln "csv: creation or write failed; report is incomplete"
        else IO.println "csv written successfully"
      if options.baseline then
        IO.println "\n-- random-policy baseline (diagnostic) --"
        let curriculum := standardCurriculum options.common.world options.common.world.raw.seed
        let count := min options.common.goals.toNat curriculum.size
        let goals := (List.finRange count).toArray.map fun (index : Fin count) =>
          have bound : index.val < curriculum.size := by
            have := index.isLt
            have := Nat.min_le_right options.common.goals.toNat curriculum.size
            omega
          (curriculum[index.val]'bound).1
        match runRandomBaseline options.common.world.raw.seed options.common.world goals options.common.steps with
        | .error _ => throw (IO.userError "random baseline world transition refused")
        | .ok baseline =>
          IO.println s!"distinct goals achieved — random policy: {(baseline.filter (·.achieved)).size}/{baseline.size}; agent: {rows.distinct}/{goals.size} (agent used {rows.attempts} attempts)"
      IO.eprintln result.resources.checkpointStatus.line
      return 0
    | .error error => throw (IO.userError (runnerError error))

end NativeApp
