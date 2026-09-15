/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.Build
import Acorn.Host.AuditPins
import NativeApp.Report

/-!
# Fixed current-agent mutation audits

Each arm executes the current full agent, with the retained seed, world and
campaign limits. Both the action digest and knowledge checksum must match.
The fixed executions are compared through these paired digests.
-/
namespace NativeApp
open Acorn Acorn.Host Acorn.Host.Viewer Acorn.Handcrafted

/-- The complete retained audit-arm domain. -/
inductive AuditArm where
  /-- Ranked, derived exploration, discounted control. -/
  | derived
  /-- Retained annealed schedule with spatial subtask interests. -/
  | annealed
  /-- Ranked, derived exploration, differential control. -/
  | differential
  deriving DecidableEq

/-- A receipt pairs the ordered action digest with the knowledge checksum. -/
structure AuditReceipt where
  /-- Ordered action/outcome/retirement digest. -/
  digest : UInt64
  /-- Complete current knowledge checksum. -/
  checksum : UInt64
  deriving DecidableEq, BEq

/-- Retained mutation pins; changing a value requires an explicit dynamics decision. -/
def AuditArm.receipt : AuditArm → AuditReceipt
  | .derived => ⟨AuditPins.derivedDigest, AuditPins.derivedChecksum⟩
  | .annealed => ⟨AuditPins.annealedDigest, AuditPins.annealedChecksum⟩
  | .differential => ⟨AuditPins.differentialDigest, AuditPins.differentialChecksum⟩

/-- Stable labels keep each mutation result attached to its actual arm. -/
def AuditArm.label : AuditArm → String
  | .derived => "deployed"
  | .annealed => "annealed incumbent arm"
  | .differential => "differential research arm"

/-- Full-width hex admission never truncates a supplied expectation. -/
def auditHex (text : String) : Option UInt64 := do
  let digits := if text.startsWith "0x" then (text.drop 2).toString else text
  if digits.isEmpty then none else
    let number ← digits.toList.foldlM (fun acc char => do
      let value := char.toNat
      let digit ← if 48 ≤ value && value ≤ 57 then some (value - 48)
        else if 65 ≤ value && value ≤ 70 then some (value - 55)
        else if 97 ≤ value && value ≤ 102 then some (value - 87) else none
      let next := acc * 16 + digit
      if next < 2 ^ 64 then some next else none) 0
    return number.toUInt64

/-- Audit selectors and expectation are validated before construction or execution. -/
def auditOptions (arguments : List String) : Except Cli.Error AuditArm := do
  Cli.scan [("--expect", true), ("--arm", true), ("--explore-rate", true)] arguments []
  let selected ← Cli.value arguments "--arm"
  let legacy ← Cli.value arguments "--explore-rate"
  let arm ← match selected, legacy with
    | none, none => pure .derived
    | some _, some _ => .error (.repeated "audit arm selector")
    | some "derived", none | none, some "derived" => pure .derived
    | some "annealed", none | none, some "annealed" => pure .annealed
    | some "differential", none => pure .differential
    | some name, none => .error (.invalid "--arm" name)
    | none, some name => .error (.invalid "--explore-rate" name)
  if let some text ← Cli.value arguments "--expect" then
    let some expected := auditHex text | .error (.invalid "--expect" text)
    if expected != arm.receipt.digest then .error (.invalid "--expect" "does not match compiled pin")
  return arm

/-- Fixed campaign dimensions and public selection metadata. The incumbent's
spatial subtask construction is owned by `AuditArm.construction`. -/
def AuditArm.options (arm : AuditArm) : Except Cli.Error Cli.Streaming := do
  let world ← (WorldConfig.standard 0x00a6000000000001 ⟨512, by decide⟩).mapError Cli.Error.world
  return {
    common := ⟨if arm = .annealed then .annealed else .ranked, world, 1500, 6, 1⟩
    attempts := 2
    criterion := some (if arm = .differential then .differential else .discounted)
    checkpoint := none, checkpointEvery := 0, baseline := false, telemetry := false
    csv := none, controlStdin := false, runId := 0, agentEpoch := 0, newAgentEpoch := 0, cleared := false }

/-- The incumbent combines annealed rates with spatial subtasks. The deployed
and differential arms retain the ordinary native construction. -/
@[noinline] def AuditArm.construction (arm : AuditArm) (options : Cli.Streaming) : AgentConstruction :=
  { nativeConstruction options with profile := match arm with
    | .derived | .differential => (nativeConstruction options).profile
    | .annealed => ⟨.final, .perStep, .annealed, .spatial⟩ }

/-- Every incumbent construction carries all four retained discriminants,
independently of the public research-profile metadata. -/
theorem AuditArm.incumbent_profile (options : Cli.Streaming) :
    (AuditArm.annealed.construction options).profile =
      ⟨.final, .perStep, .annealed, .spatial⟩ := rfl

/-- Both non-incumbent arms use the ordinary native constructor unchanged. -/
theorem AuditArm.ordinary_construction (arm : AuditArm) (options : Cli.Streaming)
    (ordinary : arm ≠ .annealed) : arm.construction options = nativeConstruction options := by
  cases arm <;> simp_all [AuditArm.construction]

/-- Ordinary audit arms traverse the public native campaign. The incumbent
uses the same stream runner with its explicit fresh spatial construction,
without telemetry or checkpoint authority. -/
def AuditArm.executeCampaign (arm : AuditArm) (options : Cli.Streaming)
    (build : TelemetryBuild) (syncProgram : System.FilePath) (sink : IO.FS.Stream)
    (outcome : GoalOutcome → IO Unit) (stop : StopFlag) :
    IO (Except RunnerError (CampaignResult options.common.world (arm.construction options).State)) :=
  match arm with
  | .derived => runNativeCampaign options build syncProgram sink outcome stop
  | .differential => runNativeCampaign options build syncProgram sink outcome stop
  | .annealed =>
    let construction := AuditArm.annealed.construction options
    runCampaign options.common.world options.common.world.raw.seed (nativeSelection options)
      options.campaign (fun _ => IO.lazyPure fun _ => construction.initial)
      Agent.callbacks { StreamObserver.none with onOutcome := outcome } none stop.requested

/-- Execute the fixed audit once; scientific capture may retain its actual receipt. -/
def executeMutationAudit (arm : AuditArm) (printReport : Bool := false) : IO AuditReceipt := do
  let options ← match arm.options with
    | .ok options => pure options
    | .error error => throw (IO.userError error.message)
  let some build := buildIdentity | throw (IO.userError "embedded native build identity is invalid")
  let stop ← StopFlag.new
  let outcomes ← IO.mkRef ({} : OutcomeReport
    (standardCurriculum options.common.world options.common.world.raw.seed).size)
  let started ← IO.monoMsNow
  let result ← arm.executeCampaign options build ((← IO.appDir) / "checkpoint-sync")
    (← IO.getStdout) (fun outcome => outcomes.modify (·.push outcome)) stop
  match result with
  | .error _ => throw (IO.userError "audit campaign refused")
  | .ok result =>
    let elapsed := (← IO.monoMsNow) - started
    if printReport then IO.print (reportText options result (← outcomes.get) elapsed).1
    let events := result.run.agent.control.runtime.lifecycle.representation.progress.events.toArray.map
      (fun event => AuditRetirement.mk event.step event.unit.val.toUInt32)
    return ⟨streamingAudit result.outcomes result.run.behavior result.totalSteps events,
      agentChecksum result.run.agent⟩

/-- Success requires both retained words; the command line cannot replace either pin. -/
def runMutationAudit (arguments : List String) : IO UInt32 := do
  let arm ← match auditOptions arguments with
    | .ok arm => pure arm
    | .error error => throw (IO.userError error.message)
  let receipt ← executeMutationAudit arm true
  IO.println s!"audit digest ({arm.label}): {hexWord receipt.digest}"
  if receipt = arm.receipt then
    IO.println s!"audit digest and checksum match the compiled {arm.label} pin ({hexWord receipt.digest} / {hexWord receipt.checksum})"
    return 0
  else
    IO.eprintln s!"audit mismatch ({arm.label}): digest expected {hexWord arm.receipt.digest}, computed {hexWord receipt.digest}; checksum expected {hexWord arm.receipt.checksum}, computed {hexWord receipt.checksum}"
    return 1

end NativeApp
