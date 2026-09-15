/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Cli
import Acorn.Host.Viewer.Supervisor

/-!
# Native viewer launch admission

Closed launch variants derive Clear availability. The ordinary variant owns
every identity and checkpoint argument. A supplied shell command is an explicit
external-process boundary and cannot claim ownership of the entire run.
-/
namespace Acorn.Host.Viewer

/-- Viewer-created terrain seeds avoid reserved audit high bits and remain exact browser integers. -/
def viewerSeed (entropy : UInt64) : UInt64 := (entropy.toNat % (2 ^ 48)).toUInt64

/-- Every generated seed belongs to the current 48-bit viewer domain. -/
theorem viewerSeed_bound (entropy : UInt64) : (viewerSeed entropy).toNat < 2 ^ 48 := by
  have bound := Nat.mod_lt entropy.toNat (by decide : 0 < 2 ^ 48)
  simp only [viewerSeed, UInt64.toNat_ofNat']
  omega

/-- Exactly one explicit core launch mode is admitted. -/
inductive LaunchMode where
  /-- The current unqualified ranked research composition. -/
  | ranked
  /-- An operator-supplied shell command with unknown persistence ownership. -/
  | fixed (command : String)

/-- Complete viewer CLI configuration. -/
structure ViewerOptions where
  /-- Loopback listening port; zero requests an OS-assigned port. -/
  port : UInt16
  /-- Whole-run directory. -/
  directory : System.FilePath
  /-- Explicit core process selection. -/
  launch : LaunchMode
  /-- Ordinary core checkpoint selection. -/
  checkpoint : Bool
  /-- Explicit operator intent to start or resume after the listener binds. -/
  start : Bool
  /-- Request the system browser after successful listener binding. -/
  openBrowser : Bool
  /-- Admit cooperative viewer shutdown from the launcher's owned stdin pipe. -/
  controlStdin : Bool

/-- Current viewer flags reuse the shared duplicate/value/unsigned admission owner. -/
def ViewerOptions.decode (arguments : List String) : Except Cli.Error ViewerOptions := do
  Cli.scan [("--port", true), ("--run-dir", true), ("--cmd", true),
    ("--research-profile", true), ("--no-checkpoint", false), ("--start", false),
    ("--open-browser", false), ("--control-stdin", false)] arguments []
  let mode ← match ← Cli.value arguments "--cmd", ← Cli.value arguments "--research-profile" with
    | some command, none => pure (LaunchMode.fixed command)
    | none, some "ranked" => pure .ranked
    | _, _ => throw (.invalid "--research-profile" "choose ranked or one --cmd")
  return ⟨(← Cli.unsigned arguments "--port" 16 8088).toUInt16,
    ⟨(← Cli.value arguments "--run-dir").getD "acorn-run"⟩, mode,
    !(arguments.contains "--no-checkpoint"), arguments.contains "--start",
    arguments.contains "--open-browser", arguments.contains "--control-stdin"⟩

/-- Clear availability follows the launch variant without a separate mutable flag. -/
def LaunchMode.clearDisabled : LaunchMode → Option String
  | .ranked => none
  | .fixed _ => some "Clear unavailable: a fixed command owns its seed and checkpoint paths"

/-- The ordinary campaign's identity comes entirely from the durable supervisor.
Arguments are a vector, so spaces in the owned checkpoint path need no shell quoting. -/
def rankedArguments (checkpoint : Bool) (launch : CoreLaunch) (path : System.FilePath) : Array String :=
  #["demo", "--research-profile", "ranked", "--telemetry", "--control-stdin",
    "--seed", toString launch.identity.seed, "--side", "1024", "--steps", "4000",
    "--attempts", "3", "--goals", "13", "--cycles", "0",
    "--run-id", toString launch.identity.run, "--agent-epoch", toString launch.identity.agentEpoch,
    "--new-agent-epoch", toString launch.newEpoch] ++
    (match launch.origin with | .fresh => #[] | .cleared => #["--cleared"]) ++
    (if checkpoint then #["--checkpoint", path.toString] else #[])

/-- A fixed command cannot acquire whole-run Clear authority. -/
theorem fixed_clear_disabled (command : String) :
    (LaunchMode.fixed command).clearDisabled.isSome = true := rfl

end Acorn.Host.Viewer
