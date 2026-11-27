import Acorn.Host.Cli
import Acorn.Host.Viewer.Supervisor

namespace Acorn.Host.Viewer

def viewerSeed (entropy : UInt64) : UInt64 := (entropy.toNat % (2 ^ 48)).toUInt64

theorem viewerSeed_bound (entropy : UInt64) : (viewerSeed entropy).toNat < 2 ^ 48 := by
  have bound := Nat.mod_lt entropy.toNat (by decide : 0 < 2 ^ 48)
  simp only [viewerSeed, UInt64.toNat_ofNat']
  omega

inductive LaunchMode where
  | ranked
  | fixed (command : String)

structure ViewerOptions where
  port : UInt16
  directory : System.FilePath
  launch : LaunchMode
  checkpoint : Bool
  start : Bool
  openBrowser : Bool
  controlStdin : Bool

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

def LaunchMode.clearDisabled : LaunchMode → Option String
  | .ranked => none
  | .fixed _ => some "Clear unavailable: a fixed command owns its seed and checkpoint paths"

def referenceLaunch : CoreLaunch := ⟨⟨0, 0, 0⟩, 0, .fresh⟩

def rankedArguments (checkpoint : Bool) (launch : CoreLaunch) (path : System.FilePath) : Array String :=
  #["demo", "--research-profile", "ranked", "--telemetry", "--control-stdin",
    "--seed", toString launch.identity.seed, "--side", "1024", "--steps", "4000",
    "--attempts", "3", "--goals", "13", "--cycles", "0",
    "--run-id", toString launch.identity.run, "--agent-epoch", toString launch.identity.agentEpoch,
    "--new-agent-epoch", toString launch.newEpoch] ++
    (match launch.origin with | .fresh => #[] | .cleared => #["--cleared"]) ++
    (if checkpoint then #["--checkpoint", path.toString] else #[])

theorem fixed_clear_disabled (command : String) :
    (LaunchMode.fixed command).clearDisabled.isSome = true := rfl

end Acorn.Host.Viewer
