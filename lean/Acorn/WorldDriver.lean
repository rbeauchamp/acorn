/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Ansi
import Acorn.Host.Baseline

/-!
# Native current-world consumer

`actions` executes a finite caller-supplied action stream through the same world
used by the runner. `terrain` admits complete raw public terrain arguments.
`admit` executes CLI admission without starting an agent, study or IO owner.
This is a direct component consumer; full learning composition remains with its
assigned owner and is never replaced by a scripted callback.
-/
namespace Acorn.WorldDriver
open Host

/-- Explicit diagnostic names for the closed current world-refusal domain. -/
def worldError : WorldError → String
  | .coordinateOverflow => "signed coordinate arithmetic overflow"

/-- Current standard/custom configuration refusal names. -/
def configError : WorldConfigError → String
  | .sideTooSmall => "SideTooSmall" | .sideTooLarge => "SideTooLarge"
  | .nonpositiveSide => "NonpositiveSide" | .zeroDayLength => "ZeroDayLength"

/-- CLI diagnostics retain their closed category and offending text. -/
def cliError : Cli.Error → String
  | .command name => s!"unknown command: {name}"
  | .unknown name => s!"unknown flag: {name}"
  | .missing name => s!"missing value: {name}"
  | .repeated name => s!"repeated flag: {name}"
  | .invalid name value => s!"invalid {name}: {value}"
  | .world error => s!"invalid world config: {configError error}"

/-- Raw text admission checks the full unsigned width before narrowing. -/
def word (text : String) (width : Nat) : Except String Nat :=
  match Cli.natural text with
  | none => .error s!"invalid unsigned integer: {text}"
  | some value => if value < 2 ^ width then .ok value else .error s!"integer overflow: {text}"

/-- Signed text uses the same complete public-side parser, independent of world bounds. -/
def coordinate (text : String) : Except String Coordinate :=
  (Cli.side ["--side", text]).mapError cliError

/-- Native world consumer executes initialization, finite-prefix transition and observation. -/
@[noinline] def execute (seed : UInt64) (side : Coordinate) (actions : List Action) : Except String String := do
  let config ← (WorldConfig.standard seed side).mapError configError
  let initial ← (World.initial config).mapError worldError
  let world ← (initial.advanceActions actions).mapError worldError
  let observation ← world.observe |>.mapError worldError
  return s!"time={world.time} x={world.body.position.x.val} y={world.body.position.y.val} energy={world.body.energy.val} day={observation.day}"

/-- Terrain consumer uses the actual raw-word scale and signed coordinates. -/
@[noinline] def executeTerrain (x y : Coordinate) (seed : UInt64) (scale : Binary32) : Except String UInt8 := do
  return (← terrain ⟨x, y⟩ seed scale |>.mapError worldError).code

/-- Closed native command routing. Admission-only output does not claim execution by a later owner. -/
def dispatch (arguments : List String) : Except String (IO String) := do
  match arguments with
  | "admit" :: rest =>
    match ← Cli.dispatch rest |>.mapError cliError with
    | .demo (.streaming _) => return pure "admitted streaming configuration; full-agent composition owner: #112"
    | .demo (.ansi _ _) => return pure "admitted ANSI configuration; full-agent composition owner: #112"
    | .external _ _ => return pure "distinct command retained with its Rust/scientific owner; migration owner: #116/#117"
  | "actions" :: seed :: side :: actionTexts =>
    let seed := (← word seed 64).toUInt64
    let side ← coordinate side
    let actions ← actionTexts.mapM (fun text => return Action.fromIndex (← word text 64))
    return do
      match execute seed side actions with
      | .error error => throw (IO.userError error)
      | .ok result => pure result
  | ["terrain", x, y, seed, scale] =>
    let x ← coordinate x
    let y ← coordinate y
    let seed := (← word seed 64).toUInt64
    let scale : Binary32 := ⟨(← word scale 32).toUInt32⟩
    return do
      match executeTerrain x y seed scale with
      | .error error => throw (IO.userError error)
      | .ok kind => pure s!"kind={kind}"
  | _ => .error "usage: world-native actions SEED SIDE [ACTION_INDEX ...] | terrain X Y SEED SCALE_BITS | admit [COMMAND FLAGS ...]"

end Acorn.WorldDriver

/-- Native startup, output and computation refusals return failure with an explicit diagnostic. -/
def main (arguments : List String) : IO UInt32 := do
  try
    match Acorn.WorldDriver.dispatch arguments with
    | .error error =>
      IO.eprintln error
      return 2
    | .ok operation =>
      IO.println (← operation)
      return 0
  catch error =>
    try IO.eprintln s!"world-native: {error}" catch _ => pure ()
    return 1
