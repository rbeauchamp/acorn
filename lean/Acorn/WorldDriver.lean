import Acorn.Host.Ansi
import Acorn.Host.Baseline

namespace Acorn.WorldDriver
open Host

def worldError : WorldError → String
  | .coordinateOverflow => "signed coordinate arithmetic overflow"
  | .inadmissibleConfig => "world configuration fails admission bounds"

def configError : WorldConfigError → String
  | .sideTooSmall => "SideTooSmall" | .sideTooLarge => "SideTooLarge"
  | .nonpositiveSide => "NonpositiveSide" | .zeroDayLength => "ZeroDayLength"
  | .sideExceedsPatch => "SideExceedsPatch" | .scaleOverflow => "ScaleOverflow"

def cliError : Cli.Error → String
  | .command name => s!"unknown command: {name}"
  | .unknown name => s!"unknown flag: {name}"
  | .missing name => s!"missing value: {name}"
  | .repeated name => s!"repeated flag: {name}"
  | .invalid name value => s!"invalid {name}: {value}"
  | .world error => s!"invalid world config: {configError error}"

def word (text : String) (width : Nat) : Except String Nat :=
  match Digits.natural text with
  | none => .error s!"invalid unsigned integer: {text}"
  | some value => if value < 2 ^ width then .ok value else .error s!"integer overflow: {text}"

def coordinate (text : String) : Except String Coordinate :=
  match Digits.integer text with
  | none => .error s!"invalid signed integer: {text}"
  | some value =>
    match Coordinate.checked value with
    | none => .error s!"coordinate overflow: {text}"
    | some coordinate => .ok coordinate

@[noinline] def execute (seed : UInt64) (side : Coordinate) (actions : List Action) : Except String String := do
  let config ← (WorldConfig.standard seed side).mapError configError
  let initial ← (World.initial config).mapError worldError
  let world ← (initial.advanceActions actions).mapError worldError
  let observation ← world.observe |>.mapError worldError
  return s!"time={world.time} x={world.body.position.x.val} y={world.body.position.y.val} energy={world.body.energy.val} day={observation.day}"

@[noinline] def executeTerrain (x y : Coordinate) (seed : UInt64) (scale : Binary32) : Except String UInt8 := do
  return (← terrain ⟨x, y⟩ seed scale |>.mapError worldError).code

def dispatch (arguments : List String) : Except String (IO String) := do
  match arguments with
  | "admit" :: rest =>
    match ← Cli.dispatch rest |>.mapError cliError with
    | .demo (.streaming _) => return pure "admitted streaming configuration; this driver checks its admission only"
    | .demo (.ansi _ _) => return pure "admitted ANSI configuration; this driver checks its admission only"
    | .external _ _ => return pure "admitted external command; this driver checks its syntax only"
  | "actions" :: seed :: side :: actionTexts =>
    let seed := (← word seed 64).toUInt64
    let side ← (Cli.side ["--side", side]).mapError cliError
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
  | _ => .error ("usage: world-native actions SEED SIDE [ACTION_INDEX ...] | " ++
    s!"terrain X Y SEED SCALE_BITS | admit [COMMAND FLAGS ...]\n{Digits.usage} " ++
    "X and Y are the digits 0 to 9 with an optional leading - or +, " ++
    "from -9223372036854775808 to 9223372036854775807.")

end Acorn.WorldDriver

def _root_.Acorn.WorldDriver.main (arguments : List String) : IO UInt32 := do
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
