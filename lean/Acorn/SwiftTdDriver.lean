import Acorn.Digits
import Acorn.SwiftTd

namespace Acorn.SwiftTdDriver

def dimension : Dimension := ⟨8, by decide, ⟨3, rfl⟩, by decide⟩

def config : Config := ⟨.control, .differential⟩

def run {config : Config} {dimension : Dimension} :
    Nat → SwiftTd.Learner config dimension → SwiftTd.Learner config dimension
  | 0, learner => learner
  | count + 1, learner =>
    let idx := FeatIdx.fromHash dimension count.toUInt64
    let features : SwiftTd.ActiveSet dimension := ⟨[idx], by simp⟩
    run count (learner.apply (.step features Binary32.one))

@[noinline] def execute (config : Config) (dimension : Dimension) (steps : Nat) :
    SwiftTd.Learner config dimension := run steps (SwiftTd.Learner.initial config dimension)

end Acorn.SwiftTdDriver

def _root_.Acorn.SwiftTdDriver.main (arguments : List String) : IO UInt32 := do
  let count := match arguments with
    | [] => some 1
    | [word] => Acorn.Digits.natural word
    | _ => none
  match count with
  | none =>
    IO.eprintln s!"usage: swifttd-native [STEP_COUNT]\n{Acorn.Digits.usage}"
    return 2
  | some steps =>
    let learner := Acorn.SwiftTdDriver.execute
      Acorn.SwiftTdDriver.config Acorn.SwiftTdDriver.dimension steps
    let checksum := learner.val.stateChecksum
    IO.println s!"steps={steps} eligible={learner.val.eligibleCount} checksum={checksum}"
    return 0
