import Acorn.Host.AgentAdmission
import Acorn.Host.Cli
import Acorn.Host.Microduck.Transport
import Acorn.Host.Forever

namespace Acorn.Host.Microduck

def Action.label : Action → String
  | .still => "still" | .forward => "forward" | .turnLeft => "turn-left"
  | .turnRight => "turn-right" | .sit => "sit" | .stand => "stand"
  | .kickLeft => "kick-left" | .kickRight => "kick-right" | .pick => "pick" | .roll => "roll"

structure Options where
  control : System.FilePath
  depth : System.FilePath
  seconds : Nat
  selection : AgentSelection
  planning : Features.PlanningSelection
  seed : UInt64

def Options.decode (arguments : List String) : Except Cli.Error Options := do
  Cli.scan [("--control", true), ("--depth", true), ("--seconds", true),
    ("--research-profile", true), ("--criterion", true), ("--planning", true),
    ("--seed", true)] arguments []
  let control ← Cli.required arguments "--control"
  let depth ← Cli.required arguments "--depth"
  let duration ← Cli.required arguments "--seconds"
  let some seconds := Digits.natural duration | throw (.invalid "--seconds" duration)
  if seconds == 0 then throw (.invalid "--seconds" duration)
  let profile ← Cli.profile (← Cli.required arguments "--research-profile")
  let criterion := (← Cli.criterion arguments).getD .discounted
  let planning ← Cli.planningSelection arguments
  let seed ← Cli.unsigned arguments "--seed" 64 Cli.defaultSeed.toNat
  return ⟨control, depth, seconds, ⟨profile, criterion⟩, planning, seed.toUInt64⟩

def Options.construction (options : Options) : Handcrafted.AgentConstruction :=
  Handcrafted.AgentConstruction.standard options.seed options.selection options.planning
    .actThenLearn

def tickPeriod : Nat := 20000000

structure Ticker where
  last : Nat
  largest : Nat
  beyond : Nat

def Ticker.tick (ticker : Ticker) (reading : Nat) : Ticker :=
  let gap := reading - ticker.last
  ⟨reading, max ticker.largest gap, ticker.beyond + if Declared.gap < gap then 1 else 0⟩

inductive Ending where
  | duration
  | closed

def Ending.label : Ending → String
  | .duration => "duration"
  | .closed => "connection-closed"

variable {State Choice : Type}

def Reply.label : Reply → String
  | .pending => "pending"
  | .accepted => "accepted"
  | .refused => "refused"

def changes {stepper : Stepper State Choice} {initial : State} (origin : Nat)
    (before after : Loop stepper initial) (sent : Nat) : List String :=
  let instant := after.last.nanoseconds - origin
  let sensed : Awaiting → String := fun awaiting =>
    let answer := match awaiting.poised.last with
      | some release => release.reply.label
      | none => "none"
    let depth := if awaiting.poised.depth.isSome then "held" else "none"
    s!"sensed\t{instant}\t{awaiting.poised.index}\t{answer}\t{depth}"
  match before.stage, after.stage with
  | .ready .., .choosing awaiting _ => [sensed awaiting]
  | .learning .., .choosing awaiting _ => [s!"learned\t{instant}", sensed awaiting]
  | .learning .., .ready .. => [s!"learned\t{instant}"]
  | .choosing awaiting _, .released idle _ =>
    let action := match idle.calm.last with
      | some release => release.record.action.label
      | none => "none"
    [s!"released\t{instant}\t{awaiting.poised.index}\t{action}\t{idle.calm.late}\t{sent}"]
  | .released .., .learning .. => [s!"learning\t{instant}"]
  | _, _ => []

def closing {stepper : Stepper State Choice} {initial : State} (origin finished : Nat)
    (loop : Loop stepper initial) (ending : Ending) (steps : Nat) (ticker : Ticker) : String :=
  let counts := loop.counts
  s!"end\t{finished - origin}\t{ending.label}\tsteps={steps}" ++
    s!"\tsensed={counts.sensed}\treleased={counts.released}\tlate={counts.late}" ++
    s!"\tunread-state={counts.unreadState}\tunread-depth={counts.unreadDepth}" ++
    s!"\tinvalid={counts.invalid}\tlargest-tick-gap={ticker.largest}" ++
    s!"\ttick-gaps-beyond={ticker.beyond}"

def Loop.finished {stepper : Stepper State Choice} {initial : State}
    (loop : Loop stepper initial) : BaseIO (Option Event) :=
  match loop.stage with
  | .choosing _ choice => do return if (← IO.hasFinished choice) then some .chosen else none
  | .learning _ agent => do return if (← IO.hasFinished agent) then some .learned else none
  | .ready _ _ => return none
  | .released _ _ => return none

private def sendAll (transport : Transport) (sends : List Send) : IO Nat := do
  let mut sent := 0
  for send in sends do
    try transport.send send
    catch _ => return sent
    sent := sent + 1
  return sent

private def advance {stepper : Stepper State Choice} {initial : State} (transport : Transport)
    (out : IO.FS.Stream) (origin : Nat) (loop : Loop stepper initial) (reading : Nat)
    (event : Event) : IO (Loop stepper initial × Nat × Bool) := do
  let deliver : Loop stepper initial → Loop stepper initial → List Send → IO Bool :=
    fun before after sends => do
      let sent ← sendAll transport sends
      let lines := changes origin before after sent
      unless lines.isEmpty do
        for line in lines do
          out.putStrLn line
        out.flush
      return sent == sends.length
  let (next, sends) := loop.step ⟨reading⟩ event
  unless ← deliver loop next sends do
    return (next, 1, false)
  match next.stage with
  | .released _ _ =>
    let (learning, more) := next.step ⟨← IO.monoNanosNow⟩ .sent
    return (learning, 2, ← deliver next learning more)
  | _ => return (next, 1, true)

def drive (stepper : Stepper State Choice) (initial : State) (control depth : System.FilePath)
    (seconds : Nat) (out : IO.FS.Stream) : IO Ending := do
  let (run, earliest) ← Transport.within control depth fun transport => do
    let origin ← IO.monoNanosNow
    let (start, opening) :=
      Loop.start stepper initial Handcrafted.Microduck.interface_timing Declared.keep ⟨origin⟩
    let sent ← sendAll transport opening
    let mut failed := sent != opening.length
    out.putStrLn s!"start\t0\torigin={origin}\topening={sent}"
    out.flush
    let deadline := origin + seconds * 1000000000
    let mut loop := start
    let mut steps := 0
    let mut ticker : Ticker := ⟨origin, 0, 0⟩
    let mut nextTick := origin + tickPeriod
    for _ in forever do
      if failed then break
      let lines ← transport.take
      for text in lines do
        let (next, taken, delivered) ←
          advance transport out origin loop (← IO.monoNanosNow) (.heard text)
        loop := next
        steps := steps + taken
        unless delivered do
          failed := true
          break
      if failed then
        break
      match ← loop.finished with
      | some event =>
        let (next, taken, delivered) ← advance transport out origin loop (← IO.monoNanosNow) event
        loop := next
        steps := steps + taken
        unless delivered do
          failed := true
          break
      | none => pure ()
      let now ← IO.monoNanosNow
      if nextTick ≤ now then
        let (next, taken, delivered) ← advance transport out origin loop now .tick
        loop := next
        steps := steps + taken
        ticker := ticker.tick now
        nextTick := now + tickPeriod
        unless delivered do
          failed := true
          break
      match ← transport.firstEnd with
      | some _ => break
      | none =>
        if deadline ≤ now then
          break
      if lines.isEmpty then
        IO.sleep 1
    let finished ← IO.monoNanosNow
    return (origin, deadline, finished, loop, steps, ticker, failed)
  let (origin, deadline, finished, loop, steps, ticker, failed) := run
  let ended := match earliest with
    | some reading => decide (reading < deadline ∧ reading ≤ finished)
    | none => false
  let ending := if failed || ended then Ending.closed else .duration
  out.putStrLn (closing origin finished loop ending steps ticker)
  out.flush
  return ending

def Options.run (options : Options) : IO Ending := do
  let construction := options.construction
  let stepper := Stepper.ofAgent construction.profile construction.config
    construction.criterion construction.dimension construction.planning
  let initial := Handcrafted.Agent.initial Handcrafted.Microduck.interface
    construction.profile construction.config construction.criterion construction.dimension
    construction.planning
  drive stepper initial options.control options.depth options.seconds (← IO.getStdout)

end Acorn.Host.Microduck

open Acorn.Host.Microduck in
def _root_.Acorn.Host.Microduck.Driver.main (arguments : List String) : IO UInt32 := do
  match Options.decode arguments with
  | .error error =>
    try IO.eprintln s!"microduck-host: {error.message}" catch _ => pure ()
    return 2
  | .ok options =>
    try
      match ← options.run with
      | .duration => return 0
      | .closed =>
        try IO.eprintln "microduck-host: a connection ended before the duration" catch _ => pure ()
        return 1
    catch error =>
      try IO.eprintln s!"microduck-host: {error}" catch _ => pure ()
      return 1
