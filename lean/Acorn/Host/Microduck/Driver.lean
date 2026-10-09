/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission
import Acorn.Host.Cli
import Acorn.Host.Microduck.Transport

/-!
# `microduck-host`: the driver of a Microduck host's loop

The executable that runs the agent of this repository in the Microduck's world: it opens the
three connections of the transport (`Transport.within`), starts the loop of
`Acorn.Host.Microduck.Loop` at a reading of the monotonic clock, sends its opening requests,
and then hands the loop its events, each with a reading of the clock, until the run's duration
has passed or a connection has ended. It holds a `Loop` and changes it only with `Loop.step`,
so every statement of that module about a loop holds of every loop of a run: what is sent, the
release of the stepper's choice for the percept sensed, and the agent that the two parts of
its steps give. The agent is the construction of the standard configuration with the selected
research profile, criterion and planning under the step order `actThenLearn`, bound by
`Stepper.ofAgent` and cold-initialised on `Handcrafted.Microduck.interface`.

**One pass of the driver**, in this order: every line taken from the transport, each as
`Event.heard` with a reading taken when it is handed; then a finished task of the loop, as
`Event.chosen` or `Event.learned`, only when `IO.hasFinished` has answered true for the task
that the loop holds, with the reading taken after that answer (`Loop.finished`), which is the
contract the loop's module states; then a tick, when the reading has reached the instant of the
next tick, every `tickPeriod`; then the end of the run when it is due; and a sleep of 1 ms when
no line was taken. The lines that a step returns go to their connections in the order
returned, by `Transport.send`, before the next step, and nothing else writes to a connection.
A step that releases an action is followed at once by `Event.sent`, at a reading taken after
the lines of the release were sent, and the loop starts the agent's learning only at that
event, so the action reaches the transport before the second part of the step begins. A send
that fails stops the sending: the lines after it are not sent, `Event.sent` is not handed, the
step's changes of stage are written with the number of lines sent, and the run ends.
The commands that can be sent are those of the command type, which has no relax, no shutdown
and no disable: at the end of a run the host sends nothing more, and the daemon replaces the
last velocity by zero at its expiry.

**The end of a run.** The loop stops at once when a send fails, and at the end of a pass when
a connection's output has ended or the duration has passed. A failed send is the only failure
the driver catches, and it takes it as the end of the send's connection; every other failure,
a write of the telemetry included, is raised through `Transport.within`, which stops every
connection. Every reader records the reading at which it ended, and the transport keeps the
earliest. The driver decides how the run ended only after the transport has stopped every
connection and joined every reader (`Transport.within`): closed when a send failed, or when a
reader ended before the deadline and at or before the reading taken when the loop stopped, and
by its duration otherwise. The ends that the stop's own kills cause come after that reading, so
they never count. The closing line, written after that decision, carries that reading.

**The clock.** The declared keeping assumes a reading of the clock, and a tick, at least every
`Declared.gap`. The driver cannot enforce that: the operating system schedules its thread. It
ticks every 20 ms and sleeps 1 ms between passes, because a longer sleep of a background
process can last far longer on macOS by timer coalescing, and it counts every gap between two
ticks above `Declared.gap` and keeps the largest, in its telemetry.

**Telemetry**, on standard output, one line for each change of the loop's stage, with the
instant in nanoseconds from the origin: `sensed` with the cycle of the percept, the daemon's
answer to the release before it as heard by then and whether a depth frame is held, `released`
with the cycle, the action, whether the release was late and the number of commands sent, and
`learned`; then one closing line with why the run ended, the steps, the loop's counts and the
gaps of the ticker. A refusal of the options is reported on standard error with the exit
status 2, and a failure of the transport, or a connection that ended before the duration,
with the exit status 1.

**Trusted, and not stated**: the transport (`Acorn.Host.Microduck.Transport`), the monotonic
clock, `IO.hasFinished` and the runtime's tasks, and the scheduling of the driver's thread.
-/
namespace Acorn.Host.Microduck

/-- The name of an action in the telemetry. -/
def Action.label : Action → String
  | .still => "still" | .forward => "forward" | .turnLeft => "turn-left"
  | .turnRight => "turn-right" | .sit => "sit" | .stand => "stand"
  | .kickLeft => "kick-left" | .kickRight => "kick-right" | .pick => "pick" | .roll => "roll"

/-- What a run of the host is given. -/
structure Options where
  /-- The socket of the state daemon. -/
  control : System.FilePath
  /-- The socket of the depth daemon. -/
  depth : System.FilePath
  /-- The duration of the run, in seconds. -/
  seconds : Nat
  /-- The research profile and the criterion of the agent. -/
  selection : AgentSelection
  /-- The planning of the agent. -/
  planning : Features.PlanningSelection
  /-- The salt of the agent's features. -/
  seed : UInt64

/-- The options of `microduck-host`, decoded with the shared admissions of `Host.Cli`, as
`Host.Viewer.ViewerOptions.decode` decodes the viewer's: an unknown or repeated option is
refused; both sockets, a positive duration and a research profile are required; the criterion
is discounted and the planning is expectation-model planning when they are not given; the seed
is `Cli.defaultSeed` when it is not given. -/
def Options.decode (arguments : List String) : Except Cli.Error Options := do
  Cli.scan [("--control", true), ("--depth", true), ("--seconds", true),
    ("--research-profile", true), ("--criterion", true), ("--planning", true),
    ("--seed", true)] arguments []
  let control ← Cli.required arguments "--control"
  let depth ← Cli.required arguments "--depth"
  let duration ← Cli.required arguments "--seconds"
  let some seconds := Cli.natural duration | throw (.invalid "--seconds" duration)
  if seconds == 0 then throw (.invalid "--seconds" duration)
  let profile ← Cli.profile (← Cli.required arguments "--research-profile")
  let criterion := (← Cli.criterion arguments).getD .discounted
  let planning ← Cli.planningSelection arguments
  let seed ← Cli.unsigned arguments "--seed" 64 Cli.defaultSeed.toNat
  return ⟨control, depth, seconds, ⟨profile, criterion⟩, planning, seed.toUInt64⟩

/-- The agent's construction for a run: the standard configuration with the selected profile,
criterion and planning, under the step order `actThenLearn`, whose two parts the loop runs. -/
def Options.construction (options : Options) : Handcrafted.AgentConstruction :=
  Handcrafted.AgentConstruction.standard options.seed options.selection options.planning
    .actThenLearn

/-- The period of the ticker, in nanoseconds: 20 ms. -/
def tickPeriod : Nat := 20000000

/-- What the driver keeps of its ticker: the instant of the last tick, the largest gap between
two ticks, and the gaps above `Declared.gap`. -/
structure Ticker where
  /-- The reading of the last tick, or of the origin before the first. -/
  last : Nat
  /-- The largest gap between two ticks, in nanoseconds. -/
  largest : Nat
  /-- The gaps between two ticks above `Declared.gap`. -/
  beyond : Nat

/-- A tick at a reading. -/
def Ticker.tick (ticker : Ticker) (reading : Nat) : Ticker :=
  let gap := reading - ticker.last
  ⟨reading, max ticker.largest gap, ticker.beyond + if Declared.gap < gap then 1 else 0⟩

/-- Why a run ended. -/
inductive Ending where
  /-- Its duration passed. -/
  | duration
  /-- A send failed, or the output of a connection ended before the deadline. -/
  | closed

/-- The name of an ending in the telemetry. -/
def Ending.label : Ending → String
  | .duration => "duration"
  | .closed => "connection-closed"

variable {State Choice : Type}

/-- The name of the daemon's answer to a release in the telemetry. -/
def Reply.label : Reply → String
  | .pending => "pending"
  | .accepted => "accepted"
  | .refused => "refused"

/-- The telemetry lines of a step from one loop to the next, with the number of lines it sent:
one for each change of stage, in order. A step can finish a learning and sense a percept. A
percept's line holds its cycle, the daemon's answer to the release before it as the host
heard it by then (none before the first release), and whether the host holds a depth
frame. -/
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
  | _, _ => []

/-- The closing line of a run, at the reading at which the driver ended it. -/
def closing {stepper : Stepper State Choice} {initial : State} (origin finished : Nat)
    (loop : Loop stepper initial) (ending : Ending) (steps : Nat) (ticker : Ticker) : String :=
  let counts := loop.counts
  s!"end\t{finished - origin}\t{ending.label}\tsteps={steps}" ++
    s!"\tsensed={counts.sensed}\treleased={counts.released}\tlate={counts.late}" ++
    s!"\tunread-state={counts.unreadState}\tunread-depth={counts.unreadDepth}" ++
    s!"\tinvalid={counts.invalid}\tlargest-tick-gap={ticker.largest}" ++
    s!"\ttick-gaps-beyond={ticker.beyond}"

/-- The event of a finished task of the loop: `chosen` when the loop chooses and the runtime
answers that its choice has finished, `learned` when it learns and its learning has finished,
and none otherwise; a released loop awaits `Event.sent`, which the driver hands after the
lines of the release. A driver takes the reading for the event after this answer. -/
def Loop.finished {stepper : Stepper State Choice} {initial : State}
    (loop : Loop stepper initial) : BaseIO (Option Event) :=
  match loop.stage with
  | .choosing _ choice => do return if (← IO.hasFinished choice) then some .chosen else none
  | .learning _ agent => do return if (← IO.hasFinished agent) then some .learned else none
  | .ready _ _ => return none
  | .released _ _ => return none

/-- Send lines in order, and say how many were sent. A send that fails stops the sending, and
the lines after it are not sent; this is the only place that catches a failure of a send. -/
private def sendAll (transport : Transport) (sends : List Send) : IO Nat := do
  let mut sent := 0
  for send in sends do
    try transport.send send
    catch _ => return sent
    sent := sent + 1
  return sent

/-- One step of the loop at a reading, the number of steps taken, and whether every line was
sent: the lines it returns are sent in order until one fails (`sendAll`), and its changes of
stage are written to the telemetry with the number of lines sent. When the step released an
action and every line of the release was sent, the event that says so follows at once, at a
reading taken after they were sent, and starts the agent's learning (`Stage.step_sent`); when
a send failed, that event is not handed. -/
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

/-- Run the loop with a stepper and its starting agent over the transport, for a duration in
seconds, writing the telemetry to a stream, and say why the run ended. A failed send ends the
loop at once, with the loop of the step that failed to send; every other failure is raised.
The ending is decided after the transport has stopped every connection and joined every
reader: closed when a send failed, or when the earliest reading at which a reader ended is
before the deadline and at or before the reading taken when the loop stopped, and by its
duration otherwise. Only then is the closing line written. -/
def drive (stepper : Stepper State Choice) (initial : State) (control depth : System.FilePath)
    (seconds : Nat) (out : IO.FS.Stream) : IO Ending := do
  let (run, earliest) ← Transport.within control depth fun transport => do
    let origin ← IO.monoNanosNow
    let (start, opening) := Loop.start stepper initial Declared.pace Declared.keep ⟨origin⟩
    let sent ← sendAll transport opening
    let mut failed := sent != opening.length
    out.putStrLn s!"start\t0\torigin={origin}\topening={sent}"
    out.flush
    let deadline := origin + seconds * 1000000000
    let mut loop := start
    let mut steps := 0
    let mut ticker : Ticker := ⟨origin, 0, 0⟩
    let mut nextTick := origin + tickPeriod
    while !failed do
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

/-- Run the agent of the options over the transport for their duration, writing the telemetry
to standard output, and say why the run ended: the construction of the options, bound by
`Stepper.ofAgent` and cold-initialised on the Microduck's interface. -/
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
/-- Decode the options and run them. A refusal of the options is reported with the exit status
2; a failure, and a connection that ended before the duration, with the exit status 1. -/
def main (arguments : List String) : IO UInt32 := do
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
