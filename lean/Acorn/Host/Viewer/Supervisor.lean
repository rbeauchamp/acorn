/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Supervision
import Acorn.Host.Viewer.SupervisedProcess
import Acorn.Host.Viewer.MapCodec
import Acorn.Host.Viewer.HttpServer
import Acorn.Host.Forever

/-!
# The viewer supervisor's native actor

The actor reads the world, hands the supervisor's pure step (`Acorn.Host.Viewer.Supervision`)
one event at a time, performs the effects the step returns, in order, and then performs the call
the step waits for and hands its outcome back before it reads anything else. HTTP only appends
to a bounded command queue. Every decision about the core process and the run's published state
is the step's; this module maps each effect and call to the native operation it names.

Each turn reads, while nothing is pending: the identity a process reported, one queued command,
the process slot, the identity again, so that a reaped process's last report is attributed
before any launch or archival, and then a tick.

The trusted base of this module is the operating system's process, signal and wait semantics,
the file system's durability of the state and map files, the Lean runtime's IO, mutexes and
clock, and the correspondence of each case of `Supervisor.perform` and `Supervisor.call` to the
operation its constructor names. The state the step returns is stored before its effects run,
so a native error that stops the effects after it leaves that state, and the next turn goes on
from it, as a restarted viewer goes on from the state file.
-/
namespace Acorn.Host.Viewer

/-- Native bootstrap supplies fixed executable configuration and a fresh seed source.
Only launch identity and the owned checkpoint path vary between processes. -/
structure SupervisorConfig where
  /-- Actual executable, resolved before supervision. -/
  executable : System.FilePath
  /-- Pure argument construction from the admitted launch and run-owned path. -/
  arguments : CoreLaunch → System.FilePath → Array String
  /-- A configuration that cannot preserve whole-run ownership disables Clear. -/
  clearDisabled : Option String
  /-- Actual native source of new terrain seeds, called only for Clear. -/
  freshSeed : IO UInt64

/-- Bounded lifecycle mailbox; there is one actor consumer. -/
def commandCapacity : Nat := 4

/-- HTTP command admission: a Clear that the configuration disables is refused, a full queue
refuses any command, and any other command is queued. -/
def admitCommand (clearDisabled : Option String) (queue : Buffer Command commandCapacity)
    (command : Command) : ControlResult × Buffer Command commandCapacity :=
  if command == .clear && clearDisabled.isSome then (.clearUnavailable, queue)
  else match queue.offer command with
    | none => (.busy, queue)
    | some queue => (.accepted, queue)

/-- **A disabled Clear never enters the queue.** -/
theorem admitCommand_clearDisabled (reason : String) (queue : Buffer Command commandCapacity) :
    admitCommand (some reason) queue .clear = (.clearUnavailable, queue) := rfl

private structure Actor (clearDisabled : Option String) where
  supervision : Supervision clearDisabled
  directory : RunDirectory

/-- Native supervisor owns its command queue and serializes complete actor turns. -/
structure Supervisor where
  private mk ::
  private config : SupervisorConfig
  private broadcast : Broadcast
  private process : SupervisedProcess
  private queue : Std.Mutex (Buffer Command commandCapacity)
  private actor : Std.Mutex (Actor config.clearDisabled)

private def Supervisor.perform (supervisor : Supervisor) (directory : RunDirectory) :
    Effect → IO Unit
  | .settle lifecycle changes detail => do
    if let .error reason := ← supervisor.broadcast.settle lifecycle changes detail then
      throw (IO.userError reason)
  | .follow (.announceExit reason) => do
    if let .error refusal := ← supervisor.broadcast.announceExit reason then
      throw (IO.userError refusal)
  | .follow .announceCleared => do
    if let .error refusal := ← supervisor.broadcast.announceCleared then
      throw (IO.userError refusal)
  | .follow (.attach generation) => supervisor.process.attach generation directory
  | .follow (.say text) => try IO.println text catch _ => pure ()
  | .follow (.complain text) => try IO.eprintln s!"viewer shutdown: {text}" catch _ => pure ()

private def Supervisor.call (supervisor : Supervisor) (directory : RunDirectory) :
    (call : Call) → IO (call.Result × RunDirectory)
  | .writeState state => do
    let result : Except String Unit ← try
        directory.writeState state
        pure (.ok ())
      catch error => pure (.error error.toString)
    return (result, directory)
  | .writeMap skip => do
    let (revision, world) ← supervisor.broadcast.worldForWrite
    if skip == some revision then return (Except.ok none, directory)
    let some ⟨_, memory⟩ := world | return (Except.ok none, directory)
    let result : Except String (Option Nat) ← try
        directory.writeMap memory
        pure (.ok (some revision))
      catch error => pure (.error error.toString)
    return (result, directory)
  | .spawn generation plan => do
    let arguments := supervisor.config.arguments plan (directory.path .weights)
    return (← supervisor.process.spawn generation supervisor.config.executable arguments,
      directory)
  | .windUp generation => return (← supervisor.process.windUp generation, directory)
  | .commit generation actual lifecycle detail =>
    return (← supervisor.broadcast.commitIdentity generation actual lifecycle detail, directory)
  | .seed => do
    let result : Except String UInt64 ← try pure (.ok (← supervisor.config.freshSeed))
      catch error => pure (.error error.toString)
    return (result, directory)
  | .archive stamp => return (← supervisor.process.archive directory stamp, directory)
  | .reopen => do
    try return (Except.ok (), ← RunDirectory.open directory.rootPath)
    catch error => return (Except.error error.toString, directory)

/-- The longest chain of calls one event makes: Clear's seed, archival, replacement directory
and replacement state, or a map write, a launch, a spawn and a wind-up. A longer chain goes on
at the next turn, before any event is read. -/
def callChainBound : Nat := 8

/-- Perform the effects of the stored state's step, then each call it waits for, storing each
outcome's state before performing that outcome's effects. -/
private def Supervisor.drive (supervisor : Supervisor) (effects : List Effect) :
    Std.AtomicT (Actor supervisor.config.clearDisabled) IO Unit := do
  let mut effects := effects
  for _ in [0:callChainBound] do
    let actor ← get
    for effect in effects do supervisor.perform actor.directory effect
    effects := []
    match waiting : actor.supervision.core.pending with
    | none => return
    | some pending =>
      let (result, directory) ← supervisor.call actor.directory
        (pending.call actor.supervision.core.lifecycle)
      let (supervision, next) := actor.supervision.resume waiting (← IO.monoMsNow) result
      set ({ supervision, directory } : Actor supervisor.config.clearDisabled)
      effects := next
  let actor ← get
  for effect in effects do supervisor.perform actor.directory effect

private def Supervisor.handle (supervisor : Supervisor) (event : Event) :
    Std.AtomicT (Actor supervisor.config.clearDisabled) IO Unit := do
  let actor ← get
  let (supervision, effects) := actor.supervision.step (← IO.monoMsNow) event
  set { actor with supervision }
  supervisor.drive effects

private def Supervisor.ready (supervisor : Supervisor) :
    Std.AtomicT (Actor supervisor.config.clearDisabled) IO Bool :=
  return (← get).supervision.core.pending.isNone

private def Supervisor.attribute (supervisor : Supervisor) :
    Std.AtomicT (Actor supervisor.config.clearDisabled) IO Unit := do
  if !(← supervisor.ready) then return
  if let some (generation, actual) := ← supervisor.broadcast.pendingIdentity then
    supervisor.handle (.candidate generation actual)

private def Supervisor.observe (supervisor : Supervisor) :
    Std.AtomicT (Actor supervisor.config.clearDisabled) IO Unit := do
  if !(← supervisor.ready) then return
  match ← supervisor.process.poll (← get).directory with
  | .quiet => pure ()
  | .exited code uptime => supervisor.handle (.exited code uptime)
  | .finished stdout stderr log => supervisor.handle (.finished stdout stderr log)
  | .refused reason => supervisor.handle (.refused reason)

/-- Construct only after the bootstrap has admitted the initial state. The state is published
before supervision begins, so no launch relies on an unpublished state, and the first control
record is the start's. -/
def Supervisor.new (config : SupervisorConfig) (directory : RunDirectory)
    (persisted : PersistedState) : IO Supervisor := do
  unless persisted.identity.browserSafe do
    throw (IO.userError "viewer identity exceeds browser integer precision; retained state is unchanged")
  directory.writeState persisted
  let mapRead ← directory.readMap persisted.identity
  let mapRefused := match mapRead with | .refused _ => true | _ => false
  let broadcast ← Broadcast.new persisted.identity persisted.desired
    (persisted.processStarted || mapRefused)
  let reason ← match mapRead with
    | .missing => pure "viewer initialized"
    | .refused reason => pure s!"viewer initialized; retained map refused: {reason}"
    | .restored _ memory =>
      let _ ← broadcast.restoreWorld memory
      pure "viewer initialized; retained map restored as partial"
  let (supervision, effects) :=
    Supervision.start config.clearDisabled persisted reason (← IO.monoMsNow)
  let supervisor : Supervisor := ⟨config, broadcast, ← SupervisedProcess.new broadcast,
    ← Std.Mutex.new .empty, ← Std.Mutex.new ⟨supervision, directory⟩⟩
  for effect in effects do supervisor.perform directory effect
  return supervisor

/-- HTTP may retain only the three closed lifecycle commands, with no process handle. -/
def Supervisor.submit (supervisor : Supervisor) (command : Command) : BaseIO ControlResult :=
  supervisor.queue.atomically do
    let (result, queue) := admitCommand supervisor.config.clearDisabled (← get) command
    set queue
    return result

/-- One consistent registration snapshot supplies control, map and subsequent replay. -/
def supervisorInitial (snapshot : ReplaySnapshot) : BaseIO InitialFrames := do
  let map := snapshot.world.bind fun ⟨_, memory⟩ => memory.frame.toOption
  return ⟨snapshot.control, map⟩

/-- HTTP and process output use this actor's exact same broadcaster. -/
def Supervisor.http (supervisor : Supervisor) (assets : ViewerAssets) : IO HttpViewer :=
  HttpViewer.new supervisor.broadcast assets supervisorInitial supervisor.submit

/-- One actor turn. It never waits for pipe EOF. Native state and map IO can block this actor
but cannot block HTTP queue admission or the core's output pipe readers. -/
def Supervisor.step (supervisor : Supervisor) : IO Unit :=
  supervisor.actor.atomically do
    supervisor.drive []
    supervisor.attribute
    if ← supervisor.ready then
      let command ← supervisor.queue.atomically do
        match (← get).pop with
        | none => return none
        | some (command, queue) => set queue; return some command
      if let some command := command then supervisor.handle (.command command)
    supervisor.observe
    supervisor.attribute
    if ← supervisor.ready then supervisor.handle .tick

/-- One turn of a closing viewer: the close is handed once, then the process is watched, the
identity its readers delivered is attributed, and a tick closes the viewer once no process
remains. The result is whether the viewer closed with a failure, once it has closed. -/
private def Supervisor.closeTurn (supervisor : Supervisor) : IO (Option Bool) :=
  supervisor.actor.atomically do
    supervisor.drive []
    if (← supervisor.ready) && (← get).supervision.core.closing == .open then
      supervisor.handle .close
    supervisor.attribute
    supervisor.observe
    supervisor.attribute
    if ← supervisor.ready then supervisor.handle .tick
    match (← get).supervision.core.closing with
    | .closed failed => return some failed
    | .open | .closing _ => return none

/-- Graceful viewer shutdown winds the core up and keeps the process slot until reap and pipe
drain. The original durable run intent is preserved for the next viewer start. Host signal
delivery and eventual pipe closure remain native liveness assumptions. A native error in a turn
is reported and the next turn goes on from the stored state, so it cannot skip wind-up;
terminal failures are reported after it. -/
def Supervisor.shutdown (supervisor : Supervisor) : IO Unit := do
  let failed ← IO.mkRef false
  for _ in forever do
    let closed ← try supervisor.closeTurn catch error => do
      failed.set true
      try IO.eprintln s!"viewer shutdown: {error}" catch _ => pure ()
      pure none
    if let some closeFailed := closed then
      if closeFailed || (← failed.get) then
        throw (IO.userError "viewer closed with failures; see the diagnostics above")
      return
    IO.sleep 50

end Acorn.Host.Viewer
