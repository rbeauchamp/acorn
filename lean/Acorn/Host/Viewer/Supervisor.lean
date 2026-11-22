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

/-- What the actor compares before it starts the configuration's child. The bootstrap builds
the constructor from the launch itself, `ranked` for the core beside the viewer and `fixed`
for a command given to a shell, so the two are told apart by construction and not by whether
the state file can hold a record of the child. -/
inductive ChildProgram where
  /-- A command given to a shell, spawned with no reading. -/
  | fixed
  /-- The ranked core: what this viewer read of the executable's file when it started, none
  when the file could not be read whole, and the one action that reads it. The bootstrap ran
  the action for `atStart` and the actor runs it again once before every start, before the
  launch is recorded, so what is compared was read the same way. -/
  | ranked (atStart : Option ProgramReading) (read : IO (Option ProgramReading))

/-- Native bootstrap supplies fixed executable configuration and a fresh seed source.
Only launch identity and the owned checkpoint path vary between processes. -/
structure SupervisorConfig where
  /-- Actual executable, resolved before supervision. -/
  executable : System.FilePath
  /-- Pure argument construction from the admitted launch and run-owned path. -/
  arguments : CoreLaunch → System.FilePath → Array String
  /-- The record of the child this configuration starts (`childRecord`), written with every
  state this viewer saves; none when sameness with another launch's child cannot be
  established or the state file cannot hold the record. The comparison before a start does
  not read it. -/
  child : Option (List String)
  /-- What the actor compares before every start of this configuration's child. -/
  program : ChildProgram
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

/-- The refusal of a start of the ranked core whose file reads now but not as it read when this
viewer started. It says what clears the refusal and directs no run. -/
def childDiffers : String :=
  "the core's program differs from what this viewer read when it started (the file at its " ++
    "path changed in length or content), so nothing was started; starting the viewer again " ++
    "records the program as it is now and clears this refusal"

/-- The refusal of a start of the ranked core whose file cannot be read whole now, though it
could when this viewer started. It says what clears the refusal and directs no run. -/
def childUnreadable : String :=
  "the core's program cannot be read now, so nothing was started; the refusal clears in " ++
    "this viewer when the file can be read again with the content it had when this viewer " ++
    "started, and starting the viewer again does not help while the file stays unreadable"

/-- The refusal of a start of the ranked core whose file could not be read whole when this
viewer started. It says what clears the refusal and directs no run. -/
def childUnread : String :=
  "the core's program could not be read when this viewer started, so nothing was started; " ++
    "starting the viewer again when the file can be read clears this refusal"

/-- Why the configuration's child may not be started now, and nothing when it may. A fixed
command is never refused here. The ranked core is refused when its file could not be read
whole when this viewer started, cannot be read whole now, or reads now otherwise than it did
then, whether or not the state file can hold a record of the child. The actor asks once before
each start, the first and every restart, before the launch is recorded (`Supervisor.call`). So
a file replaced before that reading is refused. One replaced after it, in the interval between
the reading and the operating system starting the program, in which the launch is recorded,
is not seen, and the replaced program is started. -/
private def Supervisor.refusal (supervisor : Supervisor) : IO (Option String) :=
  match supervisor.config.program with
  | .fixed => pure none
  | .ranked none _ => pure (some childUnread)
  | .ranked (some atStart) read => do
    match ← (try read catch _ => pure none) with
    | none => pure (some childUnreadable)
    | some found => pure (if found == atStart then none else some childDiffers)

/-- Each case performs the native operation its call names. Before the ranked core is started,
the first time and at every restart alike, its file is read once and compared with the
reading this viewer took when it started (`Supervisor.refusal`).

The reading is made before the launch is recorded, when `launching` says the state to write
is the one that marks a launch as attempted (`Pending.launch`). A refusal there writes nothing
and spawns nothing: the call's result is the write's error with the reason, which the step
treats as a launch that could not be recorded, so the run stops and the saved state is exactly
as it was before the refusal: no new mark of a started process and no agent epoch spent. A run
that had already started a process keeps that mark, and the running intent that a Start saved
before the launch was checked stays as saved. No process could have been created on that path. After a launch is recorded the actor spawns with no
further reading, so no refusal of this kind follows the record.

Every refusal is printed on standard error and reported in the page by the step, as the
reason of the failed call. The interval between that reading and the operating system
starting the program, in which the launch is recorded, is not compared: a file replaced in
that interval is started. The environment the child inherits is not compared either. A fixed
command is written and spawned without a reading, at a Start and at each restart alike,
whatever program the command then designates. -/
private def Supervisor.call (supervisor : Supervisor) (directory : RunDirectory)
    (launching : Bool) : (call : Call) → IO (call.Result × RunDirectory)
  | .writeState state => do
    if launching then
      if let some reason ← supervisor.refusal then
        try IO.eprintln reason catch _ => pure ()
        return (Except.error reason, directory)
    let result : Except String Unit ← try
        directory.writeState supervisor.config.child state
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
      let launching := match pending with
        | .launch _ _ => true
        | _ => false
      let (result, directory) ← supervisor.call actor.directory launching
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

/-- Construct only after the bootstrap has admitted the initial state. A state built with no
state file, or restored with the intent its file records, is published here, before the
listener binds. A state whose running intent was set aside, because it was read from an
earlier version's file or was given for another child (`StartSource.kept`), is not published
here: that file stays exactly as it is until the listener is bound, and the bootstrap then
prints and flushes the line that says why the run is shown stopped and publishes this stopped
state with this launch's record, before it prints the ready line or submits and before any
command is processed (`NativeApp.runViewer`). So a start-up that fails before that publication leaves the next
viewer the same file and the same reason for showing the run stopped. A launch relies on no
unpublished state either way, since the attempted launch is saved before the spawn
(`Pending.launch`). The first control record is the start's, and its reason carries the one
line on why the run is shown stopped (`startAccount`) whenever the start state is stopped,
under `--start` too. -/
def Supervisor.new (config : SupervisorConfig) (directory : RunDirectory)
    (persisted : PersistedState) (source : StartSource) : IO Supervisor := do
  unless persisted.identity.browserSafe do
    throw (IO.userError "viewer identity exceeds browser integer precision; retained state is unchanged")
  unless source.kept do directory.writeState config.child persisted
  let account := startAccount source persisted.desired
  let mapRead ← directory.readMap persisted.identity
  let mapRefused := match mapRead with | .refused _ => true | _ => false
  let broadcast ← Broadcast.new persisted.identity persisted.desired
    (persisted.processStarted || mapRefused)
  let initialized := "viewer initialized" ++ (account.map fun line => s!"; {line}").getD ""
  let reason ← match mapRead with
    | .missing => pure initialized
    | .refused reason => pure s!"{initialized}; retained map refused: {reason}"
    | .restored _ memory =>
      let _ ← broadcast.restoreWorld memory
      pure s!"{initialized}; retained map restored as partial"
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
