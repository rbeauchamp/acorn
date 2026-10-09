/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Microduck.Session
import Acorn.Handcrafted.StepParts

/-!
# The executing loop of a Microduck host: its pure core

A host of the Microduck's world runs a continuing loop: it hears the lines of two daemons,
reads its clock, senses a percept when a cycle is due, gives the percept to the agent,
releases the action the agent chose and lets the agent learn, while the world goes on. This
module is the loop's core, with no effect: a state, the events a driver hands it, each with
a reading of the clock, and one step for each event, which returns the next state and the
lines to send. The driver that reads a clock and sockets and runs the loop is not built here.

**The stages make the illegal states unrepresentable.** A loop is in one of three stages
(`Stage`): `ready`, with no percept awaiting and the agent free to take one; `choosing`, with
a percept awaiting while the agent computes the first part of its step; `learning`, with the
action released while the agent computes the second part. A percept awaits exactly while the
agent chooses, since `choosing` is the only stage that holds an `Awaiting`, and no percept is
sensed while the agent chooses or learns, since sensing happens only in `ready`. So the agent
takes one step at a time, in the order of its two parts.

**A loop is sealed by its run.** A `Loop` holds a stage, its counts and the instant of its
last step, with a derivation (`Ran`) from its start by steps at instants that do not go back,
for its stepper and its starting agent. There is no other way to a value, so the task of a
choosing loop computes the stepper's choice on the percept its host awaits, and a learning
loop follows a release (`Loop.agent`). `Loop.step` takes the instant of a step to be the
later of the clock's reading and the instant of the last step (`Loop.at_later`), so the
instants of a loop do not go back, whatever a driver reads. The transitions of a stage
(`Stage.step`) are what `Ran` and `Loop.step` are made of; a driver holds a `Loop`.

**The agent's work is a pure task.** The two parts are a `Stepper`: a choice from a percept,
the action of a choice, and the agent that learning a choice gives. The loop holds each part
as `Task.spawn` of that function on its inputs, so the runtime computes it apart from the
loop while the loop goes on hearing lines and reading the clock, and its value is the
function's value: the action released for a percept is the stepper's action of its choice on
that percept (`Stage.step_sense`, `Loop.step_release`). A step runs each transition once, so
it spawns each task once, and it returns the percept it sensed. A driver only says that a task
has finished, with `Event.chosen` or `Event.learned`; when it says so early, the step waits
for the task. `Stepper.ofAgent` is the agent of this repository under the step order
`actThenLearn`, whose two parts compose to `Agent.actOrdered` (`Stepper.ofAgent_step`).

**Every event goes through the host's own transitions.** A line goes through `Idle.hear` or
`Awaiting.hear`, after `Line.read` of the value that `Json.parse` gives its text, read once
for the host and the counts; a text that does not parse is the line `invalid`. A tick of the
clock goes through `Idle.tick` or `Awaiting.tick` in every stage, so the velocity of the last
release is sent again while the agent computes (`Stage.step_tick`). A finished choice goes
through `Awaiting.release` for the awaited cycle (`Stage.step_release`). After every event in
`ready`, `Idle.sense` at the step's instant starts a choice when a percept is due
(`Stage.step_sense`). The instant of a loop's step is never before its host's origin, since a
loop starts at the origin and its instants do not go back, so `Idle.sense` is the only test
of sensing.

**What is sent.** At the start, the three opening requests: the subscription to the state
stream on the state connection, the subscription to the depth stream on the depth connection
and the command that enables the policy on the control connection, with the identifiers 0,
1 and 2 (`Loop.start`). After the start, exactly the lines of the commands that the host's
tick and release return, each `Command.line` of its identifier and command on the control
connection (`Stage.step_sends`), each with an identifier of at least `opening`, so none
reuses the identifier of an opening request (`Stage.step_fresh`). The type of a command has
no relax, no shutdown and no disable.

**A refused frame.** A notification of a stream whose frame a reader refuses is counted for
its stream, and an invalid line is counted, and neither changes anything else
(`Stage.react_refused`). So a stream that sends only frames the host cannot read shows in the
counts; nothing repairs it.

**A run.** Of every loop: the agent it holds, or its task computes, is the fold of the
stepper's two parts over the percepts sensed, in order (`Loop.agent`); the step of a finished
choice releases the stepper's action of it, since the release of the awaited cycle is
admitted at every instant from the last step on (`Loop.step_release`); and the counts hold one
percept for each percept sensed and a release for each but the one awaited (`Ran.counts`).

**Trusted, and not stated.** That a driver hands the events in the order they happened, with
readings of one monotonic clock; that the runtime computes a task's value; when a task
finishes; and every effect of sending a line. A reading before the instant of the last step
is taken as that instant, so the statements here hold of every sequence of readings, and only
the timing of the world depends on the clock. The loop counts late releases; how many a run
has is a measurement.
-/
namespace Acorn.Host.Microduck

variable {State Choice : Type}

/-! ## The agent's two parts -/

/-- The two parts of the agent's step, as the loop calls them: the first part, a choice from
the agent and a percept; the action of a choice; and the second part, the agent after it
learns from a choice. -/
structure Stepper (State Choice : Type) where
  /-- The first part of a step. -/
  choose : State → Features.Percept Handcrafted.Microduck.interface → Choice
  /-- The action of a choice. -/
  action : Choice → Action
  /-- The second part of a step. -/
  learn : Choice → State

/-- The agent of this repository under the step order `actThenLearn`: the first part of its
step, the action of the action table at the index of its decision, and the second part. -/
def Stepper.ofAgent (profile : Handcrafted.FeatureProfile) (config : Features.Config)
    (criterion : Features.Criterion) (dimension : Dimension)
    (planning : Features.PlanningSelection) :
    Stepper
      (Handcrafted.Agent Handcrafted.Microduck.interface profile config criterion dimension
        planning)
      (Handcrafted.Chosen Handcrafted.Microduck.interface profile config criterion dimension
        planning) where
  choose := fun agent percept => agent.choose .actThenLearn percept
  action := fun chosen =>
    Action.named (Fin.cast Handcrafted.Microduck.interface_actions chosen.decision.action)
  learn := Handcrafted.Chosen.learn

/-- **The two parts of the bound agent are its whole step.** For every agent and percept:
learning from the choice gives the agent of `Agent.actOrdered` under `actThenLearn`, and the
action of the choice is the action at the index of its decision. -/
theorem Stepper.ofAgent_step (profile : Handcrafted.FeatureProfile) (config : Features.Config)
    (criterion : Features.Criterion) (dimension : Dimension)
    (planning : Features.PlanningSelection)
    (agent : Handcrafted.Agent Handcrafted.Microduck.interface profile config criterion
      dimension planning)
    (percept : Features.Percept Handcrafted.Microduck.interface) :
    (Stepper.ofAgent profile config criterion dimension planning).learn
        ((Stepper.ofAgent profile config criterion dimension planning).choose agent percept) =
      (agent.actOrdered .actThenLearn percept).1 ∧
      (Stepper.ofAgent profile config criterion dimension planning).action
        ((Stepper.ofAgent profile config criterion dimension planning).choose agent percept) =
        Action.named (Fin.cast Handcrafted.Microduck.interface_actions
          (agent.actOrdered .actThenLearn percept).2.action) :=
  ⟨rfl, rfl⟩

/-- The agent after both parts of a step on each percept, in order. -/
def Stepper.after (stepper : Stepper State Choice) (agent : State)
    (percepts : List (Features.Percept Handcrafted.Microduck.interface)) : State :=
  percepts.foldl (fun agent percept => stepper.learn (stepper.choose agent percept)) agent

/-! ## Lines in and out -/

/-- The connection a line travels on: the control connection of the state daemon, which
carries the commands and their answers; the subscription to the state stream; and the
subscription to the depth stream, of the depth daemon. -/
inductive Link where
  /-- Commands and their answers. -/
  | control
  /-- The state stream. -/
  | state
  /-- The depth stream. -/
  | depth
  deriving DecidableEq

/-- A line to send, and the connection it goes on. -/
structure Send where
  /-- The connection. -/
  link : Link
  /-- The text of the line, without its line break. -/
  text : String

/-- The line of a text of a daemon: the case that `Line.read` gives the value its text
parses to, and `invalid` for a text that does not parse. -/
def Line.ofText (text : String) : Line :=
  match Json.parse text with
  | .ok json => Line.read json
  | .error _ => .invalid

/-- The lines of commands, each on the control connection with its identifier. -/
def commandLines (commands : List (Nat × Command)) : List Send :=
  commands.map fun pair => ⟨.control, Command.line pair.1 pair.2⟩

/-- What a host counts while it runs. -/
structure Counts where
  /-- Notifications of the state stream whose frame was refused. -/
  unreadState : Nat
  /-- Notifications of the depth stream whose frame was refused. -/
  unreadDepth : Nat
  /-- Lines that are no notification and no response by the criteria of `Line.read`, and
  texts that do not parse. -/
  invalid : Nat
  /-- Percepts sensed. -/
  sensed : Nat
  /-- Actions released. -/
  released : Nat
  /-- Actions released at or after their deadline. -/
  late : Nat

/-- Nothing counted. -/
def Counts.zero : Counts := ⟨0, 0, 0, 0, 0, 0⟩

/-- A line is counted: a refused frame for its stream, an invalid line as invalid, and
nothing for any other line. -/
def Counts.hear (counts : Counts) : Line → Counts
  | .unread .state => { counts with unreadState := counts.unreadState + 1 }
  | .unread .depth => { counts with unreadDepth := counts.unreadDepth + 1 }
  | .invalid => { counts with invalid := counts.invalid + 1 }
  | .state _ => counts
  | .depth _ => counts
  | .notice => counts
  | .result _ _ => counts
  | .fault _ => counts

/-- Counting a line counts no percept and no release. -/
theorem Counts.hear_keeps (counts : Counts) (line : Line) :
    (counts.hear line).sensed = counts.sensed ∧ (counts.hear line).released = counts.released := by
  cases line with
  | unread stream => cases stream <;> exact ⟨rfl, rfl⟩
  | state _ | depth _ | notice | result _ _ | fault _ | invalid => exact ⟨rfl, rfl⟩

/-! ## The stages and their step -/

/-- What the loop is doing. -/
inductive Stage (State Choice : Type) where
  /-- No percept awaits, and the agent can take one. -/
  | ready (idle : Idle) (agent : State)
  /-- A percept awaits, and the agent computes the first part of its step. -/
  | choosing (awaiting : Awaiting) (choice : Task Choice)
  /-- The action is released, and the agent computes the second part of its step. -/
  | learning (idle : Idle) (agent : Task State)

/-- What a driver hands the loop. -/
inductive Event where
  /-- A daemon wrote a line, with this text. -/
  | heard (text : String)
  /-- The clock was read. -/
  | tick
  /-- The agent's choice has finished. -/
  | chosen
  /-- The agent's learning has finished. -/
  | learned

/-- The three opening requests: the subscription to the state stream, the subscription to
the depth stream and the command that enables the policy, with the identifiers 0, 1 and 2,
each on its connection. -/
def opening.lines : List Send :=
  [⟨.state, Stream.line 0 .state⟩, ⟨.depth, Stream.line 1 .depth⟩,
    ⟨.control, Command.line 2 .enable⟩]

/-- In `ready`, a percept is sensed at the instant when one is due, and the agent's choice on
it starts; the percept is returned. Every other stage is as it was, and senses nothing. -/
def Stage.attend (stepper : Stepper State Choice) (now : Instant) (stage : Stage State Choice)
    (counts : Counts) :
    Stage State Choice × Counts × Option (Features.Percept Handcrafted.Microduck.interface) :=
  match stage with
  | .ready idle agent =>
    match idle.sense now with
    | some (awaiting, sensed) =>
      (.choosing awaiting (Task.spawn fun _ => stepper.choose agent sensed.percept),
        { counts with sensed := counts.sensed + 1 }, some sensed.percept)
    | none => (.ready idle agent, counts, none)
  | .choosing awaiting choice => (.choosing awaiting choice, counts, none)
  | .learning idle agent => (.learning idle agent, counts, none)

/-- A line is heard in a stage: the host the stage holds hears it, and the agent's task is
kept. -/
def Stage.hear (line : Line) : Stage State Choice → Stage State Choice
  | .ready idle agent => .ready (idle.hear line) agent
  | .choosing awaiting choice => .choosing (awaiting.hear line) choice
  | .learning idle agent => .learning (idle.hear line) agent

/-- What an event makes of a stage, before a percept is sensed: the next stage, the counts
and the lines to send. A text heard is read once, and its line goes to the host and to the
counts. A release that the host refuses leaves the stage as it was; no loop meets one
(`Loop.step_release`). -/
def Stage.react (stepper : Stepper State Choice) (now : Instant) :
    Event → Stage State Choice → Counts → Stage State Choice × Counts × List Send
  | .heard text, stage, counts =>
    let line := Line.ofText text
    (stage.hear line, counts.hear line, [])
  | .tick, .ready idle agent, counts =>
    (.ready (idle.tick now).1 agent, counts, commandLines (idle.tick now).2.toList)
  | .tick, .choosing awaiting choice, counts =>
    (.choosing (awaiting.tick now).1 choice, counts, commandLines (awaiting.tick now).2.toList)
  | .tick, .learning idle agent, counts =>
    (.learning (idle.tick now).1 agent, counts, commandLines (idle.tick now).2.toList)
  | .chosen, .choosing awaiting choice, counts =>
    match awaiting.release awaiting.poised.index now (stepper.action choice.get) with
    | some (idle, commands) =>
      (.learning idle (Task.spawn fun _ => stepper.learn choice.get),
        { counts with
          released := counts.released + 1
          late := counts.late + if idle.calm.late then 1 else 0 },
        commandLines commands)
    | none => (.choosing awaiting choice, counts, [])
  | .chosen, .ready idle agent, counts => (.ready idle agent, counts, [])
  | .chosen, .learning idle agent, counts => (.learning idle agent, counts, [])
  | .learned, .learning idle agent, counts => (.ready idle agent.get, counts, [])
  | .learned, .ready idle agent, counts => (.ready idle agent, counts, [])
  | .learned, .choosing awaiting choice, counts => (.choosing awaiting choice, counts, [])

/-- What one step makes of a stage and its counts. -/
structure Stepped (State Choice : Type) where
  /-- The next stage. -/
  stage : Stage State Choice
  /-- The next counts. -/
  counts : Counts
  /-- The lines to send. -/
  sends : List Send
  /-- The percept sensed, if one was. -/
  sensed : Option (Features.Percept Handcrafted.Microduck.interface)

/-- One step of a stage: the event at the instant through the host's transitions, then, in
`ready`, a percept sensed when one is due. The lines to send are those of the event. Each
transition runs once, so each task is spawned once. -/
def Stage.step (stepper : Stepper State Choice) (now : Instant) (event : Event)
    (stage : Stage State Choice) (counts : Counts) : Stepped State Choice :=
  let reacted := Stage.react stepper now event stage counts
  let attended := Stage.attend stepper now reacted.1 reacted.2.1
  ⟨attended.1, attended.2.1, reacted.2.2, attended.2.2⟩

/-! ## One step of a stage -/

/-- **After the start, a step sends only lines of commands that the host's transitions
returned.** For every stage, counts, instant and event: every line sent is on the control
connection, and it is the line of a command with its identifier, among those that the host's
tick returned when the event is a tick, and those that the host's release returned when the
event is a finished choice. No other event sends a line. `Stage.step_tick` and
`Stage.step_release` state that the lines sent are exactly those. -/
theorem Stage.step_sends (stepper : Stepper State Choice) (now : Instant) (event : Event)
    (stage : Stage State Choice) (counts : Counts) (send : Send)
    (sent : send ∈ (Stage.step stepper now event stage counts).sends) :
    send.link = .control ∧ ∃ id command, send.text = Command.line id command ∧
      ((event = .tick ∧
        ((∃ idle agent, stage = .ready idle agent ∧ (idle.tick now).2 = some (id, command)) ∨
          (∃ awaiting choice, stage = .choosing awaiting choice ∧
            (awaiting.tick now).2 = some (id, command)) ∨
          (∃ idle agent, stage = .learning idle agent ∧
            (idle.tick now).2 = some (id, command)))) ∨
        (event = .chosen ∧ ∃ awaiting choice idle commands,
          stage = .choosing awaiting choice ∧
          awaiting.release awaiting.poised.index now (stepper.action choice.get) =
            some (idle, commands) ∧ (id, command) ∈ commands)) := by
  have lined : ∀ (commands : List (Nat × Command)), send ∈ commandLines commands →
      send.link = .control ∧ ∃ id command, send.text = Command.line id command ∧
        (id, command) ∈ commands := by
    intro commands inside
    obtain ⟨pair, member, rfl⟩ := List.mem_map.mp inside
    exact ⟨rfl, pair.1, pair.2, rfl, member⟩
  have ticked : ∀ (result : Option (Nat × Command)), send ∈ commandLines result.toList →
      send.link = .control ∧ ∃ id command, send.text = Command.line id command ∧
        result = some (id, command) := by
    intro result inside
    obtain ⟨linked, id, command, text, member⟩ := lined _ inside
    refine ⟨linked, id, command, text, ?_⟩
    cases result with
    | none => exact nomatch member
    | some pair =>
      cases List.mem_singleton.mp member
      rfl
  change send ∈ (Stage.react stepper now event stage counts).2.2 at sent
  cases event with
  | heard text => cases stage <;> simp [Stage.react] at sent
  | tick =>
    cases stage with
    | ready idle agent =>
      obtain ⟨linked, id, command, text, result⟩ := ticked _ sent
      exact ⟨linked, id, command, text, .inl ⟨rfl, .inl ⟨idle, agent, rfl, result⟩⟩⟩
    | choosing awaiting choice =>
      obtain ⟨linked, id, command, text, result⟩ := ticked _ sent
      exact ⟨linked, id, command, text,
        .inl ⟨rfl, .inr (.inl ⟨awaiting, choice, rfl, result⟩)⟩⟩
    | learning idle agent =>
      obtain ⟨linked, id, command, text, result⟩ := ticked _ sent
      exact ⟨linked, id, command, text,
        .inl ⟨rfl, .inr (.inr ⟨idle, agent, rfl, result⟩)⟩⟩
  | chosen =>
    cases stage with
    | choosing awaiting choice =>
      simp only [Stage.react] at sent
      split at sent
      · rename_i idle commands released
        obtain ⟨linked, id, command, text, member⟩ := lined _ sent
        exact ⟨linked, id, command, text,
          .inr ⟨rfl, awaiting, choice, idle, commands, rfl, released, member⟩⟩
      · exact nomatch sent
    | ready idle agent => simp [Stage.react] at sent
    | learning idle agent => simp [Stage.react] at sent
  | learned => cases stage <;> simp [Stage.react] at sent

/-- **A percept due at the step's instant starts the stepper's choice on it.** For every step
whose event leaves the stage ready with a host that senses a percept at the instant: after the
step the stage chooses, with the host that sensing returned and the task of the stepper's
choice by the ready agent on the percept, the step returns that percept, and it counts one
percept more. -/
theorem Stage.step_sense (stepper : Stepper State Choice) (now : Instant) (event : Event)
    (stage : Stage State Choice) (counts : Counts) (idle : Idle) (agent : State)
    (awaiting : Awaiting) (sensed : Sensed)
    (ready : (Stage.react stepper now event stage counts).1 = .ready idle agent)
    (found : idle.sense now = some (awaiting, sensed)) :
    ∃ choice, (Stage.step stepper now event stage counts).stage = .choosing awaiting choice ∧
      choice.get = stepper.choose agent sensed.percept ∧
      (Stage.step stepper now event stage counts).sensed = some sensed.percept ∧
      (Stage.step stepper now event stage counts).counts.sensed =
        (Stage.react stepper now event stage counts).2.1.sensed + 1 := by
  refine ⟨Task.spawn fun _ => stepper.choose agent sensed.percept, ?_, rfl, ?_, ?_⟩ <;>
    simp only [Stage.step, ready, Stage.attend, found]

/-- **A refused frame and an invalid line change nothing but their count.** For every stage,
counts and instant: a line heard whose text reads as a notification of a stream with a
refused frame, or as an invalid line, leaves the stage as it was, counts the line, and sends
nothing. The step may still sense a percept at the instant, as after any event. -/
theorem Stage.react_refused (stepper : Stepper State Choice) (now : Instant) (text : String)
    (stage : Stage State Choice) (counts : Counts)
    (refused : (∃ stream, Line.ofText text = .unread stream) ∨ Line.ofText text = .invalid) :
    Stage.react stepper now (.heard text) stage counts =
      (stage, counts.hear (Line.ofText text), []) := by
  have idled : ∀ idle : Idle, idle.hear (Line.ofText text) = idle := by
    intro idle
    rcases refused with ⟨stream, read⟩ | read <;> rw [read]
    · exact (idle.hear_refused stream).1
    · exact (idle.hear_refused .state).2
  have awaited : ∀ awaiting : Awaiting, awaiting.hear (Line.ofText text) = awaiting := by
    intro awaiting
    rcases refused with ⟨stream, read⟩ | read <;> rw [read]
    · exact (awaiting.hear_refused stream).1
    · exact (awaiting.hear_refused .state).2
  cases stage with
  | ready idle agent =>
    show (Stage.ready (idle.hear (Line.ofText text)) agent, _, _) = _
    rw [idled idle]
  | choosing awaiting choice =>
    show (Stage.choosing (awaiting.hear (Line.ofText text)) choice, _, _) = _
    rw [awaited awaiting]
  | learning idle agent =>
    show (Stage.learning (idle.hear (Line.ofText text)) agent, _, _) = _
    rw [idled idle]

/-- **A finished choice releases the stepper's action of it, and the agent learns from the
same choice.** For every choosing stage and every instant at which the host admits the
release of the awaited cycle with that action: after the step the stage learns, with the host
that the release returned and the task of the stepper's learning from the choice, the step
sends the lines of the commands of the release and senses nothing, and it counts one release
more, and one late release more when the release is late. -/
theorem Stage.step_release (stepper : Stepper State Choice) (now : Instant)
    (awaiting : Awaiting) (choice : Task Choice) (counts : Counts) (idle : Idle)
    (commands : List (Nat × Command))
    (released : awaiting.release awaiting.poised.index now (stepper.action choice.get) =
      some (idle, commands)) :
    ∃ agent,
      (Stage.step stepper now .chosen (.choosing awaiting choice) counts).stage =
          .learning idle agent ∧
        agent.get = stepper.learn choice.get ∧
        (Stage.step stepper now .chosen (.choosing awaiting choice) counts).sends =
          commandLines commands ∧
        (Stage.step stepper now .chosen (.choosing awaiting choice) counts).sensed = none ∧
        (Stage.step stepper now .chosen (.choosing awaiting choice) counts).counts.released =
          counts.released + 1 ∧
        (Stage.step stepper now .chosen (.choosing awaiting choice) counts).counts.late =
          counts.late + if idle.calm.late then 1 else 0 := by
  refine ⟨Task.spawn fun _ => stepper.learn choice.get, ?_, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Stage.step, Stage.react, released, Stage.attend]

/-- **A tick reaches the host in every stage.** For every instant and counts: in a choosing or
learning stage the host after a tick is the host's own tick, the task is kept, and the lines
sent are those of the command the tick returned; in a ready stage the same holds of the stage
before a percept is sensed. So the velocity of the last release is sent again while the agent
computes. -/
theorem Stage.step_tick (stepper : Stepper State Choice) (now : Instant) (counts : Counts) :
    (∀ awaiting choice,
      (Stage.step stepper now .tick (.choosing awaiting choice) counts).stage =
          .choosing (awaiting.tick now).1 choice ∧
        (Stage.step stepper now .tick (.choosing awaiting choice) counts).sends =
          commandLines (awaiting.tick now).2.toList) ∧
      (∀ idle agent,
        (Stage.step stepper now .tick (.learning idle agent) counts).stage =
            .learning (idle.tick now).1 agent ∧
          (Stage.step stepper now .tick (.learning idle agent) counts).sends =
            commandLines (idle.tick now).2.toList) ∧
      (∀ idle agent,
        (Stage.react stepper now .tick (.ready idle agent) counts).1 =
            .ready (idle.tick now).1 agent ∧
          (Stage.step stepper now .tick (.ready idle agent) counts).sends =
            commandLines (idle.tick now).2.toList) :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩

/-- The command a tick of an idle host sends has the host's next unused identifier. -/
private theorem idle_tick_fresh (idle : Idle) (now : Instant) (id : Nat) (command : Command)
    (sent : (idle.tick now).2 = some (id, command)) : opening ≤ id := by
  rw [(Idle.tick_keeps now idle).1] at sent
  obtain ⟨_, _, ticked⟩ := Option.bind_eq_some_iff.mp sent
  obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp ticked
  cases same
  exact idle.identifiers.1

/-- The command a tick of an awaiting host sends has the host's next unused identifier. -/
private theorem awaiting_tick_fresh (awaiting : Awaiting) (now : Instant) (id : Nat)
    (command : Command) (sent : (awaiting.tick now).2 = some (id, command)) : opening ≤ id := by
  rw [(Awaiting.tick_keeps now awaiting).1] at sent
  obtain ⟨_, _, ticked⟩ := Option.bind_eq_some_iff.mp sent
  obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp ticked
  cases same
  obtain ⟨_, _, reached⟩ := awaiting.reached
  exact reached.identifiers.1

/-- **No command after the start reuses the identifier of an opening request.** For every
step: every line sent is the line of a command whose identifier is at least `opening`, so
none is 0, 1 or 2, the identifiers of the subscriptions and of the enabling command, and an
answer to an opening request is never attributed to a command. -/
theorem Stage.step_fresh (stepper : Stepper State Choice) (now : Instant) (event : Event)
    (stage : Stage State Choice) (counts : Counts) (send : Send)
    (sent : send ∈ (Stage.step stepper now event stage counts).sends) :
    ∃ id command, send.text = Command.line id command ∧ opening ≤ id := by
  obtain ⟨_, id, command, text, origin⟩ :=
    Stage.step_sends stepper now event stage counts send sent
  refine ⟨id, command, text, ?_⟩
  rcases origin with
    ⟨_, ⟨idle, _, _, ticked⟩ | ⟨awaiting, _, _, ticked⟩ | ⟨idle, _, _, ticked⟩⟩ |
      ⟨_, awaiting, _, idle, commands, _, released, member⟩
  · exact idle_tick_fresh idle now id command ticked
  · exact awaiting_tick_fresh awaiting now id command ticked
  · exact idle_tick_fresh idle now id command ticked
  · obtain ⟨readings, issued, reached⟩ := awaiting.reached
    exact ((Awaiting.release_fresh _ now _ awaiting idle commands released readings issued
      reached).2 (id, command) member).2.1

/-! ## A run -/

/-- A stage and its counts are reached from the start with an agent by steps at instants that
do not go back, with the percepts sensed on the way, in order, and the instant of the last
step (the origin at the start). One constructor for each way to a stage. -/
inductive Ran (stepper : Stepper State Choice) (initial : State) :
    List (Features.Percept Handcrafted.Microduck.interface) → Instant → Stage State Choice →
      Counts → Prop where
  /-- The loop starts. -/
  | start (pace : Pace) (keep : Keep) (origin : Instant) :
      Ran stepper initial [] origin (.ready (Idle.start pace keep origin) initial) Counts.zero
  /-- The loop takes a step at an instant not before the last one. -/
  | step {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last : Instant}
      {stage : Stage State Choice} {counts : Counts}
      (ran : Ran stepper initial percepts last stage counts) (now : Instant)
      (later : last.nanoseconds ≤ now.nanoseconds) (event : Event) :
      Ran stepper initial (percepts ++ (Stage.step stepper now event stage counts).sensed.toList)
        now (Stage.step stepper now event stage counts).stage
        (Stage.step stepper now event stage counts).counts

/-- What a reached stage holds, for the percepts sensed and the instant of its last step. -/
def Held (stepper : Stepper State Choice) (initial : State)
    (percepts : List (Features.Percept Handcrafted.Microduck.interface)) (last : Instant) :
    Stage State Choice → Counts → Prop
  | .ready idle agent, counts =>
    agent = stepper.after initial percepts ∧ counts.sensed = percepts.length ∧
      counts.released = percepts.length ∧ idle.calm.origin.nanoseconds ≤ last.nanoseconds
  | .choosing awaiting choice, counts =>
    (∃ earlier percept, percepts = earlier ++ [percept] ∧
      choice.get = stepper.choose (stepper.after initial earlier) percept) ∧
      counts.sensed = percepts.length ∧ counts.released + 1 = percepts.length ∧
      (awaiting.poised.pace.boundary awaiting.poised.origin awaiting.poised.index).nanoseconds ≤
        last.nanoseconds
  | .learning idle agent, counts =>
    agent.get = stepper.after initial percepts ∧ counts.sensed = percepts.length ∧
      counts.released = percepts.length ∧ idle.calm.origin.nanoseconds ≤ last.nanoseconds

/-- What a reached stage holds at its last instant it holds at every later one. -/
private theorem Held.later {stepper : Stepper State Choice} {initial : State}
    {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last now : Instant}
    {stage : Stage State Choice} {counts : Counts}
    (held : Held stepper initial percepts last stage counts)
    (later : last.nanoseconds ≤ now.nanoseconds) :
    Held stepper initial percepts now stage counts := by
  cases stage with
  | ready idle agent =>
    obtain ⟨agreed, sensed, released, begun⟩ := held
    exact ⟨agreed, sensed, released, Nat.le_trans begun later⟩
  | choosing awaiting choice =>
    obtain ⟨chose, sensed, released, begun⟩ := held
    exact ⟨chose, sensed, released, Nat.le_trans begun later⟩
  | learning idle agent =>
    obtain ⟨agreed, sensed, released, begun⟩ := held
    exact ⟨agreed, sensed, released, Nat.le_trans begun later⟩

/-- The origin of a host is not after the start of any of its cycles. -/
private theorem origin_le_boundary (pace : Pace) (origin : Instant) (index : Nat) :
    origin.nanoseconds ≤ (pace.boundary origin index).nanoseconds :=
  Nat.le_add_right _ _

/-- A percept sensed at an instant not before the host's origin awaits a cycle that has
started at that instant. -/
private theorem sense_started (idle : Idle) (now : Instant) (awaiting : Awaiting)
    (sensed : Sensed) (found : idle.sense now = some (awaiting, sensed))
    (started : idle.calm.origin.nanoseconds ≤ now.nanoseconds) :
    (awaiting.poised.pace.boundary awaiting.poised.origin awaiting.poised.index).nanoseconds ≤
      now.nanoseconds := by
  obtain ⟨_, _, _, poised, _⟩ := (Idle.sense_iff now idle awaiting sensed).mp found
  rw [poised]
  exact (idle.calm.pace.boundary_le idle.calm.origin
    (idle.calm.pace.index idle.calm.origin now) now).mpr ⟨started, Nat.le_refl _⟩

/-- An event keeps what a reached stage holds, at a later instant. A finished choice is
released, since its cycle had started by the last step and so by this one. -/
private theorem react_held (stepper : Stepper State Choice) (initial : State)
    (percepts : List (Features.Percept Handcrafted.Microduck.interface)) (last now : Instant)
    (later : last.nanoseconds ≤ now.nanoseconds) (event : Event) (stage : Stage State Choice)
    (counts : Counts) (held : Held stepper initial percepts last stage counts) :
    Held stepper initial percepts now (Stage.react stepper now event stage counts).1
      (Stage.react stepper now event stage counts).2.1 := by
  cases event with
  | heard text =>
    obtain ⟨keptSensed, keptReleased⟩ := counts.hear_keeps (Line.ofText text)
    cases stage with
    | ready idle agent =>
      obtain ⟨agreed, sensed, released, begun⟩ := held
      refine ⟨agreed, keptSensed.trans sensed, keptReleased.trans released, ?_⟩
      show (idle.hear (Line.ofText text)).calm.origin.nanoseconds ≤ now.nanoseconds
      rw [(idle.hear_keeps (Line.ofText text)).2.2.1]
      exact Nat.le_trans begun later
    | choosing awaiting choice =>
      obtain ⟨chose, sensed, released, begun⟩ := held
      obtain ⟨paced, _, started, _, _, _, indexed, _⟩ := awaiting.hear_keeps (Line.ofText text)
      refine ⟨chose, keptSensed.trans sensed, ?_, ?_⟩
      · show (counts.hear (Line.ofText text)).released + 1 = percepts.length
        rw [keptReleased]
        exact released
      · show ((awaiting.hear (Line.ofText text)).poised.pace.boundary
          (awaiting.hear (Line.ofText text)).poised.origin
          (awaiting.hear (Line.ofText text)).poised.index).nanoseconds ≤ now.nanoseconds
        rw [paced, started, indexed]
        exact Nat.le_trans begun later
    | learning idle agent =>
      obtain ⟨agreed, sensed, released, begun⟩ := held
      refine ⟨agreed, keptSensed.trans sensed, keptReleased.trans released, ?_⟩
      show (idle.hear (Line.ofText text)).calm.origin.nanoseconds ≤ now.nanoseconds
      rw [(idle.hear_keeps (Line.ofText text)).2.2.1]
      exact Nat.le_trans begun later
  | tick =>
    cases stage with
    | ready idle agent =>
      obtain ⟨agreed, sensed, released, begun⟩ := held
      refine ⟨agreed, sensed, released, ?_⟩
      show (idle.tick now).1.calm.origin.nanoseconds ≤ now.nanoseconds
      rw [(Idle.tick_keeps now idle).2.2.2.1]
      exact Nat.le_trans begun later
    | choosing awaiting choice =>
      obtain ⟨chose, sensed, released, begun⟩ := held
      obtain ⟨_, paced, _, started, _, _, _, indexed, _, _⟩ := Awaiting.tick_keeps now awaiting
      refine ⟨chose, sensed, released, ?_⟩
      show ((awaiting.tick now).1.poised.pace.boundary (awaiting.tick now).1.poised.origin
        (awaiting.tick now).1.poised.index).nanoseconds ≤ now.nanoseconds
      rw [paced, started, indexed]
      exact Nat.le_trans begun later
    | learning idle agent =>
      obtain ⟨agreed, sensed, released, begun⟩ := held
      refine ⟨agreed, sensed, released, ?_⟩
      show (idle.tick now).1.calm.origin.nanoseconds ≤ now.nanoseconds
      rw [(Idle.tick_keeps now idle).2.2.2.1]
      exact Nat.le_trans begun later
  | chosen =>
    cases stage with
    | choosing awaiting choice =>
      obtain ⟨⟨earlier, percept, parts, chose⟩, sensed, released, begun⟩ := held
      cases result : awaiting.release awaiting.poised.index now (stepper.action choice.get) with
      | some pair =>
        obtain ⟨idle, commands⟩ := pair
        simp only [Stage.react, result]
        refine ⟨?_, sensed, released, ?_⟩
        · show stepper.learn choice.get = stepper.after initial percepts
          rw [parts, chose]
          unfold Stepper.after
          rw [List.foldl_append]
          rfl
        · show idle.calm.origin.nanoseconds ≤ now.nanoseconds
          obtain ⟨_, _, calm, _⟩ :=
            (Awaiting.release_iff _ _ _ awaiting idle commands).mp result
          rw [calm]
          exact Nat.le_trans (origin_le_boundary awaiting.poised.pace awaiting.poised.origin
            awaiting.poised.index) (Nat.le_trans begun later)
      | none =>
        have admitted := (Awaiting.release_admitted awaiting.poised.index now
          (stepper.action choice.get) awaiting).mpr ⟨rfl, Nat.le_trans begun later⟩
        rw [result] at admitted
        simp at admitted
    | ready idle agent => exact held.later later
    | learning idle agent => exact held.later later
  | learned =>
    cases stage with
    | learning idle agent => exact held.later later
    | ready idle agent => exact held.later later
    | choosing awaiting choice => exact held.later later

/-- Sensing keeps what a reached stage holds, with the percept sensed appended. -/
private theorem attend_held (stepper : Stepper State Choice) (initial : State)
    (percepts : List (Features.Percept Handcrafted.Microduck.interface)) (now : Instant)
    (stage : Stage State Choice) (counts : Counts)
    (held : Held stepper initial percepts now stage counts) :
    Held stepper initial (percepts ++ (Stage.attend stepper now stage counts).2.2.toList) now
      (Stage.attend stepper now stage counts).1 (Stage.attend stepper now stage counts).2.1 := by
  cases stage with
  | ready idle agent =>
    obtain ⟨agreed, sensed, released, begun⟩ := held
    cases found : idle.sense now with
    | none =>
      simp only [Stage.attend, found, Option.toList_none, List.append_nil]
      exact ⟨agreed, sensed, released, begun⟩
    | some pair =>
      obtain ⟨awaiting, given⟩ := pair
      simp only [Stage.attend, found, Option.toList_some]
      refine ⟨⟨percepts, given.percept, rfl, by rw [agreed]; rfl⟩, ?_, ?_,
        sense_started idle now awaiting given found begun⟩
      · rw [List.length_append, sensed]
        rfl
      · rw [List.length_append, released]
        rfl
  | choosing awaiting choice =>
    simp only [Stage.attend, Option.toList_none, List.append_nil]
    exact held
  | learning idle agent =>
    simp only [Stage.attend, Option.toList_none, List.append_nil]
    exact held

/-- **What every reached stage holds.** For every stage reached from the start with an agent,
with the percepts sensed and the instant of its last step: a ready stage holds the agent after
both parts of a step on each percept sensed, in order; a choosing stage computes the stepper's
choice on the last percept sensed, by the agent after the percepts before it, for a cycle that
had started by its last step; a learning stage computes the agent after every percept sensed;
the host of a ready or learning stage has its origin by the last step; and the counts hold one
percept for each percept sensed and one release for each, but the one a choosing stage
awaits. -/
theorem Ran.held {stepper : Stepper State Choice} {initial : State}
    {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last : Instant}
    {stage : Stage State Choice} {counts : Counts}
    (ran : Ran stepper initial percepts last stage counts) :
    Held stepper initial percepts last stage counts := by
  induction ran with
  | start pace keep origin => exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩
  | @step percepts last stage counts _ now later event hold =>
    exact attend_held stepper initial percepts now _ _
      (react_held stepper initial percepts last now later event stage counts hold)

/-- **The agent of a reached stage is the agent after its whole steps on the percepts
sensed.** For every reached stage: when ready, the agent it holds is the fold of the
stepper's two parts over the percepts sensed, in order, from the starting agent; when
learning, its task computes that agent; and when choosing, its task computes the stepper's
choice on the last percept by the agent after the ones before. -/
theorem Ran.agent {stepper : Stepper State Choice} {initial : State}
    {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last : Instant}
    {stage : Stage State Choice} {counts : Counts}
    (ran : Ran stepper initial percepts last stage counts) :
    (∀ idle agent, stage = .ready idle agent → agent = stepper.after initial percepts) ∧
      (∀ idle agent, stage = .learning idle agent →
        agent.get = stepper.after initial percepts) ∧
      (∀ awaiting choice, stage = .choosing awaiting choice →
        ∃ earlier percept, percepts = earlier ++ [percept] ∧
          choice.get = stepper.choose (stepper.after initial earlier) percept) := by
  have held := ran.held
  refine ⟨fun idle agent same => ?_, fun idle agent same => ?_,
    fun awaiting choice same => ?_⟩ <;> rw [same] at held
  · exact held.1
  · exact held.1
  · exact held.1

/-- **A reached stage that chooses has its release admitted at every instant from its last
step on.** -/
theorem Ran.release {stepper : Stepper State Choice} {initial : State}
    {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last : Instant}
    {stage : Stage State Choice} {counts : Counts}
    (ran : Ran stepper initial percepts last stage counts)
    (awaiting : Awaiting) (choice : Task Choice) (choosing : stage = .choosing awaiting choice)
    (now : Instant) (later : last.nanoseconds ≤ now.nanoseconds) (action : Action) :
    (awaiting.release awaiting.poised.index now action).isSome = true := by
  have held := ran.held
  rw [choosing] at held
  obtain ⟨_, _, _, begun⟩ := held
  exact (Awaiting.release_admitted awaiting.poised.index now action awaiting).mpr
    ⟨rfl, Nat.le_trans begun later⟩

/-- **The counts of a reached stage.** One percept counted for each percept sensed; the
releases are those percepts but the one a choosing stage awaits, so never more and at most
one fewer. -/
theorem Ran.counts {stepper : Stepper State Choice} {initial : State}
    {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last : Instant}
    {stage : Stage State Choice} {counts : Counts}
    (ran : Ran stepper initial percepts last stage counts) :
    counts.sensed = percepts.length ∧ counts.released ≤ counts.sensed ∧
      counts.sensed ≤ counts.released + 1 := by
  have held := ran.held
  cases stage with
  | ready idle agent =>
    obtain ⟨_, sensed, released, _⟩ := held
    exact ⟨sensed, by omega, by omega⟩
  | choosing awaiting choice =>
    obtain ⟨_, sensed, released, _⟩ := held
    exact ⟨sensed, by omega, by omega⟩
  | learning idle agent =>
    obtain ⟨_, sensed, released, _⟩ := held
    exact ⟨sensed, by omega, by omega⟩

/-! ## The loop -/

/-- A loop: its stage, its counts and the instant of its last step, with a derivation from
its start for its stepper and its starting agent. Every value is reached by `Loop.start` and
`Loop.step`, so its tasks compute the stepper's parts on what the loop sensed. -/
structure Loop (stepper : Stepper State Choice) (initial : State) where
  /-- The stage. -/
  stage : Stage State Choice
  /-- The counts. -/
  counts : Counts
  /-- The instant of the last step, and the origin at the start. -/
  last : Instant
  /-- The loop is reached from its start, with the percepts sensed on the way. -/
  reached : ∃ percepts, Ran stepper initial percepts last stage counts

/-- The loop at its start: ready, with a host that has heard nothing and the starting agent,
nothing counted, the origin as the instant of its last step, and the opening requests to
send. -/
def Loop.start (stepper : Stepper State Choice) (initial : State) (pace : Pace) (keep : Keep)
    (origin : Instant) : Loop stepper initial × List Send :=
  (⟨.ready (Idle.start pace keep origin) initial, Counts.zero, origin,
      [], .start pace keep origin⟩,
    opening.lines)

/-- The instant of a step at a reading of the clock: the reading, or the instant of the last
step when the reading is before it. -/
def Loop.at {stepper : Stepper State Choice} {initial : State} (loop : Loop stepper initial)
    (reading : Instant) : Instant :=
  ⟨max loop.last.nanoseconds reading.nanoseconds⟩

/-- **The instants of a loop do not go back.** For every loop and reading of the clock: the
instant of the step is not before the instant of the last step, and it is the reading when
the reading is not before it. -/
theorem Loop.at_later {stepper : Stepper State Choice} {initial : State}
    (loop : Loop stepper initial) (reading : Instant) :
    loop.last.nanoseconds ≤ (loop.at reading).nanoseconds ∧
      (loop.last.nanoseconds ≤ reading.nanoseconds → loop.at reading = reading) := by
  refine ⟨Nat.le_max_left _ _, fun later => ?_⟩
  unfold Loop.at
  rw [Nat.max_eq_right later]

/-- One step of the loop at a reading of the clock: the step of its stage at the instant that
`Loop.at` gives, which becomes the instant of its last step. The lines to send are those of
the step. -/
def Loop.step {stepper : Stepper State Choice} {initial : State} (loop : Loop stepper initial)
    (reading : Instant) (event : Event) : Loop stepper initial × List Send :=
  let now := loop.at reading
  let stepped := Stage.step stepper now event loop.stage loop.counts
  (⟨stepped.stage, stepped.counts, now,
      loop.reached.elim fun _ ran => ⟨_, ran.step now (loop.at_later reading).1 event⟩⟩,
    stepped.sends)

/-- **The step of a finished choice releases the stepper's action of it, and the agent learns
from the same choice.** For every loop that chooses and every reading of the clock: the host
admits the release of the awaited cycle with the stepper's action of the choice at the step's
instant, and after the step the loop learns, with the host that the release returned and the
task of the stepper's learning from the choice, and it sends the lines of the commands of the
release. -/
theorem Loop.step_release {stepper : Stepper State Choice} {initial : State}
    (loop : Loop stepper initial) (reading : Instant) (awaiting : Awaiting)
    (choice : Task Choice) (choosing : loop.stage = .choosing awaiting choice) :
    ∃ idle commands,
      awaiting.release awaiting.poised.index (loop.at reading) (stepper.action choice.get) =
          some (idle, commands) ∧
        ∃ agent, (loop.step reading .chosen).1.stage = .learning idle agent ∧
          agent.get = stepper.learn choice.get ∧
          (loop.step reading .chosen).2 = commandLines commands := by
  obtain ⟨_, ran⟩ := loop.reached
  obtain ⟨⟨idle, commands⟩, released⟩ := Option.isSome_iff_exists.mp
    (ran.release awaiting choice choosing (loop.at reading) (loop.at_later reading).1
      (stepper.action choice.get))
  obtain ⟨agent, stage, learned, sends, _⟩ :=
    Stage.step_release stepper (loop.at reading) awaiting choice loop.counts idle commands
      released
  refine ⟨idle, commands, released, agent, ?_, learned, ?_⟩
  · show (Stage.step stepper (loop.at reading) .chosen loop.stage loop.counts).stage = _
    rw [choosing]
    exact stage
  · show (Stage.step stepper (loop.at reading) .chosen loop.stage loop.counts).sends = _
    rw [choosing]
    exact sends

/-- **The agent a loop holds is the agent after its whole steps on the percepts it sensed.**
For every loop there are the percepts of a run from its start to it, as many as it counted,
such that: when ready, the agent it holds is the fold of the stepper's two parts over them,
in order, from the starting agent; when learning, its task computes that agent; and when
choosing, its task computes the stepper's choice on the last of them by the agent after the
ones before. -/
theorem Loop.agent {stepper : Stepper State Choice} {initial : State}
    (loop : Loop stepper initial) :
    ∃ percepts, Ran stepper initial percepts loop.last loop.stage loop.counts ∧
      loop.counts.sensed = percepts.length ∧
      (∀ idle agent, loop.stage = .ready idle agent → agent = stepper.after initial percepts) ∧
      (∀ idle agent, loop.stage = .learning idle agent →
        agent.get = stepper.after initial percepts) ∧
      (∀ awaiting choice, loop.stage = .choosing awaiting choice →
        ∃ earlier percept, percepts = earlier ++ [percept] ∧
          choice.get = stepper.choose (stepper.after initial earlier) percept) := by
  obtain ⟨percepts, ran⟩ := loop.reached
  exact ⟨percepts, ran, ran.counts.1, ran.agent⟩

end Acorn.Host.Microduck
