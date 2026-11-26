import Acorn.Host.Microduck.Session
import Acorn.Handcrafted.StepParts

namespace Acorn.Host.Microduck

variable {State Choice : Type}

structure Stepper (State Choice : Type) where
  choose : State → Features.Percept Handcrafted.Microduck.interface → Choice
  action : Choice → Action
  learn : Choice → State

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

def Stepper.after (stepper : Stepper State Choice) (agent : State)
    (percepts : List (Features.Percept Handcrafted.Microduck.interface)) : State :=
  percepts.foldl (fun agent percept => stepper.learn (stepper.choose agent percept)) agent

inductive Link where
  | control
  | state
  | depth
  deriving DecidableEq

structure Send where
  link : Link
  text : String

def Line.ofText (text : String) : Line :=
  match Json.parse text with
  | .ok json => Line.read json
  | .error _ => .invalid

def commandLines (commands : List (Nat × Command)) : List Send :=
  commands.map fun pair => ⟨.control, Command.line pair.1 pair.2⟩

structure Counts where
  unreadState : Nat
  unreadDepth : Nat
  invalid : Nat
  sensed : Nat
  released : Nat
  late : Nat

def Counts.zero : Counts := ⟨0, 0, 0, 0, 0, 0⟩

def Counts.hear (counts : Counts) : Line → Counts
  | .unread .state => { counts with unreadState := counts.unreadState + 1 }
  | .unread .depth => { counts with unreadDepth := counts.unreadDepth + 1 }
  | .invalid => { counts with invalid := counts.invalid + 1 }
  | .state _ => counts
  | .depth _ => counts
  | .notice => counts
  | .result _ _ => counts
  | .fault _ => counts

theorem Counts.hear_keeps (counts : Counts) (line : Line) :
    (counts.hear line).sensed = counts.sensed ∧ (counts.hear line).released = counts.released := by
  cases line with
  | unread stream => cases stream <;> exact ⟨rfl, rfl⟩
  | state _ | depth _ | notice | result _ _ | fault _ | invalid => exact ⟨rfl, rfl⟩

inductive Stage (State Choice : Type) where
  | ready (idle : Idle) (agent : State)
  | choosing (awaiting : Awaiting) (choice : Task Choice)
  | released (idle : Idle) (choice : Task Choice)
  | learning (idle : Idle) (agent : Task State)

def Stage.pace : Stage State Choice → Pace
  | .ready idle _ => idle.calm.pace
  | .choosing awaiting _ => awaiting.poised.pace
  | .released idle _ => idle.calm.pace
  | .learning idle _ => idle.calm.pace

theorem Stage.declared (stage : Stage State Choice) :
    Handcrafted.Microduck.interface.timing = .wallClock stage.pace := by
  cases stage with
  | ready idle _ => exact idle.declared
  | choosing awaiting _ => exact awaiting.declared
  | released idle _ => exact idle.declared
  | learning idle _ => exact idle.declared

inductive Event where
  | heard (text : String)
  | tick
  | chosen
  | sent
  | learned

def opening.lines : List Send :=
  [⟨.state, Stream.line 0 .state⟩, ⟨.depth, Stream.line 1 .depth⟩,
    ⟨.control, Command.line 2 .enable⟩]

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
  | .released idle choice => (.released idle choice, counts, none)
  | .learning idle agent => (.learning idle agent, counts, none)

def Stage.hear (line : Line) : Stage State Choice → Stage State Choice
  | .ready idle agent => .ready (idle.hear line) agent
  | .choosing awaiting choice => .choosing (awaiting.hear line) choice
  | .released idle choice => .released (idle.hear line) choice
  | .learning idle agent => .learning (idle.hear line) agent

def Stage.react (stepper : Stepper State Choice) (now : Instant) :
    Event → Stage State Choice → Counts → Stage State Choice × Counts × List Send
  | .heard text, stage, counts =>
    let line := Line.ofText text
    (stage.hear line, counts.hear line, [])
  | .tick, .ready idle agent, counts =>
    (.ready (idle.tick now).1 agent, counts, commandLines (idle.tick now).2.toList)
  | .tick, .choosing awaiting choice, counts =>
    (.choosing (awaiting.tick now).1 choice, counts, commandLines (awaiting.tick now).2.toList)
  | .tick, .released idle choice, counts =>
    (.released (idle.tick now).1 choice, counts, commandLines (idle.tick now).2.toList)
  | .tick, .learning idle agent, counts =>
    (.learning (idle.tick now).1 agent, counts, commandLines (idle.tick now).2.toList)
  | .chosen, .choosing awaiting choice, counts =>
    match awaiting.release awaiting.poised.index now (stepper.action choice.get) with
    | some (idle, commands) =>
      (.released idle choice,
        { counts with
          released := counts.released + 1
          late := counts.late + if idle.calm.late then 1 else 0 },
        commandLines commands)
    | none => (.choosing awaiting choice, counts, [])
  | .chosen, .ready idle agent, counts => (.ready idle agent, counts, [])
  | .chosen, .released idle choice, counts => (.released idle choice, counts, [])
  | .chosen, .learning idle agent, counts => (.learning idle agent, counts, [])
  | .sent, .released idle choice, counts =>
    (.learning idle (Task.spawn fun _ => stepper.learn choice.get), counts, [])
  | .sent, .ready idle agent, counts => (.ready idle agent, counts, [])
  | .sent, .choosing awaiting choice, counts => (.choosing awaiting choice, counts, [])
  | .sent, .learning idle agent, counts => (.learning idle agent, counts, [])
  | .learned, .learning idle agent, counts => (.ready idle agent.get, counts, [])
  | .learned, .ready idle agent, counts => (.ready idle agent, counts, [])
  | .learned, .choosing awaiting choice, counts => (.choosing awaiting choice, counts, [])
  | .learned, .released idle choice, counts => (.released idle choice, counts, [])

structure Stepped (State Choice : Type) where
  stage : Stage State Choice
  counts : Counts
  sends : List Send
  sensed : Option (Features.Percept Handcrafted.Microduck.interface)

def Stage.step (stepper : Stepper State Choice) (now : Instant) (event : Event)
    (stage : Stage State Choice) (counts : Counts) : Stepped State Choice :=
  let reacted := Stage.react stepper now event stage counts
  let attended := Stage.attend stepper now reacted.1 reacted.2.1
  ⟨attended.1, attended.2.1, reacted.2.2, attended.2.2⟩

theorem Stage.step_sends (stepper : Stepper State Choice) (now : Instant) (event : Event)
    (stage : Stage State Choice) (counts : Counts) (send : Send)
    (sent : send ∈ (Stage.step stepper now event stage counts).sends) :
    send.link = .control ∧ ∃ id command, send.text = Command.line id command ∧
      ((event = .tick ∧
        ((∃ idle agent, stage = .ready idle agent ∧ (idle.tick now).2 = some (id, command)) ∨
          (∃ awaiting choice, stage = .choosing awaiting choice ∧
            (awaiting.tick now).2 = some (id, command)) ∨
          (∃ idle choice, stage = .released idle choice ∧
            (idle.tick now).2 = some (id, command)) ∨
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
    | released idle choice =>
      obtain ⟨linked, id, command, text, result⟩ := ticked _ sent
      exact ⟨linked, id, command, text,
        .inl ⟨rfl, .inr (.inr (.inl ⟨idle, choice, rfl, result⟩))⟩⟩
    | learning idle agent =>
      obtain ⟨linked, id, command, text, result⟩ := ticked _ sent
      exact ⟨linked, id, command, text,
        .inl ⟨rfl, .inr (.inr (.inr ⟨idle, agent, rfl, result⟩))⟩⟩
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
    | released idle choice => simp [Stage.react] at sent
    | learning idle agent => simp [Stage.react] at sent
  | sent => cases stage <;> simp [Stage.react] at sent
  | learned => cases stage <;> simp [Stage.react] at sent

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
  | released idle choice =>
    show (Stage.released (idle.hear (Line.ofText text)) choice, _, _) = _
    rw [idled idle]
  | learning idle agent =>
    show (Stage.learning (idle.hear (Line.ofText text)) agent, _, _) = _
    rw [idled idle]

theorem Stage.step_release (stepper : Stepper State Choice) (now : Instant)
    (awaiting : Awaiting) (choice : Task Choice) (counts : Counts) (idle : Idle)
    (commands : List (Nat × Command))
    (released : awaiting.release awaiting.poised.index now (stepper.action choice.get) =
      some (idle, commands)) :
    (Stage.step stepper now .chosen (.choosing awaiting choice) counts).stage =
        .released idle choice ∧
      (Stage.step stepper now .chosen (.choosing awaiting choice) counts).sends =
        commandLines commands ∧
      (Stage.step stepper now .chosen (.choosing awaiting choice) counts).sensed = none ∧
      (Stage.step stepper now .chosen (.choosing awaiting choice) counts).counts.released =
        counts.released + 1 ∧
      (Stage.step stepper now .chosen (.choosing awaiting choice) counts).counts.late =
        counts.late + if idle.calm.late then 1 else 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Stage.step, Stage.react, released, Stage.attend]

theorem Stage.step_sent (stepper : Stepper State Choice) (now : Instant) (idle : Idle)
    (choice : Task Choice) (counts : Counts) :
    ∃ agent, (Stage.step stepper now .sent (.released idle choice) counts).stage =
        .learning idle agent ∧
      agent.get = stepper.learn choice.get ∧
      (Stage.step stepper now .sent (.released idle choice) counts).sends = [] ∧
      (Stage.step stepper now .sent (.released idle choice) counts).sensed = none ∧
      (Stage.step stepper now .sent (.released idle choice) counts).counts = counts :=
  ⟨Task.spawn fun _ => stepper.learn choice.get, rfl, rfl, rfl, rfl, rfl⟩

private theorem attend_learning (stepper : Stepper State Choice) (now : Instant)
    (stage : Stage State Choice) (counts : Counts) (idle : Idle) (agent : Task State)
    (entered : (Stage.attend stepper now stage counts).1 = .learning idle agent) :
    stage = .learning idle agent := by
  cases stage with
  | ready host held =>
    simp only [Stage.attend] at entered
    split at entered <;> simp at entered
  | choosing awaiting choice => simp [Stage.attend] at entered
  | released host choice => simp [Stage.attend] at entered
  | learning host task => simpa [Stage.attend] using entered

theorem Stage.step_learning (stepper : Stepper State Choice) (now : Instant) (event : Event)
    (stage : Stage State Choice) (counts : Counts) (idle : Idle) (agent : Task State)
    (entered : (Stage.step stepper now event stage counts).stage = .learning idle agent)
    (fresh : ∀ idle agent, stage ≠ .learning idle agent) :
    event = .sent ∧ ∃ choice, stage = .released idle choice ∧
      agent.get = stepper.learn choice.get := by
  have reacted := attend_learning stepper now (Stage.react stepper now event stage counts).1
    (Stage.react stepper now event stage counts).2.1 idle agent entered
  cases event with
  | heard text =>
    cases stage with
    | learning host task => exact absurd rfl (fresh host task)
    | _ => simp [Stage.react, Stage.hear] at reacted
  | tick =>
    cases stage with
    | learning host task => exact absurd rfl (fresh host task)
    | _ => simp [Stage.react] at reacted
  | chosen =>
    cases stage with
    | choosing awaiting choice =>
      simp only [Stage.react] at reacted
      split at reacted <;> simp at reacted
    | learning host task => exact absurd rfl (fresh host task)
    | _ => simp [Stage.react] at reacted
  | sent =>
    cases stage with
    | released host choice =>
      simp only [Stage.react, Stage.learning.injEq] at reacted
      obtain ⟨rfl, rfl⟩ := reacted
      exact ⟨rfl, choice, rfl, rfl⟩
    | learning host task => exact absurd rfl (fresh host task)
    | _ => simp [Stage.react] at reacted
  | learned =>
    cases stage with
    | learning host task => exact absurd rfl (fresh host task)
    | _ => simp [Stage.react] at reacted

theorem Stage.step_tick (stepper : Stepper State Choice) (now : Instant) (counts : Counts) :
    (∀ awaiting choice,
      (Stage.step stepper now .tick (.choosing awaiting choice) counts).stage =
          .choosing (awaiting.tick now).1 choice ∧
        (Stage.step stepper now .tick (.choosing awaiting choice) counts).sends =
          commandLines (awaiting.tick now).2.toList) ∧
      (∀ idle choice,
        (Stage.step stepper now .tick (.released idle choice) counts).stage =
            .released (idle.tick now).1 choice ∧
          (Stage.step stepper now .tick (.released idle choice) counts).sends =
            commandLines (idle.tick now).2.toList) ∧
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
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩

private theorem idle_tick_fresh (idle : Idle) (now : Instant) (id : Nat) (command : Command)
    (sent : (idle.tick now).2 = some (id, command)) : opening ≤ id := by
  rw [(Idle.tick_keeps now idle).1] at sent
  obtain ⟨_, _, ticked⟩ := Option.bind_eq_some_iff.mp sent
  obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp ticked
  cases same
  exact idle.identifiers.1

private theorem awaiting_tick_fresh (awaiting : Awaiting) (now : Instant) (id : Nat)
    (command : Command) (sent : (awaiting.tick now).2 = some (id, command)) : opening ≤ id := by
  rw [(Awaiting.tick_keeps now awaiting).1] at sent
  obtain ⟨_, _, ticked⟩ := Option.bind_eq_some_iff.mp sent
  obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp ticked
  cases same
  obtain ⟨_, _, reached⟩ := awaiting.reached
  exact reached.identifiers.1

theorem Stage.step_fresh (stepper : Stepper State Choice) (now : Instant) (event : Event)
    (stage : Stage State Choice) (counts : Counts) (send : Send)
    (sent : send ∈ (Stage.step stepper now event stage counts).sends) :
    ∃ id command, send.text = Command.line id command ∧ opening ≤ id := by
  obtain ⟨_, id, command, text, origin⟩ :=
    Stage.step_sends stepper now event stage counts send sent
  refine ⟨id, command, text, ?_⟩
  rcases origin with
    ⟨_, ⟨idle, _, _, ticked⟩ | ⟨awaiting, _, _, ticked⟩ | ⟨idle, _, _, ticked⟩ |
      ⟨idle, _, _, ticked⟩⟩ | ⟨_, awaiting, _, idle, commands, _, released, member⟩
  · exact idle_tick_fresh idle now id command ticked
  · exact awaiting_tick_fresh awaiting now id command ticked
  · exact idle_tick_fresh idle now id command ticked
  · exact idle_tick_fresh idle now id command ticked
  · obtain ⟨readings, issued, reached⟩ := awaiting.reached
    exact ((Awaiting.release_fresh _ now _ awaiting idle commands released readings issued
      reached).2 (id, command) member).2.1

inductive Ran (stepper : Stepper State Choice) (initial : State) :
    List (Features.Percept Handcrafted.Microduck.interface) → Instant → Stage State Choice →
      Counts → Prop where
  | start {pace : Pace} (declared : Handcrafted.Microduck.interface.timing = .wallClock pace)
      (keep : Keep) (origin : Instant) :
      Ran stepper initial [] origin (.ready (Idle.start declared keep origin) initial)
        Counts.zero
  | step {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last : Instant}
      {stage : Stage State Choice} {counts : Counts}
      (ran : Ran stepper initial percepts last stage counts) (now : Instant)
      (later : last.nanoseconds ≤ now.nanoseconds) (event : Event) :
      Ran stepper initial (percepts ++ (Stage.step stepper now event stage counts).sensed.toList)
        now (Stage.step stepper now event stage counts).stage
        (Stage.step stepper now event stage counts).counts

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
  | .released idle choice, counts =>
    (∃ earlier percept, percepts = earlier ++ [percept] ∧
      choice.get = stepper.choose (stepper.after initial earlier) percept) ∧
      counts.sensed = percepts.length ∧ counts.released = percepts.length ∧
      idle.calm.origin.nanoseconds ≤ last.nanoseconds
  | .learning idle agent, counts =>
    agent.get = stepper.after initial percepts ∧ counts.sensed = percepts.length ∧
      counts.released = percepts.length ∧ idle.calm.origin.nanoseconds ≤ last.nanoseconds

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
  | released idle choice =>
    obtain ⟨chose, sensed, released, begun⟩ := held
    exact ⟨chose, sensed, released, Nat.le_trans begun later⟩
  | learning idle agent =>
    obtain ⟨agreed, sensed, released, begun⟩ := held
    exact ⟨agreed, sensed, released, Nat.le_trans begun later⟩

private theorem origin_le_boundary (pace : Pace) (origin : Instant) (index : Nat) :
    origin.nanoseconds ≤ (pace.boundary origin index).nanoseconds :=
  Nat.le_add_right _ _

private theorem sense_started (idle : Idle) (now : Instant) (awaiting : Awaiting)
    (sensed : Sensed) (found : idle.sense now = some (awaiting, sensed))
    (started : idle.calm.origin.nanoseconds ≤ now.nanoseconds) :
    (awaiting.poised.pace.boundary awaiting.poised.origin awaiting.poised.index).nanoseconds ≤
      now.nanoseconds := by
  obtain ⟨_, _, _, poised, _⟩ := (Idle.sense_iff now idle awaiting sensed).mp found
  rw [poised]
  exact (idle.calm.pace.boundary_le idle.calm.origin
    (idle.calm.pace.index idle.calm.origin now) now).mpr ⟨started, Nat.le_refl _⟩

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
    | released idle choice =>
      obtain ⟨chose, sensed, released, begun⟩ := held
      refine ⟨chose, keptSensed.trans sensed, keptReleased.trans released, ?_⟩
      show (idle.hear (Line.ofText text)).calm.origin.nanoseconds ≤ now.nanoseconds
      rw [(idle.hear_keeps (Line.ofText text)).2.2.1]
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
    | released idle choice =>
      obtain ⟨chose, sensed, released, begun⟩ := held
      refine ⟨chose, sensed, released, ?_⟩
      show (idle.tick now).1.calm.origin.nanoseconds ≤ now.nanoseconds
      rw [(Idle.tick_keeps now idle).2.2.2.1]
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
        refine ⟨⟨earlier, percept, parts, chose⟩, sensed, released, ?_⟩
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
    | released idle choice => exact held.later later
    | learning idle agent => exact held.later later
  | sent =>
    cases stage with
    | released idle choice =>
      obtain ⟨⟨earlier, percept, parts, chose⟩, sensed, released, begun⟩ := held
      refine ⟨?_, sensed, released, Nat.le_trans begun later⟩
      show stepper.learn choice.get = stepper.after initial percepts
      rw [parts, chose]
      unfold Stepper.after
      rw [List.foldl_append]
      rfl
    | ready idle agent => exact held.later later
    | choosing awaiting choice => exact held.later later
    | learning idle agent => exact held.later later
  | learned =>
    cases stage with
    | learning idle agent => exact held.later later
    | ready idle agent => exact held.later later
    | choosing awaiting choice => exact held.later later
    | released idle choice => exact held.later later

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
  | released idle choice =>
    simp only [Stage.attend, Option.toList_none, List.append_nil]
    exact held
  | learning idle agent =>
    simp only [Stage.attend, Option.toList_none, List.append_nil]
    exact held

theorem Ran.held {stepper : Stepper State Choice} {initial : State}
    {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last : Instant}
    {stage : Stage State Choice} {counts : Counts}
    (ran : Ran stepper initial percepts last stage counts) :
    Held stepper initial percepts last stage counts := by
  induction ran with
  | start => exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩
  | @step percepts last stage counts _ now later event hold =>
    exact attend_held stepper initial percepts now _ _
      (react_held stepper initial percepts last now later event stage counts hold)

theorem Ran.agent {stepper : Stepper State Choice} {initial : State}
    {percepts : List (Features.Percept Handcrafted.Microduck.interface)} {last : Instant}
    {stage : Stage State Choice} {counts : Counts}
    (ran : Ran stepper initial percepts last stage counts) :
    (∀ idle agent, stage = .ready idle agent → agent = stepper.after initial percepts) ∧
      (∀ idle agent, stage = .learning idle agent →
        agent.get = stepper.after initial percepts) ∧
      (∀ awaiting choice, stage = .choosing awaiting choice →
        ∃ earlier percept, percepts = earlier ++ [percept] ∧
          choice.get = stepper.choose (stepper.after initial earlier) percept) ∧
      (∀ idle choice, stage = .released idle choice →
        ∃ earlier percept, percepts = earlier ++ [percept] ∧
          choice.get = stepper.choose (stepper.after initial earlier) percept) := by
  have held := ran.held
  refine ⟨fun idle agent same => ?_, fun idle agent same => ?_,
    fun awaiting choice same => ?_, fun idle choice same => ?_⟩ <;> rw [same] at held
  · exact held.1
  · exact held.1
  · exact held.1
  · exact held.1

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
  | released idle choice =>
    obtain ⟨_, sensed, released, _⟩ := held
    exact ⟨sensed, by omega, by omega⟩
  | learning idle agent =>
    obtain ⟨_, sensed, released, _⟩ := held
    exact ⟨sensed, by omega, by omega⟩

structure Loop (stepper : Stepper State Choice) (initial : State) where
  stage : Stage State Choice
  counts : Counts
  last : Instant
  reached : ∃ percepts, Ran stepper initial percepts last stage counts

def Loop.start (stepper : Stepper State Choice) (initial : State) {pace : Pace}
    (declared : Handcrafted.Microduck.interface.timing = .wallClock pace) (keep : Keep)
    (origin : Instant) : Loop stepper initial × List Send :=
  (⟨.ready (Idle.start declared keep origin) initial, Counts.zero, origin,
      [], .start declared keep origin⟩,
    opening.lines)

def Loop.at {stepper : Stepper State Choice} {initial : State} (loop : Loop stepper initial)
    (reading : Instant) : Instant :=
  ⟨max loop.last.nanoseconds reading.nanoseconds⟩

theorem Loop.at_later {stepper : Stepper State Choice} {initial : State}
    (loop : Loop stepper initial) (reading : Instant) :
    loop.last.nanoseconds ≤ (loop.at reading).nanoseconds ∧
      (loop.last.nanoseconds ≤ reading.nanoseconds → loop.at reading = reading) := by
  refine ⟨Nat.le_max_left _ _, fun later => ?_⟩
  unfold Loop.at
  rw [Nat.max_eq_right later]

def Loop.step {stepper : Stepper State Choice} {initial : State} (loop : Loop stepper initial)
    (reading : Instant) (event : Event) : Loop stepper initial × List Send :=
  let now := loop.at reading
  let stepped := Stage.step stepper now event loop.stage loop.counts
  (⟨stepped.stage, stepped.counts, now,
      loop.reached.elim fun _ ran => ⟨_, ran.step now (loop.at_later reading).1 event⟩⟩,
    stepped.sends)

theorem Loop.step_release {stepper : Stepper State Choice} {initial : State}
    (loop : Loop stepper initial) (reading : Instant) (awaiting : Awaiting)
    (choice : Task Choice) (choosing : loop.stage = .choosing awaiting choice) :
    ∃ idle commands,
      awaiting.release awaiting.poised.index (loop.at reading) (stepper.action choice.get) =
          some (idle, commands) ∧
        (loop.step reading .chosen).1.stage = .released idle choice ∧
        (loop.step reading .chosen).2 = commandLines commands := by
  obtain ⟨_, ran⟩ := loop.reached
  obtain ⟨⟨idle, commands⟩, released⟩ := Option.isSome_iff_exists.mp
    (ran.release awaiting choice choosing (loop.at reading) (loop.at_later reading).1
      (stepper.action choice.get))
  obtain ⟨stage, sends, _⟩ :=
    Stage.step_release stepper (loop.at reading) awaiting choice loop.counts idle commands
      released
  refine ⟨idle, commands, released, ?_, ?_⟩
  · show (Stage.step stepper (loop.at reading) .chosen loop.stage loop.counts).stage = _
    rw [choosing]
    exact stage
  · show (Stage.step stepper (loop.at reading) .chosen loop.stage loop.counts).sends = _
    rw [choosing]
    exact sends

theorem Loop.agent {stepper : Stepper State Choice} {initial : State}
    (loop : Loop stepper initial) :
    ∃ percepts, Ran stepper initial percepts loop.last loop.stage loop.counts ∧
      loop.counts.sensed = percepts.length ∧
      (∀ idle agent, loop.stage = .ready idle agent → agent = stepper.after initial percepts) ∧
      (∀ idle agent, loop.stage = .learning idle agent →
        agent.get = stepper.after initial percepts) ∧
      (∀ awaiting choice, loop.stage = .choosing awaiting choice →
        ∃ earlier percept, percepts = earlier ++ [percept] ∧
          choice.get = stepper.choose (stepper.after initial earlier) percept) ∧
      (∀ idle choice, loop.stage = .released idle choice →
        ∃ earlier percept, percepts = earlier ++ [percept] ∧
          choice.get = stepper.choose (stepper.after initial earlier) percept) := by
  obtain ⟨percepts, ran⟩ := loop.reached
  exact ⟨percepts, ran, ran.counts.1, ran.agent⟩

end Acorn.Host.Microduck
