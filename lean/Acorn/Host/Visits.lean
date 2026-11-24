import Acorn.Host.Baseline

namespace Acorn.Host

variable {order : StepOrder}

structure VisitStart (config : WorldConfig) (goal : Goal) where
  world : World config
  carried : RawStepResult
  installed : world.goal = some goal

def VisitStart.install {config : WorldConfig} (world : World config) (carried : RawStepResult)
    (goal : Goal) : VisitStart config goal :=
  ⟨world.setGoal goal, carried, rfl⟩

structure VisitRun (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  attempt : Attempt config α goal cap
  achieved : Bool
  solved : Array Bool

def VisitStart.attempt {config : WorldConfig} {α : Type} {goal : Goal} (start : VisitStart config goal)
    (cap : UInt64) (agent : α) (behavior : UInt64) : Attempt config α goal cap :=
  ⟨⟨start.world, agent, start.carried, behavior⟩, start.installed, ⟨0, by omega⟩, ⟨0⟩, .wait⟩

def VisitStart.begin {config : WorldConfig} {α : Type} {goal : Goal} (start : VisitStart config goal)
    (cap : UInt64) (agent : α) (behavior : UInt64) : VisitRun config α goal cap :=
  ⟨start.attempt cap agent behavior, false, #[]⟩

structure VisitDecision (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  action : Action
  next : VisitRun config α goal cap
  outcome : Option GoalOutcome

@[noinline] def VisitRun.decide {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (start : VisitStart config goal)
    (run : VisitRun config α goal cap) :
    Except (Refusal config α goal cap) (VisitDecision config α goal cap) :=
  let ⟨attempt, achieved, solved⟩ := run
  match sensed : attempt.run.world.observe with
  | .error error => .error ⟨error, none⟩
  | .ok observation =>
    if within : attempt.steps.val < cap.toNat then
      match (DecisionInput.selectOwned ⟨attempt, within, observation, sensed⟩ callbacks).release with
      | .refused error learned => .error ⟨error, some learned⟩
      | .accepted environment =>
        .ok ⟨environment.selected.action,
          ⟨environment.record callbacks, achieved || environment.result.done, solved⟩, none⟩
    else
      let chosen := callbacks.act attempt.run.agent observation attempt.run.carried
      let visit := solved.size.toUInt64
      let steps := attempt.steps.val.toUInt64
      let agent := callbacks.recordAttempt chosen.2 goal.family visit steps achieved
      .ok ⟨chosen.1,
        ⟨start.attempt cap agent (foldAction attempt.run.behavior chosen.1), false,
          solved.push achieved⟩,
        some ⟨0, visit, 0, steps, achieved, attempt.reward, callbacks.metrics agent,
          attempt.run.world.body.position.position⟩⟩

def VisitRun.after {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (start : VisitStart config goal)
    (initial : VisitRun config α goal cap) :
    Nat → Except (Refusal config α goal cap) (VisitRun config α goal cap)
  | 0 => .ok initial
  | count + 1 =>
    match VisitRun.after callbacks start initial count with
    | .error refusal => .error refusal
    | .ok run =>
      match run.decide callbacks start with
      | .error refusal => .error refusal
      | .ok decision => .ok decision.next

structure VisitsResult (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  run : VisitRun config α goal cap
  resources : RunnerResources
  ending : CampaignEnd

def saveAtVisitBoundary {α : Type}
    (checkpoint : Option (WritableCheckpoint × (α → System.FilePath → IO Unit))) (agent : α)
    (closing : Bool) (resources : RunnerResources) : IO RunnerResources :=
  match checkpoint with
  | none => pure resources
  | some (capability, save) =>
    if capability.due closing then saveCheckpoint capability (save agent capability.path) resources
    else pure resources

def runVisitDecisions {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (observer : StreamObserver β)
    (start : VisitStart config goal) (readStop : BaseIO Bool) :
    Nat → VisitRun config α goal cap → RunnerResources →
      Option (WritableCheckpoint × (α → System.FilePath → IO Unit)) →
      IO (Except (Refusal config α goal cap) (VisitsResult config α goal cap))
  | 0, run, resources, _ => return .ok ⟨run, resources, .complete⟩
  | fuel + 1, run, resources, checkpoint => do
    let decided ← IO.lazyPure fun _ => run.decide callbacks start
    match decided with
    | .error refusal => return .error refusal
    | .ok decision =>
      match decision.outcome with
      | none => runVisitDecisions callbacks observer start readStop fuel decision.next resources checkpoint
      | some outcome =>
        let resources ← notifyObserver (observer.onOutcome outcome) resources
        let stopping ← readStop
        let checkpoint := checkpoint.map fun (capability, save) => (capability.advance, save)
        let resources ← saveAtVisitBoundary checkpoint decision.next.attempt.run.agent
          (stopping || fuel == 0) resources
        if stopping then return .ok ⟨decision.next, resources, .stopped⟩
        else runVisitDecisions callbacks observer start readStop fuel decision.next resources checkpoint

def targetHoldsBody {config : WorldConfig} (world : World config) (target : Position) : Bool :=
  (world.setGoal (.find target)).goalSatisfied

def runVisitsFrom {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (observer : StreamObserver β)
    (start : VisitStart config goal) (readStop : BaseIO Bool) (budget : Nat) (fresh : α)
    (checkpoint : Option (CheckpointHooks α)) :
    IO (Except (Refusal config α goal cap) (VisitsResult config α goal cap)) := do
  let mut agent := fresh
  let mut writable := none
  let mut admission := CheckpointAdmission.missing
  if let some hooks := checkpoint then
    let loaded ← try hooks.load agent hooks.path catch error => pure (.refused error.toString)
    let status ← match loaded with
      | .loaded restored =>
        agent := restored
        pure CheckpointAdmission.loaded
      | .missing => pure CheckpointAdmission.missing
      | .refused message => do
        try IO.eprintln (checkpointRefusalMessage message) catch _ => pure ()
        pure CheckpointAdmission.refused
    if let some capability := WritableCheckpoint.admit hooks.path hooks.interval status then
      writable := some (capability, hooks.save)
    admission := status
  observer.onInitialized admission
  let resources : RunnerResources := { checkpointStatus :=
    if writable.isSome then .pending else if admission == .refused then .refused else .disabled }
  runVisitDecisions callbacks observer start readStop budget
    (start.begin cap agent initialBehavior) resources writable

def visitDecisions (cap : UInt64) (visits : Nat) : Nat := visits * (cap.toNat + 1)

def comparatorCallbacks : AgentCallbacks .learnThenAct Rng.Xoshiro256 Unit where
  Chosen := Rng.Xoshiro256
  choose := fun stream _ _ => baselineAction stream
  learn := id
  recordEnvironment := fun stream _ _ => stream
  recordAttempt := fun stream _ _ _ _ => stream
  capture := fun _ => ()
  metrics := fun _ => ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

end Acorn.Host
