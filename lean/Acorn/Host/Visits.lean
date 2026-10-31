/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Baseline

/-!
# Runs of visits

A run of visits holds one start and returns to it after every visit, keeping the agent. One visit
is `cap` steps of the world and `cap + 1` decisions. This loop sits beside the attempt loop, which
it does not change, and the campaign does not call it. `AcornVerif.CurrentVisits` proves that every
decision of it is one interaction of the kernel's world in visits (`Kernel.visits`). The native
entry `acorn-core visits` starts it; no theorem relates that entry to the loop.

The loop evaluates the agent's whole step before the world's transition at every step order. The
grid world waits, and `DecisionInput.chooseOwned_release` proves that one pass gives the same values
at both positions; this loop produces no reported durations. So at `.planAfterAct` and
`.actThenLearn` the values are those of the order, and the timing is not its external order.
-/

namespace Acorn.Host

variable {order : StepOrder}

/-- The state every visit of one run begins in: a world with its goal installed, and the raw
result the first percept of every visit carries. The loop holds this value and returns to it. -/
structure VisitStart (config : WorldConfig) (goal : Goal) where
  /-- The world of a visit's first state. -/
  world : World config
  /-- The raw result of a visit's first percept. -/
  carried : RawStepResult
  /-- The goal stays installed by the world's own transition. -/
  installed : world.goal = some goal

/-- Install a goal in a world, once, before the first visit. -/
def VisitStart.install {config : WorldConfig} (world : World config) (carried : RawStepResult)
    (goal : Goal) : VisitStart config goal :=
  ⟨world.setGoal goal, carried, rfl⟩

/-- A run of visits: the visit in progress and what the earlier visits showed. -/
structure VisitRun (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- The visit in progress. `steps` counts the world's steps taken in it. -/
  attempt : Attempt config α goal cap
  /-- Whether a step of the visit in progress has met the goal. -/
  achieved : Bool
  /-- For each completed visit, in order, whether a step of it met the goal. -/
  solved : Array Bool

/-- The first state of a visit: the held start, with the agent and the action fingerprint
carried over. No other value of the agent's type is in scope. -/
def VisitStart.attempt {config : WorldConfig} {α : Type} {goal : Goal} (start : VisitStart config goal)
    (cap : UInt64) (agent : α) (behavior : UInt64) : Attempt config α goal cap :=
  ⟨⟨start.world, agent, start.carried, behavior⟩, start.installed, ⟨0, by omega⟩, ⟨0⟩, .wait⟩

/-- A run before its first decision. -/
def VisitStart.begin {config : WorldConfig} {α : Type} {goal : Goal} (start : VisitStart config goal)
    (cap : UInt64) (agent : α) (behavior : UInt64) : VisitRun config α goal cap :=
  ⟨start.attempt cap agent behavior, false, #[]⟩

/-- What one decision of a visit leaves. -/
structure VisitDecision (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- The action of the decision. The world takes it, unless the decision is the visit's last. -/
  action : Action
  /-- The run after the decision. -/
  next : VisitRun config α goal cap
  /-- The visit's outcome, when the decision was the visit's last. -/
  outcome : Option GoalOutcome

/-- One decision of a run. The world is observed and the agent takes its whole step, as in
`Attempt.complete`, except in two ways. A carried completion ends nothing: the only stop is the
step count. And at a visit's last state, after `cap` steps, the agent still takes its whole step
on the percept that carries the last transition's result; the world does not take that action,
the attempt is recorded, and the run returns to the held start, which replaces the world and the
carried result and keeps the agent. -/
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

/-- The pure content of a run: a number of decisions, in order, until the world refuses. -/
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

/-- What a native run of visits returned. -/
structure VisitsResult (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- The run at its end. -/
  run : VisitRun config α goal cap
  /-- Observer and checkpoint IO failure counters. -/
  resources : RunnerResources
  /-- Whether the decision budget ran out or a stop was honored at a visit's boundary. -/
  ending : CampaignEnd

/-- The write a visit's boundary owes: the checkpoint of the agent, when it is due. -/
def saveAtVisitBoundary {α : Type}
    (checkpoint : Option (WritableCheckpoint × (α → System.FilePath → IO Unit))) (agent : α)
    (closing : Bool) (resources : RunnerResources) : IO RunnerResources :=
  match checkpoint with
  | none => pure resources
  | some (capability, save) =>
    if capability.due closing then saveCheckpoint capability (save agent capability.path) resources
    else pure resources

/-- The native loop of a run of visits. It takes each decision by evaluating `VisitRun.decide`,
and has no other path to the agent or the world. Only at a visit's boundary does it deliver the
outcome, read the stop request and, when due, write the checkpoint, so nothing durable is written
inside a visit. -/
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

/-- Whether a target's goal box holds a world's body. The target's goal is then met before any step
is taken, so it is no member of the class of concealed targets. -/
def targetHoldsBody {config : WorldConfig} (world : World config) (target : Position) : Bool :=
  (world.setGoal (.find target)).goalSatisfied

/-- Start a native run of visits from a given agent. A checkpoint is read as `runCampaign` reads it:
a loaded image replaces the agent, a missing one keeps it, and a refused one disarms every write. -/
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

/-- The decisions of a number of whole visits: `cap` steps and the last state's decision each. -/
def visitDecisions (cap : UInt64) (visits : Nat) : Nat := visits * (cap.toNat + 1)

/-- The uniform-random comparator as callbacks of the visit loop. It reads no observation. -/
def comparatorCallbacks : AgentCallbacks .learnThenAct Rng.Xoshiro256 Unit where
  Chosen := Rng.Xoshiro256
  choose := fun stream _ _ => baselineAction stream
  learn := id
  recordEnvironment := fun stream _ _ => stream
  recordAttempt := fun stream _ _ _ _ => stream
  capture := fun _ => ()
  metrics := fun _ => ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

end Acorn.Host
