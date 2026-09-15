/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Curriculum
import Acorn.Host.Control
import Acorn.Host.CheckpointDiagnostic
import Acorn.FeatureConsumers

/-!
# Native streaming runner shell

Application transitions remain in `Attempt` and `Campaign`. This shell invokes
the supplied full-agent and persistence owners, isolates observer failures,
and checks supervision only after recording an attempt. It keeps no outcome
history. Filesystem implementation belongs to the supplied persistence owner;
IO, clocks, allocator, thread scheduling and standard runtime primitives remain
explicit native trust boundaries.
-/
namespace Acorn.Host

/-- Closed current research-profile selection; there is no qualified default. -/
inductive ResearchProfile where
  /-- Ranked learned features and subtask interests. -/
  | ranked
  /-- Primitive-only comparison. -/
  | primitive
  /-- Boundary-credit comparison. -/
  | boundaryCredit
  /-- Annealed exploration-rate comparison. -/
  | annealed
  /-- Spatial feature comparison. -/
  | spatial
  deriving DecidableEq, BEq

/-- Only ranked constructions have the current checkpoint representation. -/
def ResearchProfile.resumable : ResearchProfile → Bool
  | .ranked => true
  | .primitive | .boundaryCredit | .annealed | .spatial => false

/-- Full-agent construction receives the actual profile and separate criterion. -/
structure AgentSelection where
  /-- Explicit research composition. -/
  profile : ResearchProfile
  /-- Control criterion is independent of profile. -/
  criterion : Features.Criterion

/-- Native timing and refusal evidence attached at the actual observation boundary. -/
structure CaptureMetrics where
  /-- Duration of this learner call; terminal captures perform no learner call. -/
  updateUs : UInt64
  /-- Duration of the preceding environment commit, initially zero. -/
  environmentUs : UInt64
  /-- Observer refusals before this callback. -/
  observerRefusals : UInt64
  /-- Checkpoint write refusals before this callback. -/
  checkpointFailures : UInt64
  /-- Latest successful checkpoint's observed file size, when metadata was available. -/
  checkpointBytes : Option UInt64
  /-- Latest successful checkpoint's native write duration. -/
  checkpointWriteUs : Option UInt64

/-- One-way consumers may retain rows outside the bounded runner state. -/
structure StreamObserver (β : Type) where
  /-- Actual startup checkpoint result, before any frame can be delivered. -/
  onInitialized : CheckpointAdmission → BaseIO Unit
  /-- Pre-environment observer frame. -/
  onStep : Option (StepFrame β → CaptureMetrics → IO Unit)
  /-- Fresh final-state observer frame. -/
  onAttemptEnd : StepFrame β → CaptureMetrics → IO Unit
  /-- Completed attempt row. -/
  onOutcome : GoalOutcome → IO Unit

/-- Disconnected observation performs no effect and has no influence on actions. -/
def StreamObserver.none {β : Type} : StreamObserver β :=
  ⟨fun _ => pure (), Option.none, fun _ _ => pure (), fun _ => pure ()⟩

/-- Capture is demanded only by an installed step consumer. The thunk contains
no action-selection operation and cannot change the selected transition. -/
def StreamObserver.deliverStep {β : Type} (observer : StreamObserver β)
    (frame : Unit → StepFrame β) (metrics : CaptureMetrics) : IO Unit :=
  match observer.onStep with
  | .none => pure ()
  | some consume => consume (frame ()) metrics

/-- A disconnected observer cannot demand even an arbitrary capture computation. -/
theorem StreamObserver.none_deliverStep {β : Type} (frame : Unit → StepFrame β)
    (metrics : CaptureMetrics) :
    (StreamObserver.none : StreamObserver β).deliverStep frame metrics = pure () := rfl

/-- Persisted-image IO remains an explicit hook for the full checkpoint owner. -/
inductive CheckpointLoad (α : Type) where
  /-- Only successful admission can supply replacement agent state. -/
  | loaded (agent : α)
  /-- A missing image leaves the fresh agent untouched. -/
  | missing
  /-- Refusal preserves the receiving agent and carries its diagnostic. -/
  | refused (message : String)

/-- Persisted-image IO remains an explicit hook for the full checkpoint owner. -/
structure CheckpointHooks (α : Type) where
  /-- Destination supplied once before admission. -/
  path : System.FilePath
  /-- Zero permits load but disables all writes. -/
  interval : UInt32
  /-- Read/validate/install, with a declared missing/refused result and legal returned agent. -/
  load : α → System.FilePath → IO (CheckpointLoad α)
  /-- Serialize the current legal agent to the admitted destination. -/
  save : α → System.FilePath → IO Unit

/-- Explicit shell failure leaves the caller without a false success report. -/
inductive RunnerError where
  /-- Campaign admission failure. -/
  | campaign (error : CampaignError)
  /-- World generation, observation or transition refusal. -/
  | world (error : WorldError)
  /-- Aggregate metric overflow. -/
  | metric (error : MetricError)
  /-- Startup or output IO failure with its native diagnostic text. -/
  | io (message : String)

/-- Current observer and checkpoint failure counts, with saturating word semantics. -/
structure RunnerResources where
  /-- Observer callbacks that failed; execution continues. -/
  observerRefusals : UInt64 := 0
  /-- Checkpoint writes that failed; execution continues. -/
  checkpointFailures : UInt64 := 0
  /-- Disposition of the latest boundary write, retained after the final frame. -/
  checkpointStatus : CheckpointStatus := .disabled
  /-- Preceding measured environment duration, carried across attempt boundaries. -/
  environmentUs : UInt64 := 0
  /-- Size observed after the latest successful checkpoint, if readable. -/
  checkpointBytes : Option UInt64 := none
  /-- Measured duration of the latest successful checkpoint write. -/
  checkpointWriteUs : Option UInt64 := none

/-- Elapsed native nanoseconds become saturating microseconds, without unsigned subtraction wrap. -/
def elapsedMicroseconds (before after : Nat) : UInt64 :=
  (min ((after - before) / 1000) (2 ^ 64 - 1)).toUInt64

/-- Duration conversion has the exact saturating integer meaning for every clock pair. -/
theorem elapsedMicroseconds_exact (before after : Nat) :
    (elapsedMicroseconds before after).toNat = min ((after - before) / 1000) (2 ^ 64 - 1) := by
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_right ((after - before) / 1000) (2 ^ 64 - 1)
  omega

/-- Capture metadata is a projection of the current runner resource state. -/
def RunnerResources.capture (resources : RunnerResources) (updateUs : UInt64) : CaptureMetrics :=
  ⟨updateUs, resources.environmentUs, resources.observerRefusals, resources.checkpointFailures,
    resources.checkpointBytes, resources.checkpointWriteUs⟩

/-- An observer failure affects only its refusal count. -/
def notifyObserver (operation : IO Unit) (resources : RunnerResources) : IO RunnerResources := do
  try
    operation
    return resources
  catch _ => return { resources with observerRefusals := saturatingIncrement64 resources.observerRefusals }

/-- Final observation and outcome bookkeeping use the unchanged attempt owner. -/
def finishAttempt {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks α β) (observer : StreamObserver β) (context : GoalContext)
    (attempt : Attempt config α goal cap) (resources : RunnerResources) :
    IO (Except RunnerError (RunState config α × GoalOutcome × RunnerResources)) := do
  match attempt.finish callbacks context with
  | .error error => return .error (.world error)
  | .ok (run, outcome, frame) =>
    let resources ← notifyObserver (observer.onAttemptEnd frame (resources.capture 0)) resources
    return .ok (run, outcome, resources)

/-- The runtime loop consumes the preceding attempt before selection. Structural
fuel and the attempt's own remaining witness independently bound transitions;
no imperative early-return state retains an obsolete agent through the callback. -/
def runAttemptSteps {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks α β) (observer : StreamObserver β) (context : GoalContext) :
    Nat → Attempt config α goal cap → RunnerResources →
      IO (Except RunnerError (RunState config α × GoalOutcome × RunnerResources))
  | 0, attempt, resources => finishAttempt callbacks observer context attempt resources
  | fuel + 1, attempt, resources => do
    if attempt.finished then return ← finishAttempt callbacks observer context attempt resources
    match attempt.sense with
    | .error error => return .error (.world error)
    | .ok none => finishAttempt callbacks observer context attempt resources
    | .ok (some input) =>
      let beforeUpdate ← IO.monoNanosNow
      let selected ← IO.lazyPure fun _ => input.selectOwned callbacks
      let afterUpdate ← IO.monoNanosNow
      let resources ← notifyObserver (observer.deliverStep (fun _ => selected.frame callbacks context)
        (resources.capture (elapsedMicroseconds beforeUpdate afterUpdate))) resources
      let beforeEnvironment ← IO.monoNanosNow
      let committed ← IO.lazyPure fun _ => selected.environment
      match committed with
      | .error error => return .error (.world error)
      | .ok environment =>
        let afterEnvironment ← IO.monoNanosNow
        let resources := { resources with environmentUs := elapsedMicroseconds beforeEnvironment afterEnvironment }
        runAttemptSteps callbacks observer context fuel (environment.record callbacks) resources

/-- Execute the admitted finite attempt through the same proved selection,
world transition and bookkeeping, capturing only demanded step observations. -/
def runAttempt {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks α β) (observer : StreamObserver β) (context : GoalContext)
    (initial : Attempt config α goal cap) (resources : RunnerResources) :
    IO (Except RunnerError (RunState config α × GoalOutcome × RunnerResources)) :=
  runAttemptSteps callbacks observer context cap.toNat initial resources

/-- The reason a successfully running campaign returned. -/
inductive CampaignEnd where
  /-- Finite repetition budget exhausted, including an empty finite campaign. -/
  | complete
  /-- Cooperative stop observed at the attempt boundary. -/
  | stopped
  deriving DecidableEq

/-- Final bounded runner state, with report rows owned by the observer. -/
structure CampaignResult (config : WorldConfig) (α : Type) where
  /-- Final continual stream, including the undiscarded last reward. -/
  run : RunState config α
  /-- Exact total steps across accepted outcomes. -/
  totalSteps : UInt64
  /-- Two-word summary of every completed outcome, in order. -/
  outcomes : OutcomeFold
  /-- Saturating completed-attempt total; checkpoint phase is independently indexed. -/
  attempts : UInt32
  /-- Observer and checkpoint IO failure counters. -/
  resources : RunnerResources
  /-- Actual exit boundary. -/
  ending : CampaignEnd

/-- A campaign cursor derives all outcome metadata from the admitted receiving plan. -/
def CampaignCursor.context {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (tier : UInt8) : GoalContext :=
  ⟨cursor.goal.val.toUInt64, cursor.attempt.val.toUInt64, tier, cursor.cycle⟩

/-- Reported attempt identity preserves the full admitted cursor domain. -/
theorem CampaignCursor.context_attempt {size : Nat} {plan : CampaignPlan size}
    (cursor : CampaignCursor plan) (tier : UInt8) :
    (cursor.context tier).attempt.toNat = cursor.attempt.val := by
  change cursor.attempt.val % (2 ^ 64) = cursor.attempt.val
  apply Nat.mod_eq_of_lt
  have := cursor.attempt.isLt
  have := plan.attempts.toNat_lt
  omega

/-- Execute an armed checkpoint and retain its actual result independently of
optional size/timing observations. A failed confirmation does not prove that
no bytes reached the destination. -/
def saveCheckpoint (capability : WritableCheckpoint) (write : IO Unit)
    (resources : RunnerResources) : IO RunnerResources := do
  let beforeWrite ← IO.monoNanosNow
  try
    write
    let afterWrite ← IO.monoNanosNow
    let bytes ← try pure (some (← capability.path.metadata).byteSize) catch _ => pure none
    return { resources with
      checkpointStatus := .saved
      checkpointBytes := bytes
      checkpointWriteUs := some (elapsedMicroseconds beforeWrite afterWrite) }
  catch error =>
    try IO.eprintln s!"checkpoint: cannot write {capability.path}: {error}" catch _ => pure ()
    return { resources with
      checkpointFailures := saturatingIncrement64 resources.checkpointFailures
      checkpointStatus := .failed }

/-- The actual scheduling owner selects the receiving agent and admitted path
before invoking the shared checkpoint writer. -/
def checkpointAction {size : Nat} {plan : CampaignPlan size} {α : Type}
    (agent : α) (checkpoint : Option (WritableCheckpoint × (α → System.FilePath → IO Unit)))
    (decision : BoundaryDecision plan) (resources : RunnerResources) :
    IO RunnerResources :=
  match checkpoint with
  | none => pure resources
  | some (capability, save) =>
    if capability.dueAt decision then
      saveCheckpoint capability (save agent capability.path) resources
    else pure resources

/-- Every closing boundary with a capability selects the actual writer with
exactly the current agent and admitted destination; writer admission is not assumed. -/
theorem checkpointAction_closing {size : Nat} {plan : CampaignPlan size} {α : Type}
    (agent : α) (capability : WritableCheckpoint) (save : α → System.FilePath → IO Unit)
    (decision : BoundaryDecision plan) (resources : RunnerResources)
    (closing : decision.closing = true) :
    checkpointAction agent (some (capability, save)) decision resources =
      saveCheckpoint capability (save agent capability.path) resources := by
  simp only [checkpointAction, capability.closing_due decision closing, ↓reduceIte]

/-- A boundary cannot be returned until its checkpoint action has returned.
The action includes scheduling, write failure accounting and diagnostics; IO
exceptions propagate instead of manufacturing a completion receipt. -/
def completeBoundary {size : Nat} {plan : CampaignPlan size}
    (decision : BoundaryDecision plan) (checkpoint : IO RunnerResources) :
    IO (RunnerResources × BoundaryDecision plan) :=
  EST.bind checkpoint (fun resources => EST.pure (resources, decision))

/-- The executed IO boundary returns precisely after its actual checkpoint action,
with the action's resulting native world and the unchanged execution decision.
This conditional progress law assumes effect completion, not successful saving. -/
theorem completeBoundary_returns {size : Nat} {plan : CampaignPlan size}
    (decision : BoundaryDecision plan) (checkpoint : IO RunnerResources)
    (before after : Void IO.RealWorld) (resources : RunnerResources)
    (returned : checkpoint before = .ok resources after) :
    completeBoundary decision checkpoint before = .ok (resources, decision) after := by
  simp only [completeBoundary, EST.bind, EST.pure, returned]

/-- Native failure cannot bypass the checkpoint action and claim an ending. -/
theorem completeBoundary_error {size : Nat} {plan : CampaignPlan size}
    (decision : BoundaryDecision plan) (checkpoint : IO RunnerResources)
    (before after : Void IO.RealWorld) (error : IO.Error)
    (failed : checkpoint before = .error error after) :
    completeBoundary decision checkpoint before = .error error after := by
  simp only [completeBoundary, EST.bind, failed]

/-- Any successful boundary receipt witnesses that the actual checkpoint action
returned; no independently modeled write or assumed-equivalent implementation is used. -/
theorem completeBoundary_requires {size : Nat} {plan : CampaignPlan size}
    (decision : BoundaryDecision plan) (checkpoint : IO RunnerResources)
    (before after : Void IO.RealWorld) (resources : RunnerResources)
    (returned : completeBoundary decision checkpoint before = .ok (resources, decision) after) :
    checkpoint before = .ok resources after := by
  simp only [completeBoundary, EST.bind, EST.pure] at returned
  cases actual : checkpoint before with
  | ok value world =>
    rw [actual] at returned
    cases returned
    rfl
  | error error world => rw [actual] at returned; contradiction

/-- Complete native campaign loop after domain and startup admission. -/
def runAdmittedCampaign {config : WorldConfig} {α β : Type} (curriculum : Curriculum)
    (plan : CampaignPlan curriculum.size) (callbacks : AgentCallbacks α β) (observer : StreamObserver β)
    (initial : RunState config α) (checkpoint : Option (WritableCheckpoint × (α → System.FilePath → IO Unit)))
    (readStop : BaseIO Bool) (admission : CheckpointAdmission := .missing) :
    IO (Except RunnerError (CampaignResult config α)) := do
  let mut checkpoint := checkpoint
  let mut run := initial
  let mut decision := plan.initial
  let mut totalSteps : UInt64 := 0
  let mut outcomes : OutcomeFold := {}
  let mut attempts : UInt32 := 0
  let mut resources : RunnerResources := { checkpointStatus :=
    if checkpoint.isSome then .pending else if admission == .refused then .refused else .disabled }
  repeat
    match decision with
    | .complete => return .ok ⟨run, totalSteps, outcomes, attempts, resources, .complete⟩
    | .stopped => return .ok ⟨run, totalSteps, outcomes, attempts, resources, .stopped⟩
    | .continue cursor =>
      have hg : cursor.goal.val < curriculum.size := by have := cursor.goal.isLt; have := plan.goals.isLt; omega
      let (goal, tier) := curriculum[cursor.goal.val]'hg
      let context := cursor.context tier
      let started := Attempt.start run goal plan.stepCap
      match ← runAttempt callbacks observer context started resources with
      | .error error => return .error error
      | .ok (next, outcome, observed) =>
        match addOutcomeSteps totalSteps outcome with
        | .error error => return .error (.metric error)
        | .ok total => totalSteps := total
        run := next
        outcomes := outcomes.push outcome
        resources ← notifyObserver (observer.onOutcome outcome) observed
        attempts := saturatingIncrement32 attempts
        checkpoint := checkpoint.map fun (capability, save) => (capability.advance, save)
        let stopping ← readStop
        let boundary := atAttemptBoundary cursor outcome.achieved stopping
        let (savedResources, nextDecision) ← completeBoundary boundary
          (checkpointAction run.agent checkpoint boundary resources)
        resources := savedResources
        decision := nextDecision

/-- Startup preserves refusal order and never constructs an agent before campaign admission.
Unexpected loader errors retain the fresh agent and disable writes, like a refused image. -/
def runCampaign {α β : Type} (config : WorldConfig) (seed : UInt64) (selection : AgentSelection)
    (spec : CampaignSpec) (buildAgent : AgentSelection → IO α) (callbacks : AgentCallbacks α β)
    (observer : StreamObserver β) (checkpoint : Option (CheckpointHooks α)) (readStop : BaseIO Bool) :
    IO (Except RunnerError (CampaignResult config α)) := do
  if !selection.profile.resumable && checkpoint.isSome then return .error (.campaign .nonresumableProfile)
  let curriculum := standardCurriculum config seed
  match CampaignPlan.admit curriculum.size spec with
  | .error error => return .error (.campaign error)
  | .ok plan =>
    match World.initial config with
    | .error error => return .error (.world error)
    | .ok world =>
      try
        let mut agent ← buildAgent selection
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
        let initial : RunState config α := ⟨world, agent, {}, initialBehavior⟩
        runAdmittedCampaign curriculum plan callbacks observer initial writable readStop admission
      catch error => return .error (.io error.toString)

end Acorn.Host
