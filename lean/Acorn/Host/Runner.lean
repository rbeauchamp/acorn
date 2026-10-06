/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Curriculum
import Acorn.Host.Control
import Acorn.Host.CheckpointDiagnostic
import Acorn.FeatureConsumers
import Acorn.Timing

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

variable {order : StepOrder}

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
  /-- Duration of this step's agent computation, both parts together; terminal
  captures perform no agent computation. -/
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
    (callbacks : AgentCallbacks order α β) (observer : StreamObserver β) (context : GoalContext)
    (attempt : Attempt config α goal cap) (resources : RunnerResources) :
    IO (Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources)) := do
  match attempt.finish callbacks context with
  | .error error => return .error ⟨error, none⟩
  | .ok (run, outcome, frame) =>
    let resources ← notifyObserver (observer.onAttemptEnd frame (resources.capture 0)) resources
    return .ok (run, outcome, resources)

/-- The runtime loop consumes the preceding attempt before selection. Structural
fuel and the attempt's own remaining witness independently bound transitions;
no imperative early-return state retains an obsolete agent through the callback. A
refused action returns the refusal with the stage of that pass, which the whole step
has already learned. -/
def runAttemptSteps {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks .learnThenAct α β) (observer : StreamObserver β) (context : GoalContext) :
    Nat → Attempt config α goal cap → RunnerResources →
      IO (Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources))
  | 0, attempt, resources => finishAttempt callbacks observer context attempt resources
  | fuel + 1, attempt, resources => do
    if attempt.finished then return ← finishAttempt callbacks observer context attempt resources
    match attempt.sense with
    | .error error => return .error ⟨error, none⟩
    | .ok none => finishAttempt callbacks observer context attempt resources
    | .ok (some input) =>
      let beforeUpdate ← IO.monoNanosNow
      let selected ← IO.lazyPure fun _ => input.selectOwned callbacks
      let afterUpdate ← IO.monoNanosNow
      let resources ← notifyObserver (observer.deliverStep (fun _ => selected.frame callbacks context)
        (resources.capture (elapsedMicroseconds beforeUpdate afterUpdate))) resources
      let beforeEnvironment ← IO.monoNanosNow
      let released ← IO.lazyPure fun _ => selected.release
      match released with
      | .refused error learned => return .error ⟨error, some learned⟩
      | .accepted environment =>
        let afterEnvironment ← IO.monoNanosNow
        let resources := { resources with environmentUs := elapsedMicroseconds beforeEnvironment afterEnvironment }
        runAttemptSteps callbacks observer context fuel (environment.record callbacks) resources

/-- The loop that releases the action between the two parts: the first part, the
world's transition on the released action, then the second part (PAR-19; the source
is cited in `Acorn.Timing`). The second part runs on both answers of the world, so a
refused action still has its percept learned and its step frame delivered before the
refusal is returned. `DecisionInput.chooseOwned_release` proves that the functions one
pass composes give the stage those of a pass of `runAttemptSteps` give, and
`runReleasedSteps_complete` proves that the loop returns the pure fold
`Attempt.complete`. The step frame is delivered after the second part; it holds the
pre-transition world and the learned agent. The reported agent duration is the sum of
both parts, and the reported environment duration is the preceding transition's. -/
def runReleasedSteps {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks .planAfterAct α β) (observer : StreamObserver β) (context : GoalContext) :
    Nat → Attempt config α goal cap → RunnerResources →
      IO (Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources))
  | 0, attempt, resources => finishAttempt callbacks observer context attempt resources
  | fuel + 1, attempt, resources => do
    if attempt.finished then return ← finishAttempt callbacks observer context attempt resources
    match attempt.sense with
    | .error error => return .error ⟨error, none⟩
    | .ok none => finishAttempt callbacks observer context attempt resources
    | .ok (some input) =>
      let beforeChoice ← IO.monoNanosNow
      let chosen ← IO.lazyPure fun _ => input.chooseOwned callbacks
      let afterChoice ← IO.monoNanosNow
      let released ← IO.lazyPure fun _ => chosen.release
      let afterRelease ← IO.monoNanosNow
      let learned ← IO.lazyPure fun _ => released.learn callbacks
      let afterLearning ← IO.monoNanosNow
      let update := elapsedMicroseconds (beforeChoice + afterRelease) (afterChoice + afterLearning)
      match learned with
      | .refused error selected =>
        let _ ← notifyObserver (observer.deliverStep (fun _ => selected.frame callbacks context)
          (resources.capture update)) resources
        return .error ⟨error, some selected⟩
      | .accepted environment =>
        let resources ← notifyObserver (observer.deliverStep
          (fun _ => environment.selected.frame callbacks context)
          (resources.capture update)) resources
        let resources := { resources with
          environmentUs := elapsedMicroseconds afterChoice afterRelease }
        runReleasedSteps callbacks observer context fuel (environment.record callbacks) resources

/-- Execute the admitted finite attempt through the same proved selection,
world transition and bookkeeping, capturing only demanded step observations. The
step order of the callbacks selects the loop: no caller passes an order beside them. -/
def runAttempt {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (observer : StreamObserver β)
    (context : GoalContext) (initial : Attempt config α goal cap) (resources : RunnerResources) :
    IO (Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources)) :=
  match order, callbacks with
  | .learnThenAct, callbacks =>
    runAttemptSteps callbacks observer context cap.toNat initial resources
  | .planAfterAct, callbacks =>
    runReleasedSteps callbacks observer context cap.toNat initial resources

/-! ## The native loops compute the pure fold

`IO` is a function on a world token. The statements below are about every token: if a
loop returns a value from it, the value agrees with the result of `Attempt.complete`
(`AttemptAgrees`: the same refusal with the same learned stage of the refused pass, or
the same run state and outcome). They do not state that a loop returns; that rests on `notifyObserver` catching every observer
failure and on the clock read, which cannot fail by its type. The order of effects,
the observer's own effects and the reported durations are outside these statements. -/

/-- A returned bind ran its first action to a value and its continuation from there. -/
theorem returned_bind {α β : Type} (action : IO α) (next : α → IO β)
    (world after : Void IO.RealWorld) (value : β)
    (returned : (action >>= next) world = .ok value after) :
    ∃ first middle, action world = .ok first middle ∧ next first middle = .ok value after := by
  have unfolded : (action >>= next) world = EST.bind action next world := rfl
  rw [unfolded] at returned
  unfold EST.bind at returned
  cases ran : action world with
  | ok first middle =>
    rw [ran] at returned
    exact ⟨first, middle, rfl, returned⟩
  | error failure middle =>
    rw [ran] at returned
    cases returned

/-- A returned `pure` returns its value. -/
theorem returned_pure {α : Type} (value found : α) (world after : Void IO.RealWorld)
    (returned : (pure value : IO α) world = .ok found after) : found = value := by
  have unfolded : (pure value : IO α) world = .ok value world := rfl
  rw [unfolded] at returned
  cases returned
  rfl

/-- A returned `IO.lazyPure` returns the value of its function. -/
theorem returned_lazyPure {α : Type} (fn : Unit → α) (found : α) (world after : Void IO.RealWorld)
    (returned : IO.lazyPure fn world = .ok found after) : found = fn () :=
  returned_pure (fn ()) found world after returned

/-- A value a native attempt loop returned agrees with a result of the pure fold: the
same refusal, with the same learned stage of the refused pass, or the same run state
and outcome. The fold's terminal frame and the loop's resource counters are
observations outside the agreement. -/
def AttemptAgrees {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (folded : Except (Refusal config α goal cap) (RunState config α × GoalOutcome × StepFrame β))
    (returned : Except (Refusal config α goal cap)
      (RunState config α × GoalOutcome × RunnerResources)) : Prop :=
  match folded, returned with
  | .error refused, .error found => found = refused
  | .ok (run, outcome, _), .ok (found, observed, _) => found = run ∧ observed = outcome
  | _, _ => False

/-- Whatever the final bookkeeping returns is the attempt's pure close. -/
theorem finishAttempt_returned {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (observer : StreamObserver β) (context : GoalContext)
    (attempt : Attempt config α goal cap) (resources : RunnerResources)
    (world after : Void IO.RealWorld)
    (value : Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources))
    (returned : finishAttempt callbacks observer context attempt resources world = .ok value after) :
    AttemptAgrees (attempt.close callbacks context) value := by
  unfold finishAttempt at returned
  unfold Attempt.close
  cases finished : attempt.finish callbacks context with
  | error refused =>
    rw [finished] at returned
    have same := returned_pure _ _ _ _ returned
    rw [same]
    exact rfl
  | ok result =>
    obtain ⟨run, outcome, frame⟩ := result
    rw [finished] at returned
    obtain ⟨observed, middle, _, rest⟩ := returned_bind _ _ _ _ _ returned
    have same := returned_pure _ _ _ _ rest
    rw [same]
    exact ⟨rfl, rfl⟩

/-- **The default loop computes the pure fold.** For every callback, observer, fuel,
attempt, resource record and world token: a value the loop returns agrees with the
result of `Attempt.complete` (`AttemptAgrees`). On a refused action that is the same
refusal with the same learned stage; on a refused observation, the same refusal with no
stage. No hypothesis on the clock or the observer is used. -/
theorem runAttemptSteps_complete {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks .learnThenAct α β) (observer : StreamObserver β) (context : GoalContext)
    (fuel : Nat) (attempt : Attempt config α goal cap) (resources : RunnerResources)
    (world after : Void IO.RealWorld)
    (value : Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources))
    (returned : runAttemptSteps callbacks observer context fuel attempt resources world =
      .ok value after) :
    AttemptAgrees (attempt.complete callbacks context fuel) value := by
  induction fuel generalizing attempt resources world with
  | zero =>
    unfold runAttemptSteps at returned
    unfold Attempt.complete
    exact finishAttempt_returned callbacks observer context attempt resources world after value
      returned
  | succ fuel ih =>
    unfold runAttemptSteps at returned
    unfold Attempt.complete
    cases finished : attempt.finished with
    | true =>
      simp only [finished, ↓reduceIte] at returned ⊢
      exact finishAttempt_returned callbacks observer context attempt resources world after value
        returned
    | false =>
      simp only [finished, Bool.false_eq_true, ↓reduceIte] at returned ⊢
      cases sensed : attempt.sense with
      | error refused =>
        rw [sensed] at returned
        have same := returned_pure _ _ _ _ returned
        rw [same]
        exact rfl
      | ok found =>
        cases found with
        | none =>
          rw [sensed] at returned
          exact finishAttempt_returned callbacks observer context attempt resources world after
            value returned
        | some input =>
          rw [sensed] at returned
          dsimp only at returned ⊢
          obtain ⟨beforeUpdate, w1, _, returned⟩ := returned_bind _ _ _ _ _ returned
          obtain ⟨selected, w2, chose, returned⟩ := returned_bind _ _ _ _ _ returned
          have selectedEq := returned_lazyPure _ _ _ _ chose
          subst selectedEq
          obtain ⟨afterUpdate, w3, _, returned⟩ := returned_bind _ _ _ _ _ returned
          obtain ⟨observed, w4, _, returned⟩ := returned_bind _ _ _ _ _ returned
          obtain ⟨beforeEnvironment, w5, _, returned⟩ := returned_bind _ _ _ _ _ returned
          obtain ⟨released, w6, stepped, returned⟩ := returned_bind _ _ _ _ _ returned
          have releasedEq := returned_lazyPure _ _ _ _ stepped
          subst releasedEq
          cases answer : (input.selectOwned callbacks).release with
          | refused refusal learned =>
            rw [answer] at returned
            have same := returned_pure _ _ _ _ returned
            rw [same]
            exact rfl
          | accepted environment =>
            rw [answer] at returned
            dsimp only at returned ⊢
            obtain ⟨afterEnvironment, w7, _, returned⟩ := returned_bind _ _ _ _ _ returned
            exact ih _ _ _ returned

/-- **The loop that releases the action between the parts computes the same pure
fold.** For every callback, observer, fuel, attempt, resource record and world token: a
value the loop returns agrees with the result of `Attempt.complete` (`AttemptAgrees`),
on acceptance and on a refusal. On a refused action the loop returns the stage that the
fold's refusal holds: the whole step of the callbacks, the first part and then the
second, applied once to the refused pass's own input (`Attempt.complete_learned`). So
the second part runs exactly once on a refused pass in this loop, as it does in the
default one, and on every accepted pass the next attempt is the fold's. -/
theorem runReleasedSteps_complete {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks .planAfterAct α β) (observer : StreamObserver β) (context : GoalContext)
    (fuel : Nat) (attempt : Attempt config α goal cap) (resources : RunnerResources)
    (world after : Void IO.RealWorld)
    (value : Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources))
    (returned : runReleasedSteps callbacks observer context fuel attempt resources world =
      .ok value after) :
    AttemptAgrees (attempt.complete callbacks context fuel) value := by
  induction fuel generalizing attempt resources world with
  | zero =>
    unfold runReleasedSteps at returned
    unfold Attempt.complete
    exact finishAttempt_returned callbacks observer context attempt resources world after value
      returned
  | succ fuel ih =>
    unfold runReleasedSteps at returned
    unfold Attempt.complete
    cases finished : attempt.finished with
    | true =>
      simp only [finished, ↓reduceIte] at returned ⊢
      exact finishAttempt_returned callbacks observer context attempt resources world after value
        returned
    | false =>
      simp only [finished, Bool.false_eq_true, ↓reduceIte] at returned ⊢
      cases sensed : attempt.sense with
      | error refused =>
        rw [sensed] at returned
        have same := returned_pure _ _ _ _ returned
        rw [same]
        exact rfl
      | ok found =>
        cases found with
        | none =>
          rw [sensed] at returned
          exact finishAttempt_returned callbacks observer context attempt resources world after
            value returned
        | some input =>
          rw [sensed] at returned
          dsimp only at returned ⊢
          obtain ⟨beforeChoice, w1, _, returned⟩ := returned_bind _ _ _ _ _ returned
          obtain ⟨chosen, w2, chose, returned⟩ := returned_bind _ _ _ _ _ returned
          have chosenEq := returned_lazyPure _ _ _ _ chose
          subst chosenEq
          obtain ⟨afterChoice, w3, _, returned⟩ := returned_bind _ _ _ _ _ returned
          obtain ⟨released, w4, stepped, returned⟩ := returned_bind _ _ _ _ _ returned
          have releasedEq := returned_lazyPure _ _ _ _ stepped
          subst releasedEq
          obtain ⟨afterRelease, w5, _, returned⟩ := returned_bind _ _ _ _ _ returned
          obtain ⟨learned, w6, learnt, returned⟩ := returned_bind _ _ _ _ _ returned
          have learnedEq := (returned_lazyPure _ _ _ _ learnt).trans
            (input.chooseOwned_release callbacks)
          subst learnedEq
          obtain ⟨afterLearning, w7, _, returned⟩ := returned_bind _ _ _ _ _ returned
          cases answer : (input.selectOwned callbacks).release with
          | refused refusal selected =>
            rw [answer] at returned
            dsimp only at returned ⊢
            obtain ⟨observed, w8, _, returned⟩ := returned_bind _ _ _ _ _ returned
            have same := returned_pure _ _ _ _ returned
            rw [same]
            exact rfl
          | accepted environment =>
            rw [answer] at returned
            dsimp only at returned ⊢
            obtain ⟨observed, w8, _, returned⟩ := returned_bind _ _ _ _ _ returned
            exact ih _ _ _ returned

/-- **Either loop of an attempt computes the pure fold.** Whatever step order the
callbacks have, a value the attempt runner returns agrees with the result of
`Attempt.complete` at the attempt's own step cap (`AttemptAgrees`). -/
theorem runAttempt_complete {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (observer : StreamObserver β)
    (context : GoalContext) (initial : Attempt config α goal cap) (resources : RunnerResources)
    (world after : Void IO.RealWorld)
    (value : Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources))
    (returned : runAttempt callbacks observer context initial resources world =
      .ok value after) :
    AttemptAgrees (initial.complete callbacks context cap.toNat) value := by
  cases order with
  | learnThenAct =>
    exact runAttemptSteps_complete callbacks observer context cap.toNat initial resources world
      after value returned
  | planAfterAct =>
    exact runReleasedSteps_complete callbacks observer context cap.toNat initial resources world
      after value returned

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

/-- A campaign between attempts: the run state and the bookkeeping the loop carries. -/
structure CampaignProgress (config : WorldConfig) (α : Type) {size : Nat}
    (plan : CampaignPlan size) where
  /-- Current stream state. -/
  run : RunState config α
  /-- What the campaign does next. -/
  decision : BoundaryDecision plan
  /-- Exact total steps across accepted outcomes. -/
  totalSteps : UInt64
  /-- Two-word summary of every completed outcome, in order. -/
  outcomes : OutcomeFold
  /-- Saturating completed-attempt total. -/
  attempts : UInt32
  /-- Observer and checkpoint IO failure counters. -/
  resources : RunnerResources
  /-- The writable checkpoint capability and its save action, when admitted. -/
  checkpoint : Option (WritableCheckpoint × (α → System.FilePath → IO Unit))

/-- One campaign boundary: the result at an ending, or the next attempt with its outcome
bookkeeping and boundary checkpoint. The progress record is taken apart on entry and its
run state is handed to the attempt, so nothing else refers to the agent while the attempt
runs and the attempt's first writes can reuse the agent's storage. That reuse is a
property of the compiled code, not of these values. -/
def campaignStep {config : WorldConfig} {α β : Type} (curriculum : Curriculum)
    {plan : CampaignPlan curriculum.size} (callbacks : AgentCallbacks order α β)
    (observer : StreamObserver β) (readStop : BaseIO Bool)
    (progress : CampaignProgress config α plan) :
    IO (CampaignProgress config α plan ⊕ Except RunnerError (CampaignResult config α)) := do
  let ⟨run, decision, totalSteps, outcomes, attempts, resources, checkpoint⟩ := progress
  match decision with
  | .complete => return .inr (.ok ⟨run, totalSteps, outcomes, attempts, resources, .complete⟩)
  | .stopped => return .inr (.ok ⟨run, totalSteps, outcomes, attempts, resources, .stopped⟩)
  | .continue cursor =>
    have hg : cursor.goal.val < curriculum.size := by
      have := cursor.goal.isLt; have := plan.goals.isLt; omega
    let (goal, tier) := curriculum[cursor.goal.val]'hg
    let context := cursor.context tier
    let started := Attempt.start run goal plan.stepCap
    match ← runAttempt callbacks observer context started resources with
    | .error refusal => return .inr (.error (.world refusal.error))
    | .ok (next, outcome, observed) =>
      match addOutcomeSteps totalSteps outcome with
      | .error error => return .inr (.error (.metric error))
      | .ok total =>
        let outcomes := outcomes.push outcome
        let resources ← notifyObserver (observer.onOutcome outcome) observed
        let attempts := saturatingIncrement32 attempts
        let checkpoint := checkpoint.map fun (capability, save) => (capability.advance, save)
        let stopping ← readStop
        let boundary := atAttemptBoundary cursor outcome.achieved stopping
        let (savedResources, nextDecision) ← completeBoundary boundary
          (checkpointAction next.agent checkpoint boundary resources)
        return .inl ⟨next, nextDecision, total, outcomes, attempts, savedResources, checkpoint⟩

/-- **A campaign boundary that continues ran one attempt of the pure fold.** For every
curriculum, plan, callback record, observer, stop reader, progress record and world
token: when the boundary returns the next progress, the progress it took held a cursor,
and the pure fold of the callbacks, from the run state that progress held and for the
goal of that cursor at the plan's step cap, returns the run state of the next progress.
So every run state that the campaign loop carries from one boundary to the next is made
from the one before by the given callbacks through `Attempt.complete`, and by nothing
else. The statement is about one boundary; the loop that repeats it is a library
iteration and is outside it. -/
theorem campaignStep_attempt {config : WorldConfig} {α β : Type} (curriculum : Curriculum)
    {plan : CampaignPlan curriculum.size} (callbacks : AgentCallbacks order α β)
    (observer : StreamObserver β) (readStop : BaseIO Bool)
    (progress next : CampaignProgress config α plan) (world after : Void IO.RealWorld)
    (returned : campaignStep curriculum callbacks observer readStop progress world =
      .ok (.inl next) after) :
    ∃ (cursor : CampaignCursor plan) (bound : cursor.goal.val < curriculum.size)
        (outcome : GoalOutcome) (frame : StepFrame β),
      progress.decision = .continue cursor ∧
        (Attempt.start progress.run (curriculum[cursor.goal.val]'bound).1 plan.stepCap).complete
            callbacks (cursor.context (curriculum[cursor.goal.val]'bound).2) plan.stepCap.toNat =
          .ok (next.run, outcome, frame) := by
  obtain ⟨run, decision, totalSteps, outcomes, attempts, resources, checkpoint⟩ := progress
  unfold campaignStep at returned
  cases decision with
  | complete =>
    have same := returned_pure _ _ _ _ returned
    cases same
  | stopped =>
    have same := returned_pure _ _ _ _ returned
    cases same
  | «continue» cursor =>
    have bound : cursor.goal.val < curriculum.size := by
      have := cursor.goal.isLt
      have := plan.goals.isLt
      omega
    dsimp only at returned
    obtain ⟨attempted, w1, ran, returned⟩ := returned_bind _ _ _ _ _ returned
    have agrees := runAttempt_complete callbacks observer _ _ _ _ _ _ ran
    cases attempted with
    | error refusal =>
      have same := returned_pure _ _ _ _ returned
      cases same
    | ok result =>
      obtain ⟨following, outcome, observed⟩ := result
      dsimp only at returned
      cases added : addOutcomeSteps totalSteps outcome with
      | error failure =>
        rw [added] at returned
        have same := returned_pure _ _ _ _ returned
        cases same
      | ok total =>
        rw [added] at returned
        dsimp only at returned
        obtain ⟨noted, w2, _, returned⟩ := returned_bind _ _ _ _ _ returned
        obtain ⟨stopping, w3, _, returned⟩ := returned_bind _ _ _ _ _ returned
        obtain ⟨saved, w4, _, returned⟩ := returned_bind _ _ _ _ _ returned
        obtain ⟨savedResources, nextDecision⟩ := saved
        have same := returned_pure _ _ _ _ returned
        cases same
        refine ⟨cursor, bound, outcome, ?_⟩
        dsimp only
        revert agrees
        cases Attempt.complete callbacks (cursor.context (curriculum[cursor.goal.val]'bound).2)
            plan.stepCap.toNat
            (Attempt.start run (curriculum[cursor.goal.val]'bound).1 plan.stepCap) with
        | error refused =>
          intro agrees
          exact agrees.elim
        | ok result =>
          intro agrees
          obtain ⟨kept, seen, frame⟩ := result
          obtain ⟨rfl, rfl⟩ := agrees
          exact ⟨frame, rfl, rfl⟩

/-- Complete native campaign loop after domain and startup admission. The loop carries
either the progress between attempts or the campaign's result, and each pass hands the
progress to `campaignStep`: no return follows that call, so the loop keeps no second
reference to the run state across an attempt. -/
def runAdmittedCampaign {config : WorldConfig} {α β : Type} (curriculum : Curriculum)
    (plan : CampaignPlan curriculum.size) (callbacks : AgentCallbacks order α β)
    (observer : StreamObserver β)
    (initial : RunState config α) (checkpoint : Option (WritableCheckpoint × (α → System.FilePath → IO Unit)))
    (readStop : BaseIO Bool) (admission : CheckpointAdmission := .missing) :
    IO (Except RunnerError (CampaignResult config α)) := do
  let resources : RunnerResources := { checkpointStatus :=
    if checkpoint.isSome then .pending else if admission == .refused then .refused else .disabled }
  let mut phase : CampaignProgress config α plan ⊕ Except RunnerError (CampaignResult config α) :=
    .inl ⟨initial, plan.initial, 0, {}, 0, resources, checkpoint⟩
  repeat
    match phase with
    | .inr result => return result
    | .inl progress => phase ← campaignStep curriculum callbacks observer readStop progress

/-- Startup preserves refusal order and never constructs an agent before campaign admission.
Unexpected loader errors retain the fresh agent and disable writes, like a refused image.
The step order is the index of the callbacks and it selects the loop, so the two parts
and the loop are of one order. The callbacks, the constructor and the checkpoint hooks
share the agent type `α`. For the Acorn agent that type is the state type of one
construction, which holds the order, so the hooks stamp and admit that order as well. -/
def runCampaign {α β : Type} (config : WorldConfig) (seed : UInt64) (selection : AgentSelection)
    (spec : CampaignSpec) (buildAgent : AgentSelection → IO α)
    (callbacks : AgentCallbacks order α β)
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
        runAdmittedCampaign curriculum plan callbacks observer initial writable
          readStop admission
      catch error => return .error (.io error.toString)

end Acorn.Host
