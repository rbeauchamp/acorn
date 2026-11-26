import Acorn.Host.Curriculum
import Acorn.Host.Control
import Acorn.Host.CheckpointDiagnostic
import Acorn.FeatureConsumers
import Acorn.Timing
import Acorn.Host.Forever

namespace Acorn.Host

variable {order : StepOrder}

inductive ResearchProfile where
  | ranked
  | primitive
  | boundaryCredit
  | annealed
  | spatial
  deriving DecidableEq, BEq

def ResearchProfile.resumable : ResearchProfile → Bool
  | .ranked => true
  | .primitive | .boundaryCredit | .annealed | .spatial => false

structure AgentSelection where
  profile : ResearchProfile
  criterion : Features.Criterion

structure CaptureMetrics where
  updateUs : UInt64
  environmentUs : UInt64
  observerRefusals : UInt64
  checkpointFailures : UInt64
  checkpointBytes : Option UInt64
  checkpointWriteUs : Option UInt64

structure StreamObserver (β : Type) where
  onInitialized : CheckpointAdmission → BaseIO Unit
  onStep : Option (StepFrame β → CaptureMetrics → IO Unit)
  onAttemptEnd : StepFrame β → CaptureMetrics → IO Unit
  onOutcome : GoalOutcome → IO Unit

def StreamObserver.none {β : Type} : StreamObserver β :=
  ⟨fun _ => pure (), Option.none, fun _ _ => pure (), fun _ => pure ()⟩

def StreamObserver.deliverStep {β : Type} (observer : StreamObserver β)
    (frame : Unit → StepFrame β) (metrics : CaptureMetrics) : IO Unit :=
  match observer.onStep with
  | .none => pure ()
  | some consume => consume (frame ()) metrics

theorem StreamObserver.none_deliverStep {β : Type} (frame : Unit → StepFrame β)
    (metrics : CaptureMetrics) :
    (StreamObserver.none : StreamObserver β).deliverStep frame metrics = pure () := rfl

inductive CheckpointLoad (α : Type) where
  | loaded (agent : α)
  | missing
  | refused (message : String)

structure CheckpointHooks (α : Type) where
  path : System.FilePath
  interval : UInt32
  load : α → System.FilePath → IO (CheckpointLoad α)
  save : α → System.FilePath → IO Unit

inductive RunnerError where
  | campaign (error : CampaignError)
  | world (error : WorldError)
  | metric (error : MetricError)
  | io (message : String)

structure RunnerResources where
  observerRefusals : UInt64 := 0
  checkpointFailures : UInt64 := 0
  checkpointStatus : CheckpointStatus := .disabled
  environmentUs : UInt64 := 0
  checkpointBytes : Option UInt64 := none
  checkpointWriteUs : Option UInt64 := none

def elapsedMicroseconds (before after : Nat) : UInt64 :=
  (min ((after - before) / 1000) (2 ^ 64 - 1)).toUInt64

theorem elapsedMicroseconds_exact (before after : Nat) :
    (elapsedMicroseconds before after).toNat = min ((after - before) / 1000) (2 ^ 64 - 1) := by
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_right ((after - before) / 1000) (2 ^ 64 - 1)
  omega

def RunnerResources.capture (resources : RunnerResources) (updateUs : UInt64) : CaptureMetrics :=
  ⟨updateUs, resources.environmentUs, resources.observerRefusals, resources.checkpointFailures,
    resources.checkpointBytes, resources.checkpointWriteUs⟩

def notifyObserver (operation : IO Unit) (resources : RunnerResources) : IO RunnerResources := do
  try
    operation
    return resources
  catch _ => return { resources with observerRefusals := saturatingIncrement64 resources.observerRefusals }

def finishAttempt {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (observer : StreamObserver β) (context : GoalContext)
    (attempt : Attempt config α goal cap) (resources : RunnerResources) :
    IO (Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources)) := do
  match attempt.finish callbacks context with
  | .error error => return .error ⟨error, none⟩
  | .ok (run, outcome, frame) =>
    let resources ← notifyObserver (observer.onAttemptEnd frame (resources.capture 0)) resources
    return .ok (run, outcome, resources)

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

def runReleasedSteps {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (releases : order.Releases)
    (observer : StreamObserver β) (context : GoalContext) :
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
        runReleasedSteps callbacks releases observer context fuel (environment.record callbacks)
          resources

def runAttempt {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (observer : StreamObserver β)
    (context : GoalContext) (initial : Attempt config α goal cap) (resources : RunnerResources) :
    IO (Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources)) :=
  match order, callbacks with
  | .learnThenAct, callbacks =>
    runAttemptSteps callbacks observer context cap.toNat initial resources
  | .planAfterAct, callbacks =>
    runReleasedSteps callbacks (fun same => StepOrder.noConfusion same) observer context cap.toNat
      initial resources
  | .actThenLearn, callbacks =>
    runReleasedSteps callbacks (fun same => StepOrder.noConfusion same) observer context cap.toNat
      initial resources

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

theorem returned_pure {α : Type} (value found : α) (world after : Void IO.RealWorld)
    (returned : (pure value : IO α) world = .ok found after) : found = value := by
  have unfolded : (pure value : IO α) world = .ok value world := rfl
  rw [unfolded] at returned
  cases returned
  rfl

theorem returned_lazyPure {α : Type} (fn : Unit → α) (found : α) (world after : Void IO.RealWorld)
    (returned : IO.lazyPure fn world = .ok found after) : found = fn () :=
  returned_pure (fn ()) found world after returned

def AttemptAgrees {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (folded : Except (Refusal config α goal cap) (RunState config α × GoalOutcome × StepFrame β))
    (returned : Except (Refusal config α goal cap)
      (RunState config α × GoalOutcome × RunnerResources)) : Prop :=
  match folded, returned with
  | .error refused, .error found => found = refused
  | .ok (run, outcome, _), .ok (found, observed, _) => found = run ∧ observed = outcome
  | _, _ => False

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

theorem runReleasedSteps_complete {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (releases : order.Releases)
    (observer : StreamObserver β) (context : GoalContext)
    (fuel : Nat) (attempt : Attempt config α goal cap) (resources : RunnerResources)
    (world after : Void IO.RealWorld)
    (value : Except (Refusal config α goal cap) (RunState config α × GoalOutcome × RunnerResources))
    (returned : runReleasedSteps callbacks releases observer context fuel attempt resources world =
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
    exact runReleasedSteps_complete callbacks _ observer context cap.toNat initial resources world
      after value returned
  | actThenLearn =>
    exact runReleasedSteps_complete callbacks _ observer context cap.toNat initial resources world
      after value returned

inductive CampaignEnd where
  | complete
  | stopped
  deriving DecidableEq

structure CampaignResult (config : WorldConfig) (α : Type) where
  run : RunState config α
  totalSteps : UInt64
  outcomes : OutcomeFold
  attempts : UInt32
  resources : RunnerResources
  ending : CampaignEnd

def CampaignCursor.context {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (tier : UInt8) : GoalContext :=
  ⟨cursor.goal.val.toUInt64, cursor.attempt.val.toUInt64, tier, cursor.cycle⟩

theorem CampaignCursor.context_attempt {size : Nat} {plan : CampaignPlan size}
    (cursor : CampaignCursor plan) (tier : UInt8) :
    (cursor.context tier).attempt.toNat = cursor.attempt.val := by
  change cursor.attempt.val % (2 ^ 64) = cursor.attempt.val
  apply Nat.mod_eq_of_lt
  have := cursor.attempt.isLt
  have := plan.attempts.toNat_lt
  omega

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

theorem checkpointAction_closing {size : Nat} {plan : CampaignPlan size} {α : Type}
    (agent : α) (capability : WritableCheckpoint) (save : α → System.FilePath → IO Unit)
    (decision : BoundaryDecision plan) (resources : RunnerResources)
    (closing : decision.closing = true) :
    checkpointAction agent (some (capability, save)) decision resources =
      saveCheckpoint capability (save agent capability.path) resources := by
  simp only [checkpointAction, capability.closing_due decision closing, ↓reduceIte]

def completeBoundary {size : Nat} {plan : CampaignPlan size}
    (decision : BoundaryDecision plan) (checkpoint : IO RunnerResources) :
    IO (RunnerResources × BoundaryDecision plan) :=
  EST.bind checkpoint (fun resources => EST.pure (resources, decision))

theorem completeBoundary_returns {size : Nat} {plan : CampaignPlan size}
    (decision : BoundaryDecision plan) (checkpoint : IO RunnerResources)
    (before after : Void IO.RealWorld) (resources : RunnerResources)
    (returned : checkpoint before = .ok resources after) :
    completeBoundary decision checkpoint before = .ok (resources, decision) after := by
  simp only [completeBoundary, EST.bind, EST.pure, returned]

theorem completeBoundary_error {size : Nat} {plan : CampaignPlan size}
    (decision : BoundaryDecision plan) (checkpoint : IO RunnerResources)
    (before after : Void IO.RealWorld) (error : IO.Error)
    (failed : checkpoint before = .error error after) :
    completeBoundary decision checkpoint before = .error error after := by
  simp only [completeBoundary, EST.bind, failed]

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

structure CampaignProgress (config : WorldConfig) (α : Type) {size : Nat}
    (plan : CampaignPlan size) where
  run : RunState config α
  decision : BoundaryDecision plan
  totalSteps : UInt64
  outcomes : OutcomeFold
  attempts : UInt32
  resources : RunnerResources
  checkpoint : Option (WritableCheckpoint × (α → System.FilePath → IO Unit))

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
  for _ in forever do
    match phase with
    | .inr result => return result
    | .inl progress => phase ← campaignStep curriculum callbacks observer readStop progress
  throw (IO.userError "campaign loop ended without a result")

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
