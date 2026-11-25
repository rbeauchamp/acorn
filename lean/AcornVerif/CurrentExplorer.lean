import AcornVerif.CurrentGridWorld
import AcornVerif.CurrentPreReward
import AcornVerif.TemporalSupport

namespace AcornVerif.CurrentExplorer
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentControl AcornVerif.CurrentGridWorld AcornVerif.CurrentLearner
open AcornVerif.CurrentPreReward AcornVerif.CurrentTemporal

variable {count : Word.Count}

def restingPolicy (count : Word.Count) : PolicySnapshot count :=
  ⟨Vector.replicate _ .zero, declaredRate⟩

theorem restingPolicy_settled (count : Word.Count) : Settled (restingPolicy count) := by
  intro action
  simp only [restingPolicy, Vector.get, Vector.getElem_toArray, Vector.getElem_replicate]
  decide

structure Explorer (count : Word.Count) where
  run : Option (ExploratoryRun count)
  rng : Rng.Xoshiro256

def Explorer.stepOver (explorer : Explorer count) (policy : PolicySnapshot count) :
    Action count.word.toNat × Explorer count :=
  match explorer.run.bind ExploratoryRun.serve with
  | some served => (served.1, ⟨some served.2, explorer.rng⟩)
  | none =>
    let drawn := policy.drawPersistent explorer.rng
    (drawn.1.action, ⟨leftToServe drawn.1.run, drawn.2⟩)

def Explorer.step (explorer : Explorer count) : Action count.word.toNat × Explorer count :=
  explorer.stepOver (restingPolicy count)

def Explorer.after (explorer : Explorer count) : ℕ → Explorer count
  | 0 => explorer
  | time + 1 => (explorer.after time).step.2

def Explorer.actionAt (explorer : Explorer count) (time : ℕ) : Action count.word.toNat :=
  (explorer.after time).step.1

def Explorer.cold (count : Word.Count) (seed : UInt64) : Explorer count :=
  ⟨none, Rng.Xoshiro256.seed (Rng.streamKey seed 0xA6E0000000000001)⟩

theorem draw_congr (left right : PolicySnapshot count) (rate : left.epsilon = right.epsilon)
    (candidates : left.candidates = right.candidates) (rng : Rng.Xoshiro256) :
    (left.drawPersistent rng).1.action = (right.drawPersistent rng).1.action ∧
      (left.drawPersistent rng).1.run = (right.drawPersistent rng).1.run ∧
      (left.drawPersistent rng).2 = (right.drawPersistent rng).2 := by
  have greedy : ∀ generator, left.greedy generator = right.greedy generator :=
    fun generator => by
      rw [PolicySnapshot.greedy_def, PolicySnapshot.greedy_def, candidates]
  rw [PolicySnapshot.drawPersistent_def, PolicySnapshot.drawPersistent_def, rate]
  dsimp only
  cases (beginExploration count right.epsilon rng).1 with
  | some run => exact ⟨rfl, rfl, rfl⟩
  | none =>
    dsimp only
    rw [greedy]
    exact ⟨rfl, rfl, rfl⟩

theorem Explorer.stepOver_congr (explorer : Explorer count) (left right : PolicySnapshot count)
    (rate : left.epsilon = right.epsilon) (candidates : left.candidates = right.candidates) :
    explorer.stepOver left = explorer.stepOver right := by
  unfold Explorer.stepOver
  cases explorer.run.bind ExploratoryRun.serve with
  | some served => rfl
  | none =>
    obtain ⟨action, run, generator⟩ := draw_congr left right rate candidates explorer.rng
    dsimp only
    rw [action, run, generator]

theorem Explorer.stepOver_greedy (explorer : Explorer count) (policy : PolicySnapshot count)
    (unserved : explorer.run.bind ExploratoryRun.serve = none)
    (calm : (beginExploration count policy.epsilon explorer.rng).1 = none) :
    (explorer.stepOver policy).1 =
      (policy.greedy (beginExploration count policy.epsilon explorer.rng).2).1 := by
  unfold Explorer.stepOver
  rw [unserved]
  dsimp only
  rw [PolicySnapshot.drawPersistent_def]
  dsimp only
  rw [calm]

theorem settled_candidates (snapshot : PolicySnapshot count) (settled : Settled snapshot) :
    snapshot.candidates = (restingPolicy count).candidates :=
  candidates_related snapshot (restingPolicy count) (fun action =>
    ⟨CurrentControl.zero_finite _ (settled action),
      CurrentControl.zero_finite _ (restingPolicy_settled count action),
      (zero_key _ (settled action)).trans (zero_key _ (restingPolicy_settled count action)).symm⟩)

theorem restingPolicy_candidates (count : Word.Count) :
    (restingPolicy count).candidates = List.finRange count.word.toNat := by
  have value : ∀ action, (restingPolicy count).values.get action = Binary32.zero := by
    intro action
    simp only [restingPolicy, Vector.get, Vector.getElem_toArray, Vector.getElem_replicate]
  have best : (restingPolicy count).best = Binary32.zero := by
    rw [PolicySnapshot.best_def, value]
    have zeros : ∀ word ∈ (restingPolicy count).values.toList.drop 1, word = Binary32.zero := by
      intro word member
      have inside := List.mem_of_mem_drop member
      simp only [restingPolicy, Vector.toList_replicate, List.mem_replicate] at inside
      exact inside.2
    generalize (restingPolicy count).values.toList.drop 1 = rest at zeros
    induction rest with
    | nil => rfl
    | cons head tail ih =>
      rw [List.foldl_cons, zeros head List.mem_cons_self, ite_self]
      exact ih (fun word member => zeros word (List.mem_cons_of_mem _ member))
  rw [PolicySnapshot.candidates_def, best]
  dsimp only
  refine List.filter_eq_self.mpr (fun action _ => ?_)
  rw [value]
  decide

def naturalReservoir {actions : ℕ} :
    List (Action actions) → ℕ → Action actions → Rng.Xoshiro256 →
      Action actions × Rng.Xoshiro256
  | [], _, pick, rng => (pick, rng)
  | action :: rest, seen, pick, rng =>
    naturalReservoir rest (seen + 1)
      (if rng.next.1.toNat * (seen + 1) < 2 ^ 64 then action else pick) rng.next.2

theorem reservoir_natural {actions : ℕ} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256)
    (fits : seen.toNat + pending.length < 2 ^ 64) :
    reservoir pending seen pick rng = naturalReservoir pending seen.toNat pick rng := by
  induction pending generalizing seen pick rng with
  | nil => rfl
  | cons action rest ih =>
    rw [List.length_cons] at fits
    have one : (1 : UInt64).toNat = 1 := rfl
    have next : (seen + 1).toNat = seen.toNat + 1 := by
      rw [UInt64.toNat_add, one]
      exact Nat.mod_eq_of_lt (by omega)
    have counted : (Word.Count.ofWord (seen + 1)).word = seen + 1 := by
      unfold Word.Count.ofWord
      split
      · rfl
      · omega
    have quotient : (rng.nextBelow (Word.Count.ofWord (seen + 1))).1.val.toNat =
        rng.next.1.toNat * (seen.toNat + 1) / 2 ^ 64 := by
      rw [Rng.nextBelow_quotient, counted, next]
    have zero : ((rng.nextBelow (Word.Count.ofWord (seen + 1))).1.val == 0) =
        decide (rng.next.1.toNat * (seen.toNat + 1) < 2 ^ 64) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, quotient]
      change _ / 2 ^ 64 = 0 ↔ _
      rw [Nat.div_eq_zero_iff]
      omega
    rw [reservoir_cons]
    dsimp only
    rw [zero, Rng.nextBelow_transition, ih _ _ _ (by omega), next]
    simp only [naturalReservoir, decide_eq_true_eq]

def Explorer.byWord (explorer : Explorer count) : Action count.word.toNat × Explorer count :=
  match explorer.run.bind ExploratoryRun.serve with
  | some served => (served.1, ⟨some served.2, explorer.rng⟩)
  | none =>
    if (explorer.rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23 then
      let duration := explorer.rng.next.2.nextF64
      let action := uniformAction count duration.2
      (action.1, ⟨leftToServe (some ⟨action.1, durationRemaining duration.1⟩), action.2⟩)
    else
      let greedy := naturalReservoir (List.finRange count.word.toNat) 0 (firstAction count)
        explorer.rng.next.2
      (greedy.1, ⟨none, greedy.2⟩)

theorem Explorer.step_eq (explorer : Explorer count) : explorer.step = explorer.byWord := by
  unfold Explorer.step Explorer.stepOver Explorer.byWord
  cases explorer.run.bind ExploratoryRun.serve with
  | some served => rfl
  | none =>
    dsimp only
    have rate : (restingPolicy count).epsilon = declaredRate := rfl
    have fits : (0 : UInt64).toNat + (List.finRange count.word.toNat).length < 2 ^ 64 := by
      rw [List.length_finRange]
      exact (Nat.zero_add _).symm ▸ count.word.toNat_lt
    rw [PolicySnapshot.drawPersistent_def, rate]
    unfold beginExploration
    dsimp only
    rw [TemporalSupport.declared_branch, Rng.nextF64_transition]
    by_cases below : (explorer.rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23
    · simp only [below, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · simp only [below, decide_false, Bool.not_false, ↓reduceIte, PolicySnapshot.greedy_def,
        restingPolicy_candidates, reservoir_natural _ _ _ _ fits]
      rfl

def Explorer.actions : ℕ → Explorer count → List (Action count.word.toNat)
  | 0, _ => []
  | steps + 1, explorer =>
    match explorer.byWord with
    | (action, next) => action :: Explorer.actions steps next

theorem Explorer.after_shift (explorer : Explorer count) (time : ℕ) :
    explorer.after (time + 1) = explorer.step.2.after time := by
  induction time with
  | zero => rfl
  | succ time ih => exact congrArg (fun later : Explorer count => later.step.2) ih

theorem Explorer.actions_get (explorer : Explorer count) (steps time : ℕ)
    (within : time < steps) :
    (explorer.actions steps)[time]? = some (explorer.actionAt time) := by
  induction steps generalizing explorer time with
  | zero => exact absurd within (Nat.not_lt_zero time)
  | succ steps ih =>
    have unfolded : explorer.actions (steps + 1) =
        explorer.step.1 :: explorer.step.2.actions steps := by
      rw [explorer.step_eq]
      rfl
    rw [unfolded]
    cases time with
    | zero => rfl
    | succ time =>
      rw [List.getElem?_cons_succ, ih explorer.step.2 time (Nat.lt_of_succ_lt_succ within)]
      exact congrArg some (congrArg (fun later : Explorer count => later.step.1)
        (explorer.after_shift time).symm)

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

def explorerOf (state : TemporalControl interface profile config criterion dimension) :
    Explorer interface.actions :=
  ⟨committedRun state.runtime.references.phase, state.runtime.references.rng⟩

theorem unserved_run (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (unserved : state.serve features = none) :
    (explorerOf state).run.bind ExploratoryRun.serve = none := by
  unfold TemporalControl.serve at unserved
  change (committedRun state.runtime.references.phase).bind ExploratoryRun.serve = none
  cases phase : state.runtime.references.phase with
  | idle => rfl
  | option slot activation => rfl
  | exploring committed =>
    simp only [phase] at unserved
    cases service : committed.run.serve with
    | none =>
      change committed.run.serve = none
      exact service
    | some pair => simp [service] at unserved

theorem prepare_control (state : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (state.prepareSelection models features reward).runtime.lifecycle.consumers.control =
      state.runtime.lifecycle.consumers.control := by
  simp [TemporalControl.prepareSelection, primitive]

theorem select_draws
    (state next : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (potentials : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features potentials reward goal =
      some (next, decision)) :
    decision.action = ((explorerOf state).stepOver
        (state.runtime.lifecycle.consumers.control.snapshot features declaredRate)).1 ∧
      explorerOf next = ((explorerOf state).stepOver
        (state.runtime.lifecycle.consumers.control.snapshot features declaredRate)).2 := by
  unfold TemporalControl.selectWithOperations at executed
  have frame := prepare_frame state models features reward
  have kept := prepare_control state primitive models features reward
  generalize state.prepareSelection models features reward = prepared at executed frame kept
  have same : explorerOf prepared = explorerOf state := by
    change Explorer.mk _ _ = Explorer.mk _ _
    rw [frame.1, frame.2]
  rw [← same, ← kept]
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    obtain ⟨held, rest, holds, service, -, stored, generator⟩ :=
      prepared.serve_frame next features decision served
    have run : (explorerOf prepared).run.bind ExploratoryRun.serve =
        some (decision.action, rest) := by
      change (committedRun prepared.runtime.references.phase).bind ExploratoryRun.serve = _
      rw [holds]
      exact service
    unfold Explorer.stepOver
    rw [run]
    refine ⟨rfl, ?_⟩
    change Explorer.mk (committedRun next.runtime.references.phase) next.runtime.references.rng =
      Explorer.mk (some rest) prepared.runtime.references.rng
    rw [stored, generator]
    rfl
  | none =>
    simp only [served] at executed
    have unserved := unserved_run prepared features served
    split at executed
    · have chosen : (prepared.withPhase .idle).choosePrimitive features
          (Vector.replicate _ .zero) none none = (next, decision) := Option.some.inj executed
      have drawn := choosePrimitive_drawn (prepared.withPhase .idle) features
        (Vector.replicate _ .zero) none none
      rw [chosen, (TemporalControl.declared_rates (prepared.withPhase .idle) declared).1] at drawn
      obtain ⟨action, -, -, -, generator, committed⟩ := drawn
      unfold Explorer.stepOver
      rw [unserved]
      refine ⟨action, ?_⟩
      change Explorer.mk (committedRun next.runtime.references.phase)
        next.runtime.references.rng = _
      rw [committed, generator]
      rfl
    · rename_i hierarchy
      simp [primitive] at hierarchy

theorem select_explores
    (state next : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (still : Still state.runtime.lifecycle.consumers.control)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (potentials : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features potentials reward goal =
      some (next, decision)) :
    decision.action = (explorerOf state).step.1 ∧
      explorerOf next = (explorerOf state).step.2 := by
  have drawn := select_draws state next primitive declared models plan features potentials reward
    goal decision executed
  rw [(explorerOf state).stepOver_congr
    (state.runtime.lifecycle.consumers.control.snapshot features declaredRate)
    (restingPolicy interface.actions) rfl
    (settled_candidates _ (still.snapshot features declaredRate))] at drawn
  exact drawn

theorem learn_phase (selected : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    (selected.learn features obs reward goal decision).runtime.references.phase =
      selected.runtime.references.phase := by
  unfold TemporalControl.learn
  dsimp only
  rw [TemporalControl.finish_eq]
  dsimp only
  have followed : (selected.followOptions (modelOperations criterion dimension) features
      obs.declared reward goal decision).runtime.references.phase =
        selected.runtime.references.phase := by
    rw [TemporalControl.followOptions_eq]
    split <;> rfl
  rw [← followed]
  generalize selected.followOptions (modelOperations criterion dimension) features
    obs.declared reward goal decision = followed
  cases selected.takeoverValue features obs.declared goal decision with
  | none => rfl
  | some value =>
    rw [TemporalControl.closeSpan_eq]
    rfl

theorem retire_phase (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (state.retire active).control.runtime.references.phase =
      state.control.runtime.references.phase := by
  unfold Agent.retire
  split
  · rfl
  · exact congrArg (·.phase) (state.control.runtime.retire_references active)

theorem learn_explorer (chosen : Chosen interface profile config criterion dimension planning)
    (ordered : chosen.order = .learnThenAct) :
    explorerOf chosen.learn.control = explorerOf chosen.control := by
  have phase : chosen.learn.control.runtime.references.phase =
      chosen.control.runtime.references.phase := by
    refine (retire_phase chosen.learned chosen.units).trans ?_
    refine (learn_phase _ chosen.features chosen.percept.frame chosen.percept.reward
      chosen.percept.frame.achieved chosen.decision).trans ?_
    rw [ordered]
    rfl
  change Explorer.mk _ _ = Explorer.mk _ _
  rw [phase, chosen.learn_rng]

theorem act_draws (agent : Agent interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (percept : Percept interface) :
    (agent.act percept).2.action = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.choose .learnThenAct percept).features declaredRate)).1 ∧
      explorerOf (agent.act percept).1.control = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.choose .learnThenAct percept).features declaredRate)).2 := by
  rw [Agent.act_parts]
  obtain ⟨selected, ordered, -, encoded, -⟩ :=
    agent.choose_selected .learnThenAct (by decide) percept
  unfold TemporalControl.select at selected
  have drawn := select_draws agent.advanceClock.control _ primitive declared _ _ _ _ _ _ _
    selected
  rw [encoded]
  exact ⟨drawn.1, (learn_explorer (agent.choose .learnThenAct percept) ordered).trans drawn.2⟩

theorem act_explores (agent : Agent interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (still : Still agent.control.runtime.lifecycle.consumers.control)
    (percept : Percept interface) :
    (agent.act percept).2.action = (explorerOf agent.control).step.1 ∧
      explorerOf (agent.act percept).1.control = (explorerOf agent.control).step.2 := by
  have drawn := act_draws agent primitive declared percept
  rw [(explorerOf agent.control).stepOver_congr
    (agent.control.runtime.lifecycle.consumers.control.snapshot
      (agent.choose .learnThenAct percept).features declaredRate)
    (restingPolicy interface.actions) rfl
    (settled_candidates _ (still.snapshot _ declaredRate))] at drawn
  exact drawn

theorem act_quiet (agent : Agent interface profile config criterion dimension planning)
    (quiet : Quiet agent.control) (percept : Percept interface)
    (unpaid : percept.reward.isZero = true) : Quiet (agent.act percept).1.control := by
  rw [Agent.act_parts]
  exact quiet.actOrdered .learnThenAct percept (Inert32.ofZero unpaid)

theorem quiet_actions (primitive : profile.usesHierarchy = false)
    (declared : profile.rate = .declared)
    (agent : Agent interface profile config criterion dimension planning)
    (quiet : Quiet agent.control) (world : Kernel.World interface) (start : world.State)
    (time : ℕ)
    (unpaid : ∀ earlier, earlier < time →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward.isZero = true) :
    Quiet (Kernel.memoryAt world (executedAgent agent) start time).control ∧
      explorerOf (Kernel.memoryAt world (executedAgent agent) start time).control =
        (explorerOf agent.control).after time ∧
      Kernel.actionAt world (executedAgent agent) start time =
        (explorerOf agent.control).actionAt time := by
  have reached : Quiet (Kernel.memoryAt world (executedAgent agent) start time).control ∧
      explorerOf (Kernel.memoryAt world (executedAgent agent) start time).control =
        (explorerOf agent.control).after time := by
    induction time with
    | zero => exact ⟨quiet, rfl⟩
    | succ time ih =>
      obtain ⟨rest, tracked⟩ := ih (fun earlier before => unpaid earlier (Nat.lt_succ_of_lt before))
      have stepped := act_explores (Kernel.memoryAt world (executedAgent agent) start time)
        primitive declared rest.control (Kernel.perceptAt world (executedAgent agent) start time)
      refine ⟨act_quiet (Kernel.memoryAt world (executedAgent agent) start time) rest
        (Kernel.perceptAt world (executedAgent agent) start time)
        (unpaid time (Nat.lt_succ_self time)), ?_⟩
      change explorerOf ((Kernel.memoryAt world (executedAgent agent) start time).act
        (Kernel.perceptAt world (executedAgent agent) start time)).1.control = _
      rw [stepped.2, tracked]
      rfl
  refine ⟨reached.1, reached.2, ?_⟩
  have stepped := act_explores (Kernel.memoryAt world (executedAgent agent) start time)
    primitive declared reached.1.control
    (Kernel.perceptAt world (executedAgent agent) start time)
  change ((Kernel.memoryAt world (executedAgent agent) start time).act
    (Kernel.perceptAt world (executedAgent agent) start time)).2.action = _
  rw [stepped.1, reached.2]
  rfl

theorem cold_actions (primitive : profile.usesHierarchy = false)
    (declared : profile.rate = .declared) (planning : PlanningSelection)
    (world : Kernel.World interface) (start : world.State) (time : ℕ)
    (unpaid : ∀ earlier, earlier < time →
      (Kernel.perceptAt world
        (executedAgent (Agent.initial interface profile config criterion dimension planning))
        start earlier).reward.isZero = true) :
    Kernel.actionAt world
        (executedAgent (Agent.initial interface profile config criterion dimension planning))
        start time =
      (Explorer.cold interface.actions config.seed).actionAt time :=
  (quiet_actions primitive declared
    (Agent.initial interface profile config criterion dimension planning) Quiet.initial world
    start time unpaid).2.2

end AcornVerif.CurrentExplorer
