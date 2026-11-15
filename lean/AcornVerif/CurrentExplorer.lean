/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentGridWorld
import AcornVerif.CurrentPreReward
import AcornVerif.TemporalSupport

/-!
# The actions of primitive control before a first reward

Before its first reward every control weight of the executed agent is a zero word
(`AcornVerif.CurrentPreReward.pre_reward_weights_zero`). This module says what its actions then
are, for a profile with no hierarchy under the declared exploration rate, which the primitive
research profile is, at the default step order: they are the actions of an `Explorer`, a machine
whose whole state is the exploratory run it has committed to and the action generator. It reads
no percept.

`Explorer.step` is one decision. A committed run with a step left serves its action and draws
nothing. Otherwise the decision is one persistent draw (`Acorn.Features.PolicySnapshot
.drawPersistent`, departure D3 of `docs/learned-only-binding.md`) from a policy all of whose values
are zero words, at the declared rate (departure D6): one branch word; then either a duration word
and an action word, which begin a run, or one word for each of the interface's actions, since
every action is within the tie window of the maximum and the ordered reservoir draws once for
each candidate. `Explorer.step_eq` proves that description: a step is `Explorer.byWord`, which
compares the branch word's numerator with the declared rate's exact share and runs the reservoir
in natural-number arithmetic (`reservoir_natural`). `Explorer.actions` lists an explorer's first
actions in one pass (`Explorer.actions_get`), the form a kernel evaluation reads.

`select_explores` proves that the executed selection of such a profile, from a state whose
primitive controller is at rest, returns the explorer's action and leaves the explorer's next
state. `act_explores` carries it through the whole step under the default order, on every
percept: the step selects before it learns from its percept's reward. `quiet_actions` carries it
through a kernel run: in every world, from every start, if every reward word delivered before a
time is a zero word, the executed agent takes the explorer's action at that time, from every
state of it whose learners are at rest (`AcornVerif.CurrentPreReward.Quiet`). `cold_actions` is
the statement from cold initialization, where the explorer holds no run and the generator the
agent seeds for its action stream.

So up to and including the decision on the first percept whose reward word is not a zero word,
the cold agent's actions are one fixed sequence, a function of its feature configuration's seed
and of the number of actions alone: they do not depend on the world or on the frames it
delivers, and so on nothing a learner comes to hold from those frames. This is a model of the
executed agent's draws along a run, which obligation 15 of `docs/mission-contract.md` asks for,
for that stretch of the run and for this profile. It is a statement about the executed
generator. It assumes nothing about how the generator's words are distributed, and gives no
probability.

What it does not cover: a profile with a hierarchy, whose meta-controller draws before primitive
control does and whose options draw their own actions; a rate policy other than the declared one;
a step order other than the default; and every decision after the first percept whose reward word
is not a zero word.
-/

namespace AcornVerif.CurrentExplorer
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentControl AcornVerif.CurrentGridWorld AcornVerif.CurrentLearner
open AcornVerif.CurrentPreReward AcornVerif.CurrentTemporal

variable {count : Word.Count}

/-! ## The explorer -/

/-- The frozen policy of a controller at rest under the declared rate: every value the positive
zero word. -/
def restingPolicy (count : Word.Count) : PolicySnapshot count :=
  ⟨Vector.replicate _ .zero, declaredRate⟩

/-- Every value of the resting policy is a zero word. -/
theorem restingPolicy_settled (count : Word.Count) : Settled (restingPolicy count) := by
  intro action
  simp only [restingPolicy, Vector.get, Vector.getElem_toArray, Vector.getElem_replicate]
  decide

/-- What primitive control's choice of action reads while its controller is at rest: the
exploratory run it has committed to, and the action generator. -/
structure Explorer (count : Word.Count) where
  /-- The committed run, if any. A run with no step left serves nothing. -/
  run : Option (ExploratoryRun count)
  /-- The action generator. -/
  rng : Rng.Xoshiro256

/-- One decision of the explorer: the next action of a committed run with a step left, with no
draw; otherwise one persistent draw from the resting policy, which leaves the generator after
its words and commits the part of a drawn run that is left to serve. -/
def Explorer.step (explorer : Explorer count) : Action count.word.toNat × Explorer count :=
  match explorer.run.bind ExploratoryRun.serve with
  | some served => (served.1, ⟨some served.2, explorer.rng⟩)
  | none =>
    let drawn := (restingPolicy count).drawPersistent explorer.rng
    (drawn.1.action, ⟨leftToServe drawn.1.run, drawn.2⟩)

/-- The explorer after a number of decisions. -/
def Explorer.after (explorer : Explorer count) : ℕ → Explorer count
  | 0 => explorer
  | time + 1 => (explorer.after time).step.2

/-- The action of the explorer's decision at a time. -/
def Explorer.actionAt (explorer : Explorer count) (time : ℕ) : Action count.word.toNat :=
  (explorer.after time).step.1

/-- The explorer of a cold start with a seed: no committed run, and the generator the agent
seeds for its action stream (`Acorn.Features.TemporalReferences.cold`). -/
def Explorer.cold (count : Word.Count) (seed : UInt64) : Explorer count :=
  ⟨none, Rng.Xoshiro256.seed (Rng.streamKey seed 0xA6E0000000000001)⟩

/-- A persistent draw from a policy all of whose values are zero words, at the declared rate,
takes the action of the draw from the resting policy, commits its run and leaves its generator:
the two policies have one rate and one list of candidates. -/
theorem settled_draw (snapshot : PolicySnapshot count) (settled : Settled snapshot)
    (declared : snapshot.epsilon = declaredRate) (rng : Rng.Xoshiro256) :
    (snapshot.drawPersistent rng).1.action = ((restingPolicy count).drawPersistent rng).1.action ∧
      (snapshot.drawPersistent rng).1.run = ((restingPolicy count).drawPersistent rng).1.run ∧
      (snapshot.drawPersistent rng).2 = ((restingPolicy count).drawPersistent rng).2 := by
  have candidates : snapshot.candidates = (restingPolicy count).candidates :=
    candidates_related snapshot (restingPolicy count) (fun action =>
      ⟨CurrentControl.zero_finite _ (settled action),
        CurrentControl.zero_finite _ (restingPolicy_settled count action),
        (zero_key _ (settled action)).trans (zero_key _ (restingPolicy_settled count action)).symm⟩)
  have greedy : ∀ generator, snapshot.greedy generator = (restingPolicy count).greedy generator :=
    fun generator => by
      rw [PolicySnapshot.greedy_def, PolicySnapshot.greedy_def, candidates]
  have rate : (restingPolicy count).epsilon = declaredRate := rfl
  rw [PolicySnapshot.drawPersistent_def, PolicySnapshot.drawPersistent_def, declared, rate]
  dsimp only
  cases (beginExploration count declaredRate rng).1 with
  | some run => exact ⟨rfl, rfl, rfl⟩
  | none =>
    dsimp only
    rw [greedy]
    exact ⟨rfl, rfl, rfl⟩

/-- Every action is a candidate of the resting policy: every value is within the tie window of
the maximum. -/
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

/-- The ordered reservoir in the arithmetic of natural numbers: the candidate at count `seen + 1`
replaces the pick exactly when the next word times that count is below `2^64`, which is when the
executed range selection returns zero. -/
def naturalReservoir {actions : ℕ} :
    List (Action actions) → ℕ → Action actions → Rng.Xoshiro256 →
      Action actions × Rng.Xoshiro256
  | [], _, pick, rng => (pick, rng)
  | action :: rest, seen, pick, rng =>
    naturalReservoir rest (seen + 1)
      (if rng.next.1.toNat * (seen + 1) < 2 ^ 64 then action else pick) rng.next.2

/-- The executed reservoir is the reservoir in natural-number arithmetic, while its count of
candidates stays within a word. -/
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

/-- One decision of the explorer, word by word. A committed run with a step left serves its
action. Otherwise the decision reads one word of the generator. If that word's 53-bit numerator
is below `10737418 · 2^23`, the declared rate's exact share, it reads a duration word and an
action word, takes the action the action word selects and commits the rest of the run. If not, it
takes the pick of the ordered reservoir over every action, which reads one word for each. -/
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

/-- **One decision of the explorer is its decision word by word.** The branch of a persistent draw
at the declared rate is an integer comparison on the first word
(`AcornVerif.TemporalSupport.declared_branch`), and the greedy draw of the resting policy is the
reservoir over every action. -/
theorem Explorer.step_eq (explorer : Explorer count) : explorer.step = explorer.byWord := by
  unfold Explorer.step Explorer.byWord
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

/-- The first actions of an explorer, in one pass over its decisions word by word. -/
def Explorer.actions : ℕ → Explorer count → List (Action count.word.toNat)
  | 0, _ => []
  | steps + 1, explorer =>
    match explorer.byWord with
    | (action, next) => action :: Explorer.actions steps next

/-- The explorer one decision later is the explorer of its next state. -/
theorem Explorer.after_shift (explorer : Explorer count) (time : ℕ) :
    explorer.after (time + 1) = explorer.step.2.after time := by
  induction time with
  | zero => rfl
  | succ time ih => exact congrArg (fun later : Explorer count => later.step.2) ih

/-- The list of an explorer's first actions holds its action at each time. -/
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

/-! ## The executed selection -/

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- What the explorer reads of a temporal state: the run its occupancy has committed, and its
action generator. -/
def explorerOf (state : TemporalControl interface profile config criterion dimension) :
    Explorer interface.actions :=
  ⟨committedRun state.runtime.references.phase, state.runtime.references.rng⟩

/-- A state that serves no step holds no committed run with a step left. -/
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

/-- Preparing selection writes no learner of a profile with no hierarchy. -/
theorem prepare_control (state : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (state.prepareSelection models features reward).runtime.lifecycle.consumers.control =
      state.runtime.lifecycle.consumers.control := by
  simp [TemporalControl.prepareSelection, primitive]

/-- **The executed selection explores.** For a profile with no hierarchy under the declared rate,
from a state whose primitive controller is at rest, every decision the executed selection returns
takes the explorer's action, and the returned state holds the explorer's next run and
generator: for every frame, reward word and model and planning implementation. -/
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
  unfold TemporalControl.selectWithOperations at executed
  have frame := prepare_frame state models features reward
  have kept := prepare_control state primitive models features reward
  generalize state.prepareSelection models features reward = prepared at executed frame kept
  have same : explorerOf prepared = explorerOf state := by
    change Explorer.mk _ _ = Explorer.mk _ _
    rw [frame.1, frame.2]
  rw [← same]
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
    unfold Explorer.step
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
      rw [chosen] at drawn
      obtain ⟨action, -, -, -, generator, committed⟩ := drawn
      have stillPrepared :
          Still (prepared.withPhase .idle).runtime.lifecycle.consumers.control := by
        change Still prepared.runtime.lifecycle.consumers.control
        rw [kept]
        exact still
      obtain ⟨sameAction, sameRun, sameRng⟩ := settled_draw _
        (stillPrepared.snapshot features (prepared.withPhase .idle).controlRate)
        ((TemporalControl.declared_rates (prepared.withPhase .idle) declared).1)
        (prepared.withPhase .idle).runtime.references.rng
      unfold Explorer.step
      rw [unserved]
      refine ⟨action.trans sameAction, ?_⟩
      change Explorer.mk (committedRun next.runtime.references.phase)
        next.runtime.references.rng = _
      rw [committed, generator, sameRun, sameRng]
      rfl
    · rename_i hierarchy
      simp [primitive] at hierarchy

/-! ## The whole step -/

/-- The learning part of a local transition leaves occupancy as it received it. -/
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

/-- The tester leaves occupancy untouched. -/
theorem retire_phase (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (state.retire active).control.runtime.references.phase =
      state.control.runtime.references.phase := by
  unfold Agent.retire
  split
  · rfl
  · exact congrArg (·.phase) (state.control.runtime.retire_references active)

/-- Under the default order the second part of the step leaves the explorer's state as the
first part left it: it draws nothing and moves no occupancy. -/
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

/-- **The executed step explores.** For a profile with no hierarchy under the declared rate, from
an agent state whose primitive controller is at rest, the executed step takes the explorer's
action on every percept, whatever its reward word, and the agent it returns holds the explorer's
next state. Under the default order the step selects before it learns from its percept's
reward. -/
theorem act_explores (agent : Agent interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (still : Still agent.control.runtime.lifecycle.consumers.control)
    (percept : Percept interface) :
    (agent.act percept).2.action = (explorerOf agent.control).step.1 ∧
      explorerOf (agent.act percept).1.control = (explorerOf agent.control).step.2 := by
  rw [Agent.act_parts]
  obtain ⟨selected, ordered, -⟩ := agent.choose_selected .learnThenAct (by decide) percept
  unfold TemporalControl.select at selected
  have explored := select_explores agent.advanceClock.control _ primitive declared still
    _ _ _ _ _ _ _ selected
  exact ⟨explored.1,
    (learn_explorer (agent.choose .learnThenAct percept) ordered).trans explored.2⟩

/-- The executed step keeps an agent's learners at rest on a percept whose reward word is a zero
word. -/
theorem act_quiet (agent : Agent interface profile config criterion dimension planning)
    (quiet : Quiet agent.control) (percept : Percept interface)
    (unpaid : percept.reward.isZero = true) : Quiet (agent.act percept).1.control := by
  rw [Agent.act_parts]
  exact quiet.actOrdered .learnThenAct percept (Inert32.ofZero unpaid)

/-! ## A kernel run -/

/-- **The executed agent's actions up to a first reward.** For a profile with no hierarchy under
the declared rate, from an agent state whose learners are at rest: in every world of the agent's
interface, from every start, if every reward word the world delivers before a time is a zero
word, then at that time the agent is at rest, holds the explorer's state after that many
decisions, and takes the explorer's action, whatever reward word that time's percept carries. -/
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

/-- **From cold initialization the agent takes the explorer's actions.** For a profile with no
hierarchy under the declared rate, in every world of the agent's interface and from every start:
if every reward word delivered before a time is a zero word, the cold agent's action at that time
is the action, at that time, of the explorer that holds no run and the generator seeded from the
feature configuration's seed. The decision on the first percept that carries another reward word
is among them. -/
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
