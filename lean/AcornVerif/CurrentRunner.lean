/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Ansi
import Acorn.Host.Baseline

/-!
# Current attempt and supervision invariants

The same prepared-action and commit definitions are called by the native
runner. Callbacks supply the full agent; no learned transition is modeled or
invented here. IO event order is linked through the native call gate and source
review, while these universal claims own the pure admission and progression.
The last section states the random-policy comparator's action law, its
correspondence with the agent's attempt and its completion.
-/
namespace AcornVerif.CurrentRunner
open Acorn Acorn.Host

variable {order : StepOrder}

/-- Every successful commit consumes exactly one of the prepared remaining steps. -/
theorem commit_steps {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) (callbacks : AgentCallbacks order α β)
    (next : Attempt config α goal cap) (h : prepared.commit callbacks = .ok next) :
    next.steps.val = prepared.before.steps.val + 1 := by
  unfold PreparedStep.commit PreparedStep.environment at h
  split at h
  · contradiction
  · cases Except.ok.inj h
    rfl

/-- The world phase of a prepared commit advances exactly one physical clock tick. -/
theorem commit_clock {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) (callbacks : AgentCallbacks order α β)
    (next : Attempt config α goal cap) (h : prepared.commit callbacks = .ok next) :
    next.run.world.time = prepared.before.run.world.time + 1 := by
  unfold PreparedStep.commit PreparedStep.environment at h
  split at h
  · contradiction
  · rename_i world result hs
    cases Except.ok.inj h
    exact World.step_clock _ _ _ _ hs

/-- Every admitted attempt state preserves its receiving task and finite step budget. -/
theorem attempt_bounds {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) :
    attempt.run.world.goal = some goal ∧ attempt.steps.val ≤ cap.toNat :=
  ⟨attempt.installed, by have := attempt.steps.isLt; omega⟩

/-- A non-stopping boundary never produces the stopped outcome. -/
theorem boundary_running {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (achieved : Bool) : atAttemptBoundary cursor achieved false ≠ .stopped := by
  unfold atAttemptBoundary atAttemptBoundary.nextGoal
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · split
    · intro h; cases h
    · split
      · intro h; cases h
      · split <;> intro h <;> cases h
  · split
    · intro h; cases h
    · split <;> intro h <;> cases h

/-- A refused image cannot yield a writable destination, even at a stop boundary. -/
theorem checkpoint_refusal (path : System.FilePath) (interval : UInt32) :
    WritableCheckpoint.admit path interval .refused = none := rfl

/-- Empty unbounded input has no campaign plan, for every curriculum size. -/
theorem empty_unbounded_refused (size : Nat) (steps attempts : UInt64) :
    CampaignPlan.admit size ⟨steps, attempts, 0, 0⟩ =
      .error (if 0 < steps.toNat then .emptyUnbounded else .stepCapZero) := by
  by_cases h : 0 < steps.toNat <;> simp [CampaignPlan.admit, h]

/-! ## Random-policy comparator

The comparator of `Acorn.Host.Baseline` against the agent's attempt and campaign
definitions. `Corresponds` relates an agent attempt to a comparator attempt;
the theorems that follow show that the relation holds at goal installation, is
kept by every step on which both arms take the same action, ends both attempts
together and gives both the same outcome row. The agent's side is the reference
transition `Attempt.tick`, to which `DecisionInput.selectOwned_eq` and
`SelectedStep.owned_commit` link the native loop.
-/

/-- Every action code survives the world's code conversion. -/
theorem fromIndex_index : ∀ code, code < 9 → (Action.fromIndex code).index.val = code := by
  decide

/-- The comparator's action code is the high word of nine times the stream's
output word w: ⌊9w / 2⁶⁴⌋. -/
theorem baseline_action_code (rng : Rng.Xoshiro256) :
    (baselineAction rng).1.index.val = rng.next.1.toNat * 9 / 2 ^ 64 := by
  have bound : (rng.nextBelow baselineActionCount).1.val.toNat < 9 :=
    (rng.nextBelow baselineActionCount).1.property
  have quotient := Rng.nextBelow_quotient rng baselineActionCount
  change (Action.fromIndex (rng.nextBelow baselineActionCount).1.val.toNat).index.val = _
  rw [fromIndex_index _ bound, quotient]
  rfl

/-- A comparator draw consumes exactly one output of the stream, whatever the action. -/
theorem baseline_action_stream (rng : Rng.Xoshiro256) : (baselineAction rng).2 = rng.next.2 := rfl

/-- The number of output words that select wait or eat; every other action has
one more (`action_word_count`). -/
def actionWords : Nat := 2049638230412172401

/-- The 2⁶⁴ output words are nine blocks of `actionWords` and seven more. -/
theorem word_space : 2 ^ 64 = 9 * actionWords + 7 := by decide

/-- The output words that select one action code are exactly one interval. -/
theorem action_word_interval (word code : Nat) (bound : code < 9) :
    word * 9 / 2 ^ 64 = code ↔
      code * actionWords + (7 * code + 8) / 9 ≤ word ∧
        word < (code + 1) * actionWords + (7 * code + 15) / 9 := by
  have cases : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 ∨ code = 4 ∨ code = 5 ∨ code = 6 ∨
      code = 7 ∨ code = 8 := by omega
  unfold actionWords
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- The interval of an action code holds `actionWords` words for wait (code 4)
and eat (code 8) and one more for each of the other seven actions, so under a
uniform output word every action has probability within 2⁻⁶⁴ of 1/9. -/
theorem action_word_count : ∀ code, code < 9 →
    ((code + 1) * actionWords + (7 * code + 15) / 9) - (code * actionWords + (7 * code + 8) / 9) =
      if code = 4 ∨ code = 8 then actionWords else actionWords + 1 := by
  decide

/-- The comparator attempt that carries the world side of an agent attempt. -/
structure Corresponds {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) (state : BaselineAttempt config cap) : Prop where
  /-- The same physical world, installed goal included. -/
  world : state.world = attempt.run.world
  /-- The same number of steps taken. -/
  steps : state.steps = attempt.steps
  /-- The comparator's completion flag is the agent's reason to end early: the
  carried flag, once this attempt has taken a step. -/
  done : state.result.done = (attempt.steps.val != 0 && attempt.run.carried.events.done)

/-- Goal installation puts both arms in corresponding states from one world,
whatever result the agent's stream carries in. -/
theorem start_corresponds {config : WorldConfig} {α : Type} (run : RunState config α)
    (rng : Rng.Xoshiro256) (goal : Goal) (cap : UInt64) :
    Corresponds (Attempt.start run goal cap) (BaselineAttempt.start run.world rng goal cap) :=
  ⟨rfl, rfl, rfl⟩

/-- A sensed decision belongs to an unfinished attempt and returns that attempt. -/
theorem sense_some {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) (input : DecisionInput config α goal cap)
    (h : attempt.sense = .ok (some input)) : attempt.finished = false ∧ input.before = attempt := by
  unfold Attempt.sense at h
  cases finished : attempt.finished with
  | true => simp [finished, pure, Except.pure] at h
  | false =>
    simp only [finished, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        exact ⟨rfl, by rw [← h]⟩
    · simp [pure, Except.pure] at h

/-- An attempt that senses nothing is finished. -/
theorem sense_none {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) (h : attempt.sense = .ok none) :
    attempt.finished = true := by
  unfold Attempt.sense at h
  cases finished : attempt.finished with
  | true => rfl
  | false =>
    simp only [finished, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [pure, Except.pure] at h
    · rename_i full
      have bound := attempt.steps.isLt
      have equal : attempt.steps.val = cap.toNat := by omega
      simp [Attempt.finished, equal] at finished

/-- A successful commit ran the world's transition on the prepared action, kept
its result as the carried result and counted one step. -/
theorem commit_world {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) (callbacks : AgentCallbacks order α β)
    (next : Attempt config α goal cap) (h : prepared.commit callbacks = .ok next) :
    prepared.before.run.world.step prepared.action = .ok (next.run.world, next.run.carried.events) ∧
      next.steps.val = prepared.before.steps.val + 1 := by
  unfold PreparedStep.commit PreparedStep.environment at h
  split at h
  · contradiction
  · rename_i world result stepped
    cases Except.ok.inj h
    exact ⟨stepped, rfl⟩

/-- An agent tick that acted belonged to an unfinished attempt below its cap, ran
the world's transition on the frame's action and counted one step. -/
theorem tick_acted {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt next : Attempt config α goal cap) (frame : StepFrame β)
    (h : attempt.tick callbacks context = .ok (next, some frame)) :
    attempt.finished = false ∧ attempt.steps.val < cap.toNat ∧
      attempt.run.world.step frame.action = .ok (next.run.world, next.run.carried.events) ∧
      next.steps.val = attempt.steps.val + 1 := by
  unfold Attempt.tick Attempt.prepare at h
  cases sensed : attempt.sense with
  | error error => simp [sensed, bind, Except.bind] at h
  | ok decision =>
    cases decision with
    | none => simp [sensed, bind, Except.bind, pure, Except.pure] at h
    | some input =>
      obtain ⟨unfinished, before⟩ := sense_some attempt input sensed
      subst before
      simp only [sensed, bind, Except.bind, pure, Except.pure, Option.map] at h
      cases committed : ((input.select callbacks).capture callbacks context).commit callbacks with
      | error error => simp [committed] at h
      | ok after =>
        simp only [committed, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨stepped, count⟩ := commit_world _ callbacks after committed
        exact ⟨unfinished, input.remaining, stepped, count⟩

/-- An agent tick that took no action left a finished attempt unchanged. -/
theorem tick_idle {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt next : Attempt config α goal cap)
    (h : attempt.tick callbacks context = .ok (next, none)) :
    attempt.finished = true ∧ next = attempt := by
  unfold Attempt.tick Attempt.prepare at h
  cases sensed : attempt.sense with
  | error error => simp [sensed, bind, Except.bind] at h
  | ok decision =>
    cases decision with
    | none =>
      simp only [sensed, bind, Except.bind, pure, Except.pure, Option.map, Except.ok.injEq,
        Prod.mk.injEq, and_true] at h
      exact ⟨sense_none attempt sensed, h.symm⟩
    | some input =>
      simp only [sensed, bind, Except.bind, pure, Except.pure, Option.map] at h
      cases committed : ((input.select callbacks).capture callbacks context).commit callbacks with
      | error error => simp [committed] at h
      | ok after => simp [committed] at h

/-- Step correspondence. When the agent's tick acts and the comparator draws the
same action from a corresponding state, the comparator's tick takes that step
too and the states correspond again, for every agent callback. The comparator's
stream advances by exactly that draw. -/
theorem tick_corresponds {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt next : Attempt config α goal cap) (frame : StepFrame β)
    (state : BaselineAttempt config cap) (related : Corresponds attempt state)
    (acted : attempt.tick callbacks context = .ok (next, some frame))
    (drawn : (baselineAction state.rng).1 = frame.action) :
    ∃ after, state.tick = .ok after ∧ Corresponds next after ∧
      after.rng = (baselineAction state.rng).2 := by
  obtain ⟨unfinished, room, stepped, count⟩ := tick_acted callbacks context attempt next frame acted
  have equal := congrArg Fin.val related.steps
  have pending : state.result.done = false := by
    rw [related.done]
    unfold Attempt.finished at unfinished
    simp only [Bool.or_eq_false_iff] at unfinished
    exact unfinished.2
  have space : state.steps.val < cap.toNat := by omega
  refine ⟨⟨next.run.world, (baselineAction state.rng).2, ⟨state.steps.val + 1, by omega⟩,
    next.run.carried.events⟩, ?_, ⟨rfl, Fin.ext ?_, ?_⟩, rfl⟩
  · unfold BaselineAttempt.tick
    simp only [pending, Bool.false_eq_true, ↓reduceIte, space, ↓reduceDIte, drawn, related.world,
      stepped]
  · show state.steps.val + 1 = next.steps.val
    omega
  · simp [count]

/-- Stop correspondence. When the agent's tick takes no action, the comparator's
tick from a corresponding state takes none either. -/
theorem idle_corresponds {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt next : Attempt config α goal cap) (state : BaselineAttempt config cap)
    (related : Corresponds attempt state)
    (idle : attempt.tick callbacks context = .ok (next, none)) : state.tick = .ok state := by
  have finished := (tick_idle callbacks context attempt next idle).1
  have equal := congrArg Fin.val related.steps
  unfold BaselineAttempt.tick
  cases flag : state.result.done with
  | true => simp
  | false =>
    have full : ¬ state.steps.val < cap.toNat := by
      rw [related.done] at flag
      unfold Attempt.finished at finished
      simp only [flag, Bool.or_false, beq_iff_eq] at finished
      omega
    simp [full]

/-- Outcome correspondence. After at least one step, the agent's outcome row and
the comparator's row from a corresponding state report the same steps,
completion flag and position, and both arms carry the same world onward. -/
theorem outcome_corresponds {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt : Attempt config α goal cap) (state : BaselineAttempt config cap)
    (related : Corresponds attempt state) (taken : attempt.steps.val ≠ 0)
    (run : RunState config α) (outcome : GoalOutcome) (frame : StepFrame β)
    (h : attempt.finish callbacks context = .ok (run, outcome, frame)) :
    outcome.steps = (state.outcome context).steps ∧
      outcome.achieved = (state.outcome context).achieved ∧
      outcome.position = (state.outcome context).position ∧ run.world = state.world := by
  unfold Attempt.finish at h
  cases sensed : attempt.run.world.observe with
  | error refusal => simp [sensed, bind, Except.bind] at h
  | ok observation =>
    simp only [sensed, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_, related.world.symm⟩
    · simp [BaselineAttempt.outcome, related.steps]
    · simp [BaselineAttempt.outcome, related.done, taken]
    · simp [BaselineAttempt.outcome, related.world]

/-- With one attempt per goal the next cursor does not depend on the outcome:
both arms visit the same goals in the same order, whatever either achieves. -/
theorem boundary_single_attempt {size : Nat} {plan : CampaignPlan size}
    (single : plan.attempts.toNat = 1) (cursor : CampaignCursor plan) (first second : Bool) :
    atAttemptBoundary cursor first false = atAttemptBoundary cursor second false := by
  have last : ¬ cursor.attempt.val + 1 < plan.attempts.toNat := by omega
  unfold atAttemptBoundary
  simp only [Bool.false_eq_true, ↓reduceIte, last, ↓reduceDIte, ite_self]

/-- Attempts that precede a cursor when every attempt fails: its position in the
schedule of cycles, goals and attempts. -/
def cursorRank {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan) : Nat :=
  (cursor.cycle.toNat * plan.goals.val + cursor.goal.val) * plan.attempts.toNat + cursor.attempt.val

/-- A cursor inside a bounded campaign's cycles lies inside its attempt budget. -/
theorem cursorRank_lt {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (live : cursor.cycle.toNat < plan.cycles.toNat) : cursorRank cursor < plan.attemptBudget := by
  unfold cursorRank CampaignPlan.attemptBudget
  have goal := cursor.goal.isLt
  have attempt := cursor.attempt.isLt
  have cycles := Nat.mul_le_mul_right plan.goals.val (Nat.succ_le_of_lt live)
  rw [Nat.succ_mul] at cycles
  have slots : cursor.cycle.toNat * plan.goals.val + cursor.goal.val + 1 ≤
      plan.cycles.toNat * plan.goals.val := by omega
  have attempts := Nat.mul_le_mul_right plan.attempts.toNat slots
  rw [Nat.add_mul, Nat.one_mul] at attempts
  omega

/-- The first attempt of the next goal slot follows every attempt of this one. -/
theorem slot_advance (slot next attempts attempt : Nat) (successor : next = slot + 1)
    (within : attempt < attempts) : slot * attempts + attempt < next * attempts + 0 := by
  subst successor
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The saturating increment is exact below the word boundary. -/
theorem increment_exact (value : UInt64) (room : value.toNat + 1 < 2 ^ 64) :
    (saturatingIncrement64 value).toNat = value.toNat + 1 := by
  change min (value.toNat + 1) (2 ^ 64 - 1) % (2 ^ 64) = value.toNat + 1
  rw [Nat.min_eq_left (by omega)]
  exact Nat.mod_eq_of_lt room

/-- A goal that is achieved or out of attempts ends the campaign or moves to a
later cursor inside the campaign's cycles. -/
theorem goal_advances {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (live : cursor.cycle.toNat < plan.cycles.toNat) :
    atAttemptBoundary cursor true false = .complete ∨
      ∃ next, atAttemptBoundary cursor true false = .continue next ∧
        next.cycle.toNat < plan.cycles.toNat ∧ cursorRank cursor < cursorRank next := by
  have goal := cursor.goal.isLt
  have attempt := cursor.attempt.isLt
  have width := plan.cycles.toNat_lt
  unfold atAttemptBoundary atAttemptBoundary.nextGoal
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  split
  · refine .inr ⟨_, rfl, live, ?_⟩
    simp only [cursorRank]
    exact slot_advance _ _ _ _ (by omega) attempt
  · rename_i last
    split
    · exact .inl rfl
    · rename_i open_
      have step := increment_exact cursor.cycle (by omega)
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and, ge_iff_le,
        UInt64.le_iff_toNat_le, step] at open_
      have inside := open_ (by
        intro zero
        rw [zero] at live
        simp at live)
      refine .inr ⟨_, rfl, ?_, ?_⟩
      · simp only [step]
        omega
      · simp only [cursorRank, step]
        refine slot_advance _ _ _ _ ?_ attempt
        rw [Nat.add_mul, Nat.one_mul]
        omega

/-- Every boundary without a stop request ends the campaign or moves to a later
cursor inside the campaign's cycles. -/
theorem boundary_advances {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (live : cursor.cycle.toNat < plan.cycles.toNat) (achieved : Bool) :
    atAttemptBoundary cursor achieved false = .complete ∨
      ∃ next, atAttemptBoundary cursor achieved false = .continue next ∧
        next.cycle.toNat < plan.cycles.toNat ∧ cursorRank cursor < cursorRank next := by
  cases achieved with
  | true => exact goal_advances cursor live
  | false =>
    by_cases more : cursor.attempt.val + 1 < plan.attempts.toNat
    · refine .inr ⟨{ cursor with attempt := ⟨cursor.attempt.val + 1, more⟩ }, ?_, live, ?_⟩
      · unfold atAttemptBoundary
        simp [more]
      · simp only [cursorRank]
        omega
    · have exhausted :
          atAttemptBoundary cursor false false = atAttemptBoundary cursor true false := by
        unfold atAttemptBoundary
        simp [more]
      rw [exhausted]
      exact goal_advances cursor live

/-- The comparator's campaign never runs out of fuel inside a bounded campaign's
cycles: with the remaining attempt budget as fuel it ends at the completing
boundary or at a world refusal. -/
theorem baseline_campaign_finishes {config : WorldConfig} (curriculum : Curriculum)
    (plan : CampaignPlan curriculum.size) :
    ∀ (fuel : Nat) (cursor : CampaignCursor plan) (world : World config) (rng : Rng.Xoshiro256)
      (outcomes : Array BaselineOutcome), cursor.cycle.toNat < plan.cycles.toNat →
      plan.attemptBudget ≤ fuel + cursorRank cursor →
      runBaselineCampaign curriculum plan fuel cursor world rng outcomes ≠ .error .unfinished := by
  intro fuel
  induction fuel with
  | zero =>
    intro cursor world rng outcomes live budget
    have := cursorRank_lt cursor live
    omega
  | succ fuel ih =>
    intro cursor world rng outcomes live budget
    rw [runBaselineCampaign]
    split
    · simp
    · rename_i state _
      rcases boundary_advances cursor live state.result.done with
        complete | ⟨next, continues, inside, rank⟩
      · simp [complete]
      · simp only [continues]
        exact ih next _ _ _ inside (by omega)

/-- A bounded campaign always has a complete comparator record or an explicit
world refusal: the comparator never reports it unfinished. -/
theorem baseline_finishes (config : WorldConfig) (seed : UInt64) (spec : CampaignSpec)
    (plan : CampaignPlan (standardCurriculum config seed).size)
    (admitted : CampaignPlan.admit (standardCurriculum config seed).size spec = .ok plan)
    (bounded : plan.cycles.toNat ≠ 0) :
    runRandomBaseline config seed spec ≠ .error .unfinished := by
  unfold runRandomBaseline
  simp only [admitted]
  cases World.initial config with
  | error error => simp
  | ok world =>
    by_cases populated : 0 < plan.goals.val
    · simp only [CampaignPlan.initial, populated, ↓reduceDIte]
      refine baseline_campaign_finishes _ plan _ _ _ _ _ ?_ (by simp [cursorRank])
      show (0 : UInt64).toNat < plan.cycles.toNat
      simp only [UInt64.toNat_zero]
      omega
    · simp [CampaignPlan.initial, populated]

/-- Two callback records, at any two indices, with the same whole step and the same host
functions. A copy of a record under another index is one case. -/
structure SameParts {other : StepOrder} {α β : Type} (first : AgentCallbacks order α β)
    (second : AgentCallbacks other α β) : Prop where
  /-- The whole step, the first part and then the second, is the same function. -/
  whole : ∀ agent observation carried,
    first.act agent observation carried = second.act agent observation carried
  /-- The environment bookkeeping is the same function. -/
  environment : first.recordEnvironment = second.recordEnvironment
  /-- The attempt bookkeeping is the same function. -/
  attempt : first.recordAttempt = second.recordAttempt
  /-- The observer snapshot is the same function. -/
  capture : first.capture = second.capture
  /-- The terminal observations are the same function. -/
  metrics : first.metrics = second.metrics

/-- **The pure fold reads the whole step and the host functions, and not the index.**
For every two callback records with the same whole step and the same host functions, at
any two indices, and every context, fuel and attempt, the fold `Attempt.complete` is the
same value. Both native loops return what this fold returns (`runAttemptSteps_complete`,
`runReleasedSteps_complete`). So a record that is copied under the other index, and run
by the loop of that index, returns the run state, the outcome and the refusal of the
record itself: the copy changes the time of the world's transition, the reported
durations and the order of the frame delivery, and no returned value. The world of this
protocol takes one transition for each action and waits for it; the statement is about
that world. -/
theorem complete_parts {other : StepOrder} {config : WorldConfig} {α β : Type} {goal : Goal}
    {cap : UInt64} (first : AgentCallbacks order α β) (second : AgentCallbacks other α β)
    (same : SameParts first second) (context : GoalContext) (fuel : Nat)
    (attempt : Attempt config α goal cap) :
    attempt.complete first context fuel = attempt.complete second context fuel := by
  have selected : ∀ input : DecisionInput config α goal cap,
      input.selectOwned first = input.selectOwned second := by
    intro input
    cases input with
    | mk before remaining observation sensed =>
      cases before with
      | mk run installed steps reward lastAction =>
        cases run
        simp only [DecisionInput.selectOwned, same.whole]
  have closed : ∀ current : Attempt config α goal cap,
      current.close first context = current.close second context := by
    intro current
    simp only [Attempt.close, Attempt.finish, captureFrame, same.attempt, same.capture,
      same.metrics]
  have recorded : ∀ environment : OwnedEnvironment config α goal cap,
      environment.record first = environment.record second := by
    intro environment
    simp only [OwnedEnvironment.record, same.environment]
  induction fuel generalizing attempt with
  | zero =>
    unfold Attempt.complete
    exact closed attempt
  | succ fuel ih =>
    unfold Attempt.complete
    rw [closed attempt]
    split
    · rfl
    · cases attempt.sense with
      | error refusal => rfl
      | ok found =>
        cases found with
        | none => rfl
        | some input =>
          dsimp only
          rw [selected input]
          cases (input.selectOwned second).release with
          | refused error learned => rfl
          | accepted environment =>
            dsimp only
            rw [recorded environment]
            exact ih _

end AcornVerif.CurrentRunner
