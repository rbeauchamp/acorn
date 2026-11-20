/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LearnedStateSmall

/-! # What the frame refuses, and what it admits

**Refused, by the property every member of the kind has.**
* *The agent's own step is supplied or changed by the submission.* A result is about
  `assembled`, which is the base agent on extended percepts. A submission supplies a mechanism
  and a task, and no step, no split of a step, no encoding of what is kept and no credited
  type. So there is nothing for it to write that behaves one way on the agent's own values and
  another way on replaced ones.
* *The answer is what the mechanism holds.* If stores fixed in advance meet the goal, no result
  (`fixed_stores_refused`). Example: where both hidden bits are false the remembered cue is the
  answer, tables that return their key meet the goal, and `Small.latch` has no result
  (`Small.remembered_refused`).
* *The goal can be satisfied without the past.* If an agent whose output is a function of the
  current percept meets the goal in every world, no result (`Result.history_free_refused`). A
  goal with an added alternative that a constant emitter satisfies is of this kind
  (`Small.alternative_refused`), and so is a goal that a responder copying part of the current
  percept satisfies.
* *The mechanism holds nothing of the stream.* `Result.handout_not_rule` and
  `Result.stateless_refused`: a hand-out that is a rule of the time and the current percept,
  as a clock's is, has no result.

**Admitted.**
* *A goal that only recognizes the submission.* `Small.recognizer_admitted` is a result of the
  small agent for the goal "the trace is this agent's at some seed". `recognized_iff` shows
  this is general.
* *A memory written by an authored rule.* `Small.latch` holds the last cue by a rule written by
  hand, and `Small.inhabited` is its result. The frame says nothing of how a memory is written.

**Not ordered.** Overwriting more stores does not make failure easier to obtain, nor harder, as
a rule. `Small.overwriting_more_can_restore`: for the goal "at the second asking step the action
equals the forecast" over two worlds, the small agent with either store alone on any schedule
fails, and with both stores on constant tables it meets the goal. So the two statements about
one store hold for that goal and the statement about both does not.
-/

namespace AcornVerif.LearnedState

variable {S : Setting} {mechanism : Mechanism S} {task : Task S}

/-- If, at some seed, stores fixed in advance meet the goal in every world, there is no
result: a preset schedule of the two stores suffices for the goal. -/
theorem fixed_stores_refused (seed : S.Seed) (predictions : Nat → S.Predictor)
    (controls : Nat → S.Controller)
    (met : ∀ member, task.goal member
      (trace S (withoutLearning S mechanism predictions controls) seed (task.world member)))
    (result : Result S mechanism task) : False := by
  obtain ⟨member, fails⟩ := result.learningNeeded seed predictions controls
  exact fails (met member)

namespace Small

/-- The members whose hidden bits are both false, so that the cue is the action that pays and
the echo. -/
def rememberedTask : Task setting where
  Family := Nat → Bool
  world cues := world ⟨false, false, cues⟩
  goal cues := Answered ⟨false, false, cues⟩
  sameWorld := sameWorld_of_injective (S := setting) _ _ fun first second same =>
    congrArg Member.cues (world_injective ⟨false, false, first⟩ ⟨false, false, second⟩ same)

/-- A table that returns its key. -/
def obey (_ : Nat) (key : Option Bool) : Option Bool := key

/-- One step of the latch with both stores on `obey` keeps: asked, the latch holds the trial's
cue. -/
theorem obey_step (cues : Nat → Bool) (board : Board) (state : (Mind × Option Bool) × Nat)
    (before : board.asking = true → state.1.2 = some (cues board.trial)) :
    ((world ⟨false, false, cues⟩).step board
        ((withoutLearning setting latch obey obey).step state
          ((world ⟨false, false, cues⟩).percept board)).1.action).asking = true →
      ((withoutLearning setting latch obey obey).step state
          ((world ⟨false, false, cues⟩).percept board)).2.1.2 =
        some (cues ((world ⟨false, false, cues⟩).step board
          ((withoutLearning setting latch obey obey).step state
            ((world ⟨false, false, cues⟩).percept board)).1.action).trial) := by
  obtain ⟨trial, asking, paid, heard⟩ := board
  cases asking with
  | false => intro _; rfl
  | true => intro impossible; cases impossible

/-- Along every run with both stores on `obey`, asked, the latch holds the trial's cue. -/
theorem obey_holds (cues : Nat → Bool) (draw : Bool) (time : Nat) :
    (run setting (withoutLearning setting latch obey obey) draw
        (world ⟨false, false, cues⟩) time).1.asking = true →
      (run setting (withoutLearning setting latch obey obey) draw
          (world ⟨false, false, cues⟩) time).2.1.2 =
        some (cues (run setting (withoutLearning setting latch obey obey) draw
          (world ⟨false, false, cues⟩) time).1.trial) := by
  induction time with
  | zero => intro impossible; cases impossible
  | succ time ih => exact obey_step cues _ _ ih

/-- Asked while the latch holds the trial's cue, the agent with both stores on `obey` answers
right. -/
theorem obey_answers (cues : Nat → Bool) (board : Board) (state : (Mind × Option Bool) × Nat)
    (holds : board.asking = true → state.1.2 = some (cues board.trial))
    (asking : board.asking = true) :
    ((withoutLearning setting latch obey obey).step state
          ((world ⟨false, false, cues⟩).percept board)).1.action =
        need ⟨false, false, cues⟩ board.trial ∧
      ((withoutLearning setting latch obey obey).step state
          ((world ⟨false, false, cues⟩).percept board)).1.forecast =
        echo ⟨false, false, cues⟩ board.trial := by
  obtain ⟨⟨mind, held⟩, clock⟩ := state
  obtain ⟨trial, asked, paid, heard⟩ := board
  obtain rfl : asked = true := asking
  obtain rfl : held = some (cues trial) := holds rfl
  change (cues trial = (cues trial != false)) ∧ (cues trial = (cues trial != false))
  cases cues trial <;> exact ⟨rfl, rfl⟩

/-- **The answer is what the mechanism holds: refused.** Where both hidden bits are false, the
latch has no result, because tables that return their key meet the goal. -/
theorem remembered_refused : ¬ Result setting latch rememberedTask :=
  fixed_stores_refused false obey obey fun cues time asking _ =>
    obey_answers cues _ _ (obey_holds cues false time) asking

/-- The small task with an alternative added to its goal: or the first forecast is true. -/
def alternativeTask : Task setting where
  Family := Member
  world := world
  goal member trace := Answered member trace ∨ (trace 0).2.forecast = true
  sameWorld := sameWorld_of_injective (S := setting) world _ world_injective

/-- **An added alternative that a constant emitter satisfies: refused.** -/
theorem alternative_refused : ¬ Result setting latch alternativeTask := by
  intro result
  obtain ⟨member, fails⟩ := result.historyNeeded false fun _ _ => ⟨false, true⟩
  exact fails (Or.inr rfl)

/-- **Admitted: a goal that only recognizes the submission.** The small agent has a result for
the goal "the trace is this agent's at some seed", over the same worlds. -/
theorem recognizer_admitted : Result setting latch (recognizer setting latch world) :=
  inhabited.recognized

/-! ## Overwriting more stores can restore a goal -/

/-- A member with every cue false and one hidden bit deciding both the paying action and the
echo. -/
def twin (hidden : Bool) : Member := ⟨hidden, hidden, fun _ => false⟩

/-- The goal over those two worlds: at the second asking step the action equals the forecast. -/
def agreeTask : Task setting where
  Family := Bool
  world hidden := world (twin hidden)
  goal _ trace := (trace 3).2.action = (trace 3).2.forecast
  sameWorld := sameWorld_of_injective (S := setting) _ _ fun first second same =>
    congrArg Member.swap (world_injective (twin first) (twin second) same)

/-- The small agent meets it: both tables learn the hidden bit. -/
theorem agree_meets : Meets setting (assembled setting latch) agreeTask := by
  intro draw hidden
  cases draw <;> cases hidden <;> rfl

/-- With the prediction store alone on any schedule the agent fails: the control table still
learns the hidden bit, and the scheduled forecast is chosen against. -/
theorem agree_predictionNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutPrediction setting latch schedule) agreeTask draw := by
  refine ⟨!(schedule 3 (some false)).getD false, fun agree => ?_⟩
  have differs : ∀ forecast seed : Bool,
      (if (seed == (false != !forecast)) = true then seed else !seed) ≠ forecast := by decide
  exact differs _ draw agree

/-- With the control store alone on any schedule the agent fails: the prediction table still
learns the hidden bit, and the scheduled action is chosen against. -/
theorem agree_controlNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutControl setting latch schedule) agreeTask draw := by
  refine ⟨!(schedule 3 (some false)).getD draw, fun agree => ?_⟩
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ agree

/-- With both stores on constant tables the agent meets the goal, at every seed and in both
worlds. -/
theorem agree_both_meets :
    Meets setting (withoutLearning setting latch (fun _ _ => some false) fun _ _ => some false)
      agreeTask := by
  intro draw hidden
  rfl

/-- **Overwriting more stores can restore a goal that overwriting fewer breaks.** For
`agreeTask` the small agent meets the goal, fails with either store alone on any schedule, and
with both stores on some schedules does not fail. -/
theorem overwriting_more_can_restore :
    Meets setting (assembled setting latch) agreeTask ∧
      (∀ draw schedule,
        Fails setting (withoutPrediction setting latch schedule) agreeTask draw) ∧
      (∀ draw schedule, Fails setting (withoutControl setting latch schedule) agreeTask draw) ∧
      ∃ predictions controls, ∀ draw,
        ¬ Fails setting (withoutLearning setting latch predictions controls) agreeTask draw :=
  ⟨agree_meets, agree_predictionNeeded, agree_controlNeeded,
    _, _, fun draw ⟨hidden, fails⟩ => fails (agree_both_meets draw hidden)⟩

end Small

end AcornVerif.LearnedState
