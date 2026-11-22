/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LearnedStateSmall

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
  condition cues := Answered ⟨false, false, cues⟩
  scored _ _ _ := True
  sameWorld := sameWorld_of_injective (S := setting) _ _ _ fun first second same =>
    congrArg Member.cues (world_injective ⟨false, false, first⟩ ⟨false, false, second⟩ same)

/-- A table that returns its key. -/
def obey (_ : Nat) (key : Option Bool) : Option Bool := key

/-- One step of the latch with both stores on `obey` keeps: asked, the latch holds the trial's
cue. -/
theorem obey_step (cues : Nat → Bool) (board : Board) (state : (Mind × Option Bool) × Nat)
    (before : board.asking = true → state.1.2 = some (cues board.trial)) :
    ((world ⟨false, false, cues⟩).step board
        ((withoutLearning setting latch obey obey).step state
          ((world ⟨false, false, cues⟩).percept board)).1.shown.action).asking = true →
      ((withoutLearning setting latch obey obey).step state
          ((world ⟨false, false, cues⟩).percept board)).2.1.2 =
        some (cues ((world ⟨false, false, cues⟩).step board
          ((withoutLearning setting latch obey obey).step state
            ((world ⟨false, false, cues⟩).percept board)).1.shown.action).trial) := by
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
          ((world ⟨false, false, cues⟩).percept board)).1.shown.action =
        need ⟨false, false, cues⟩ board.trial ∧
      ((withoutLearning setting latch obey obey).step state
          ((world ⟨false, false, cues⟩).percept board)).1.shown.forecast =
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
  fixed_stores_refused false obey obey fun cues => ⟨fun time asking _ =>
    obey_answers cues _ _ (obey_holds cues false time) asking, 0, fun _ _ _ => trivial⟩

/-- The small task with an alternative added to its goal: or the first forecast is true. -/
def alternativeTask : Task setting where
  Family := Member
  world := world
  condition member trace := Answered member trace ∨ (trace 0).2.forecast = true
  scored _ _ _ := True
  sameWorld := sameWorld_of_injective (S := setting) world _ _ world_injective

/-- **An added alternative that a constant emitter satisfies: refused.** -/
theorem alternative_refused : ¬ Result setting latch alternativeTask := by
  intro result
  obtain ⟨member, fails⟩ := result.historyNeeded false fun _ _ => ⟨false, true⟩
  exact fails ⟨Or.inr rfl, 0, fun _ _ _ => trivial⟩

theorem base_unflagged (mind : Mind) (percept : Percept) :
    (base.step mind percept).1.explored = false := by
  obtain ⟨cue, paid, echo, held⟩ := percept
  cases cue <;> rfl

theorem recognized_fails (agent : Agent setting.Seed setting.Percept setting.Output)
    (draw : Bool)
    (calm : ∀ state percept, (agent.step state percept).1.explored = false)
    (fails : Fails setting agent Small.task draw) :
    Fails setting agent (recognizer setting latch world) draw := by
  obtain ⟨member, failed⟩ := fails
  refine ⟨member, fun ⟨⟨other, same⟩, _⟩ => failed ?_⟩
  have equal : trace setting (assembled setting latch) other (world member) =
      trace setting agent draw (world member) :=
    trace_eq_of_flagFree same fun _ => (base_unflagged _ _).trans (calm _ _).symm
  change Small.task.goal member (trace setting agent draw (world member))
  rw [← equal]
  exact meets other member

theorem recognizer_admitted : Result setting latch (recognizer setting latch world) :=
  ⟨fun draw _ => ⟨⟨draw, rfl⟩, 0, fun _ _ _ => trivial⟩,
    fun draw => recognized_fails _ draw (fun _ _ => base_unflagged _ _) (baseFails draw),
    fun draw reply => recognized_fails _ draw (fun _ _ => rfl) (historyNeeded draw reply),
    fun draw rule => recognized_fails _ draw (fun _ _ => base_unflagged _ _)
      (stateNeeded draw rule),
    fun draw schedule => recognized_fails _ draw (fun _ _ => base_unflagged _ _)
      (predictionNeeded draw schedule),
    fun draw schedule => recognized_fails _ draw (fun _ _ => base_unflagged _ _)
      (controlNeeded draw schedule),
    fun draw predictions controls => recognized_fails _ draw (fun _ _ => base_unflagged _ _)
      (learningNeeded draw predictions controls)⟩

/-! ## Overwriting more stores can restore a goal -/

/-- A member with every cue false and one hidden bit deciding both the paying action and the
echo. -/
def twin (hidden : Bool) : Member := ⟨hidden, hidden, fun _ => false⟩

/-- The goal over those two worlds: at the second asking step the action equals the forecast. -/
def agreeTask : Task setting where
  Family := Bool
  world hidden := world (twin hidden)
  condition _ trace := (trace 3).2.action = (trace 3).2.forecast
  scored _ _ _ := True
  sameWorld := sameWorld_of_injective (S := setting) _ _ _ fun first second same =>
    congrArg Member.swap (world_injective (twin first) (twin second) same)

/-- The small agent meets it: both tables learn the hidden bit. -/
theorem agree_meets : Meets setting (assembled setting latch) agreeTask := by
  intro draw hidden
  cases draw <;> cases hidden <;> exact ⟨rfl, 0, fun _ _ _ => trivial⟩

/-- With the prediction store alone on any schedule the agent fails: the control table still
learns the hidden bit, and the scheduled forecast is chosen against. -/
theorem agree_predictionNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutPrediction setting latch schedule) agreeTask draw := by
  refine ⟨!(schedule 3 (some false)).getD false, fun ⟨agree, _⟩ => ?_⟩
  have differs : ∀ forecast seed : Bool,
      (if (seed == (false != !forecast)) = true then seed else !seed) ≠ forecast := by decide
  exact differs _ draw agree

/-- With the control store alone on any schedule the agent fails: the prediction table still
learns the hidden bit, and the scheduled action is chosen against. -/
theorem agree_controlNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutControl setting latch schedule) agreeTask draw := by
  refine ⟨!(schedule 3 (some false)).getD draw, fun ⟨agree, _⟩ => ?_⟩
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ agree

/-- With both stores on constant tables the agent meets the goal, at every seed and in both
worlds. -/
theorem agree_both_meets :
    Meets setting (withoutLearning setting latch (fun _ _ => some false) fun _ _ => some false)
      agreeTask := by
  intro draw hidden
  exact ⟨rfl, 0, fun _ _ _ => trivial⟩

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

namespace Converse

structure Mind where
  clock : Nat
  prediction : Bool
  control : Bool

def base : Agent Unit (Option Bool × Option Bool) (Emitted Unit) where
  State := Mind
  cold _ := ⟨0, false, false⟩
  step mind percept :=
    (⟨(), if mind.clock = 0 then true
        else if mind.clock = 1 then
          (percept.2 == some mind.prediction && percept.2 == some mind.control)
        else false⟩,
      ⟨mind.clock + 1, percept.1.getD mind.prediction, percept.1.getD mind.control⟩)

abbrev setting : Setting where
  Seed := Unit
  seeded := ⟨()⟩
  Percept := Option Bool × Option Bool
  Action := Unit
  Shown := Unit
  action _ := ()
  base := base
  Extra := Option Bool
  extend percept handed := (percept.1, handed)
  Predictor := Bool
  Controller := Bool
  predictor mind := mind.prediction
  controller mind := mind.control
  setPredictor mind value := { mind with prediction := value }
  setController mind value := { mind with control := value }
  predictor_same _ := rfl
  controller_same _ := rfl

def latch : Mechanism setting where
  Memory := Option Bool
  cold _ := none
  read held percept :=
    match percept.1 with
    | some cue => (some cue, some cue)
    | none => (held, held)
  note held _ := held

def world (cue : Bool) : World (Option Bool × Option Bool) Unit where
  State := Nat
  start := 0
  step time _ := time + 1
  percept time := if time = 0 then (some cue, none) else (none, none)

theorem assembled_flag (other : Unit) (cue : Bool) :
    (trace setting (assembled setting latch) other (world cue) 1).2.explored = true := by
  cases cue <;> rfl

theorem fed_flag (rule : Nat → Option Bool × Option Bool → Option Bool) (cue : Bool) :
    (trace setting (fed setting rule) () (world cue) 1).2.explored =
      (rule 1 (none, none) == some cue && rule 1 (none, none) == some cue) := rfl

theorem prediction_flag (schedule : Nat → Bool) (cue : Bool) :
    (trace setting (withoutPrediction setting latch schedule) () (world cue) 1).2.explored =
      (some cue == some (schedule 1) && some cue == some cue) := rfl

theorem control_flag (schedule : Nat → Bool) (cue : Bool) :
    (trace setting (withoutControl setting latch schedule) () (world cue) 1).2.explored =
      (some cue == some cue && some cue == some (schedule 1)) := rfl

theorem learning_flag (predictions controls : Nat → Bool) (cue : Bool) :
    (trace setting (withoutLearning setting latch predictions controls) () (world cue)
        1).2.explored =
      (some cue == some (predictions 1) && some cue == some (controls 1)) := rfl

theorem unrecognized_of_flag {agent : Agent setting.Seed setting.Percept setting.Output}
    (cue : Bool) (differs : (trace setting agent () (world cue) 1).2.explored = false) :
    Unrecognized setting latch world agent () := by
  refine ⟨cue, fun ⟨other, same⟩ => ?_⟩
  have flag : (trace setting (assembled setting latch) other (world cue) 1).2.explored =
      (trace setting agent () (world cue) 1).2.explored :=
    congrArg (fun step => step.2.explored) (congrFun same 1)
  rw [assembled_flag, differs] at flag
  cases flag

theorem separated : Separated setting latch world := by
  refine ⟨fun () => unrecognized_of_flag true rfl,
    fun () _ => unrecognized_of_flag true rfl,
    fun () rule => unrecognized_of_flag (!(rule 1 (none, none) == some true)) ?_,
    fun () schedule => unrecognized_of_flag (!(schedule 1)) ?_,
    fun () schedule => unrecognized_of_flag (!(schedule 1)) ?_,
    fun () predictions controls => unrecognized_of_flag (!(predictions 1)) ?_⟩
  · rw [fed_flag]
    generalize rule 1 (none, none) = handed
    cases handed with
    | none => rfl
    | some value => cases value <;> rfl
  · rw [prediction_flag]
    generalize schedule 1 = value
    cases value <;> rfl
  · rw [control_flag]
    generalize schedule 1 = value
    cases value <;> rfl
  · rw [learning_flag]
    generalize predictions 1 = value
    generalize controls 1 = other
    cases value <;> cases other <;> rfl

theorem world_clock (agent : Agent setting.Seed setting.Percept setting.Output) (cue : Bool)
    (time : Nat) : (run setting agent () (world cue) time).1 = time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [run_succ]
    exact congrArg (· + 1) ih

theorem assembled_clock (cue : Bool) (time : Nat) :
    (run setting (assembled setting latch) () (world cue) time).2.1.1.clock = time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [run_succ]
    exact congrArg (· + 1) ih

theorem base_late (mind : Mind) (percept : Option Bool × Option Bool) (late : 2 ≤ mind.clock) :
    (base.step mind percept).1.explored = false := by
  obtain ⟨clock, prediction, control⟩ := mind
  change 2 ≤ clock at late
  have zero : clock ≠ 0 := by omega
  have one : clock ≠ 1 := by omega
  simp [base, zero, one]

theorem assembled_calm (cue : Bool) (time : Nat) (late : 2 ≤ time) :
    (trace setting (assembled setting latch) () (world cue) time).2.explored = false :=
  base_late (run setting (assembled setting latch) () (world cue) time).2.1.1 _
    (by rw [assembled_clock]; exact late)

theorem no_result : ¬ ∃ condition scored sameWorld,
    Result setting latch ⟨Bool, world, condition, scored, sameWorld⟩ := by
  rintro ⟨condition, scored, sameWorld, result⟩
  obtain ⟨cue, fails⟩ := result.historyNeeded () fun _ _ => ()
  apply fails
  refine Verdict.explores_more ?_ ⟨2, fun time late _ => assembled_calm cue time late⟩
    (result.meets () cue)
  funext time
  show ((run setting (assembled setting latch) () (world cue) time).1, ()) =
    ((run setting (responding setting fun _ _ => ()) () (world cue) time).1, ())
  rw [world_clock, world_clock]

theorem separation_without_result : Separated setting latch world ∧
    ¬ ∃ condition scored sameWorld,
      Result setting latch ⟨Bool, world, condition, scored, sameWorld⟩ :=
  ⟨separated, no_result⟩

end Converse

end AcornVerif.LearnedState
