import AcornVerif.LearnedStateSmall

namespace AcornVerif.LearnedState

variable {S : Setting} {mechanism : Mechanism S} {task : Task S}

theorem fixed_stores_refused (seed : S.Seed) (predictions : Nat → S.Predictor)
    (controls : Nat → S.Controller)
    (met : ∀ member, task.goal member
      (trace S (withoutLearning S mechanism predictions controls) seed (task.world member)))
    (result : Result S mechanism task) : False := by
  obtain ⟨member, fails⟩ := result.learningNeeded seed predictions controls
  exact fails (met member)

namespace Small

def rememberedTask : Task setting where
  Family := Nat → Bool
  world cues := world ⟨false, false, cues⟩
  goal cues := Answered ⟨false, false, cues⟩
  sameWorld := sameWorld_of_injective (S := setting) _ _ fun first second same =>
    congrArg Member.cues (world_injective ⟨false, false, first⟩ ⟨false, false, second⟩ same)

def obey (_ : Nat) (key : Option Bool) : Option Bool := key

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

theorem remembered_refused : ¬ Result setting latch rememberedTask :=
  fixed_stores_refused false obey obey fun cues time asking _ =>
    obey_answers cues _ _ (obey_holds cues false time) asking

def alternativeTask : Task setting where
  Family := Member
  world := world
  goal member trace := Answered member trace ∨ (trace 0).2.forecast = true
  sameWorld := sameWorld_of_injective (S := setting) world _ world_injective

theorem alternative_refused : ¬ Result setting latch alternativeTask := by
  intro result
  obtain ⟨member, fails⟩ := result.historyNeeded false fun _ _ => ⟨false, true⟩
  exact fails (Or.inr rfl)

theorem recognizer_admitted : Result setting latch (recognizer setting latch world) :=
  inhabited.recognized

def twin (hidden : Bool) : Member := ⟨hidden, hidden, fun _ => false⟩

def agreeTask : Task setting where
  Family := Bool
  world hidden := world (twin hidden)
  goal _ trace := (trace 3).2.action = (trace 3).2.forecast
  sameWorld := sameWorld_of_injective (S := setting) _ _ fun first second same =>
    congrArg Member.swap (world_injective (twin first) (twin second) same)

theorem agree_meets : Meets setting (assembled setting latch) agreeTask := by
  intro draw hidden
  cases draw <;> cases hidden <;> rfl

theorem agree_predictionNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutPrediction setting latch schedule) agreeTask draw := by
  refine ⟨!(schedule 3 (some false)).getD false, fun agree => ?_⟩
  have differs : ∀ forecast seed : Bool,
      (if (seed == (false != !forecast)) = true then seed else !seed) ≠ forecast := by decide
  exact differs _ draw agree

theorem agree_controlNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutControl setting latch schedule) agreeTask draw := by
  refine ⟨!(schedule 3 (some false)).getD draw, fun agree => ?_⟩
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ agree

theorem agree_both_meets :
    Meets setting (withoutLearning setting latch (fun _ _ => some false) fun _ _ => some false)
      agreeTask := by
  intro draw hidden
  rfl

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
