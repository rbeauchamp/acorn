import AcornVerif.LearnedStateFrame

namespace AcornVerif.LearnedState.Small

structure Percept where
  cue : Option Bool
  paid : Bool
  echo : Bool
  held : Option Bool

structure Output where
  action : Bool
  forecast : Bool

structure Member where
  swap : Bool
  shift : Bool
  cues : Nat → Bool

def need (member : Member) (trial : Nat) : Bool := member.cues trial != member.swap

def echo (member : Member) (trial : Nat) : Bool := member.cues trial != member.shift

structure Board where
  trial : Nat
  asking : Bool
  paid : Bool
  echo : Bool

def world (member : Member) : World Percept Bool where
  State := Board
  start := ⟨0, false, false, false⟩
  step board action :=
    if board.asking then
      ⟨board.trial + 1, false, action == need member board.trial, echo member board.trial⟩
    else ⟨board.trial, true, false, false⟩
  percept board :=
    if board.asking then ⟨none, false, false, none⟩
    else ⟨some (member.cues board.trial), board.paid, board.echo, none⟩

def write (table : Option Bool → Option Bool) (key : Option Bool) (value : Bool) :
    Option Bool → Option Bool :=
  fun other => if other = key then some value else table other

structure Mind where
  draw : Bool
  pending : Option (Option Bool × Bool)
  echoes : Option Bool → Option Bool
  payers : Option Bool → Option Bool

def Mind.record (mind : Mind) (paid echo : Bool) : Mind :=
  match mind.pending with
  | some (key, action) =>
    { mind with
      pending := none
      echoes := write mind.echoes key echo
      payers := write mind.payers key (if paid then action else !action) }
  | none => mind

def base : Agent Bool Percept Output where
  State := Mind
  cold draw := ⟨draw, none, fun _ => none, fun _ => none⟩
  step mind percept :=
    match percept.cue with
    | some _ => (⟨false, false⟩, mind.record percept.paid percept.echo)
    | none =>
      (⟨(mind.payers percept.held).getD mind.draw, (mind.echoes percept.held).getD false⟩,
        { mind with
          pending := some (percept.held, (mind.payers percept.held).getD mind.draw) })

def setting : Setting where
  Seed := Bool
  seeded := ⟨false⟩
  Percept := Percept
  Action := Bool
  Output := Output
  action := Output.action
  base := base
  Extra := Option Bool
  extend percept held := { percept with held := held }
  Predictor := Option Bool → Option Bool
  Controller := Option Bool → Option Bool
  predictor mind := mind.echoes
  controller mind := mind.payers
  setPredictor mind table := { mind with echoes := table }
  setController mind table := { mind with payers := table }
  predictor_same _ := rfl
  controller_same _ := rfl

def latch : Mechanism setting where
  Memory := Option Bool
  cold _ := none
  read held percept :=
    match percept.cue with
    | some cue => (some cue, some cue)
    | none => (held, held)
  note held _ := held

def Answered (member : Member) (trace : Nat → Board × Output) : Prop :=
  ∀ time, (trace time).1.asking = true →
    (∃ earlier, earlier < (trace time).1.trial ∧
      member.cues earlier = member.cues (trace time).1.trial) →
    (trace time).2.action = need member (trace time).1.trial ∧
      (trace time).2.forecast = echo member (trace time).1.trial

theorem world_injective (first second : Member) (same : world first = world second) :
    first = second := by
  unfold world at same
  injection same with _ _ steps percepts
  have cue : ∀ trial, first.cues trial = second.cues trial := fun trial =>
    Option.some.inj (congrArg Percept.cue (congrFun percepts ⟨trial, false, false, false⟩))
  have paid : (false == need first 0) = (false == need second 0) :=
    congrArg Board.paid (congrFun (congrFun steps ⟨0, true, false, false⟩) false)
  have heard : echo first 0 = echo second 0 :=
    congrArg Board.echo (congrFun (congrFun steps ⟨0, true, false, false⟩) false)
  obtain ⟨swap, shift, cues⟩ := first
  obtain ⟨swap', shift', cues'⟩ := second
  obtain rfl : cues = cues' := funext cue
  simp only [need, echo] at paid heard
  have swaps : swap = swap' := by
    revert paid
    cases cues 0 <;> cases swap <;> cases swap' <;> decide
  have shifts : shift = shift' := by
    revert heard
    cases cues 0 <;> cases shift <;> cases shift' <;> decide
  rw [swaps, shifts]

def task : Task setting where
  Family := Member
  world := world
  goal := Answered
  sameWorld := sameWorld_of_injective (S := setting) world Answered world_injective

def Tracks (member : Member) (mind : Mind) (count : Nat) : Prop :=
  ∀ trial, trial < count →
    mind.echoes (some (member.cues trial)) = some (echo member trial) ∧
      mind.payers (some (member.cues trial)) = some (need member trial)

def Sound (member : Member) (board : Board) (mind : Mind) (held : Option Bool) : Prop :=
  if board.asking then held = some (member.cues board.trial) ∧ Tracks member mind board.trial
  else Tracks member (mind.record board.paid board.echo) board.trial

theorem written_payer (action wanted : Bool) :
    (if action == wanted then action else !action) = wanted := by
  cases action <;> cases wanted <;> rfl

theorem sound_step (member : Member) (board : Board) (state : (Mind × Option Bool) × Nat)
    (before : Sound member board state.1.1 state.1.2) :
    Sound member
      ((world member).step board
        ((assembled setting latch).step state ((world member).percept board)).1.action)
      ((assembled setting latch).step state ((world member).percept board)).2.1.1
      ((assembled setting latch).step state ((world member).percept board)).2.1.2 := by
  obtain ⟨⟨mind, held⟩, clock⟩ := state
  obtain ⟨trial, asking, paid, heard⟩ := board
  cases asking with
  | false => exact ⟨rfl, before⟩
  | true =>
    obtain ⟨holds, tracks⟩ := before
    have held' : held = some (member.cues trial) := holds
    subst held'
    intro earlier less
    change earlier < trial + 1 at less
    by_cases same : member.cues earlier = member.cues trial
    · have payer := written_payer ((mind.payers (some (member.cues trial))).getD mind.draw)
        (need member trial)
      simp only [world, setting, base, latch, Mind.record, write, same, need, echo,
        ite_true] at payer ⊢
      exact ⟨trivial, congrArg some payer⟩
    · have earlier' : earlier < trial := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp less with less | equal
        · exact less
        · exact absurd (congrArg member.cues equal) same
      have differs : some (member.cues earlier) ≠ some (member.cues trial) :=
        fun equal => same (Option.some.inj equal)
      simp only [world, setting, base, latch, Mind.record, write, differs, ite_false, ite_true]
      exact tracks earlier earlier'

theorem sound (member : Member) (draw : Bool) (time : Nat) :
    Sound member (run setting (assembled setting latch) draw (world member) time).1
      (run setting (assembled setting latch) draw (world member) time).2.1.1
      (run setting (assembled setting latch) draw (world member) time).2.1.2 := by
  induction time with
  | zero => intro trial before; cases before
  | succ time ih => exact sound_step member _ _ ih

theorem sound_answers (member : Member) (board : Board) (state : (Mind × Option Bool) × Nat)
    (here : Sound member board state.1.1 state.1.2) (asking : board.asking = true)
    (seen : ∃ earlier, earlier < board.trial ∧ member.cues earlier = member.cues board.trial) :
    ((assembled setting latch).step state ((world member).percept board)).1.action =
        need member board.trial ∧
      ((assembled setting latch).step state ((world member).percept board)).1.forecast =
        echo member board.trial := by
  obtain ⟨⟨mind, held⟩, clock⟩ := state
  obtain ⟨trial, asked, paid, heard⟩ := board
  obtain rfl : asked = true := asking
  obtain ⟨holds, tracks⟩ := here
  obtain ⟨earlier, before, same⟩ := seen
  have held' : held = some (member.cues trial) := holds
  subst held'
  obtain ⟨echoed, payer⟩ := tracks earlier before
  change member.cues earlier = member.cues trial at same
  simp only [need, echo, same] at echoed payer
  simp only [world, setting, base, latch, need, echo, ite_true]
  rw [payer, echoed]
  exact ⟨rfl, rfl⟩

theorem meets : Meets setting (assembled setting latch) task :=
  fun draw member time asking seen =>
    sound_answers member _ _ (sound member draw time) asking seen

theorem baseFails (draw : Bool) : Fails setting setting.base task draw := by
  refine ⟨⟨false, false, fun trial => trial == 1⟩, fun answered => ?_⟩
  have third := (answered 5 rfl ⟨0, Nat.zero_lt_succ 1, rfl⟩).1
  cases draw <;> exact absurd third (by decide)

theorem historyNeeded (draw : Bool) (reply : Nat → Percept → Output) :
    Fails setting (responding setting reply) task draw := by
  refine ⟨⟨!(reply 3 ⟨none, false, false, none⟩).action, false, fun _ => false⟩,
    fun answered => ?_⟩
  have second := (answered 3 rfl ⟨0, Nat.zero_lt_succ 0, rfl⟩).1
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ second

def cuesFor (third : Bool) (trial : Nat) : Bool :=
  if trial = 0 then false else if trial = 1 then true else third

theorem seen_before (third : Bool) :
    ∃ earlier, earlier < 2 ∧ cuesFor third earlier = cuesFor third 2 := by
  cases third
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩

theorem stateNeeded (draw : Bool) (rule : Nat → Percept → Option Bool) :
    Fails setting (fed setting rule) task draw := by
  refine ⟨⟨false, false, cuesFor
    (!(trace setting (fed setting rule) draw (world ⟨false, false, cuesFor false⟩) 5).2.action)⟩,
    fun answered => ?_⟩
  have third := (answered 5 rfl (seen_before _)).1
  have differs : ∀ action : Bool, action ≠ (!action != false) := by decide
  exact differs _ third

theorem controlNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutControl setting latch schedule) task draw := by
  refine ⟨⟨!(schedule 3 (some false)).getD draw, false, fun _ => false⟩, fun answered => ?_⟩
  have second := (answered 3 rfl ⟨0, Nat.zero_lt_succ 0, rfl⟩).1
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ second

theorem predictionNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutPrediction setting latch schedule) task draw := by
  refine ⟨⟨false, !(schedule 3 (some false)).getD false, fun _ => false⟩, fun answered => ?_⟩
  have second := (answered 3 rfl ⟨0, Nat.zero_lt_succ 0, rfl⟩).2
  have differs : ∀ forecast : Bool, forecast ≠ (false != !forecast) := by decide
  exact differs _ second

theorem learningNeeded (draw : Bool) (predictions controls : Nat → Option Bool → Option Bool) :
    Fails setting (withoutLearning setting latch predictions controls) task draw := by
  refine ⟨⟨!(controls 3 (some false)).getD draw, false, fun _ => false⟩, fun answered => ?_⟩
  have second := (answered 3 rfl ⟨0, Nat.zero_lt_succ 0, rfl⟩).1
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ second

theorem inhabited : Result setting latch task :=
  ⟨meets, baseFails, historyNeeded, stateNeeded, predictionNeeded, controlNeeded,
    learningNeeded⟩

end AcornVerif.LearnedState.Small
