/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LearnedStateFrame

/-! # A small agent with a complete result

The frame of `AcornVerif.LearnedState` is not empty: `inhabited` is a complete result of a
small base agent with a state mechanism. It shows that the seven obligations can be met together. It says
nothing of Acorn's agent.

**The worlds.** A world runs in trials of two steps. At the first it shows a cue, one bit. At
the second it shows nothing and asks: the agent emits an action and a forecast, each one bit.
With the next cue the world delivers whether the action paid and an echo. A member of the
family fixes the cue of every trial and two hidden bits: `swap`, which with the cue decides the
action that pays, and `shift`, which with the cue decides the echo.

**The goal.** At every asking step whose cue was the cue of an earlier trial, the action pays
and the forecast is the echo that follows.

**The base agent** has two tables, keyed by what a mechanism hands it with the percept, which
are its two stores. The prediction table keeps the echo that followed each key. The control
table keeps the action that pays after each key, written from whether its own action paid. Both
start empty. Alone, the base agent is handed nothing, so it has one key.

**The mechanism** (`latch`) holds the last cue and hands it to the base agent.

**Why each obligation holds.**
* `meets`: after the feedback of a trial both tables are right at that trial's cue (`Tracks`),
  so a later asking step with that cue is answered right.
* `baseFails`: with cues false, true, false and both hidden bits false, the base agent answers
  the third trial with the action that paid after the second cue.
* `historyNeeded`: asked, a responder with no history sees the same percept whatever the cue
  and the hidden bits are. The hidden bit is chosen against its action.
* `stateNeeded`: a rule of the time and the percept hands the base agent the same key at an
  asking step whatever the trial's cue was. The third cue is chosen against the action it then
  takes.
* `predictionNeeded`, `controlNeeded`, `learningNeeded`: a table fixed in advance holds no
  hidden bit. With all cues false, the hidden bit is chosen against the table's entry.
-/

namespace AcornVerif.LearnedState.Small

/-- What the base agent steps on. -/
structure Percept where
  /-- The cue, at the first step of a trial. -/
  cue : Option Bool
  /-- Whether the action of the preceding trial paid. -/
  paid : Bool
  /-- The echo of the preceding trial. -/
  echo : Bool
  /-- What a state mechanism hands the base agent. A world delivers nothing here. -/
  held : Option Bool

/-- What the agent emits at a step. -/
structure Output where
  /-- The action. -/
  action : Bool
  /-- The forecast of the echo. -/
  forecast : Bool

/-- A member of the family. -/
structure Member where
  /-- With the cue, decides the action that pays. -/
  swap : Bool
  /-- With the cue, decides the echo. -/
  shift : Bool
  /-- The cue of each trial. -/
  cues : Nat → Bool

/-- The action that pays at a trial. -/
def need (member : Member) (trial : Nat) : Bool := member.cues trial != member.swap

/-- The echo of a trial. -/
def echo (member : Member) (trial : Nat) : Bool := member.cues trial != member.shift

/-- The state of a world. -/
structure Board where
  /-- The trial. -/
  trial : Nat
  /-- Whether this is the asking step of the trial. -/
  asking : Bool
  /-- Whether the action of the preceding trial paid. -/
  paid : Bool
  /-- The echo of the preceding trial. -/
  echo : Bool

/-- The world of a member. -/
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

/-- A table with one entry written. -/
def write (table : Option Bool → Option Bool) (key : Option Bool) (value : Bool) :
    Option Bool → Option Bool :=
  fun other => if other = key then some value else table other

/-- What the base agent holds. -/
structure Mind where
  /-- The seed: the action taken when the control table has no entry. -/
  draw : Bool
  /-- The key and the action of the trial whose feedback is due. -/
  pending : Option (Option Bool × Bool)
  /-- The prediction table: the echo that followed each key. -/
  echoes : Option Bool → Option Bool
  /-- The control table: the action that pays after each key. -/
  payers : Option Bool → Option Bool

/-- Both tables are written from the feedback of the pending trial. -/
def Mind.record (mind : Mind) (paid echo : Bool) : Mind :=
  match mind.pending with
  | some (key, action) =>
    { mind with
      pending := none
      echoes := write mind.echoes key echo
      payers := write mind.payers key (if paid then action else !action) }
  | none => mind

/-- The base agent. With a cue it records the feedback. Asked, it emits the control table's
action at the key it is handed, or the seed's, and the prediction table's forecast, or false. -/
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

/-- The setting: the seed is the first action, a mechanism hands the base agent a key, and the
two stores are the two tables. -/
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

/-- The mechanism: it holds the last cue and hands it to the base agent. -/
def latch : Mechanism setting where
  Memory := Option Bool
  cold _ := none
  read held percept :=
    match percept.cue with
    | some cue => (some cue, some cue)
    | none => (held, held)
  note held _ := held

/-- The goal over a member's cues and hidden bits, on a trace of boards and outputs. -/
def Answered (member : Member) (trace : Nat → Board × Output) : Prop :=
  ∀ time, (trace time).1.asking = true →
    (∃ earlier, earlier < (trace time).1.trial ∧
      member.cues earlier = member.cues (trace time).1.trial) →
    (trace time).2.action = need member (trace time).1.trial ∧
      (trace time).2.forecast = echo member (trace time).1.trial

/-- A member is determined by its world: the world shows the cues, pays by `swap` and echoes by
`shift`. -/
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

/-- The task: every member, and the goal. -/
def task : Task setting where
  Family := Member
  world := world
  goal := Answered
  sameWorld := sameWorld_of_injective (S := setting) world Answered world_injective

/-! ## The assembled agent meets the goal -/

/-- Both tables are right at the cue of every trial before `count`. -/
def Tracks (member : Member) (mind : Mind) (count : Nat) : Prop :=
  ∀ trial, trial < count →
    mind.echoes (some (member.cues trial)) = some (echo member trial) ∧
      mind.payers (some (member.cues trial)) = some (need member trial)

/-- What holds of the board, the mind and the latch before each step: asked, the latch holds
the trial's cue and the mind tracks every earlier trial; shown a cue, the mind tracks every
earlier trial once it has recorded the feedback shown. -/
def Sound (member : Member) (board : Board) (mind : Mind) (held : Option Bool) : Prop :=
  if board.asking then held = some (member.cues board.trial) ∧ Tracks member mind board.trial
  else Tracks member (mind.record board.paid board.echo) board.trial

/-- The entry written from whether an action paid is the action that pays. -/
theorem written_payer (action wanted : Bool) :
    (if action == wanted then action else !action) = wanted := by
  cases action <;> cases wanted <;> rfl

/-- One step keeps soundness. -/
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

/-- Soundness holds along every run of the assembled agent. -/
theorem sound (member : Member) (draw : Bool) (time : Nat) :
    Sound member (run setting (assembled setting latch) draw (world member) time).1
      (run setting (assembled setting latch) draw (world member) time).2.1.1
      (run setting (assembled setting latch) draw (world member) time).2.1.2 := by
  induction time with
  | zero => intro trial before; cases before
  | succ time ih => exact sound_step member _ _ ih

/-- Asked at a sound board, mind and latch, about a cue of an earlier trial, the assembled
agent answers right. -/
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

/-- **The assembled agent meets the goal** from its cold construction, at every seed, in every
member. -/
theorem meets : Meets setting (assembled setting latch) task :=
  fun draw member time asking seen =>
    sound_answers member _ _ (sound member draw time) asking seen

/-! ## The base agent fails it, and so does the base agent fed by a rule -/

/-- **The base agent fails the goal** at every seed. -/
theorem baseFails (draw : Bool) : Fails setting setting.base task draw := by
  refine ⟨⟨false, false, fun trial => trial == 1⟩, fun answered => ?_⟩
  have third := (answered 5 rfl ⟨0, Nat.zero_lt_succ 1, rfl⟩).1
  cases draw <;> exact absurd third (by decide)

/-- **The task needs the past.** Every responder with no history fails: asked, it sees the same
percept whatever the cue was, and the hidden bit is chosen against its action. -/
theorem historyNeeded (draw : Bool) (reply : Nat → Percept → Output) :
    Fails setting (responding setting reply) task draw := by
  refine ⟨⟨!(reply 3 ⟨none, false, false, none⟩).action, false, fun _ => false⟩,
    fun answered => ?_⟩
  have second := (answered 3 rfl ⟨0, Nat.zero_lt_succ 0, rfl⟩).1
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ second

/-- Cues false, true, and then a chosen third cue. -/
def cuesFor (third : Bool) (trial : Nat) : Bool :=
  if trial = 0 then false else if trial = 1 then true else third

/-- Whatever the third cue is, it is the cue of an earlier trial. -/
theorem seen_before (third : Bool) :
    ∃ earlier, earlier < 2 ∧ cuesFor third earlier = cuesFor third 2 := by
  cases third
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩

/-- **State is needed.** The base agent fed by any rule of the time and the percept fails, at
every seed: at an asking step the rule sees the same percept whatever the trial's cue was. -/
theorem stateNeeded (draw : Bool) (rule : Nat → Percept → Option Bool) :
    Fails setting (fed setting rule) task draw := by
  refine ⟨⟨false, false, cuesFor
    (!(trace setting (fed setting rule) draw (world ⟨false, false, cuesFor false⟩) 5).2.action)⟩,
    fun answered => ?_⟩
  have third := (answered 5 rfl (seen_before _)).1
  have differs : ∀ action : Bool, action ≠ (!action != false) := by decide
  exact differs _ third

/-! ## The two stores are needed -/

/-- **The control store is needed.** -/
theorem controlNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutControl setting latch schedule) task draw := by
  refine ⟨⟨!(schedule 3 (some false)).getD draw, false, fun _ => false⟩, fun answered => ?_⟩
  have second := (answered 3 rfl ⟨0, Nat.zero_lt_succ 0, rfl⟩).1
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ second

/-- **The prediction store is needed.** -/
theorem predictionNeeded (draw : Bool) (schedule : Nat → Option Bool → Option Bool) :
    Fails setting (withoutPrediction setting latch schedule) task draw := by
  refine ⟨⟨false, !(schedule 3 (some false)).getD false, fun _ => false⟩, fun answered => ?_⟩
  have second := (answered 3 rfl ⟨0, Nat.zero_lt_succ 0, rfl⟩).2
  have differs : ∀ forecast : Bool, forecast ≠ (false != !forecast) := by decide
  exact differs _ second

/-- **Both stores together are needed.** With both on schedules the agent fails. -/
theorem learningNeeded (draw : Bool) (predictions controls : Nat → Option Bool → Option Bool) :
    Fails setting (withoutLearning setting latch predictions controls) task draw := by
  refine ⟨⟨!(controls 3 (some false)).getD draw, false, fun _ => false⟩, fun answered => ?_⟩
  have second := (answered 3 rfl ⟨0, Nat.zero_lt_succ 0, rfl⟩).1
  have differs : ∀ action : Bool, action ≠ (false != !action) := by decide
  exact differs _ second

/-- **The frame is inhabited.** -/
theorem inhabited : Result setting latch task :=
  ⟨meets, baseFails, historyNeeded, stateNeeded, predictionNeeded, controlNeeded,
    learningNeeded⟩

end AcornVerif.LearnedState.Small
