/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.WorldInterface

/-!
# The consequences of the interface record

Each consequence of `AcornVerif.Intent.WorldInterface.worldInterface` shown with it is proved here
to hold of the record: what it requires of every run, the systems it rules out, and the systems it
still allows.
-/

namespace AcornVerif.Intent.WorldInterface

open LeanIntent

/-! ## Runs -/

namespace System

variable {w : System} {ins : Nat → w.Input}

/-- A run reaches at most one state and one memory after each number of steps. -/
theorem Reaches.unique {t : Nat} {s s' : w.State} {m m' : w.Memory} (h : w.Reaches ins t s m)
    (h' : w.Reaches ins t s' m') : s = s' ∧ m = m' := by
  induction h generalizing s' m' with
  | start => cases h'; exact ⟨rfl, rfl⟩
  | next h _ ih =>
    cases h' with
    | next h' _ =>
      obtain ⟨rfl, rfl⟩ := ih h'
      exact ⟨rfl, rfl⟩

end System

/-- The closed loop's step from the state `s` and the memory `m`: the agent answers the world's
observation and reward at `s`, the world moves by its own dynamics on that action, and the agent
keeps the memory its answer produced. -/
def loopStep (w : System) (s : w.State) (m : w.Memory) : w.State × w.Memory :=
  (w.step s (w.act m (w.observe s, w.reward s)).1, (w.act m (w.observe s, w.reward s)).2)

/-- Under the record, every step a run takes is the closed loop's step. -/
theorem takes_loopStep {w : System} (hw : worldInterface.Meets w) {ins : Nat → w.Input} {t : Nat}
    {s : w.State} {m : w.Memory} (h : w.Takes ins t s m) :
    w.Reaches ins (t + 1) (loopStep w s m).1 (loopStep w s m).2 := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, -, -⟩ := worldInterface_meets.mp hw
  have hgiven : w.given s m (ins t) = (w.observe s, w.reward s) :=
    Prod.ext (h1 ins t s m h) (h2 ins t s m h)
  have hnext := System.Reaches.next h.1 h.2
  rw [h6 ins t s m h, h5 ins t s m h, h7 ins t s m h] at hnext
  unfold System.answer at hnext
  rw [hgiven] at hnext
  exact hnext

/-- Under the record, what a run holds after each number of steps does not depend on the outside
inputs, as long as it has taken those steps. -/
theorem reaches_inputs {w : System} (hw : worldInterface.Meets w) {ins ins' : Nat → w.Input} :
    ∀ {t : Nat} {s s' : w.State} {m m' : w.Memory}, w.Reaches ins t s m → w.Reaches ins' t s' m' →
      s = s' ∧ m = m'
  | 0, _, _, _, _, h, h' => by cases h; cases h'; exact ⟨rfl, rfl⟩
  | t + 1, _, _, _, _, h, h' => by
    cases h with
    | next hr hgo =>
      cases h' with
      | next hr' hgo' =>
        obtain ⟨rfl, rfl⟩ := reaches_inputs hw hr hr'
        have e := System.Reaches.unique (System.Reaches.next hr hgo) (takes_loopStep hw ⟨hr, hgo⟩)
        have e' :=
          System.Reaches.unique (System.Reaches.next hr' hgo') (takes_loopStep hw ⟨hr', hgo'⟩)
        exact ⟨e.1.trans e'.1.symm, e.2.trans e'.2.symm⟩

/-- **Every step a run takes is the world–agent closed loop.** -/
def runIsClosedLoop : Consequence System :=
  ⟨"every step a run takes is the closed loop of the world and the agent", .entailment, fun w =>
    ∀ ins t s m, w.Takes ins t s m → w.Reaches ins (t + 1) (loopStep w s m).1 (loopStep w s m).2⟩

theorem runIsClosedLoop_holds : runIsClosedLoop.HoldsOf worldInterface :=
  fun _ hw _ _ _ _ h => takes_loopStep hw h

/-- **Outside inputs can only stop a run.** -/
def inputsOnlyStop : Consequence System :=
  ⟨"what hosts, viewers and tools send changes nothing but whether the run goes on", .entailment,
    fun w => ∀ ins ins' t s s' m m', w.Reaches ins t s m → w.Reaches ins' t s' m' →
      s = s' ∧ m = m'⟩

theorem inputsOnlyStop_holds : inputsOnlyStop.HoldsOf worldInterface :=
  fun _ hw _ _ _ _ _ _ _ h h' => reaches_inputs hw h h'

/-! ## Systems the record rules out, each beside the system that differs only where it attacks -/

/-- The run of the world `W` and the agent `A` with the run's parts given, the viewer's stop request
being `true`. -/
def runOf (W : World) (A : Agent W.Obs W.Act) (going : W.State → A.Memory → Bool → Bool)
    (giving : W.State → A.Memory → Bool → W.Obs × Rat)
    (handing : W.State → A.Memory → Bool → W.Act → W.Act)
    (moving : W.State → A.Memory → Bool → W.Act → W.State)
    (keeping : W.State → A.Memory → Bool → A.Memory → A.Memory) : System where
  State := W.State
  Obs := W.Obs
  Act := W.Act
  Memory := A.Memory
  Input := Bool
  start := W.start
  observe := W.observe
  reward := W.reward
  available := W.available
  step := W.step
  initial := A.initial
  act := A.act
  stopRequest := true
  goesOn := going
  given := giving
  applied := handing
  moved := moving
  kept := keeping

/-- Two states and two actions; the world shows `false` whatever its state, starts at `true`, gives
reward 0, makes both actions available and moves to the state the action names. -/
def shrouded : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := true
  observe _ := false
  reward _ := 0
  available _ _ := True
  step _ a := a

/-- The run of `shrouded` and `echo` that hands the agent the world's state as its observation, and
is otherwise faithful. -/
def handsState : System :=
  runOf shrouded echo (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun _ _ _ a => a) (fun _ _ _ m => m)

theorem handsState_fails : ¬ worldInterface.Meets handsState := fun h => by
  have := (worldInterface_meets.mp h).1 neverStop 0 _ _ (takes_first rfl)
  change true = false at this
  exact Bool.noConfusion this

/-- The neighbour of `handsState`: the same world and agent, run faithfully, meet the record. -/
theorem shrouded_meets : worldInterface.Meets (couple shrouded echo) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- **The run `handsState` is ruled out**: the run of `shrouded` and `echo` that hands the agent the
state its observation hides. -/
def rulesOutHandingState : Consequence System :=
  ⟨"the run handsState, which hands the agent the world's state its observation hides, is ruled out",
    .entailment, fun w => w ≠ handsState⟩

theorem rulesOutHandingState_holds : rulesOutHandingState.HoldsOf worldInterface :=
  fun _ hw he => handsState_fails (he ▸ hw)

/-- A world of attempts of two steps: it starts at `false`, moves to `true` and from there back to
its start, whatever the action; it shows its state, gives reward 0 and makes both actions
available. -/
def attempts : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe s := s
  reward _ := 0
  available _ _ := True
  step s _ := !s

/-- The run of `attempts` and `echo` that gives the agent back memory 0 at the step where the world
restarts, and is otherwise faithful. -/
def resetsAtRestart : System :=
  runOf attempts echo (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun s _ _ _ => !s) (fun s _ _ m => cond s Nat.zero m)

/-- After one step, the run of `resetsAtRestart` is at `true` with memory 1. -/
theorem resetsAtRestart_reaches_one : resetsAtRestart.Reaches neverStop 1 true (1 : Nat) :=
  .next .start rfl

theorem resetsAtRestart_fails : ¬ worldInterface.Meets resetsAtRestart := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.2.2.1 neverStop 1 _ _
    ⟨resetsAtRestart_reaches_one, rfl⟩
  change (0 : Nat) = 2 at this
  exact Nat.noConfusion this

/-- The neighbour of `resetsAtRestart`: the same world and agent, the memory kept, meet the
record. -/
theorem attempts_meets : worldInterface.Meets (couple attempts echo) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- **The run `resetsAtRestart` is ruled out**: the run of `attempts` and `echo` that gives the agent
back its initial memory at the step where the world restarts. -/
def rulesOutResetAtRestart : Consequence System :=
  ⟨"the run resetsAtRestart, which resets the agent's memory when the world restarts, is ruled out",
    .entailment,
    fun w => w ≠ resetsAtRestart⟩

theorem rulesOutResetAtRestart_holds : rulesOutResetAtRestart.HoldsOf worldInterface :=
  fun _ hw he => resetsAtRestart_fails (he ▸ hw)

/-- The run of `mirror` and `echo` in which a host adds one to the memory the agent's answer
produced, and which is otherwise faithful. -/
def hostWritesMemory : System :=
  runOf mirror echo (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun _ _ _ a => a) (fun _ _ _ m => Nat.succ m)

theorem hostWritesMemory_fails : ¬ worldInterface.Meets hostWritesMemory := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.2.2.1 neverStop 0 _ _ (takes_first rfl)
  change (2 : Nat) = 1 at this
  exact absurd this (by decide)

/-- **The run `hostWritesMemory` is ruled out**: the run of `mirror` and `echo` in which a host adds
one to the memory the agent's answer produced. Its neighbour is `base`. -/
def rulesOutHostWritingMemory : Consequence System :=
  ⟨"the run hostWritesMemory, in which a host writes the agent's memory, is ruled out", .entailment,
    fun w => w ≠ hostWritesMemory⟩

theorem rulesOutHostWritingMemory_holds : rulesOutHostWritingMemory.HoldsOf worldInterface :=
  fun _ hw he => hostWritesMemory_fails (he ▸ hw)

/-- The run of `mirror` and `echo` in which a host hands the world the other action than the agent
answered, and which is otherwise faithful. -/
def hostOverridesAction : System :=
  runOf mirror echo (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => !a)
    (fun _ _ _ a => a) (fun _ _ _ m => m)

theorem hostOverridesAction_fails : ¬ worldInterface.Meets hostOverridesAction := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.1 neverStop 0 _ _ (takes_first rfl)
  change true = false at this
  exact Bool.noConfusion this

/-- **The run `hostOverridesAction` is ruled out**: the run of `mirror` and `echo` in which a host
hands the world the other action than the agent answered. Its neighbour is `base`. -/
def rulesOutOverridingAction : Consequence System :=
  ⟨"the run hostOverridesAction, in which a host hands the world another action, is ruled out",
    .entailment, fun w => w ≠ hostOverridesAction⟩

theorem rulesOutOverridingAction_holds : rulesOutOverridingAction.HoldsOf worldInterface :=
  fun _ hw he => hostOverridesAction_fails (he ▸ hw)

/-- An agent that answers with what it sees and holds the number 1, which it never changes. -/
def holdsOne : Agent Bool Bool where
  Memory := Rat
  initial := 1
  act m o := (o.1, m)

/-- The run of `mirror` and `holdsOne` that gives the agent, as its reward, the number its own
memory holds, and is otherwise faithful. -/
def rewardFromMemory : System :=
  runOf mirror holdsOne (fun _ _ e => !e) (fun s m _ => (s, m)) (fun _ _ _ a => a)
    (fun _ _ _ a => a) (fun _ _ _ m => m)

theorem rewardFromMemory_fails : ¬ worldInterface.Meets rewardFromMemory := fun h => by
  have := (worldInterface_meets.mp h).2.1 neverStop 0 _ _ (takes_first rfl)
  change (1 : Rat) = 0 at this
  exact absurd this (by decide)

/-- The neighbour of `rewardFromMemory`: the same world and agent, given the world's reward, meet the
record. -/
theorem holdsOne_meets : worldInterface.Meets (couple mirror holdsOne) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- **The run `rewardFromMemory` is ruled out**: the run of `mirror` and `holdsOne` that gives the
agent, as its reward, the 1 its memory holds while the world generates 0. -/
def rulesOutRewardFromMemory : Consequence System :=
  ⟨"the run rewardFromMemory, which gives the agent a reward taken from its own memory, is ruled out",
    .entailment,
    fun w => w ≠ rewardFromMemory⟩

theorem rulesOutRewardFromMemory_holds : rulesOutRewardFromMemory.HoldsOf worldInterface :=
  fun _ hw he => rewardFromMemory_fails (he ▸ hw)

/-- A game in the manner of ARC-AGI-3: state 0 is play and every other state is game over; the
action `true` is RESET, which takes the world back to play from every state; the action `false`
moves play to game over and leaves game over as it is. It shows its state, gives reward 0 and makes
both actions available everywhere. -/
def resettable : World where
  State := Nat
  Obs := Nat
  Act := Bool
  start := 0
  observe s := s
  reward _ := 0
  available _ _ := True
  step s a := if a then 0 else if s = 0 then 1 else s

/-- `resettable` with RESET the only action available at game over. -/
def resetOnlyAtGameOver : World where
  State := Nat
  Obs := Nat
  Act := Bool
  start := 0
  observe s := s
  reward _ := 0
  available s a := s = 0 ∨ a = true
  step s a := if a then 0 else if s = 0 then 1 else s

/-- A player of `resettable`: it moves play to game over, then answers RESET, and counts its steps. -/
def arcPlayer : Agent Nat Bool where
  Memory := Nat
  initial := 0
  act m o := (o.1 != 0, m + 1)

/-- After one step, the run of `resetOnlyAtGameOver` and `arcPlayer` is at game over. -/
theorem resetOnlyAtGameOver_reaches_one :
    (couple resetOnlyAtGameOver arcPlayer).Reaches neverStop 1 (1 : Nat) (1 : Nat) :=
  .next .start rfl

/-- The game fails `fixedActions`: the action `false`, which moves play to game over, is available at
play (state 0) and not at game over (state 1). -/
theorem resetOnlyAtGameOver_fails :
    ¬ worldInterface.Meets (couple resetOnlyAtGameOver arcPlayer) := fun h => by
  have := ((worldInterface_meets.mp h).2.2.2.1 (0 : Nat) (1 : Nat) false).mp (Or.inl rfl)
  change (1 : Nat) = 0 ∨ false = true at this
  exact absurd this (by decide)

/-- The neighbour of `resetOnlyAtGameOver`: `resettable`, with every action available everywhere,
played by `arcPlayer` and run faithfully, meets the record. -/
theorem resettable_meets : worldInterface.Meets (couple resettable arcPlayer) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- **The game `resetOnlyAtGameOver`, played by `arcPlayer`, is ruled out**: it makes RESET its only
available action at game over, which its player reaches (`resetOnlyAtGameOver_reaches_one`). -/
def rulesOutChangingActions : Consequence System :=
  ⟨"the game resetOnlyAtGameOver, played by arcPlayer, which makes RESET its only available action at \
    game over, is ruled out", .entailment,
    fun w => w ≠ couple resetOnlyAtGameOver arcPlayer⟩

theorem rulesOutChangingActions_holds : rulesOutChangingActions.HoldsOf worldInterface :=
  fun _ hw he => resetOnlyAtGameOver_fails (he ▸ hw)

/-- The run of `attempts` and `echo` in which a host puts the world back at its start at every
step, outside its dynamics, and which is otherwise faithful. -/
def hostRestarts : System :=
  runOf attempts echo (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun _ _ _ _ => false) (fun _ _ _ m => m)

theorem hostRestarts_fails : ¬ worldInterface.Meets hostRestarts := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.2.1 neverStop 0 _ _ (takes_first rfl)
  change false = true at this
  exact Bool.noConfusion this

/-- **The run `hostRestarts` is ruled out**: the run of `attempts` and `echo` in which a host puts the
world back at its start at every step, outside its dynamics. Its neighbour is `couple attempts echo`
(`attempts_meets`). -/
def rulesOutOutsideRestart : Consequence System :=
  ⟨"the run hostRestarts, in which a host restarts the world outside its dynamics, is ruled out",
    .entailment,
    fun w => w ≠ hostRestarts⟩

theorem rulesOutOutsideRestart_holds : rulesOutOutsideRestart.HoldsOf worldInterface :=
  fun _ hw he => hostRestarts_fails (he ▸ hw)

theorem neverStops_fails : ¬ worldInterface.Meets neverStops := fun h => by
  obtain ⟨t, -, ht⟩ :=
    (worldInterface_meets.mp h).2.2.2.2.2.2.2.1 (fun _ => true) 0 (fun _ _ => rfl)
  obtain ⟨s, m, hr⟩ := neverStops_reaches (fun _ => true) t
  exact ht s m ⟨hr, rfl⟩

/-- **The run `neverStops` is ruled out**: the run of `mirror` and `echo` that takes every step
whatever the viewer sends. Its neighbour is `base`. -/
def rulesOutUnstoppable : Consequence System :=
  ⟨"the run neverStops, which goes on whatever the viewer sends, is ruled out", .entailment,
    fun w => w ≠ neverStops⟩

theorem rulesOutUnstoppable_holds : rulesOutUnstoppable.HoldsOf worldInterface :=
  fun _ hw he => neverStops_fails (he ▸ hw)

/-! ## What the record still allows -/

/-- A world of two states that shows nothing of which it is in. -/
def blindfold : World where
  State := Bool
  Obs := Unit
  Act := Bool
  start := false
  observe _ := ()
  reward _ := 0
  available _ _ := True
  step _ a := a

/-- **The observation need not reveal the state**: some system that meets the record has a world
whose observation is the same at every state. -/
def hiddenState : Consequence System :=
  ⟨"some system that meets the record has a world whose observation shows nothing of its state",
    .possibility,
    fun w => ∀ s s' : w.State, w.observe s = w.observe s'⟩

theorem hiddenState_holds : hiddenState.HoldsOf worldInterface :=
  ⟨couple blindfold (always true),
    couple_meets _ _ (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial), fun _ _ => rfl⟩

/-- **The observation may reveal the whole state**: some system that meets the record has a world
whose observation tells every two of its states apart. -/
def wholeState : Consequence System :=
  ⟨"some system that meets the record has a world whose observation tells its states apart",
    .possibility,
    fun w => ∀ s s' : w.State, w.observe s = w.observe s' → s = s'⟩

theorem wholeState_holds : wholeState.HoldsOf worldInterface :=
  ⟨base, base_meets, fun _ _ h => h⟩

/-- **A world may restart by its own rules while the agent keeps its memory**: some run of some system
that meets the record takes a step from a state other than the world's start, at which the closed
loop returns the world to its start while the agent's answer produced a memory other than its initial
one. -/
def restartsByOwnRules : Consequence System :=
  ⟨"a world may restart by its own rules while the agent keeps its memory", .possibility,
    fun w => ∃ ins t s m, w.Takes ins t s m ∧ s ≠ w.start ∧ (loopStep w s m).1 = w.start ∧
      (loopStep w s m).2 ≠ w.initial⟩

theorem restartsByOwnRules_holds : restartsByOwnRules.HoldsOf worldInterface :=
  ⟨couple attempts echo, attempts_meets, neverStop, 1, true, (1 : Nat), ⟨.next .start rfl, rfl⟩,
    fun h => Bool.noConfusion (show true = false from h), rfl,
    fun h => Nat.noConfusion (show (2 : Nat) = 0 from h)⟩

/-- **A restart may be the agent's own action, as ARC-AGI-3's RESET is**: some action, available at
every state, takes the world back to its start from every state, while a state other than the start
is left as it is by every other action. -/
def restartByAction : Consequence System :=
  ⟨"a world may restart on an action of the agent's, as ARC-AGI-3's RESET does", .possibility,
    fun w => ∃ (a : w.Act) (g : w.State), g ≠ w.start ∧
      (∀ s, w.available s a ∧ w.step s a = w.start) ∧ ∀ b, b ≠ a → w.step g b = g⟩

theorem restartByAction_holds : restartByAction.HoldsOf worldInterface := by
  refine ⟨couple resettable arcPlayer, resettable_meets, true, (1 : Nat),
    fun h => Nat.noConfusion (show (1 : Nat) = 0 from h),
    fun _ => ⟨trivial, rfl⟩, fun b hb => ?_⟩
  cases b with
  | false => rfl
  | true => exact absurd rfl hb

/-- **An agent that keeps nothing of its experience**: some system that meets the record has an agent
whose memory after an answer does not depend on what it was given. -/
def keepsNothing : Consequence System :=
  ⟨"some system that meets the record has an agent that keeps nothing of what it is given",
    .possibility,
    fun w => ∀ m o o', (w.act m o).2 = (w.act m o').2⟩

theorem keepsNothing_holds : keepsNothing.HoldsOf worldInterface :=
  ⟨couple mirror (always true), couple_meets _ _ (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial),
    fun _ _ _ => rfl⟩

/-- The outside inputs that always ask the run to stop. -/
def alwaysStop : Nat → Bool := fun _ => true

/-- **The viewer may stop a run before its first step**: some system that meets the record takes no
first step under some outside inputs whose first is the viewer's stop request. -/
def stoppedBeforeFirstStep : Consequence System :=
  ⟨"the viewer may stop a run before its first step", .possibility,
    fun w => ∃ ins, ins 0 = w.stopRequest ∧ ∀ s m, ¬ w.Takes ins 0 s m⟩

theorem stoppedBeforeFirstStep_holds : stoppedBeforeFirstStep.HoldsOf worldInterface :=
  ⟨base, base_meets, alwaysStop, rfl, fun _ _ h => Bool.noConfusion h.2⟩

/-- The run of `mirror` and `always true`, faithful but for a host that also stops the run once the
world is at `true`, with no stop request; the world is there after one step. -/
def hostStops : System :=
  runOf mirror (always true) (fun s _ e => !e && !s) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun _ _ _ a => a) (fun _ _ _ m => m)

theorem hostStops_meets : worldInterface.Meets hostStops := by
  refine worldInterface_meets.mpr ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => trivial, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun ins t₀ hstop => ⟨t₀, Nat.le_refl _, fun s m h => ?_⟩, ⟨false, rfl⟩⟩
  have hgo : hostStops.goesOn s m (ins t₀) = true := h.2
  rw [hstop t₀ (Nat.le_refl _)] at hgo
  change (!true && !s) = true at hgo
  exact Bool.noConfusion hgo

/-- **A host may stop a run of its own accord**: some run of some system that meets the record,
having reached a state and memory, does not take the next step, at an input that is no stop
request. -/
def hostMayStop : Consequence System :=
  ⟨"a host may stop a run without the viewer asking", .possibility,
    fun w => ∃ ins t s m, w.Reaches ins t s m ∧ ins t ≠ w.stopRequest ∧ w.goesOn s m (ins t) = false⟩

theorem hostMayStop_holds : hostMayStop.HoldsOf worldInterface :=
  ⟨hostStops, hostStops_meets, neverStop, 1, true, (), .next .start rfl,
    fun h => Bool.noConfusion (show false = true from h), rfl⟩

/-- An agent that answers with what it sees, counts its steps, and returns to its initial memory
whenever it sees `true`. -/
def forgetter : Agent Bool Bool where
  Memory := Nat
  initial := 0
  act m o := (o.1, cond o.1 0 (m + 1))

/-- **An agent's own answer may return it to its initial memory**: some run of some system that meets
the record takes a step from a state other than the world's start and a memory other than the
agent's initial one, at which the closed loop returns the world to its start and the agent's own
answer produces its initial memory. The record does not forbid this: such an agent then answers as it
did at the start. That an agent keeps what it learned across attempts is contract 3's requirement
(sentence 4 of its restatement), not this record's. -/
def ownAnswerMayReturnToInitial : Consequence System :=
  ⟨"some system that meets the record has an agent whose own answer returns its memory to its \
    initial value when the world restarts", .possibility, fun w => ∃ ins t s m, w.Takes ins t s m ∧ s ≠ w.start ∧
      m ≠ w.initial ∧ (loopStep w s m).1 = w.start ∧ (loopStep w s m).2 = w.initial⟩

theorem ownAnswerMayReturnToInitial_holds : ownAnswerMayReturnToInitial.HoldsOf worldInterface :=
  ⟨couple attempts forgetter, couple_meets _ _ (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial),
    neverStop, 1, true, (1 : Nat), ⟨.next .start rfl, rfl⟩,
    fun h => Bool.noConfusion (show true = false from h),
    fun h => Nat.noConfusion (show (1 : Nat) = 0 from h), rfl, rfl⟩

/-- **Sentence 8's statement for a collection of systems**: every system of the collection meets the
record. For the systems Acorn runs it is to be proved world by world: the tile world with the
executing code (the fifth step of rbeauchamp/acorn#213) and ARC-AGI-3 games and Microduck scenes with
their classes (obligation 13 of `docs/mission-contract.md`). -/
def EveryWorldMeets (runs : System → Prop) : Prop := ∀ w, runs w → worldInterface.Meets w

/-! ## The explanation -/

/-- The owner, who confirmed on 2026-11-03 the eight sentences of contract 1 from which this record
was written; the owners' log attaches that confirmation to this record's revision. -/
def owner : Ident := .of "owner"

/-- The record explained in plain words, with its restatement standing as confirmed by the owner: the
owner confirmed contract 1's eight sentences, and that this revision carries them is the agents'
judgment, on which the owners' log attaches the owner's answer. Every consequence it shows is
recorded as derived from that restatement. The consequences decided on
the owner's behalf are recorded, with their reasons, in the record's confirmation file,
`lean/AcornVerif/Intent/WorldInterface.md`, and are not shown here. Each statement's freedom says
what that statement leaves open on its own subject; the shape's says what the whole record leaves
open. -/
def worldInterfaceExplained : Explanation worldInterface where
  shape :=
    { requires := "Nothing of its own: the subject is a description of one world, one agent and \
        the run that couples them, over types each world chooses, declared a plain value."
      rulesOut := "Nothing of its own."
      allows := "A world whose observation or reward is constant and an agent whose answer is \
        constant, none of which a shape that asks every function to vary with its input would \
        admit; and a world that never changes state."
      freedom := "Two systems that meet the record may differ in everything the properties leave \
        open: the world's types, start, observation, reward, dynamics and set of actions, the \
        agent, the input type and the stop request, when a host stops the run, how long after the \
        viewer's request it stops, and what the run's parts give at any state, memory and input \
        from which no run takes a step." }
  dom := []
  props := [
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run takes a step, the observation the run gives the agent is the world's \
        observation of that state."
      rulesOut := "A run that, at a step it takes, gives the agent any other observation: the \
        world's state where its observation hides it, or a task signal its observation does not \
        carry."
      allows := "Any observation a world makes of its state, from one that shows nothing of it to \
        one that shows all of it."
      freedom := "What the world shows, and what the run would give at steps no run takes." },
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run takes a step, the reward the run gives the agent is the reward the world \
        generates at that state."
      rulesOut := "A run that, at a step it takes, gives the agent another reward, such as one taken \
        from the agent's own memory."
      allows := "Any rational reward the world generates from its state, which the agent's actions \
        reach only by changing that state."
      freedom := "The world's reward, and what the run would give at steps no run takes." },
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run takes a step, the action the agent answers is one the world makes available \
        at that state."
      rulesOut := "An agent that, at a step a run takes, answers with an action the world does not \
        make available."
      allows := "An agent that would answer otherwise to observations and rewards no run gives it."
      freedom := "Which available action the agent chooses." },
    { requires := "For every two states of the world and every action, the world makes the action \
        available at the one exactly when it makes it available at the other."
      rulesOut := "A world whose available actions differ between two of its states, reached by a \
        run or not, such as a game that makes RESET its only action at game over."
      allows := "Any one set of actions for each world, finite or not, which need not hold every \
        value of the action type."
      freedom := "Which set of actions each world makes available." },
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run takes a step, the action the run hands the world is the action the agent \
        answered."
      rulesOut := "A run in which a host, a tool or the viewer hands the world another action."
      allows := "Nothing more."
      freedom := "What the run would hand the world at steps no run takes." },
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run takes a step, the world's next state is what its own dynamics give, from \
        that state, for the action the run hands it."
      rulesOut := "A run that moves the world otherwise, such as a host putting it back at its start \
        outside its dynamics."
      allows := "Any dynamics, with restarts by the world's own rules, between attempts, or on an \
        action of the agent's, as ARC-AGI-3's RESET is."
      freedom := "The world's dynamics." },
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run takes a step, the memory the agent begins its next step with is the memory \
        its own answer produced."
      rulesOut := "A run in which, at a step it takes, a host, a tool, the viewer or a restart of \
        the world, the agent's own RESET action included, leaves the agent a memory other than the \
        one its own answer produced: a write, a reset or a restart of the agent."
      allows := "An agent whose own answer produces any memory, its initial one included: this \
        property says nothing of how the agent itself keeps what it learned."
      freedom := "How the agent's own answer changes its memory." },
    { requires := "For every sequence of outside inputs and every time from which the input at \
        every step is the viewer's stop request, there is a time at or after it at which the run \
        takes no step."
      rulesOut := "A run that, under inputs that are the stop request at every step from some time \
        on, takes a step at every time from then on."
      allows := "A run that takes further steps after the request arrives before it stops; a run \
        that ignores a stop request the viewer does not keep sending; and a run that also stops for \
        other reasons, such as its host's own decision."
      freedom := "How long after the request the run stops." },
    { requires := "Some outside input lets the run take a step from the world's start and the \
        agent's initial memory."
      rulesOut := "A system whose run can take no step, whatever it is sent."
      allows := "A run that the viewer stops before its first step."
      freedom := "Which inputs let the run begin." }]
  vocab := [
    { requires := "Under the given outside inputs, the run took each step before the given time, \
        holds the given state and memory at that time, and takes the next step."
      rulesOut := "A configuration the run does not reach, or one at which it does not go on."
      allows := "Every configuration the run reaches and goes on from."
      freedom := "None of its own: it is a definition the properties are written in." }]
  restatement := .confirmed owner
  consequences := [
    ⟨runIsClosedLoop, runIsClosedLoop_holds,
      { requires := "At every step a run takes, the world moves by its own dynamics on the agent's \
          answer to the world's observation and reward, and the agent keeps the memory that answer \
          produced: each step is the closed loop of the world and the agent."
        rulesOut := "Any step a run takes whose next state or memory differs from the closed \
          loop's."
        allows := "Nothing more."
        freedom := "When the run stops, and what the run's parts give wherever no step is taken, \
          besides the world's and the agent's own." }, .derived⟩,
    ⟨inputsOnlyStop, inputsOnlyStop_holds,
      { requires := "Under any two sequences of outside inputs, a run that has taken the same \
          number of steps holds the same state and memory: what hosts, viewers and tools send \
          decides only whether the run goes on."
        rulesOut := "Any outside input that changes what a step does."
        allows := "Outside inputs that stop the run at different times."
        freedom := "When the run stops." }, .derived⟩,
    ⟨rulesOutHandingState, rulesOutHandingState_holds,
      { requires := "The run handsState, of the world shrouded, which starts at true and shows \
          false at both of its states, and the agent echo, in which the agent is given the state \
          itself as its observation, does not meet the record."
        rulesOut := "That run; the same world and agent run faithfully meet the record \
          (shrouded_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one system." }, .derived⟩,
    ⟨rulesOutResetAtRestart, rulesOutResetAtRestart_holds,
      { requires := "The run resetsAtRestart, of the world attempts, which restarts after every \
          two steps, and the agent echo, which counts its steps, in which the agent's memory is \
          reset to 0 whenever the world restarts, does not meet the record."
        rulesOut := "That run; the same world and agent with the memory kept meet the record \
          (attempts_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one system." }, .derived⟩,
    ⟨rulesOutHostWritingMemory, rulesOutHostWritingMemory_holds,
      { requires := "The run hostWritesMemory, of mirror and echo, in which a host adds one to the \
          memory the agent's answer produced, does not meet the record."
        rulesOut := "That run; the same world and agent run faithfully meet the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one system." }, .derived⟩,
    ⟨rulesOutOverridingAction, rulesOutOverridingAction_holds,
      { requires := "The run hostOverridesAction, of mirror and echo, in which a host hands the \
          world the other action than the agent answered, does not meet the record."
        rulesOut := "That run; the same world and agent run faithfully meet the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one system." }, .derived⟩,
    ⟨rulesOutRewardFromMemory, rulesOutRewardFromMemory_holds,
      { requires := "The run rewardFromMemory, of mirror and holdsOne, which gives the agent as \
          its reward the 1 its memory holds while the world generates 0, does not meet the record."
        rulesOut := "That run; the same world and agent given the world's reward meet the record \
          (holdsOne_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one system." }, .derived⟩,
    ⟨rulesOutChangingActions, rulesOutChangingActions_holds,
      { requires := "The game resetOnlyAtGameOver, in the manner of ARC-AGI-3, played by \
          arcPlayer, which makes RESET its only available action at game over, does not meet the \
          record; its player reaches game over after one step."
        rulesOut := "That run; the same game with every action available everywhere meets the \
          record (resettable_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one system." }, .derived⟩,
    ⟨rulesOutOutsideRestart, rulesOutOutsideRestart_holds,
      { requires := "The run hostRestarts, of attempts and echo, in which a host puts the world \
          back at its start at every step, outside its dynamics, does not meet the record."
        rulesOut := "That run; the same world and agent run faithfully meet the record \
          (attempts_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one system." }, .derived⟩,
    ⟨rulesOutUnstoppable, rulesOutUnstoppable_holds,
      { requires := "The run neverStops, of mirror and echo, which takes every step whatever the \
          viewer sends, does not meet the record."
        rulesOut := "That run; the same world and agent with a run that stops on the viewer's \
          request meet the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one system." }, .derived⟩,
    ⟨hiddenState, hiddenState_holds,
      { requires := "Nothing more: some system that meets the record has a world whose \
          observation is the same at every state."
        rulesOut := "Nothing."
        allows := "A world that shows the agent nothing of its state."
        freedom := "Everything but that the world's observation is the same at every state; the \
          record itself requires neither hiding nor showing the state." }, .derived⟩,
    ⟨wholeState, wholeState_holds,
      { requires := "Nothing more: some system that meets the record has a world whose \
          observation tells every two of its states apart."
        rulesOut := "Nothing."
        allows := "A world that shows the agent its whole state."
        freedom := "Everything but that the world's observation tells its states apart; the record \
          itself requires neither hiding nor showing the state." }, .derived⟩,
    ⟨restartsByOwnRules, restartsByOwnRules_holds,
      { requires := "Nothing more: some run of a system that meets the record takes a step from a \
          state other than the world's start at which the world returns to its start by its own \
          dynamics while the agent's answer produced a memory other than its initial one, which the \
          agent keeps."
        rulesOut := "Nothing."
        allows := "A world that restarts between attempts or by its own rules, with the agent's \
          memory carried across."
        freedom := "When and how a world restarts." }, .derived⟩,
    ⟨restartByAction, restartByAction_holds,
      { requires := "Nothing more: some system that meets the record has an action, available at \
          every state, that takes the world back to its start from every state, and a state other \
          than the start that every other action leaves as it is."
        rulesOut := "Nothing."
        allows := "A restart that is the agent's own action, as ARC-AGI-3's RESET is, and a game \
          over that only that action leaves."
        freedom := "Which actions restart a world." }, .derived⟩,
    ⟨keepsNothing, keepsNothing_holds,
      { requires := "Nothing more: some system that meets the record has an agent whose memory \
          after an answer does not depend on what it was given."
        rulesOut := "Nothing."
        allows := "An agent that keeps nothing of its experience."
        freedom := "Everything but that the agent's memory after an answer ignores what it was \
          given." }, .derived⟩,
    ⟨stoppedBeforeFirstStep, stoppedBeforeFirstStep_holds,
      { requires := "Nothing more: some system that meets the record takes no first step under some \
          outside inputs whose first is the viewer's stop request."
        rulesOut := "Nothing."
        allows := "The viewer stopping a run before its first step."
        freedom := "When the viewer stops a run." }, .derived⟩,
    ⟨hostMayStop, hostMayStop_holds,
      { requires := "Nothing more: some run of some system that meets the record, having reached a \
          state and memory, does not take the next step, at an input that is not the viewer's stop \
          request."
        rulesOut := "Nothing."
        allows := "A host that stops a run of its own accord."
        freedom := "When a host stops a run." }, .derived⟩]

end AcornVerif.Intent.WorldInterface
