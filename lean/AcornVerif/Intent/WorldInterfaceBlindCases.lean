/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.WorldInterfaceConsequences

/-!
# The blind cases reading of contract 1, with the record's verdicts

The second, blind reading of contract 1's eight sentences that OpenAI's gpt-6-astra made for
concrete cases with verdicts, after the record `AcornVerif.Intent.WorldInterface.worldInterface`
was sealed at commit f6c9c73. It is no deliverable and no part of the owner's intent: it is a
second model's reading of the owner's words. Each of its 34 cases is stated here as a system, and
the theorems `c1` to `c34` prove the record's verdict on each: that its system meets the record,
or that it does not. How each verdict compares with the cases reading's is in the record's
confirmation file, `lean/AcornVerif/Intent/WorldInterface.md`.

States 0 and 1 are `false` and `true`; `flip` and `advance` are `true`, `hold` and `reset` are
`false`; `run` and `stop` are `false` and `true`, except in cases 31 and 32.
-/

namespace AcornVerif.Intent.WorldInterface.Cases

open LeanIntent AcornVerif.Intent.WorldInterface

/-- Whether a system meets the record. -/
abbrev M := worldInterface.Meets

/-- A world of two states that the action `true` flips and `false` keeps, starting at `st`, with
the available actions `avail`, the observation `obs` and reward 0. -/
def wFlip (avail : Bool → Bool → Prop) (obs : Bool → Bool) (st : Bool := false) : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := st
  observe := obs
  reward _ := 0
  available := avail
  step s a := cond a (!s) s

/-- A world of two states that every action moves to `false`, starting at `st` and showing its
state, with the available actions `avail` and reward 0. -/
def wStill (avail : Bool → Bool → Prop) (st : Bool) : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := st
  observe s := s
  reward _ := 0
  available := avail
  step _ _ := false

/-- An agent that always answers `true` and counts its steps from `init`. -/
def flipper (init : Nat := 0) : Agent Bool Bool where
  Memory := Nat
  initial := init
  act m _ := (true, m + 1)

/-- An agent that always answers `false` and counts its steps. -/
def holder : Agent Bool Bool where
  Memory := Nat
  initial := 0
  act m _ := (false, m + 1)

/-- The world `wFlip` with both actions available everywhere, showing its state. -/
def w1 : World := wFlip (fun _ _ => True) id

theorem c1 : M (couple w1 (flipper)) := couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

theorem c2 : M (couple (wFlip (fun _ a => a = true) id) (flipper)) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => rfl

theorem c3 : ¬ M (couple (wFlip (fun s a => a = true ∨ s = false) id) (flipper)) := fun h => by
  have := ((worldInterface_meets.mp h).2.2.2.1 false true false).mp (Or.inr rfl)
  change false = true ∨ true = false at this
  exact absurd this (by decide)

theorem c4 : ¬ M (couple (wFlip (fun _ a => a = true) id) holder) := fun h => by
  have := (worldInterface_meets.mp h).2.2.1 neverStop 0 _ _ (takes_first rfl)
  change false = true at this
  exact Bool.noConfusion this

theorem c5 : ¬ M (couple (wFlip (fun _ _ => False) id) (flipper)) := fun h =>
  (worldInterface_meets.mp h).2.2.1 neverStop 0 _ _ (takes_first rfl)

theorem c6 : M (couple (wFlip (fun _ _ => True) (fun _ => false)) (flipper)) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- Case 7's system: the run of `wFlip` with an observation that is always `false` and `flipper`,
which gives the agent the world's state in place of its observation. -/
def s7 : System :=
  runOf (wFlip (fun _ _ => True) (fun _ => false)) (flipper) (fun _ _ e => !e) (fun s _ _ => (s, 0))
    (fun _ _ _ a => a) (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)

theorem c7 : ¬ M s7 := fun h => by
  have := (worldInterface_meets.mp h).1 neverStop 1 true (1 : Nat) ⟨.next .start rfl, rfl⟩
  change true = false at this
  exact Bool.noConfusion this

/-- -1/2, written as a reduced fraction. -/
def minusHalf : Rat := ⟨-1, 2, by decide, by decide⟩
/-- 3/2, written as a reduced fraction. -/
def threeHalves : Rat := ⟨3, 2, by decide, by decide⟩

/-- A world of two states that the action `true` flips, showing nothing, whose reward is 3/2 at
the state `true` and -1/2 at `false`, with both actions available everywhere. -/
def w8 : World where
  State := Bool
  Obs := Unit
  Act := Bool
  start := false
  observe _ := ()
  reward s := cond s threeHalves minusHalf
  available _ _ := True
  step s a := cond a (!s) s

/-- An agent that always answers `true` and keeps the sum of the rewards it is given. -/
def ratAgent : Agent Unit Bool where
  Memory := Rat
  initial := 0
  act m o := (true, m + o.2)

theorem c8 : M (couple w8 ratAgent) := couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

theorem c9 : ¬ M (runOf w8 ratAgent (fun _ _ e => !e) (fun _ m _ => ((), m)) (fun _ _ _ a => a)
    (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)) := fun h => by
  have := (worldInterface_meets.mp h).2.1 neverStop 0 _ _ (takes_first rfl)
  change (0 : Rat) = minusHalf at this
  exact absurd this (by decide)

/-- A world of two states that the action `true` flips, whose observation `obs` is a pair of
signals, with reward 0 and both actions available everywhere. -/
def w10 (obs : Bool → Bool × Bool) : World where
  State := Bool
  Obs := Bool × Bool
  Act := Bool
  start := false
  observe := obs
  reward _ := 0
  available _ _ := True
  step s a := cond a (!s) s

/-- An agent that answers the negation of its observation's second signal and counts its
steps. -/
def task : Agent (Bool × Bool) Bool where
  Memory := Nat
  initial := 0
  act m o := (!o.1.2, m + 1)

theorem c10 : M (couple (w10 fun s => (false, s)) task) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- Case 11's system: the run of `w10` with an observation that is always `(false, false)` and
`task`, which gives the agent the world's state as the observation's second signal. -/
def s11 : System :=
  runOf (w10 fun _ => (false, false)) task (fun _ _ e => !e) (fun s _ _ => ((false, s), 0))
    (fun _ _ _ a => a) (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)

theorem c11 : ¬ M s11 := fun h => by
  have := (worldInterface_meets.mp h).1 neverStop 1 true (1 : Nat) ⟨.next .start rfl, rfl⟩
  change (false, true) = (false, false) at this
  exact absurd this (by decide)

/-- The run of `W` and `A` that goes on unless the viewer asks it to stop, its other parts still
to be given. -/
def faithfulBut (W : World) (A : Agent W.Obs W.Act) := runOf W A (fun _ _ e => !e)

theorem c12 : ¬ M (runOf w1 (flipper) (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ _ => false)
    (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)) := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.1 neverStop 0 _ _ (takes_first rfl)
  change false = true at this
  exact Bool.noConfusion this

theorem c13 : ¬ M (runOf w1 (flipper) (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun s _ _ a => cond a (!s) s) (fun _ m _ _ => Nat.add m 2)) := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.2.2.1 neverStop 0 _ _ (takes_first rfl)
  change (2 : Nat) = 1 at this
  exact absurd this (by decide)

theorem c14 : ¬ M (runOf w1 (flipper) (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun _ _ _ _ => false) (fun _ _ _ m => m)) := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.2.1 neverStop 0 _ _ (takes_first rfl)
  change false = true at this
  exact Bool.noConfusion this

theorem c15 : M (couple (wStill (fun _ _ => True) false) (flipper)) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- A world of two states that moves to the state the action names and shows its state, with
reward 0 and both actions available everywhere. -/
def w16 : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe s := s
  reward _ := 0
  available _ _ := True
  step _ a := a

/-- An agent that answers the negation of its observation and keeps the list of the observations
it is given. -/
def histAgent : Agent Bool Bool where
  Memory := List Bool
  initial := []
  act h o := (!o.1, h ++ [o.1])

theorem c16 : M (couple w16 histAgent) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- Case 17's system: the run of `w16` and `histAgent` that empties the agent's memory on each step
from the state `true`, the step on which the agent's answer returns the world to its start. -/
def s17 : System :=
  runOf w16 histAgent (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => a) (fun _ _ _ a => a)
    (fun s _ _ n => cond s List.nil n)

theorem c17 : ¬ M s17 := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.2.2.1 neverStop 1 true [false]
    ⟨.next .start rfl, rfl⟩
  change ([] : List Bool) = [false, true] at this
  exact absurd this (by decide)

/-- An agent that answers the negation of its observation, and empties its own memory when its
observation is `true` and adds `false` to it otherwise. -/
def clearer : Agent Bool Bool where
  Memory := List Bool
  initial := []
  act h o := (!o.1, cond o.1 [] (h ++ [false]))

/-- Case 18: the record's verdict differs from the cases reading's, which judged that an agent
clearing its own memory when it resets the world fails sentence 7. This verdict was decided on
the owner's behalf by the agent supervising Acorn's research, as the record's confirmation file,
`lean/AcornVerif/Intent/WorldInterface.md`, says. -/
theorem c18 : M (couple w16 clearer) := couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- A world of one state, one observation and one action, with reward 0. -/
def w19 : World where
  State := Unit
  Obs := Unit
  Act := Unit
  start := ()
  observe _ := ()
  reward _ := 0
  available _ _ := True
  step _ _ := ()

/-- An agent that keeps the parity of the number of steps it has taken. -/
def parity : Agent Unit Unit where
  Memory := Bool
  initial := false
  act m _ := ((), !m)

theorem c19 : M (couple w19 parity) := couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

theorem c20 : ¬ M (runOf w19 parity (fun _ _ e => !e) (fun _ _ _ => ((), 0)) (fun _ _ _ a => a)
    (fun _ _ _ _ => ()) (fun _ _ _ _ => false)) := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.2.2.1 neverStop 0 _ _ (takes_first rfl)
  change false = true at this
  exact Bool.noConfusion this

/-- Case 21's system: the run of `w1` and `flipper` that goes on whatever it is sent. -/
def s21 : System :=
  runOf w1 (flipper) (fun _ _ _ => true) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)

theorem s21_reaches (ins : Nat → Bool) : ∀ t, ∃ s m, s21.Reaches ins t s m
  | 0 => ⟨_, _, .start⟩
  | t + 1 =>
    let ⟨_, _, h⟩ := s21_reaches ins t
    ⟨_, _, .next h rfl⟩

theorem c21 : ¬ M s21 := fun h => by
  obtain ⟨t, -, ht⟩ :=
    (worldInterface_meets.mp h).2.2.2.2.2.2.2.1 (fun _ => true) 0 (fun _ _ => rfl)
  obtain ⟨s, m, hr⟩ := s21_reaches (fun _ => true) t
  exact ht s m ⟨hr, rfl⟩

/-- Case 22's system: the run of `w1` and `flipper` that gives the agent reward 1 when the viewer
asks it to stop, where it takes no step. -/
def s22 : System :=
  runOf w1 (flipper) (fun _ _ e => !e) (fun s _ e => (s, cond e 1 0)) (fun _ _ _ a => a)
    (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)

theorem c22 : M s22 := by
  refine worldInterface_meets.mpr ⟨fun _ _ _ _ _ => rfl, fun ins t s m h => ?_,
    fun _ _ _ _ _ => trivial, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun ins t₀ hs => ⟨t₀, Nat.le_refl _, fun s m ht => ?_⟩, ⟨false, rfl⟩⟩
  · have hg : (!(ins t)) = true := h.2
    change (cond (ins t) 1 0 : Rat) = 0
    revert hg
    cases ins t with
    | false => exact fun _ => rfl
    | true => exact fun hg => Bool.noConfusion hg
  · have hg : (!(ins t₀)) = true := ht.2
    rw [hs t₀ (Nat.le_refl _)] at hg
    exact Bool.noConfusion hg

theorem c23 : ¬ M (runOf w1 (flipper) (fun _ _ _ => false) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)) := fun h => by
  obtain ⟨_, he⟩ := (worldInterface_meets.mp h).2.2.2.2.2.2.2.2
  exact Bool.noConfusion he

/-- Case 24's system: the run of `wStill` from `false` and `flipper`, which gives the agent the
observation `false` at every state, the world's own at the only state a run reaches. -/
def s24 : System :=
  runOf (wStill (fun _ _ => True) false) (flipper) (fun _ _ e => !e) (fun _ _ _ => (false, 0))
    (fun _ _ _ a => a) (fun _ _ _ _ => false) (fun _ _ _ m => m)

theorem c24 : M s24 := by
  refine worldInterface_meets.mpr ⟨fun ins t s m h => ?_, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => trivial, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun ins t₀ hs => ⟨t₀, Nat.le_refl _, fun s m ht => ?_⟩, ⟨false, rfl⟩⟩
  · cases h.1 <;> rfl
  · have hg : (!(ins t₀)) = true := ht.2
    rw [hs t₀ (Nat.le_refl _)] at hg
    exact Bool.noConfusion hg

theorem c25 : ¬ M (runOf (wStill (fun _ _ => True) true) (flipper) (fun _ _ e => !e)
    (fun _ _ _ => (false, 0)) (fun _ _ _ a => a) (fun _ _ _ _ => false) (fun _ _ _ m => m)) :=
  fun h => by
  have := (worldInterface_meets.mp h).1 neverStop 0 _ _ (takes_first rfl)
  change false = true at this
  exact Bool.noConfusion this

/-- A world of one state in which only the action `true` is available, with reward 0. -/
def w26 : World where
  State := Unit
  Obs := Unit
  Act := Bool
  start := ()
  observe _ := ()
  reward _ := 0
  available _ a := a = true
  step _ _ := ()

/-- An agent that answers `true` exactly when its reward is 0 and keeps nothing. -/
def okIfZero : Agent Unit Bool where
  Memory := Unit
  initial := ()
  act _ o := (decide (o.2 = 0), ())

theorem c26 : M (couple w26 okIfZero) := by
  refine worldInterface_meets.mpr ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => ?_, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun ins t₀ hs => ⟨t₀, Nat.le_refl _, fun s m ht => ?_⟩, ⟨false, rfl⟩⟩
  · change decide ((0 : Rat) = 0) = true
    decide
  · have hg : (!(ins t₀)) = true := ht.2
    rw [hs t₀ (Nat.le_refl _)] at hg
    exact Bool.noConfusion hg

theorem c27 : ¬ M (couple w26 (always false)) := fun h => by
  have := (worldInterface_meets.mp h).2.2.1 neverStop 0 _ _ (takes_first rfl)
  change false = true at this
  exact Bool.noConfusion this

theorem c28 : M (couple w1 (flipper 7)) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

/-- A world that counts its steps and shows the count, with the available actions `avail` and
reward 0. -/
def w29 (avail : Nat → Nat → Prop) : World where
  State := Nat
  Obs := Nat
  Act := Nat
  start := 0
  observe s := s
  reward _ := 0
  available := avail
  step s _ := s + 1

/-- An agent that always answers 0 and counts its steps. -/
def zeroer : Agent Nat Nat where
  Memory := Nat
  initial := 0
  act m _ := (0, m + 1)

theorem c29 : M (couple (w29 fun _ _ => True) zeroer) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

theorem c30 : ¬ M (couple (w29 fun s a => a ≤ s) zeroer) := fun h => by
  have := ((worldInterface_meets.mp h).2.2.2.1 (1 : Nat) (0 : Nat) (1 : Nat)).mp (Nat.le_refl 1)
  change 1 ≤ 0 at this
  exact absurd this (by decide)

/-- Inputs 0 (run), 1 (override) and 2 (stop). -/
def s31 (override : Bool) : System where
  State := Bool
  Obs := Bool
  Act := Bool
  Memory := Nat
  Input := Nat
  start := false
  observe s := s
  reward _ := 0
  available _ _ := True
  step s a := cond a (!s) s
  initial := 0
  act m _ := (true, m + 1)
  stopRequest := 2
  goesOn _ _ e := e != 2
  given s _ _ := (s, 0)
  applied _ _ e a := cond (override && e == 1) false a
  moved s _ _ a := cond a (!s) s
  kept _ _ _ m := m

theorem c31 : M (s31 false) := by
  refine worldInterface_meets.mpr ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => trivial, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun ins t₀ hs => ⟨t₀, Nat.le_refl _, fun s m ht => ?_⟩, ⟨(0 : Nat), rfl⟩⟩
  have hg := ht.2
  rw [hs t₀ (Nat.le_refl _)] at hg
  change ((2 : Nat) != 2) = true at hg
  exact absurd hg (by decide)

theorem c32 : ¬ M (s31 true) := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.1 (fun _ => (1 : Nat)) 0 _ _ (takes_first rfl)
  change false = true at this
  exact Bool.noConfusion this

theorem c33 : M (couple w19 (always ())) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

theorem c34 : ¬ M (couple (wStill (fun s a => a = true ∨ s = false) false) (flipper)) := fun h => by
  have := ((worldInterface_meets.mp h).2.2.2.1 false true false).mp (Or.inr rfl)
  change false = true ∨ true = false at this
  exact absurd this (by decide)

end AcornVerif.Intent.WorldInterface.Cases
