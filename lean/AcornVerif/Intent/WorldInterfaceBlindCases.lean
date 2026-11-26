import AcornVerif.Intent.WorldInterfaceConsequences

namespace AcornVerif.Intent.WorldInterface.Cases

open LeanIntent AcornVerif.Intent.WorldInterface

abbrev M := worldInterface.Meets

def wFlip (avail : Bool → Bool → Prop) (obs : Bool → Bool) (st : Bool := false) : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := st
  observe := obs
  reward _ := 0
  available := avail
  step s a := cond a (!s) s

def wStill (avail : Bool → Bool → Prop) (st : Bool) : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := st
  observe s := s
  reward _ := 0
  available := avail
  step _ _ := false

def flipper (init : Nat := 0) : Agent Bool Bool where
  Memory := Nat
  initial := init
  act m _ := (true, m + 1)

def holder : Agent Bool Bool where
  Memory := Nat
  initial := 0
  act m _ := (false, m + 1)

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

def s7 : System :=
  runOf (wFlip (fun _ _ => True) (fun _ => false)) (flipper) (fun _ _ e => !e) (fun s _ _ => (s, 0))
    (fun _ _ _ a => a) (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)

theorem c7 : ¬ M s7 := fun h => by
  have := (worldInterface_meets.mp h).1 neverStop 1 true (1 : Nat) ⟨.next .start rfl, rfl⟩
  change true = false at this
  exact Bool.noConfusion this

def minusHalf : Rat := ⟨-1, 2, by decide, by decide⟩
def threeHalves : Rat := ⟨3, 2, by decide, by decide⟩

def w8 : World where
  State := Bool
  Obs := Unit
  Act := Bool
  start := false
  observe _ := ()
  reward s := cond s threeHalves minusHalf
  available _ _ := True
  step s a := cond a (!s) s

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

def w10 (obs : Bool → Bool × Bool) : World where
  State := Bool
  Obs := Bool × Bool
  Act := Bool
  start := false
  observe := obs
  reward _ := 0
  available _ _ := True
  step s a := cond a (!s) s

def task : Agent (Bool × Bool) Bool where
  Memory := Nat
  initial := 0
  act m o := (!o.1.2, m + 1)

theorem c10 : M (couple (w10 fun s => (false, s)) task) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

def s11 : System :=
  runOf (w10 fun _ => (false, false)) task (fun _ _ e => !e) (fun s _ _ => ((false, s), 0))
    (fun _ _ _ a => a) (fun s _ _ a => cond a (!s) s) (fun _ _ _ m => m)

theorem c11 : ¬ M s11 := fun h => by
  have := (worldInterface_meets.mp h).1 neverStop 1 true (1 : Nat) ⟨.next .start rfl, rfl⟩
  change (false, true) = (false, false) at this
  exact absurd this (by decide)

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

def w16 : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe s := s
  reward _ := 0
  available _ _ := True
  step _ a := a

def histAgent : Agent Bool Bool where
  Memory := List Bool
  initial := []
  act h o := (!o.1, h ++ [o.1])

theorem c16 : M (couple w16 histAgent) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

def s17 : System :=
  runOf w16 histAgent (fun _ _ e => !e) (fun s _ _ => (s, 0)) (fun _ _ _ a => a) (fun _ _ _ a => a)
    (fun s _ _ n => cond s List.nil n)

theorem c17 : ¬ M s17 := fun h => by
  have := (worldInterface_meets.mp h).2.2.2.2.2.2.1 neverStop 1 true [false]
    ⟨.next .start rfl, rfl⟩
  change ([] : List Bool) = [false, true] at this
  exact absurd this (by decide)

def clearer : Agent Bool Bool where
  Memory := List Bool
  initial := []
  act h o := (!o.1, cond o.1 [] (h ++ [false]))

theorem c18 : M (couple w16 clearer) := couple_meets _ _ (fun _ _ _ => Iff.rfl) fun _ _ _ => trivial

def w19 : World where
  State := Unit
  Obs := Unit
  Act := Unit
  start := ()
  observe _ := ()
  reward _ := 0
  available _ _ := True
  step _ _ := ()

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

def w26 : World where
  State := Unit
  Obs := Unit
  Act := Bool
  start := ()
  observe _ := ()
  reward _ := 0
  available _ a := a = true
  step _ _ := ()

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

def w29 (avail : Nat → Nat → Prop) : World where
  State := Nat
  Obs := Nat
  Act := Nat
  start := 0
  observe s := s
  reward _ := 0
  available := avail
  step s _ := s + 1

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
