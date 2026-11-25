import AcornVerif.Intent.Postcondition

namespace AcornVerif.Intent.BigClass

open LeanIntent WorldInterface Postcondition

def afterActions {Obs Act : Type} (M : Member Obs Act) (s : M.State) (acts : List Act) : M.State :=
  acts.foldl M.step s

def given {Obs Act : Type} (M : Member Obs Act) (A : Agent Obs Act) (t : Nat) : Obs × Rat :=
  (M.observe (M.run A t).1, M.reward (M.run A t).1)

def goalsReachable : Clause Trial :=
  ⟨"every member's goal can be reached within an attempt from the state the attempt starts in",
    fun w =>
    ∀ (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat),
      ∃ acts : List w.Act, acts.length < w.length ∧
        (w.member i).goal
          (afterActions (w.member i) (w.stateAt A i (w.length * n)) acts) = true⟩

def goalsConcealed : Clause Trial :=
  ⟨"until a member's goal is first met, the member gives every agent what one reference world \
    gives it", fun w =>
    ∃ R : Member w.Obs w.Act, ∀ (A : Agent w.Obs w.Act) (i : w.Index) (t : Nat),
      (∀ u, u ≤ t → (w.member i).goal (w.stateAt A i u) = false) →
        given (w.member i) A t = given R A t⟩

def frozenShareSmall : Clause Trial :=
  ⟨"on every attempt, an agent that keeps nothing of its experience solves at most a number of \
    the counted members that is smaller than their count", fun w =>
    ∃ k, k < w.counted.length ∧
      ∀ B : Agent w.Obs w.Act, KeepsNothing B → ∀ n, w.solvedCount B n ≤ k⟩

def successShows : Clause Trial :=
  ⟨"one reading of what a member gives an agent says, at every time, whether the member's goal \
    is met then", fun w =>
    ∃ signal : w.Obs × Rat → Bool, ∀ (A : Agent w.Obs w.Act) (i : w.Index) (t : Nat),
      signal (given (w.member i) A t) = (w.member i).goal (w.stateAt A i t)⟩

def attemptsRecur : Clause Trial :=
  ⟨"every attempt of every agent's run in a member starts from the state the member's world \
    starts in", fun w =>
    ∀ (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat),
      w.stateAt A i (w.length * n) = (w.member i).start⟩

abbrev Moment : Type 1 :=
  (w : Trial) × Agent w.Obs w.Act × w.Index × Nat

def bigClass : IntentRecord Trial where
  shape := .value _
  dom := []
  props := [goalsReachable, goalsConcealed, frozenShareSmall, successShows, attemptsRecur]
  vocab := [
    ⟨"the agent keeps nothing of its experience", Entrant, fun c => KeepsNothing c.2⟩,
    ⟨"the member's goal is met at the time", Moment,
      fun c => (c.1.member c.2.2.1).goal (c.1.stateAt c.2.1 c.2.2.1 c.2.2.2) = true⟩]

theorem bigClass_meets {w : Trial} :
    bigClass.Meets w ↔
      goalsReachable.holds w ∧ goalsConcealed.holds w ∧ frozenShareSmall.holds w ∧
        successShows.holds w ∧ attemptsRecur.holds w := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [bigClass]), h _ (by simp [bigClass]), h _ (by simp [bigClass]),
      h _ (by simp [bigClass]), h _ (by simp [bigClass])⟩
  · intro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [bigClass, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

def wall : Member (Option Bool) Bool where
  State := Door
  start := .ask
  observe := fun
    | .ask => none
    | .hit => some true
    | .miss => some false
  reward := fun _ => 0
  step := fun
    | .ask, _ => .miss
    | _, _ => .ask
  goal := fun _ => false

theorem door_next_wall (pay : Rat) (b : Bool) (A : Agent (Option Bool) Bool) (c : Door × A.Memory)
    (h : (door pay b).goal c.1 = false)
    (h' : (door pay b).goal ((door pay b).next A c).1 = false) :
    (door pay b).next A c = wall.next A c := by
  obtain ⟨s, m⟩ := c
  cases s with
  | ask =>
    have hg : (door pay b).goal
        (bif (A.act m (none, 0)).1 == b then Door.hit else Door.miss) = false := h'
    show ((bif (A.act m (none, 0)).1 == b then Door.hit else Door.miss), (A.act m (none, 0)).2) =
      (Door.miss, (A.act m (none, 0)).2)
    cases hab : (A.act m (none, 0)).1 == b
    · rfl
    · rw [hab] at hg
      have hf : true = false := hg
      exact Bool.noConfusion hf
  | hit =>
    have hf : true = false := h
    exact Bool.noConfusion hf
  | miss => rfl

theorem door_run_wall (pay : Rat) (b : Bool) (A : Agent (Option Bool) Bool) :
    ∀ t, (∀ u, u ≤ t → (door pay b).goal ((door pay b).run A u).1 = false) →
      (door pay b).run A t = wall.run A t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := door_run_wall pay b A t (fun u hu => h u (Nat.le_succ_of_le hu))
    show (door pay b).next A ((door pay b).run A t) = wall.next A (wall.run A t)
    rw [← ih]
    exact door_next_wall pay b A _ (h t (Nat.le_succ t)) (h (t + 1) (Nat.le_refl _))

variable (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)

theorem doors_goalsReachable : goalsReachable.holds (doors total pay X) :=
  fun (A : Agent (Option Bool) Bool) (b : Bool) n => ⟨[b], Nat.lt_succ_self 1, by
    show (door pay b).goal (afterActions (door pay b) ((door pay b).run A (2 * n)).1 [b]) = true
    rw [door_ask]
    cases b <;> rfl⟩

theorem doors_goalsConcealed : goalsConcealed.holds (doors total pay X) :=
  ⟨wall, fun (A : Agent (Option Bool) Bool) (b : Bool) t h => by
    have hs : (door pay b).goal ((door pay b).run A t).1 = false := h t (Nat.le_refl t)
    show ((door pay b).observe ((door pay b).run A t).1,
      (door pay b).reward ((door pay b).run A t).1) =
        (wall.observe (wall.run A t).1, wall.reward (wall.run A t).1)
    rw [← door_run_wall pay b A t h]
    generalize ((door pay b).run A t).1 = s at hs
    cases s with
    | ask => rfl
    | hit =>
      have hf : true = false := hs
      exact Bool.noConfusion hf
    | miss => rfl⟩

theorem doors_frozenShareSmall : frozenShareSmall.holds (doors total pay X) :=
  ⟨1, Nat.lt_succ_self 1, fun (B : Agent (Option Bool) Bool) hB n => by
    rw [doors_solvedCount, doors_solves, doors_solves, keepsNothing_tried pay hB,
      keepsNothing_tried pay hB]
    cases guess B n <;> decide⟩

theorem doors_successShows : successShows.holds (doors total pay X) :=
  ⟨fun (o : Option Bool × Rat) => o.1 == some true,
    fun (A : Agent (Option Bool) Bool) (b : Bool) t => by
    show ((door pay b).observe ((door pay b).run A t).1 == some true) =
      (door pay b).goal ((door pay b).run A t).1
    generalize ((door pay b).run A t).1 = s
    cases s <;> rfl⟩

theorem doors_attemptsRecur : attemptsRecur.holds (doors total pay X) :=
  fun (A : Agent (Option Bool) Bool) (b : Bool) n => door_ask pay b A n

theorem doors_big : bigClass.Meets (doors total pay X) :=
  bigClass_meets.mpr ⟨doors_goalsReachable total pay X, doors_goalsConcealed total pay X,
    doors_frozenShareSmall total pay X, doors_successShows total pay X,
    doors_attemptsRecur total pay X⟩

theorem bigClass_o2 : O2 bigClass := by
  refine (o2_correct _).mpr ⟨⟨base, fun _ h => nomatch h⟩, fun p hp => ?_⟩
  simp only [bigClass, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨base, always true⟩, always_keepsNothing true⟩
  · exact ⟨⟨base, finder, true, 1⟩, rfl⟩

theorem bigClass_o2Run : O2Run bigClass :=
  (o2Run_correct _).mpr ⟨base, (doors_big List.sum 1 finder).1, (doors_big List.sum 1 finder).2⟩

def classOf (member : Bool → Member (Option Bool) Bool) : Trial where
  Obs := Option Bool
  Act := Bool
  Index := Bool
  member := member
  counted := [true, false]
  length := 2
  total := List.sum
  horizon := 3
  lapses := 0
  agent := finder

def unreachable : Trial := classOf fun b => { door 1 b with goal := fun _ => false }

def revealing : Trial :=
  classOf fun b =>
    { door 1 b with
      observe := fun (s : Door) =>
        match s with
        | .ask => some b
        | .hit => some true
        | .miss => some false }

def sameDoor : Trial := classOf fun _ => door 1 true

def hidden : Trial :=
  classOf fun b =>
    { door 0 b with
      observe := fun (s : Door) =>
        match s with
        | .ask => none
        | _ => some false }

def stuck : Trial :=
  classOf fun b => { door 1 b with step := fun (_ : Door) (_ : Bool) => Door.miss }

theorem bigClass_o3 : O3 bigClass := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [bigClass, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · refine ⟨unreachable, fun h => ?_⟩
    obtain ⟨acts, _, hg⟩ := h finder true 0
    have hf : false = true := hg
    exact Bool.noConfusion hf
  · refine ⟨revealing, fun ⟨R, h⟩ => ?_⟩
    have e := (h finder true 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)).trans
      (h finder false 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)).symm
    have e' : some true = some false := congrArg Prod.fst e
    exact absurd e' (by decide)
  · refine ⟨sameDoor, fun ⟨k, hk, h⟩ => ?_⟩
    have h2 : sameDoor.solvedCount (always true) 0 ≤ k :=
      h (always true) (always_keepsNothing true) 0
    have hk' : k < 2 := hk
    have h3 : sameDoor.solvedCount (always true) 0 = 2 := by decide
    omega
  · refine ⟨hidden, fun ⟨signal, h⟩ => ?_⟩
    have h1 : signal (some false, 0) = true := h (always true) true 1
    have h2 : signal (some false, 0) = false := h (always true) false 1
    exact Bool.noConfusion (h1.symm.trans h2)
  · refine ⟨stuck, fun h => ?_⟩
    have e : Door.miss = Door.ask := h finder true 1
    exact absurd e (by decide)

theorem bigClass_o4 : O4 bigClass := (o4_correct _).mpr trivial

theorem bigClass_o5_widest : O5 bigClass .widest := o5_widest _

theorem bigClass_not_o5_eq : ¬ O5 bigClass .eq := by
  refine not_o5_eq (doors_big List.sum 1 finder) (doors_big (fun l => l.sum + l.sum) 1 finder)
    fun h => ?_
  have ht : base.total [1] = doubled.total [1] := congrArg (fun w : Trial => w.total [1]) h
  exact absurd ht (by decide +kernel)

theorem bigClass_pairs :
    ∀ c ∈ bigClass.props, OPair (Pair.whole bigClass c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨base, trivial, fun _ => (doors_big List.sum 1 finder).2 c hc⟩

end AcornVerif.Intent.BigClass
