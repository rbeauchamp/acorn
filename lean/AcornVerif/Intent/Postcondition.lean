import AcornVerif.Intent.WorldInterface

namespace AcornVerif.Intent.Postcondition

open LeanIntent WorldInterface

structure Member (Obs Act : Type) where
  State : Type
  start : State
  observe : State → Obs
  reward : State → Rat
  step : State → Act → State
  goal : State → Bool

namespace Member

variable {Obs Act : Type}

def next (M : Member Obs Act) (A : Agent Obs Act) (c : M.State × A.Memory) : M.State × A.Memory :=
  (M.step c.1 (A.act c.2 (M.observe c.1, M.reward c.1)).1,
    (A.act c.2 (M.observe c.1, M.reward c.1)).2)

def run (M : Member Obs Act) (A : Agent Obs Act) : Nat → M.State × A.Memory
  | 0 => (M.start, A.initial)
  | t + 1 => M.next A (M.run A t)

end Member

def KeepsNothing {Obs Act : Type} (A : Agent Obs Act) : Prop :=
  ∀ m o o', (A.act m o).2 = (A.act m o').2

structure Trial where
  Obs : Type
  Act : Type
  Index : Type
  member : Index → Member Obs Act
  counted : List Index
  length : Nat
  total : List Rat → Rat
  horizon : Nat
  lapses : Nat
  agent : Agent Obs Act

namespace Trial

variable (w : Trial)

def stateAt (A : Agent w.Obs w.Act) (i : w.Index) (t : Nat) : (w.member i).State :=
  ((w.member i).run A t).1

def attemptTimes (n : Nat) : List Nat :=
  (List.range w.length).map (w.length * n + ·)

def solves (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat) : Bool :=
  (w.attemptTimes n).any fun t => (w.member i).goal (w.stateAt A i t)

def earned (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat) : Rat :=
  w.total ((w.attemptTimes n).map fun t => (w.member i).reward (w.stateAt A i t))

def classReward (A : Agent w.Obs w.Act) (n : Nat) : Rat :=
  (w.counted.map fun i => w.earned A i n).sum

def solvedCount (A : Agent w.Obs w.Act) (n : Nat) : Nat :=
  (w.counted.filter fun i => w.solves A i n).length

def Compared (A : Agent w.Obs w.Act) : Prop :=
  A = w.agent ∨ KeepsNothing A

def SameProblem (i : w.Index) (n n' : Nat) : Prop :=
  w.stateAt w.agent i (w.length * n') = w.stateAt w.agent i (w.length * n)

end Trial

def rewardCountsMembers : Clause Trial :=
  ⟨"among the agents compared, and for any attempt of each, one earns more reward across the \
    class on its attempt than the other on its own exactly when it solves more members on it",
    fun w =>
    ∀ A B, w.Compared A → w.Compared B → ∀ n k,
      (w.classReward B k < w.classReward A n ↔ w.solvedCount B k < w.solvedCount A n)⟩

def earnsMoreInTime : Clause Trial :=
  ⟨"on some attempt that leaves more later attempts before a stated attempt than a stated number \
    of lapses, the agent earns more reward across the class than any agent that keeps nothing of \
    its experience earns on any attempt", fun w =>
    ∃ n, n + w.lapses + 1 < w.horizon ∧
      ∀ B, KeepsNothing B → ∀ k, w.classReward B k < w.classReward w.agent n⟩

def keepsSolving : Clause Trial :=
  ⟨"once the agent has solved a member, it solves it again on every later attempt before a \
    stated attempt, but for at most a stated number of them, while the member's attempts start \
    from the same state", fun w =>
    ∀ i, ∃ lapsed : List Nat, lapsed.length ≤ w.lapses ∧
      ∀ n n', n ≤ n' → n' < w.horizon → (∀ k, n ≤ k → k ≤ n' → w.SameProblem i n k) →
        w.solves w.agent i n = true → n' ∉ lapsed → w.solves w.agent i n' = true⟩

def learnsAgain : Clause Trial :=
  ⟨"once the agent has solved a member, it solves it again within the stated number of lapses \
    and one attempt more, once the member's attempts have come back for good to the state the \
    solved one started from, where those attempts come before the stated attempt", fun w =>
    ∀ i n n', n ≤ n' → n' + w.lapses < w.horizon → (∀ k, n' ≤ k → w.SameProblem i n k) →
      w.solves w.agent i n = true →
        ∃ n'', n' ≤ n'' ∧ n'' ≤ n' + w.lapses ∧ w.solves w.agent i n'' = true⟩

abbrev Entrant : Type 1 :=
  (w : Trial) × Agent w.Obs w.Act

abbrev Attempt : Type 1 :=
  (w : Trial) × Agent w.Obs w.Act × w.Index × Nat

def postcondition : IntentRecord Trial where
  shape := .value _
  dom := []
  props := [rewardCountsMembers, earnsMoreInTime, keepsSolving, learnsAgain]
  vocab := [
    ⟨"the agent keeps nothing of its experience", Entrant, fun c => KeepsNothing c.2⟩,
    ⟨"the agent solves the member on the attempt", Attempt,
      fun c => c.1.solves c.2.1 c.2.2.1 c.2.2.2 = true⟩]

theorem postcondition_meets {w : Trial} :
    postcondition.Meets w ↔
      rewardCountsMembers.holds w ∧ earnsMoreInTime.holds w ∧ keepsSolving.holds w ∧
        learnsAgain.holds w := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [postcondition]), h _ (by simp [postcondition]),
      h _ (by simp [postcondition]), h _ (by simp [postcondition])⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [postcondition, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4

inductive Door where
  | ask
  | hit
  | miss
  deriving DecidableEq

def door (pay : Rat) (b : Bool) : Member (Option Bool) Bool where
  State := Door
  start := .ask
  observe := fun
    | .ask => none
    | .hit => some true
    | .miss => some false
  reward := fun
    | .hit => pay
    | _ => 0
  step := fun
    | .ask, a => bif a == b then .hit else .miss
    | _, _ => .ask
  goal := fun
    | .hit => true
    | _ => false

def doors (total : List Rat → Rat) (pay : Rat) (A : Agent (Option Bool) Bool) : Trial where
  Obs := Option Bool
  Act := Bool
  Index := Bool
  member := door pay
  counted := [true, false]
  length := 2
  total := total
  horizon := 3
  lapses := 0
  agent := A

def tried (pay : Rat) (A : Agent (Option Bool) Bool) (b : Bool) (n : Nat) : Bool :=
  (A.act ((door pay b).run A (2 * n)).2
    ((door pay b).observe ((door pay b).run A (2 * n)).1,
      (door pay b).reward ((door pay b).run A (2 * n)).1)).1

theorem door_restart (pay : Rat) (b a a' : Bool) :
    (door pay b).step ((door pay b).step Door.ask a) a' = Door.ask := by
  cases a <;> cases b <;> rfl

theorem door_ask (pay : Rat) (b : Bool) (A : Agent (Option Bool) Bool) :
    ∀ n, ((door pay b).run A (2 * n)).1 = Door.ask
  | 0 => rfl
  | n + 1 => by
    have h := door_ask pay b A n
    show (door pay b).step ((door pay b).step ((door pay b).run A (2 * n)).1 _) _ = Door.ask
    rw [h]
    exact door_restart pay b _ _

theorem door_tried (pay : Rat) (b : Bool) (A : Agent (Option Bool) Bool) (n : Nat) :
    ((door pay b).run A (2 * n + 1)).1 = bif tried pay A b n == b then Door.hit else Door.miss := by
  show (door pay b).step ((door pay b).run A (2 * n)).1 (tried pay A b n) = _
  rw [door_ask]
  rfl

variable (total : List Rat → Rat) (pay : Rat) (X A : Agent (Option Bool) Bool)

theorem doors_solves (b : Bool) (n : Nat) :
    (doors total pay X).solves A b n = (tried pay A b n == b) := by
  show ((door pay b).goal ((door pay b).run A (2 * n)).1 ||
    ((door pay b).goal ((door pay b).run A (2 * n + 1)).1 || false)) = _
  rw [door_tried, door_ask]
  cases tried pay A b n == b <;> rfl

def paid (s : Bool) : Rat :=
  total [0, bif s then pay else 0]

theorem doors_earned (b : Bool) (n : Nat) :
    (doors total pay X).earned A b n = paid total pay ((doors total pay X).solves A b n) := by
  rw [doors_solves]
  show total [(door pay b).reward ((door pay b).run A (2 * n)).1,
    (door pay b).reward ((door pay b).run A (2 * n + 1)).1] = _
  rw [door_tried, door_ask]
  cases tried pay A b n == b <;> rfl

theorem doors_classReward (n : Nat) :
    (doors total pay X).classReward A n =
      paid total pay ((doors total pay X).solves A true n) +
        (paid total pay ((doors total pay X).solves A false n) + 0) := by
  show (doors total pay X).earned A true n + ((doors total pay X).earned A false n + 0) = _
  rw [doors_earned, doors_earned]

def tally (s t : Bool) : Nat :=
  (bif s then 1 else 0) + (bif t then 1 else 0)

theorem doors_solvedCount (n : Nat) :
    (doors total pay X).solvedCount A n =
      tally ((doors total pay X).solves A true n) ((doors total pay X).solves A false n) := by
  show ([true, false].filter fun i => (doors total pay X).solves A i n).length = _
  cases h1 : (doors total pay X).solves A true n <;>
    cases h2 : (doors total pay X).solves A false n <;> simp only [List.filter, h1, h2] <;> rfl

def Fair : Prop :=
  ∀ s1 s2 s3 s4 : Bool,
    (paid total pay s3 + (paid total pay s4 + 0) < paid total pay s1 + (paid total pay s2 + 0) ↔
      tally s3 s4 < tally s1 s2)

theorem doors_rewardCounts (h : Fair total pay) :
    rewardCountsMembers.holds (doors total pay X) :=
  fun (A B : Agent (Option Bool) Bool) _ _ n k => by
    rw [doors_classReward, doors_classReward, doors_solvedCount, doors_solvedCount]
    exact h _ _ _ _

def drift {Obs Act : Type} (B : Agent Obs Act) (o : Obs × Rat) : Nat → B.Memory
  | 0 => B.initial
  | t + 1 => (B.act (drift B o t) o).2

theorem keepsNothing_memory {Obs Act : Type} {B : Agent Obs Act} (h : KeepsNothing B)
    (M : Member Obs Act) (o : Obs × Rat) : ∀ t, (M.run B t).2 = drift B o t
  | 0 => rfl
  | t + 1 => by
    show (B.act (M.run B t).2 _).2 = (B.act (drift B o t) o).2
    rw [keepsNothing_memory h M o t]
    exact h _ _ _

def guess (B : Agent (Option Bool) Bool) (n : Nat) : Bool :=
  (B.act (drift B (none, 0) (2 * n)) (none, 0)).1

theorem keepsNothing_tried {B : Agent (Option Bool) Bool} (h : KeepsNothing B) (b : Bool)
    (n : Nat) : tried pay B b n = guess B n := by
  unfold tried
  rw [door_ask, keepsNothing_memory h (door pay b) (none, 0)]
  rfl

theorem always_keepsNothing {Obs Act : Type} (a : Act) : KeepsNothing (always (Obs := Obs) a) :=
  fun _ _ _ => rfl

def finder : Agent (Option Bool) Bool where
  Memory := Option Bool × Bool
  initial := (none, true)
  act := fun m o =>
    match o.1 with
    | none => (m.1.getD true, (m.1, m.1.getD true))
    | some true => (true, (some m.2, m.2))
    | some false => (true, (some (!m.2), m.2))

theorem finder_round (b x : Bool) :
    (door pay b).next finder ((door pay b).next finder (Door.ask, (some b, x))) =
      (Door.ask, (some b, b)) := by
  cases b <;> rfl

theorem finder_knows (b : Bool) :
    ∀ n, ∃ x, (door pay b).run finder (2 * (n + 1)) = (Door.ask, (some b, x))
  | 0 => by cases b <;> exact ⟨_, rfl⟩
  | n + 1 => by
    obtain ⟨x, h⟩ := finder_knows b n
    refine ⟨b, ?_⟩
    show (door pay b).next finder ((door pay b).next finder
      ((door pay b).run finder (2 * (n + 1)))) = _
    rw [h]
    exact finder_round pay b x

theorem finder_solves (b : Bool) (n : Nat) :
    (doors total pay X).solves finder b (n + 1) = true := by
  obtain ⟨x, h⟩ := finder_knows pay b n
  rw [doors_solves]
  unfold tried
  rw [h]
  cases b <;> rfl

theorem doors_finder_meets (h : Fair total pay) :
    postcondition.Meets (doors total pay finder) := by
  refine postcondition_meets.mpr ⟨doors_rewardCounts total pay finder h,
    ⟨1, show 1 + 0 + 1 < 3 by decide, fun (B : Agent (Option Bool) Bool) hB k => ?_⟩,
    fun b => ⟨[], Nat.le_refl 0, fun n n' hle _ _ hs _ => ?_⟩,
    fun b n n' hle room _ hs => ?_⟩
  · show (doors total pay finder).classReward B k < (doors total pay finder).classReward finder 1
    rw [doors_classReward, doors_classReward, finder_solves, finder_solves, doors_solves,
      doors_solves, keepsNothing_tried pay hB, keepsNothing_tried pay hB]
    exact (h _ _ _ _).mpr (by cases guess B k <;> decide)
  · cases n' with
    | zero => exact (Nat.le_zero.mp hle) ▸ hs
    | succ n' => exact finder_solves ..
  · cases n' with
    | zero => exact ⟨0, Nat.le_refl 0, Nat.le_add_right _ _, (Nat.le_zero.mp hle) ▸ hs⟩
    | succ n' => exact ⟨n' + 1, Nat.le_refl _, Nat.le_add_right _ _, finder_solves ..⟩

theorem fair_sum_one : Fair List.sum 1 := by
  intro s1 s2 s3 s4
  cases s1 <;> cases s2 <;> cases s3 <;> cases s4 <;> decide +kernel

def base : Trial := doors List.sum 1 finder

theorem base_meets : postcondition.Meets base :=
  doors_finder_meets _ _ fair_sum_one

theorem postcondition_o2 : O2 postcondition := by
  refine (o2_correct _).mpr ⟨⟨base, fun _ h => nomatch h⟩, fun p hp => ?_⟩
  simp only [postcondition, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨base, always true⟩, always_keepsNothing true⟩
  · exact ⟨⟨base, finder, true, 0⟩, rfl⟩

theorem postcondition_o2Run : O2Run postcondition :=
  (o2Run_correct _).mpr ⟨base, base_meets.1, base_meets.2⟩

def unpaid : Trial := doors List.sum 0 finder

def fixed : Trial := doors List.sum 1 (always true)

def once : Agent (Option Bool) Bool where
  Memory := Nat
  initial := 0
  act := fun m _ => (m == 0, m + 1)

def forgetful : Trial := doors List.sum 1 once

theorem once_memory (M : Member (Option Bool) Bool) : ∀ t, (M.run once t).2 = t
  | 0 => rfl
  | t + 1 => congrArg (· + 1) (once_memory M t)

theorem once_misses (n : Nat) : (doors total pay X).solves once true (n + 1) = false := by
  have h : tried pay once true (n + 1) = false := by
    unfold tried
    rw [once_memory]
    rfl
  rw [doors_solves, h]
  rfl

theorem doors_sameProblem (b : Bool) (n k : Nat) : (doors total pay X).SameProblem b n k :=
  (door_ask pay b X k).trans (door_ask pay b X n).symm

theorem not_earnsMore_of_keepsNothing {w : Trial} (h : KeepsNothing w.agent) :
    ¬ earnsMoreInTime.holds w :=
  fun ⟨n, _, hn⟩ => Rat.lt_irrefl (hn w.agent h n)

theorem postcondition_o3 : O3 postcondition := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [postcondition, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine ⟨unpaid, fun h => ?_⟩
    have hlt : unpaid.classReward (always true) 0 < unpaid.classReward finder 1 :=
      (h finder (always true) (.inl rfl) (.inr (always_keepsNothing true)) 1 0).mpr (by decide)
    exact absurd hlt (by decide +kernel)
  · exact ⟨fixed, not_earnsMore_of_keepsNothing (w := fixed) (always_keepsNothing true)⟩
  · refine ⟨forgetful, fun h => ?_⟩
    obtain ⟨lapsed, few, keeps⟩ := h true
    have none : lapsed = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp few)
    have hs : forgetful.solves once true 1 = true :=
      keeps 0 1 (by decide) (by decide)
        (fun k _ _ => doors_sameProblem List.sum 1 once true 0 k) rfl
        (by rw [none]; exact List.not_mem_nil)
    exact absurd hs (by decide)
  · refine ⟨forgetful, fun h => ?_⟩
    obtain ⟨n, hn, -, hs⟩ :=
      h true 0 1 (by decide) (by decide)
        (fun k _ => doors_sameProblem List.sum 1 once true 0 k) rfl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Bool.noConfusion (hs.symm.trans (once_misses List.sum 1 once m))

theorem postcondition_o4 : O4 postcondition := (o4_correct _).mpr trivial

theorem postcondition_o5_widest : O5 postcondition .widest := o5_widest _

theorem fair_double_one : Fair (fun l => l.sum + l.sum) 1 := by
  intro s1 s2 s3 s4
  cases s1 <;> cases s2 <;> cases s3 <;> cases s4 <;> decide +kernel

def doubled : Trial := doors (fun l => l.sum + l.sum) 1 finder

theorem doubled_meets : postcondition.Meets doubled :=
  doors_finder_meets _ _ fair_double_one

theorem postcondition_not_o5_eq : ¬ O5 postcondition .eq := by
  refine not_o5_eq base_meets doubled_meets fun h => ?_
  have ht : base.total [1] = doubled.total [1] := congrArg (fun w : Trial => w.total [1]) h
  exact absurd ht (by decide +kernel)

theorem postcondition_pairs :
    ∀ c ∈ postcondition.props, OPair (Pair.whole postcondition c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨base, trivial, fun _ => base_meets.2 c hc⟩

end AcornVerif.Intent.Postcondition
