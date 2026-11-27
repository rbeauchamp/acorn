import AcornVerif.Intent.BigClass
import AcornVerif.Intent.PostconditionConsequences

namespace AcornVerif.Intent.BigClass

open LeanIntent WorldInterface Postcondition

theorem reads_class (w : Trial) (A : Agent w.Obs w.Act) (f : List Rat → Rat)
    (horizon lapses : Nat) :
    bigClass.Meets { w with agent := A, total := f, horizon := horizon, lapses := lapses } ↔
      bigClass.Meets w := by
  rw [bigClass_meets, bigClass_meets]
  exact Iff.rfl

def noFrozenAgentSolvesAll : Consequence Trial :=
  ⟨"no agent that keeps nothing of its experience solves every counted member on an attempt",
    .entailment, fun w =>
    ∀ B : Agent w.Obs w.Act, KeepsNothing B → ∀ n, w.solvedCount B n < w.counted.length⟩

theorem noFrozenAgentSolvesAll_holds : noFrozenAgentSolvesAll.HoldsOf bigClass :=
  fun _ hw B hB n =>
    let ⟨_, hk, h⟩ := (bigClass_meets.mp hw).2.2.1
    Nat.lt_of_le_of_lt (h B hB n) hk

def hasCountedMember : Consequence Trial :=
  ⟨"the class counts at least one member", .entailment, fun w => w.counted ≠ []⟩

theorem hasCountedMember_holds : hasCountedMember.HoldsOf bigClass := by
  intro w hw he
  obtain ⟨k, hk, _⟩ := (bigClass_meets.mp hw).2.2.1
  rw [he] at hk
  exact Nat.not_lt_zero k hk

def script {Obs Act : Type} (R : Member Obs Act) (A : Agent Obs Act) : Agent Obs Act where
  Memory := Nat
  initial := 0
  act := fun t _ => ((A.act (R.run A t).2 (given R A t)).1, t + 1)

theorem script_keepsNothing {Obs Act : Type} (R : Member Obs Act) (A : Agent Obs Act) :
    KeepsNothing (script R A) :=
  fun _ _ _ => rfl

theorem script_memory {Obs Act : Type} (R : Member Obs Act) (A : Agent Obs Act)
    (M : Member Obs Act) : ∀ t, (M.run (script R A) t).2 = t
  | 0 => rfl
  | t + 1 => congrArg (· + 1) (script_memory R A M t)

theorem script_follows {Obs Act : Type} (R M : Member Obs Act) (A : Agent Obs Act)
    (hM : ∀ t, (∀ u, u ≤ t → M.goal (M.run A u).1 = false) → given M A t = given R A t) :
    ∀ t, (∀ u, u < t → M.goal (M.run A u).1 = false) →
      (M.run (script R A) t).1 = (M.run A t).1 ∧ (M.run A t).2 = (R.run A t).2
  | 0, _ => ⟨rfl, rfl⟩
  | t + 1, h => by
    obtain ⟨ihs, ihm⟩ := script_follows R M A hM t (fun u hu => h u (Nat.lt_succ_of_lt hu))
    have hg : given M A t = given R A t := hM t (fun u hu => h u (Nat.lt_succ_of_le hu))
    have hmem := script_memory R A M t
    refine ⟨?_, ?_⟩
    · show M.step (M.run (script R A) t).1
          ((script R A).act (M.run (script R A) t).2
            (M.observe (M.run (script R A) t).1, M.reward (M.run (script R A) t).1)).1 =
        M.step (M.run A t).1 (A.act (M.run A t).2 (given M A t)).1
      rw [hmem, ihs, ihm, hg]
      rfl
    · show (A.act (M.run A t).2 (given M A t)).2 = (A.act (R.run A t).2 (given R A t)).2
      rw [ihm, hg]

theorem script_meets {Obs Act : Type} (R M : Member Obs Act) (A : Agent Obs Act)
    (hM : ∀ t, (∀ u, u ≤ t → M.goal (M.run A u).1 = false) → given M A t = given R A t)
    (t : Nat) :
    M.goal (M.run A t).1 = true →
      ∃ t', t' ≤ t ∧ M.goal (M.run (script R A) t').1 = true := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    rcases Classical.em (∀ u, u < t → M.goal (M.run A u).1 = false) with hall | hall
    · exact ⟨t, Nat.le_refl t, by rw [(script_follows R M A hM t hall).1]; exact ht⟩
    · have hex : ∃ u, u < t ∧ M.goal (M.run A u).1 = true := by
        apply Classical.byContradiction
        intro hne
        apply hall
        intro u hu
        cases hgu : M.goal (M.run A u).1
        · rfl
        · exact absurd ⟨u, hu, hgu⟩ hne
      obtain ⟨u, hu, hgu⟩ := hex
      obtain ⟨t', ht', hg'⟩ := ih u hu hgu
      exact ⟨t', Nat.le_trans ht' (Nat.le_of_lt hu), hg'⟩

theorem solves_first_iff (w : Trial) (A : Agent w.Obs w.Act) (i : w.Index) :
    w.solves A i 0 = true ↔
      ∃ t, t < w.length ∧ (w.member i).goal (w.stateAt A i t) = true := by
  simp only [Trial.solves, Trial.attemptTimes, List.any_eq_true, List.mem_map, List.mem_range,
    Nat.mul_zero, Nat.zero_add]
  constructor
  · intro ⟨t, ⟨k, hk, hkt⟩, hg⟩
    exact ⟨t, hkt ▸ hk, hg⟩
  · intro ⟨t, ht, hg⟩
    exact ⟨t, ⟨t, ht, rfl⟩, hg⟩

theorem filter_length_mono {α : Type} (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    ∀ l : List α, (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl _
  | x :: l => by
    have ih := filter_length_mono p q h l
    cases hp : p x
    · cases hq : q x <;> simp only [List.filter, hp, hq, List.length_cons] <;> omega
    · have hq := h x hp
      simp only [List.filter, hp, hq, List.length_cons]
      omega

def firstAttemptSmall : Consequence Trial :=
  ⟨"on its first attempt, every agent solves at most a number of the counted members that is \
    smaller than their count", .entailment, fun w =>
    ∃ k, k < w.counted.length ∧ ∀ A : Agent w.Obs w.Act, w.solvedCount A 0 ≤ k⟩

theorem firstAttemptSmall_holds : firstAttemptSmall.HoldsOf bigClass := by
  intro w hw
  obtain ⟨_, ⟨R, hR⟩, ⟨k, hk, hfrozen⟩, _, _⟩ := bigClass_meets.mp hw
  refine ⟨k, hk, fun A => Nat.le_trans ?_ (hfrozen (script R A) (script_keepsNothing R A) 0)⟩
  show (w.counted.filter fun i => w.solves A i 0).length ≤
    (w.counted.filter fun i => w.solves (script R A) i 0).length
  apply filter_length_mono
  intro i hi
  obtain ⟨t, ht, hg⟩ := (solves_first_iff w A i).mp hi
  obtain ⟨t', ht', hg'⟩ := script_meets R (w.member i) A (fun t h => hR A i t h) t hg
  exact (solves_first_iff w (script R A) i).mpr ⟨t', Nat.lt_of_le_of_lt ht' ht, hg'⟩

theorem unreachable_fails : ¬ bigClass.Meets unreachable := fun h => by
  obtain ⟨acts, _, hg⟩ := (bigClass_meets.mp h).1 finder true 0
  have hf : false = true := hg
  exact Bool.noConfusion hf

def rulesOutUnreachableGoals : Consequence Trial :=
  ⟨"the trial unreachable, whose members' goals no state meets, is ruled out", .entailment,
    fun w => w ≠ unreachable⟩

theorem rulesOutUnreachableGoals_holds : rulesOutUnreachableGoals.HoldsOf bigClass :=
  fun _ hw he => unreachable_fails (he ▸ hw)

theorem revealing_fails : ¬ bigClass.Meets revealing := fun h => by
  obtain ⟨R, hR⟩ := (bigClass_meets.mp h).2.1
  have e := (hR finder true 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)).trans
    (hR finder false 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)).symm
  have e' : some true = some false := congrArg Prod.fst e
  exact absurd e' (by decide)

def rulesOutShownGoals : Consequence Trial :=
  ⟨"the trial revealing, whose members show their door before it is tried, is ruled out",
    .entailment, fun w => w ≠ revealing⟩

theorem rulesOutShownGoals_holds : rulesOutShownGoals.HoldsOf bigClass :=
  fun _ hw he => revealing_fails (he ▸ hw)

theorem sameDoor_fails : ¬ bigClass.Meets sameDoor := fun h => by
  obtain ⟨k, hk, hf⟩ := (bigClass_meets.mp h).2.2.1
  have h2 : sameDoor.solvedCount (always true) 0 ≤ k :=
    hf (always true) (always_keepsNothing true) 0
  have hk' : k < 2 := hk
  have h3 : sameDoor.solvedCount (always true) 0 = 2 := by decide
  omega

def rulesOutOneAnswer : Consequence Trial :=
  ⟨"the trial sameDoor, whose members are all solved by trying one door, is ruled out",
    .entailment, fun w => w ≠ sameDoor⟩

theorem rulesOutOneAnswer_holds : rulesOutOneAnswer.HoldsOf bigClass :=
  fun _ hw he => sameDoor_fails (he ▸ hw)

theorem hidden_fails : ¬ bigClass.Meets hidden := fun h => by
  obtain ⟨signal, hs⟩ := (bigClass_meets.mp h).2.2.2.1
  have h1 : signal (some false, 0) = true := hs (always true) true 1
  have h2 : signal (some false, 0) = false := hs (always true) false 1
  exact Bool.noConfusion (h1.symm.trans h2)

def rulesOutHiddenSuccess : Consequence Trial :=
  ⟨"the trial hidden, whose members show and pay the same whether or not their goal is met, is \
    ruled out", .entailment, fun w => w ≠ hidden⟩

theorem rulesOutHiddenSuccess_holds : rulesOutHiddenSuccess.HoldsOf bigClass :=
  fun _ hw he => hidden_fails (he ▸ hw)

theorem stuck_fails : ¬ bigClass.Meets stuck := fun h => by
  have e : Door.miss = Door.ask := (bigClass_meets.mp h).2.2.2.2 finder true 1
  exact absurd e (by decide)

def rulesOutNoRecurrence : Consequence Trial :=
  ⟨"the trial stuck, whose members never return to the state they start in, is ruled out",
    .entailment, fun w => w ≠ stuck⟩

theorem rulesOutNoRecurrence_holds : rulesOutNoRecurrence.HoldsOf bigClass :=
  fun _ hw he => stuck_fails (he ▸ hw)

def agentMayKeepNothing : Consequence Trial :=
  ⟨"a class may meet these conditions whatever its agent, even one that keeps nothing of its \
    experience", .possibility, fun w => KeepsNothing w.agent⟩

theorem agentMayKeepNothing_holds : agentMayKeepNothing.HoldsOf bigClass :=
  ⟨fixed, doors_big List.sum 1 (always true), always_keepsNothing true⟩

theorem frozenShareSmall_of_postcondition {w : Trial} (h : postcondition.Meets w) :
    frozenShareSmall.holds w := by
  obtain ⟨n, -, hn⟩ := solvesMoreInTime_holds w h
  have hle : w.solvedCount w.agent n ≤ w.counted.length := List.length_filter_le _ _
  have hpos := hn (shell w.agent) (shell_keepsNothing _) 0
  refine ⟨w.solvedCount w.agent n - 1, by omega, fun B hB k => ?_⟩
  have hlt := hn B hB k
  omega

theorem sameProblem_of_big {w : Trial} (hb : bigClass.Meets w) (i : w.Index) (n k : Nat) :
    w.SameProblem i n k :=
  ((bigClass_meets.mp hb).2.2.2.2 w.agent i k).trans
    ((bigClass_meets.mp hb).2.2.2.2 w.agent i n).symm

theorem retention_unconditional {w : Trial} (hb : bigClass.Meets w) (hk : keepsSolving.holds w)
    (i : w.Index) :
    ∃ lapsed : List Nat, lapsed.length ≤ w.lapses ∧ ∀ n n', n ≤ n' → n' < w.horizon →
      w.solves w.agent i n = true → n' ∉ lapsed → w.solves w.agent i n' = true := by
  obtain ⟨lapsed, few, keeps⟩ := hk i
  exact ⟨lapsed, few, fun n n' hle before hs out =>
    keeps n n' hle before (fun k _ _ => sameProblem_of_big hb i n k) hs out⟩

theorem advantage_solved_again {w : Trial} (hb : bigClass.Meets w)
    (hp : postcondition.Meets w) :
    ∃ n, (∀ B, KeepsNothing B → ∀ k, w.classReward B k < w.classReward w.agent n) ∧
      ∀ i, w.solves w.agent i n = true →
        ∃ n', n < n' ∧ n' < w.horizon ∧ w.solves w.agent i n' = true := by
  obtain ⟨n, more, again⟩ := advantageSolvedAgain_holds w hp
  exact ⟨n, more, fun i solved => again i solved fun k _ => sameProblem_of_big hb i n k⟩

def Served (w : Trial) : Prop :=
  ∃ A : Agent w.Obs w.Act, postcondition.Meets { w with agent := A }

theorem doors_served (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (h : Fair total pay) : Served (doors total pay X) :=
  ⟨finder, doors_finder_meets total pay h⟩

end AcornVerif.Intent.BigClass
