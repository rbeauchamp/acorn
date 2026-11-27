import AcornVerif.Intent.Postcondition

namespace AcornVerif.Intent.Postcondition

open LeanIntent WorldInterface

def Member.world {Obs Act : Type} (M : Member Obs Act) : World where
  State := M.State
  Obs := Obs
  Act := Act
  start := M.start
  observe := M.observe
  reward := M.reward
  available := fun _ _ => True
  step := M.step

theorem run_reaches {Obs Act : Type} (M : Member Obs Act) (A : Agent Obs Act) :
    ∀ t, (couple M.world A).Reaches neverStop t (M.run A t).1 (M.run A t).2
  | 0 => .start
  | t + 1 => .next (run_reaches M A t) rfl

def learnerKeepsSomething : Consequence Trial :=
  ⟨"the agent keeps something of its experience", .entailment, fun w => ¬ KeepsNothing w.agent⟩

theorem learnerKeepsSomething_holds : learnerKeepsSomething.HoldsOf postcondition :=
  fun _ hw hk => not_earnsMore_of_keepsNothing hk (postcondition_meets.mp hw).2.1

def solvesMoreInTime : Consequence Trial :=
  ⟨"on some attempt that leaves more later attempts before the stated attempt than the stated \
    number of lapses, the agent solves more members than any agent that keeps nothing of its \
    experience solves on any attempt", .entailment, fun w =>
    ∃ n, n + w.lapses + 1 < w.horizon ∧
      ∀ B, KeepsNothing B → ∀ k, w.solvedCount B k < w.solvedCount w.agent n⟩

theorem solvesMoreInTime_holds : solvesMoreInTime.HoldsOf postcondition :=
  fun w hw =>
    let ⟨h1, ⟨n, room, hn⟩, _, _⟩ := postcondition_meets.mp hw
    ⟨n, room, fun B hB k => (h1 w.agent B (.inl rfl) (.inr hB) n k).mp (hn B hB k)⟩

def advantageSolvedAgain : Consequence Trial :=
  ⟨"each member the agent solves on the attempt of its advantage it solves again on a later \
    attempt before the stated attempt, where the member's later attempts start from the same \
    state", .entailment, fun w =>
    ∃ n, (∀ B, KeepsNothing B → ∀ k, w.classReward B k < w.classReward w.agent n) ∧
      ∀ i, w.solves w.agent i n = true → (∀ k, n < k → w.SameProblem i n k) →
        ∃ n', n < n' ∧ n' < w.horizon ∧ w.solves w.agent i n' = true⟩

theorem advantageSolvedAgain_holds : advantageSolvedAgain.HoldsOf postcondition :=
  fun w hw =>
    let ⟨_, ⟨n, room, more⟩, _, again⟩ := postcondition_meets.mp hw
    ⟨n, more, fun i solved same =>
      let ⟨n', low, high, hs⟩ := again i n (n + 1) (Nat.le_succ n) (by omega)
        (fun k later => same k later) solved
      ⟨n', low, by omega, hs⟩⟩

def shell {Obs Act : Type} (A : Agent Obs Act) : Agent Obs Act where
  Memory := Unit
  initial := ()
  act := fun _ o => ((A.act A.initial o).1, ())

theorem shell_keepsNothing {Obs Act : Type} (A : Agent Obs Act) : KeepsNothing (shell A) :=
  fun _ _ _ => rfl

def countsSomeMember : Consequence Trial :=
  ⟨"the class counts at least one member", .entailment, fun w => w.counted ≠ []⟩

theorem countsSomeMember_holds : countsSomeMember.HoldsOf postcondition := by
  intro w hw he
  obtain ⟨n, -, hn⟩ := (postcondition_meets.mp hw).2.1
  have h := hn (shell w.agent) (shell_keepsNothing _) n
  unfold Trial.classReward at h
  rw [he] at h
  exact Rat.lt_irrefl h

theorem fixed_fails : ¬ postcondition.Meets fixed := fun h =>
  not_earnsMore_of_keepsNothing (w := fixed) (always_keepsNothing true)
    (postcondition_meets.mp h).2.1

def rulesOutFixedAgent : Consequence Trial :=
  ⟨"the trial fixed, whose agent tries the same door on every attempt, is ruled out", .entailment,
    fun w => w ≠ fixed⟩

theorem rulesOutFixedAgent_holds : rulesOutFixedAgent.HoldsOf postcondition :=
  fun _ hw he => fixed_fails (he ▸ hw)

theorem unpaid_fails : ¬ postcondition.Meets unpaid := fun h => by
  have hlt : unpaid.classReward (always true) 0 < unpaid.classReward finder 1 :=
    ((postcondition_meets.mp h).1 finder (always true) (.inl rfl)
      (.inr (always_keepsNothing true)) 1 0).mpr (by decide)
  exact absurd hlt (by decide +kernel)

def rulesOutUnpaidGoals : Consequence Trial :=
  ⟨"the trial unpaid, whose members generate no reward at their goals, is ruled out", .entailment,
    fun w => w ≠ unpaid⟩

theorem rulesOutUnpaidGoals_holds : rulesOutUnpaidGoals.HoldsOf postcondition :=
  fun _ hw he => unpaid_fails (he ▸ hw)

theorem forgetful_fails : ¬ postcondition.Meets forgetful := fun h => by
  obtain ⟨lapsed, few, keeps⟩ := (postcondition_meets.mp h).2.2.1 true
  have none : lapsed = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp few)
  exact absurd (keeps 0 1 (by decide) (by decide)
    (fun k _ _ => doors_sameProblem List.sum 1 once true 0 k) rfl
    (by rw [none]; exact List.not_mem_nil)) (by decide)

def rulesOutSolvingOnce : Consequence Trial :=
  ⟨"the trial forgetful, whose agent solves a member on its first attempt and never again, is \
    ruled out", .entailment, fun w => w ≠ forgetful⟩

theorem rulesOutSolvingOnce_holds : rulesOutSolvingOnce.HoldsOf postcondition :=
  fun _ hw he => forgetful_fails (he ▸ hw)

def flash : Agent (Option Bool) Bool where
  Memory := Nat × Option Bool
  initial := (0, none)
  act := fun m o =>
    (if m.1 == 0 then true else if m.1 == 2 then m.2.getD true else !(m.2.getD true),
      (m.1 + 1, if m.1 == 1 then o.1 else m.2))

theorem flash_memory (pay : Rat) (b : Bool) :
    ∀ t, ((door pay b).run flash (t + 2)).2 = (t + 2, some b)
  | 0 => by cases b <;> rfl
  | t + 1 => by
    have ih := flash_memory pay b t
    show (flash.act ((door pay b).run flash (t + 2)).2 _).2 = _
    rw [ih]
    rfl

theorem flash_hits (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (b : Bool) : (doors total pay X).solves flash b 1 = true := by
  rw [doors_solves]
  cases b <;> rfl

theorem flash_misses (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (b : Bool) (n : Nat) : (doors total pay X).solves flash b (n + 2) = false := by
  have h : tried pay flash b (n + 2) = !b := by
    unfold tried
    have e : 2 * (n + 2) = 2 * n + 2 + 2 := by omega
    rw [e, flash_memory]
    rfl
  rw [doors_solves, h]
  cases b <;> rfl

def flashy : Trial := doors List.sum 1 flash

theorem flashy_earnsMore : earnsMoreInTime.holds flashy := by
  refine ⟨1, show 1 + 0 + 1 < 3 by decide, fun (B : Agent (Option Bool) Bool) hB k => ?_⟩
  show (doors List.sum 1 flash).classReward B k < (doors List.sum 1 flash).classReward flash 1
  rw [doors_classReward, doors_classReward, flash_hits, flash_hits, doors_solves, doors_solves,
    keepsNothing_tried 1 hB, keepsNothing_tried 1 hB]
  exact (fair_sum_one _ _ _ _).mpr (by cases guess B k <;> decide)

theorem flashy_fails : ¬ postcondition.Meets flashy := fun h => by
  obtain ⟨lapsed, few, keeps⟩ := (postcondition_meets.mp h).2.2.1 true
  have none : lapsed = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp few)
  have again := keeps 1 2 (by decide) (by decide)
    (fun k _ _ => doors_sameProblem List.sum 1 flash true 1 k) (flash_hits List.sum 1 flash true)
    (by rw [none]; exact List.not_mem_nil)
  exact Bool.noConfusion (again.symm.trans (flash_misses List.sum 1 flash true 0))

def rulesOutAdvantageOnce : Consequence Trial :=
  ⟨"the trial flashy, whose agent earns the advantage on its second attempt and solves no member \
    afterwards, is ruled out", .entailment, fun w => w ≠ flashy⟩

theorem rulesOutAdvantageOnce_holds : rulesOutAdvantageOnce.HoldsOf postcondition :=
  fun _ hw he => flashy_fails (he ▸ hw)

def uncounted : Trial := { base with counted := [] }

theorem uncounted_fails : ¬ postcondition.Meets uncounted := fun h =>
  countsSomeMember_holds _ h rfl

def noFirstAttemptAdvantage : Consequence Trial :=
  ⟨"on its first attempt the agent may earn no more than an agent that keeps nothing of its \
    experience", .possibility, fun w =>
    ∃ B, KeepsNothing B ∧ ¬ w.classReward B 0 < w.classReward w.agent 0⟩

theorem noFirstAttemptAdvantage_holds : noFirstAttemptAdvantage.HoldsOf postcondition :=
  ⟨base, base_meets, always true, always_keepsNothing true, by decide +kernel⟩

def firstAttemptMayFail : Consequence Trial :=
  ⟨"the agent may fail to solve a member on its first attempt", .possibility, fun w =>
    ∃ i, i ∈ w.counted ∧ w.solves w.agent i 0 = false⟩

theorem firstAttemptMayFail_holds : firstAttemptMayFail.HoldsOf postcondition :=
  ⟨base, base_meets, false, .tail _ (.head _), rfl⟩

theorem keepsSolving_of_lapses (w : Trial) (covered : w.horizon ≤ w.lapses + 1) :
    keepsSolving.holds w :=
  fun _ => ⟨List.range' 1 (w.horizon - 1), by rw [List.length_range']; omega,
    fun n n' hle before _ hs out => by
      have zero : n' = 0 := by
        rcases Nat.eq_zero_or_pos n' with h | h
        · exact h
        · exact absurd (List.mem_range'_1.mpr ⟨h, by omega⟩) out
      subst zero
      have first : n = 0 := Nat.le_zero.mp hle
      subst first
      exact hs⟩

theorem learnsAgain_of_lapses (w : Trial) (covered : w.horizon ≤ w.lapses + 1) :
    learnsAgain.holds w :=
  fun _ n n' hle room _ hs => by
    have zero : n' = 0 := by omega
    subst zero
    have first : n = 0 := Nat.le_zero.mp hle
    subst first
    exact ⟨0, Nat.le_refl 0, Nat.zero_le _, hs⟩

def hurried : Trial := { base with horizon := 2 }

theorem hurried_fails : ¬ postcondition.Meets hurried := fun h => by
  obtain ⟨n, room, more⟩ := (postcondition_meets.mp h).2.1
  have small : n + 0 + 1 < 2 := room
  have first : n = 0 := by omega
  subst first
  exact absurd (more (always true) (always_keepsNothing true) 0) (by decide +kernel)

def rulesOutLateAdvantage : Consequence Trial :=
  ⟨"the trial hurried, whose agent earns the advantage on the last attempt before the stated \
    attempt, is ruled out", .entailment, fun w => w ≠ hurried⟩

theorem rulesOutLateAdvantage_holds : rulesOutLateAdvantage.HoldsOf postcondition :=
  fun _ hw he => hurried_fails (he ▸ hw)

theorem unmet_of_lapses (w : Trial) (covered : w.horizon ≤ w.lapses + 1) :
    ¬ postcondition.Meets w := fun h => by
  obtain ⟨n, room, -⟩ := (postcondition_meets.mp h).2.1
  omega

end AcornVerif.Intent.Postcondition
