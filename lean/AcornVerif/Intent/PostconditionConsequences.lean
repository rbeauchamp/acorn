/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.Postcondition
import AcornVerif.Intent.WorldInterfaceConsequences

/-!
# The consequences of the record of the postcondition

Each consequence of `AcornVerif.Intent.Postcondition.postcondition` stated here is proved to hold of
the record: what it requires of every trial that meets it, the trials it rules out, each beside
`base`, the trial that differs from it only where it attacks and meets the record, and what the
record still allows. `postconditionExplained` gives the record's plain words and the consequences
shown with it; the status of every consequence is in the record's confirmation file,
`lean/AcornVerif/Intent/Postcondition.md`.

One thing is not proved here, and it is a consequence labelled unproved, never a pass: a class
whose members never start two attempts from the same state asks neither solving again nor learning
again, since `keepsSolving` and `learnsAgain` then hold of every agent. No trial is exhibited that
meets the record while its agent solves a member once and never again, and no trial of such a
class is refuted. In a
class that meets the record of contract 2 every attempt starts from the same state, so there solving
again is asked with no condition on the member's attempts
(`AcornVerif.Intent.BigClass.retention_unconditional`).

The record ties the two numbers a class names, its horizon and its lapses, through the attempt of
the advantage, which leaves more later attempts before the horizon than the lapses. So each
member the agent solves on that attempt it solves again on a later one, where that member's
later attempts start from the same state (`advantageSolvedAgain`), as they do in every class
that meets the record of contract 2 (`AcornVerif.Intent.BigClass.advantage_solved_again`). A
two-door agent that earns its advantage once and solves nothing afterwards fails the record
(`rulesOutAdvantageOnce`), and so does the class whose horizon comes right after the attempt of
its agent's advantage (`rulesOutLateAdvantage`). A class that allows as many lapses as it has
attempts before its horizon, less one, asks no solving again, since `keepsSolving` then holds of
every agent (`keepsSolving_of_lapses`); no agent meets the record in such a class, because no
attempt leaves that room (`unmet_of_lapses`). The promise of solving again reads nothing from the
horizon on: the trial `halted` meets the record with an agent that solves no member from the
horizon on (`mayStopAtHorizon`). The lemma on reward and the comparison of the advantage read every
attempt, and learning again names no attempt.

An agent that stores what it is given and never reads it acts as an agent that keeps nothing of its
experience acts, so it fails the record in every class (`actionReadsMemory`), though
`KeepsNothing` does not hold of it.

The fourth property, `learnsAgain`, asks something only where a member's attempts leave the state
of a solved attempt and come back to it for good. In the detour class the two agents below make the
member's attempts do so: `quitting`, whose agent never solves the member again, fails the property
(`quitting_fails`), and `returning`, whose agent misses the first attempt back and solves from the
next one on, has it (`returning_learnsAgain`, with `returning_leaves` for what the property asks of
it). Each of the two agents keeps nothing of its experience (`quits_keepsNothing`,
`returns_keepsNothing`), so neither trial meets the whole record: `returning` is a model of the
fourth property and `quitting` a refutation of it, and neither is a model of the record.
`PromptlyAgain` is the form the property had before the record was compared with its blind
readings, kept so that what changed is a theorem: `returning` fails that form
(`returning_not_promptly`), and wherever every attempt of every member starts from one state the
record asks the same in both forms (`meets_iff_promptly`).

Two checks of lean-intent were not run:

* Its degenerate-subject and trivial-witness checks cover a subject in `Type`, and `Trial` carries
  its own types, so it lives one universe higher (rbeauchamp/lean-intent#43). The interim class for
  a plain value asks for its empty value and `default`, and `Trial` has neither. The nearest
  subjects are attacked by hand and both fail the record: a class that counts no member
  (`countsSomeMember_holds`, `uncounted_fails`), and an agent that keeps nothing of its experience,
  which a script of timed actions is, in every class (`not_earnsMore_of_keepsNothing`,
  `learnerKeepsSomething_holds`).
* Its cone exclusion: no implementation of this record is named yet, and the record's module
  imports the module of its subject's types and, through it, contract 1's record and the bridge to
  lean-intent only, so none of the modules that define the kernel's worlds, classes and visits, or
  the executing agent, is in its imports.

The pair whose input is the class of worlds is not discharged here. With no domain hypothesis the
record admits classes that no agent can serve, as `uncounted_fails` shows, so that pair needs the
preconditions of contract 2. The record of contract 2, `AcornVerif.Intent.BigClass.bigClass`, states
them, and the module of its consequences states the pair (`AcornVerif.Intent.BigClass.Served`) and
leaves it unproved for every class but the two-door ones. What is proved here is the pair with the
trivial input (`postcondition_pairs`) and that one agent, `finder`, serves every two-door class
with a fair aggregation and payment (`doors_finder_meets`).
-/

namespace AcornVerif.Intent.Postcondition

open LeanIntent WorldInterface

/-! ## The run is contract 1's -/

/-- The member `M` as a world of contract 1, with every action available at every state. -/
def Member.world {Obs Act : Type} (M : Member Obs Act) : World where
  State := M.State
  Obs := Obs
  Act := Act
  start := M.start
  observe := M.observe
  reward := M.reward
  available := fun _ _ => True
  step := M.step

/-- **The run the record computes with is contract 1's faithful run, never stopped.** After any
number of steps, the faithful run of contract 1 of a member's world and an agent, sent no stop
request, has reached the state and the memory that `Member.run` gives. -/
theorem run_reaches {Obs Act : Type} (M : Member Obs Act) (A : Agent Obs Act) :
    ∀ t, (couple M.world A).Reaches neverStop t (M.run A t).1 (M.run A t).2
  | 0 => .start
  | t + 1 => .next (run_reaches M A t) rfl

/-! ## Counting -/

/-- A list of numbers with no repeat, each of which a function that tells them apart sends into
another list, is no longer than that list. -/
theorem length_le_of_injective {f : Nat → Nat} (inj : ∀ a b, f a = f b → a = b) :
    ∀ {l₁ l₂ : List Nat}, l₁.Nodup → (∀ a ∈ l₁, f a ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, l₂, nodup, sub => by
    have ha : f a ∈ l₂ := sub a (List.mem_cons_self ..)
    have hl := List.nodup_cons.mp nodup
    have ih := length_le_of_injective inj (l₂ := l₂.erase (f a)) hl.2 fun b hb =>
      (List.mem_erase_of_ne (fun (e : f b = f a) => hl.1 (inj b a e ▸ hb))).mpr
        (sub b (List.mem_cons_of_mem _ hb))
    rw [List.length_erase_of_mem ha] at ih
    have pos : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- Of any run of attempts one longer than a list of lapses, one is not in the list. -/
theorem exists_not_lapsed (lapsed : List Nat) (from_ : Nat) :
    ∃ d, d ≤ lapsed.length ∧ from_ + d ∉ lapsed := by
  refine Classical.byContradiction fun none => ?_
  have all : ∀ d ∈ List.range (lapsed.length + 1), from_ + d ∈ lapsed := fun d hd =>
    Classical.byContradiction fun out =>
      none ⟨d, Nat.le_of_lt_succ (List.mem_range.mp hd), out⟩
  have := length_le_of_injective (f := (from_ + ·))
    (fun a b (e : from_ + a = from_ + b) => by omega) List.nodup_range all
  rw [List.length_range] at this
  omega

/-! ## What the record requires -/

/-- **The agent keeps something of its experience.** -/
def learnerKeepsSomething : Consequence Trial :=
  ⟨"the agent keeps something of its experience", .entailment, fun w => ¬ KeepsNothing w.agent⟩

theorem learnerKeepsSomething_holds : learnerKeepsSomething.HoldsOf postcondition :=
  fun _ hw hk => not_earnsMore_of_keepsNothing hk (postcondition_meets.mp hw).2.1

/-- **The promise about reward is a promise about members solved.** On some attempt that leaves
more later attempts before the horizon than the lapses, the agent solves more of the counted
members than any agent that keeps nothing of its experience solves on any attempt. -/
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

/-- **Before the horizon the agent solves more members than an agent that keeps nothing.** On some
attempt before the class's horizon the agent solves more of the counted members than any agent that
keeps nothing of its experience solves on any attempt. This is `solvesMoreInTime` without the room
it asks after that attempt. -/
def solvesMoreBeforeHorizon : Consequence Trial :=
  ⟨"on some attempt before the stated attempt, the agent solves more members than any agent that \
    keeps nothing of its experience solves on any attempt", .entailment, fun w =>
    ∃ n, n < w.horizon ∧ ∀ B, KeepsNothing B → ∀ k, w.solvedCount B k < w.solvedCount w.agent n⟩

theorem solvesMoreBeforeHorizon_holds : solvesMoreBeforeHorizon.HoldsOf postcondition :=
  fun w hw =>
    let ⟨n, room, more⟩ := solvesMoreInTime_holds w hw
    ⟨n, by omega, more⟩

/-- **The members solved on the attempt of the advantage are solved again.** On some attempt the
agent earns more across the class than any agent that keeps nothing of its experience earns on
any attempt, and each member it solves on that attempt it solves again on a later attempt before
the horizon, where that member's later attempts start from the state that attempt started from. -/
def advantageSolvedAgain : Consequence Trial :=
  ⟨"each member the agent solves on the attempt of its advantage it solves again on a later \
    attempt before the stated attempt, where the member's later attempts start from the same \
    state", .entailment, fun w =>
    ∃ n, (∀ B, KeepsNothing B → ∀ k, w.classReward B k < w.classReward w.agent n) ∧
      ∀ i, w.solves w.agent i n = true → (∀ k, n < k → w.SameProblem i n k) →
        ∃ n', n < n' ∧ n' < w.horizon ∧ w.solves w.agent i n' = true⟩

theorem advantageSolvedAgain_holds : advantageSolvedAgain.HoldsOf postcondition :=
  fun w hw =>
    let ⟨_, ⟨n, room, more⟩, keeps, _⟩ := postcondition_meets.mp hw
    ⟨n, more, fun i solved same => by
      obtain ⟨lapsed, few, kept⟩ := keeps i
      obtain ⟨d, short, out⟩ := exists_not_lapsed lapsed (n + 1)
      refine ⟨n + 1 + d, by omega, by omega, kept n (n + 1 + d) (by omega) (by omega)
        (fun k low _ => ?_) solved out⟩
      rcases Nat.eq_or_lt_of_le low with rfl | later
      · rfl
      · exact same k later⟩

/-- The agent that answers each thing it is given as `A` answers it from its initial memory, and
keeps nothing of its experience. -/
def shell {Obs Act : Type} (A : Agent Obs Act) : Agent Obs Act where
  Memory := Unit
  initial := ()
  act := fun _ o => ((A.act A.initial o).1, ())

theorem shell_keepsNothing {Obs Act : Type} (A : Agent Obs Act) : KeepsNothing (shell A) :=
  fun _ _ _ => rfl

/-- **The class counts at least one member.** With no member counted, every agent earns nothing
across the class on every attempt, so the agent earns no more than an agent that keeps nothing. -/
def countsSomeMember : Consequence Trial :=
  ⟨"the class counts at least one member", .entailment, fun w => w.counted ≠ []⟩

theorem countsSomeMember_holds : countsSomeMember.HoldsOf postcondition := by
  intro w hw he
  obtain ⟨n, -, hn⟩ := (postcondition_meets.mp hw).2.1
  have h := hn (shell w.agent) (shell_keepsNothing _) n
  unfold Trial.classReward at h
  rw [he] at h
  exact Rat.lt_irrefl h

/-! ## What the record rules out -/

theorem fixed_fails : ¬ postcondition.Meets fixed := fun h =>
  not_earnsMore_of_keepsNothing (w := fixed) (always_keepsNothing true)
    (postcondition_meets.mp h).2.1

/-- **An agent that always acts the same is ruled out**: the trial `fixed`, whose agent tries the
first door on every attempt. Its neighbour is `base`. -/
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

/-- **A class whose reward does not show its goals is ruled out**: the trial `unpaid`, whose members
pay nothing when their door is tried. Its neighbour is `base`. -/
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

/-- **Solving a member once and never again is ruled out**, where the member's attempts start from
the same state, a later attempt comes before the class's horizon and the class allows no lapse:
the trial `forgetful`. Its neighbour is `base`. -/
def rulesOutSolvingOnce : Consequence Trial :=
  ⟨"the trial forgetful, whose agent solves a member on its first attempt and never again, is \
    ruled out", .entailment, fun w => w ≠ forgetful⟩

theorem rulesOutSolvingOnce_holds : rulesOutSolvingOnce.HoldsOf postcondition :=
  fun _ hw he => forgetful_fails (he ▸ hw)

/-- An agent that tries the first door on its first attempt, the member's door on its second
attempt, and the other door ever after. Its memory counts its steps and keeps the door the first
attempt showed. -/
def flash : Agent (Option Bool) Bool where
  Memory := Nat × Option Bool
  initial := (0, none)
  act := fun m o =>
    (if m.1 == 0 then true else if m.1 == 2 then m.2.getD true else !(m.2.getD true),
      (m.1 + 1, if m.1 == 1 then o.1 else m.2))

/-- From its second attempt on, `flash` has counted its steps and holds the member's door. -/
theorem flash_memory (pay : Rat) (b : Bool) :
    ∀ t, ((door pay b).run flash (t + 2)).2 = (t + 2, some b)
  | 0 => by cases b <;> rfl
  | t + 1 => by
    have ih := flash_memory pay b t
    show (flash.act ((door pay b).run flash (t + 2)).2 _).2 = _
    rw [ih]
    rfl

/-- On its second attempt `flash` solves each member of a two-door class. -/
theorem flash_hits (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (b : Bool) : (doors total pay X).solves flash b 1 = true := by
  rw [doors_solves]
  cases b <;> rfl

/-- From its third attempt on `flash` solves no member of a two-door class. -/
theorem flash_misses (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (b : Bool) (n : Nat) : (doors total pay X).solves flash b (n + 2) = false := by
  have h : tried pay flash b (n + 2) = !b := by
    unfold tried
    have e : 2 * (n + 2) = 2 * n + 2 + 2 := by omega
    rw [e, flash_memory]
    rfl
  rw [doors_solves, h]
  cases b <;> rfl

/-- `base` whose agent is `flash`: it earns the advantage on its second attempt and solves no
member afterwards. -/
def flashy : Trial := doors List.sum 1 flash

/-- `flashy` meets the record's property on the advantage: on its second attempt its agent earns
more than any agent that keeps nothing of its experience, with a later attempt left before the
horizon. -/
theorem flashy_earnsMore : earnsMoreInTime.holds flashy := by
  refine ⟨1, show 1 + 0 + 1 < 3 by decide, fun (B : Agent (Option Bool) Bool) hB k => ?_⟩
  show (doors List.sum 1 flash).classReward B k < (doors List.sum 1 flash).classReward flash 1
  rw [doors_classReward, doors_classReward, flash_hits, flash_hits, doors_solves, doors_solves,
    keepsNothing_tried 1 hB, keepsNothing_tried 1 hB]
  exact (fair_sum_one _ _ _ _).mpr (by cases guess B k <;> decide)

/-- `flashy` fails the record: it solves the first member on its second attempt and not on its
third, which comes before the horizon, and the class allows no lapse. -/
theorem flashy_fails : ¬ postcondition.Meets flashy := fun h => by
  obtain ⟨lapsed, few, keeps⟩ := (postcondition_meets.mp h).2.2.1 true
  have none : lapsed = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp few)
  have again := keeps 1 2 (by decide) (by decide)
    (fun k _ _ => doors_sameProblem List.sum 1 flash true 1 k) (flash_hits List.sum 1 flash true)
    (by rw [none]; exact List.not_mem_nil)
  exact Bool.noConfusion (again.symm.trans (flash_misses List.sum 1 flash true 0))

/-- **An advantage earned once and never repeated is ruled out**: the trial `flashy`, whose agent
earns more than every agent that keeps nothing on its second attempt and solves no member from
its third attempt on. It meets the record's first two properties (`doors_rewardCounts`,
`flashy_earnsMore`) and fails by `keepsSolving`. Its neighbour is `base`. -/
def rulesOutAdvantageOnce : Consequence Trial :=
  ⟨"the trial flashy, whose agent earns the advantage on its second attempt and solves no member \
    afterwards, is ruled out", .entailment, fun w => w ≠ flashy⟩

theorem rulesOutAdvantageOnce_holds : rulesOutAdvantageOnce.HoldsOf postcondition :=
  fun _ hw he => flashy_fails (he ▸ hw)

/-- `base` with no member counted. -/
def uncounted : Trial := { base with counted := [] }

theorem uncounted_fails : ¬ postcondition.Meets uncounted := fun h =>
  countsSomeMember_holds _ h rfl

/-! ## What the record still allows -/

/-- **No advantage on a first attempt**: some trial that meets the record has an agent that, on its
first attempt, earns no more across the class than an agent that keeps nothing of its experience. -/
def noFirstAttemptAdvantage : Consequence Trial :=
  ⟨"on its first attempt the agent may earn no more than an agent that keeps nothing of its \
    experience", .possibility, fun w =>
    ∃ B, KeepsNothing B ∧ ¬ w.classReward B 0 < w.classReward w.agent 0⟩

theorem noFirstAttemptAdvantage_holds : noFirstAttemptAdvantage.HoldsOf postcondition :=
  ⟨base, base_meets, always true, always_keepsNothing true, by decide +kernel⟩

/-- **A member may go unsolved on a first attempt**: some trial that meets the record has an agent
that does not solve one of the counted members on its first attempt. -/
def firstAttemptMayFail : Consequence Trial :=
  ⟨"the agent may fail to solve a member on its first attempt", .possibility, fun w =>
    ∃ i, i ∈ w.counted ∧ w.solves w.agent i 0 = false⟩

theorem firstAttemptMayFail_holds : firstAttemptMayFail.HoldsOf postcondition :=
  ⟨base, base_meets, false, .tail _ (.head _), rfl⟩

/-- **A class whose lapses cover its later attempts asks no solving again.** Where a class allows
as many lapses as it has attempts before its horizon, less one, `keepsSolving` holds of every
agent: every attempt before the horizon but the first may be a lapse, and the first attempt is
later than none. -/
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

/-- `base` with its promises read over its first two attempts only. -/
def hurried : Trial := { base with horizon := 2 }

/-- `hurried` fails the record: only its first attempt leaves a later attempt before the horizon,
and on that attempt `finder` earns no more than the agent that always tries the first door. -/
theorem hurried_fails : ¬ postcondition.Meets hurried := fun h => by
  obtain ⟨n, room, more⟩ := (postcondition_meets.mp h).2.1
  have small : n + 0 + 1 < 2 := room
  have first : n = 0 := by omega
  subst first
  exact absurd (more (always true) (always_keepsNothing true) 0) (by decide +kernel)

/-- **An advantage that comes too late for the horizon is ruled out**: the trial `hurried`, whose
agent earns the advantage on its second attempt, the last before the class's horizon. Its
neighbour is `base`, which reads one attempt more. -/
def rulesOutLateAdvantage : Consequence Trial :=
  ⟨"the trial hurried, whose agent earns the advantage on the last attempt before the stated \
    attempt, is ruled out", .entailment, fun w => w ≠ hurried⟩

theorem rulesOutLateAdvantage_holds : rulesOutLateAdvantage.HoldsOf postcondition :=
  fun _ hw he => hurried_fails (he ▸ hw)

/-- **No agent meets the record in a class whose lapses leave no room.** Where a class allows as
many lapses as it has attempts before its horizon, less one, no attempt leaves more later
attempts before the horizon than the lapses, so the record's property on the advantage fails of
every agent. -/
theorem unmet_of_lapses (w : Trial) (covered : w.horizon ≤ w.lapses + 1) :
    ¬ postcondition.Meets w := fun h => by
  obtain ⟨n, room, -⟩ := (postcondition_meets.mp h).2.1
  omega

/-! ## An agent whose action never reads its memory -/

/-- The runs of an agent whose action does not depend on its memory, and of its `shell`, pass
through the same states in every member. -/
theorem run_shell {Obs Act : Type} {A : Agent Obs Act}
    (blind : ∀ m m' o, (A.act m o).1 = (A.act m' o).1) (M : Member Obs Act) :
    ∀ t, (M.run (shell A) t).1 = (M.run A t).1
  | 0 => rfl
  | t + 1 => by
    show M.step (M.run (shell A) t).1 (A.act A.initial
        (M.observe (M.run (shell A) t).1, M.reward (M.run (shell A) t).1)).1 =
      M.step (M.run A t).1 (A.act (M.run A t).2
        (M.observe (M.run A t).1, M.reward (M.run A t).1)).1
    rw [run_shell blind M t]
    exact congrArg (M.step _) (blind _ _ _)

/-- An agent whose action does not depend on its memory earns across the class, on every attempt,
what its `shell` earns. -/
theorem classReward_shell {w : Trial} {A : Agent w.Obs w.Act}
    (blind : ∀ m m' o, (A.act m o).1 = (A.act m' o).1) (n : Nat) :
    w.classReward (shell A) n = w.classReward A n := by
  unfold Trial.classReward Trial.earned Trial.stateAt
  simp only [run_shell blind]

/-- **The agent's action depends on its memory.** An agent that stores what it is given and never
reads it acts, in every member, as an agent that keeps nothing of its experience acts, so it earns
no more than one. -/
def actionReadsMemory : Consequence Trial :=
  ⟨"what the agent does depends on its memory", .entailment, fun w =>
    ¬ ∀ m m' o, (w.agent.act m o).1 = (w.agent.act m' o).1⟩

theorem actionReadsMemory_holds : actionReadsMemory.HoldsOf postcondition :=
  fun w hw blind => by
    obtain ⟨n, -, more⟩ := (postcondition_meets.mp hw).2.1
    have h := more (shell w.agent) (shell_keepsNothing _) n
    rw [classReward_shell blind] at h
    exact Rat.lt_irrefl h

/-! ## An agent that stops at the horizon -/

/-- An agent for the two-door class that tries the first door on its first attempt, the member's
door on its second and third attempts, and the other door ever after. Its memory counts its steps
and keeps the door the first attempt showed. -/
def halts : Agent (Option Bool) Bool where
  Memory := Nat × Option Bool
  initial := (0, none)
  act := fun m o =>
    (if m.1 == 0 then true else if m.1 == 2 || m.1 == 4 then m.2.getD true else !(m.2.getD true),
      (m.1 + 1, if m.1 == 1 then o.1 else m.2))

/-- From its second attempt on, `halts` has counted its steps and holds the member's door. -/
theorem halts_memory (pay : Rat) (b : Bool) :
    ∀ t, ((door pay b).run halts (t + 2)).2 = (t + 2, some b)
  | 0 => by cases b <;> rfl
  | t + 1 => by
    have ih := halts_memory pay b t
    show (halts.act ((door pay b).run halts (t + 2)).2 _).2 = _
    rw [ih]
    rfl

/-- On its second and third attempts `halts` solves each member of a two-door class. -/
theorem halts_hits (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (b : Bool) : (doors total pay X).solves halts b 1 = true ∧
      (doors total pay X).solves halts b 2 = true := by
  rw [doors_solves, doors_solves]
  cases b <;> exact ⟨rfl, rfl⟩

/-- From its fourth attempt on `halts` tries the door that is not the member's. -/
theorem halts_other (pay : Rat) (b : Bool) (n : Nat) : tried pay halts b (n + 3) = !b := by
  unfold tried
  have e : 2 * (n + 3) = 2 * n + 4 + 2 := by omega
  rw [e, halts_memory]
  rfl

/-- From its fourth attempt on `halts` solves no member of a two-door class. -/
theorem halts_misses (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (b : Bool) (n : Nat) : (doors total pay X).solves halts b (n + 3) = false := by
  rw [doors_solves, halts_other]
  cases b <;> rfl

/-- `base` whose agent is `halts`: it earns the advantage on its second attempt, solves both
members again on its third, and solves no member from its fourth attempt, the horizon, on. -/
def halted : Trial := doors List.sum 1 halts

/-- `halted` meets the record. -/
theorem halted_meets : postcondition.Meets halted := by
  refine postcondition_meets.mpr ⟨doors_rewardCounts List.sum 1 halts fair_sum_one,
    ⟨1, show 1 + 0 + 1 < 3 by decide, fun (B : Agent (Option Bool) Bool) hB k => ?_⟩,
    fun b => ⟨[], Nat.le_refl 0, fun n n' hle before _ hs _ => ?_⟩,
    fun b n g _ _ _ left _ _ => absurd (doors_sameProblem List.sum 1 halts b n g) left⟩
  · show (doors List.sum 1 halts).classReward B k < (doors List.sum 1 halts).classReward halts 1
    rw [doors_classReward, doors_classReward, (halts_hits List.sum 1 halts true).1,
      (halts_hits List.sum 1 halts false).1, doors_solves, doors_solves,
      keepsNothing_tried 1 hB, keepsNothing_tried 1 hB]
    exact (fair_sum_one _ _ _ _).mpr (by cases guess B k <;> decide)
  · have small : n' < 3 := before
    match n', small with
    | 0, _ => exact (Nat.le_zero.mp hle) ▸ hs
    | 1, _ => exact (halts_hits List.sum 1 halts b).1
    | 2, _ => exact (halts_hits List.sum 1 halts b).2

/-- **The agent may solve nothing from the horizon on**: some trial that meets the record has an
agent that solves no member on any attempt from the class's horizon on. -/
def mayStopAtHorizon : Consequence Trial :=
  ⟨"the agent may solve no member from the stated attempt on", .possibility, fun w =>
    ∀ i n, w.horizon ≤ n → w.solves w.agent i n = false⟩

theorem mayStopAtHorizon_holds : mayStopAtHorizon.HoldsOf postcondition :=
  ⟨halted, halted_meets, fun b n late => by
    have three : 3 ≤ n := late
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    exact halts_misses List.sum 1 halts b m⟩

/-! ## The fourth property, in the form it had and the form it has

The fourth property was restated when the record was compared with its second, blind readings
(`lean/AcornVerif/Intent/Postcondition.md`). `PromptlyAgain` is the form it had: it gave the agent
the lapses and one attempt more to solve a member again from the attempt at which the member's
attempts were back for good, before the horizon. That asks more than the postcondition's fourth
sentence says, which lets the agent give up what it no longer needs and promises only the ability to
learn it again, with no time named. The trial `returning` shows the difference: its agent misses the
first attempt back and solves from the next one on. Wherever every member's attempts always start
from one state, as in every class that meets the record of contract 2, both forms ask nothing beyond
`keepsSolving` (`promptlyAgain_of_keeps`, `learnsAgain_of_same`). -/

/-- The form the record's fourth property had before it was compared with its blind readings: once
the agent has solved a member on an attempt, then from any later attempt after which that member's
attempts all start from the state the solved attempt started from, it solves the member again on
that attempt or on one of the next ones, as many as the class's number of lapses, where all of
those come before the class's horizon. -/
def PromptlyAgain (w : Trial) : Prop :=
  ∀ i n n', n ≤ n' → n' + w.lapses < w.horizon → (∀ k, n' ≤ k → w.SameProblem i n k) →
    w.solves w.agent i n = true →
      ∃ n'', n' ≤ n'' ∧ n'' ≤ n' + w.lapses ∧ w.solves w.agent i n'' = true

/-- Where every attempt of every member starts from one state, an agent that keeps solving has the
earlier form of the fourth property. -/
theorem promptlyAgain_of_keeps {w : Trial} (same : ∀ i n k, w.SameProblem i n k)
    (keeps : keepsSolving.holds w) : PromptlyAgain w := by
  intro i n n' hle room _ solved
  obtain ⟨lapsed, few, kept⟩ := keeps i
  obtain ⟨d, short, out⟩ := exists_not_lapsed lapsed n'
  exact ⟨n' + d, by omega, by omega,
    kept n (n' + d) (by omega) (by omega) (fun k _ _ => same i n k) solved out⟩

/-- Where every attempt of every member starts from one state, the fourth property holds of every
agent: no member's attempts leave the state of a solved attempt. -/
theorem learnsAgain_of_same {w : Trial} (same : ∀ i n k, w.SameProblem i n k) :
    learnsAgain.holds w :=
  fun i n g _ _ _ left _ _ => absurd (same i n g) left

/-- **Where every attempt of every member starts from one state, the record asks the same in both
forms of its fourth property.** A trial meets the record exactly when it has the record's first
three properties and the earlier form of the fourth. -/
theorem meets_iff_promptly {w : Trial} (same : ∀ i n k, w.SameProblem i n k) :
    postcondition.Meets w ↔
      rewardCountsMembers.holds w ∧ earnsMoreInTime.holds w ∧ keepsSolving.holds w ∧
        PromptlyAgain w := by
  rw [postcondition_meets]
  exact ⟨fun ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3, promptlyAgain_of_keeps same h3⟩,
    fun ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3, learnsAgain_of_same same⟩⟩

/-- An agent for the detour world that solves on its first step, leaves on its second, waits through
the attempt that starts away and through the first attempt back, and from its fourth attempt on
solves at each attempt's first step and waits at its second. Its memory counts its steps. -/
def returns : Agent Unit Move where
  Memory := Nat
  initial := 0
  act := fun m _ =>
    (match m with
      | 0 => .solve
      | 1 => .leave
      | k + 2 => if 4 ≤ k ∧ k % 2 = 0 then .solve else .wait, m + 1)

/-- After `t` steps of its run in any member, `returns` has counted `t` steps. -/
theorem returns_memory (M : Member Unit Move) : ∀ t, (M.run returns t).2 = t
  | 0 => rfl
  | t + 1 => congrArg (· + 1) (returns_memory M t)

/-- From its fourth attempt on, the run of `returns` in the detour world starts each attempt at
`home` and wins it. -/
theorem returns_late : ∀ j, (detour.run returns (2 * j + 6)).1 = Spot.home ∧
    (detour.run returns (2 * j + 7)).1 = Spot.won
  | 0 => ⟨rfl, rfl⟩
  | j + 1 => by
    obtain ⟨_, won⟩ := returns_late j
    have waits : (returns.act (2 * j + 7) ((), 1)).1 = Move.wait := by
      show (if 4 ≤ 2 * j + 5 ∧ (2 * j + 5) % 2 = 0 then Move.solve else Move.wait) = Move.wait
      split
      · rename_i even
        exact absurd even.2 (by omega)
      · rfl
    have home : (detour.run returns (2 * (j + 1) + 6)).1 = Spot.home := by
      show detour.step (detour.run returns (2 * j + 7)).1
        (returns.act (detour.run returns (2 * j + 7)).2
          (detour.observe (detour.run returns (2 * j + 7)).1,
            detour.reward (detour.run returns (2 * j + 7)).1)).1 = Spot.home
      rw [won, returns_memory]
      show detour.step Spot.won (returns.act (2 * j + 7) ((), 1)).1 = Spot.home
      rw [waits]
      rfl
    have solves : (returns.act (2 * j + 8) ((), 0)).1 = Move.solve := by
      show (if 4 ≤ 2 * j + 6 ∧ (2 * j + 6) % 2 = 0 then Move.solve else Move.wait) = Move.solve
      split
      · rfl
      · rename_i odd
        exact absurd ⟨by omega, by omega⟩ odd
    refine ⟨home, ?_⟩
    show detour.step (detour.run returns (2 * (j + 1) + 6)).1
      (returns.act (detour.run returns (2 * (j + 1) + 6)).2
        (detour.observe (detour.run returns (2 * (j + 1) + 6)).1,
          detour.reward (detour.run returns (2 * (j + 1) + 6)).1)).1 = Spot.won
    rw [home, returns_memory]
    show detour.step Spot.home (returns.act (2 * j + 8) ((), 0)).1 = Spot.won
    rw [solves]
    rfl

/-- The detour class with `returns`: its agent solves the member on its first attempt, the second
attempt starts away, every later attempt starts at `home` again, and the agent misses the first of
them and solves the member on every attempt after it. -/
def returning : Trial := detours returns

/-- From its fourth attempt on, `returns` solves the member of the detour class. -/
theorem returning_solves (n : Nat) (late : 3 ≤ n) : returning.solves returns () n = true := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have e : 2 * (j + 3) = 2 * j + 6 := by omega
  show (detour.goal (detour.run returns (2 * (j + 3) + 0)).1 ||
    (detour.goal (detour.run returns (2 * (j + 3) + 1)).1 || false)) = true
  rw [Nat.add_zero, e, (returns_late j).1,
    show (detour.run returns (2 * j + 6 + 1)).1 = Spot.won from (returns_late j).2]
  rfl

/-- From its third attempt on, the member of `returning` starts each attempt from the state its
first attempt started from. -/
theorem returning_back (k : Nat) (late : 2 ≤ k) : returning.SameProblem () 0 k := by
  rcases Nat.eq_or_lt_of_le late with rfl | later
  · rfl
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have e : 2 * (j + 3) = 2 * j + 6 := by omega
    show (detour.run returns (2 * (j + 3))).1 = (detour.run returns (2 * 0)).1
    rw [e, (returns_late j).1]
    rfl

/-- The member of `returning` leaves and comes back: its second attempt starts from another state
than its first, which the agent solved, and every attempt from the third on starts from the first
one's state. So the fourth property asks something of `returning`. -/
theorem returning_leaves : returning.solves returns () 0 = true ∧
    ¬ returning.SameProblem () 0 1 ∧ ∀ k, 2 ≤ k → returning.SameProblem () 0 k :=
  ⟨rfl, fun h => Spot.noConfusion (h : Spot.away = Spot.home), returning_back⟩

/-- **The fourth property admits an agent that misses the first attempt back and solves a later
one**: `returning` has it. -/
theorem returning_learnsAgain : learnsAgain.holds returning :=
  fun _ _ g _ _ _ _ _ _ =>
    ⟨max (g + 1) 3, Nat.lt_of_lt_of_le (Nat.lt_succ_self g) (Nat.le_max_left _ _),
      returning_solves _ (Nat.le_max_right _ _)⟩

/-- `returns` keeps nothing of its experience: its memory counts its steps. -/
theorem returns_keepsNothing : KeepsNothing returns :=
  fun _ _ _ => rfl

/-- **The earlier form of the fourth property refused that agent**: `returning` allows no lapse, its
third attempt is the first from which the member's attempts are back for good, and its agent does
not solve the member on it. -/
theorem returning_not_promptly : ¬ PromptlyAgain returning := fun h => by
  obtain ⟨n'', low, high, hs⟩ := h () 0 2 (by decide) (by decide) returning_back rfl
  have two : n'' = 2 := Nat.le_antisymm high low
  subst two
  exact absurd hs (by decide)

/-! ## The record explained -/

/-- The record explained in plain words, with its restatement standing as confirmed by the owner:
the owner confirmed the postcondition's six sentences on 2026-11-03 and, on 2026-11-17, a reading
of the fourth and that the advantage is read before the stated attempt, and on 2026-11-18 that
the stated number is how many later attempts the agent may miss; that this revision carries
them is the agents' judgment, on which the owners' log attaches the owner's answers. Every
consequence it shows is recorded as derived from what the owner confirmed. Two consequences whose
statements are themselves a reading decided on the owner's behalf are not shown here:
`solvesMoreInTime`, which states the room after the attempt of the advantage, and
`mayStopAtHorizon`. They are recorded with the other decisions made on the owner's behalf in the
record's confirmation file, `lean/AcornVerif/Intent/Postcondition.md`. The plain words are trusted,
not proved. -/
def postconditionExplained : Explanation postcondition where
  shape :=
    { requires := "Nothing of its own: the subject is a class of worlds with what the class \
        states and the agent that learns in it, declared a plain value."
      rulesOut := "Nothing of its own."
      allows := "A world or an agent whose functions are constant, which a shape that asks every \
        function to vary with its input would not admit."
      freedom := "Two trials that meet the record may differ in everything the properties leave \
        open: the worlds, their rewards and goals, the members counted, how an attempt's rewards \
        are aggregated, how long an attempt lasts, the horizon and the lapses within the room the \
        advantage needs, and the agent." }
  dom := []
  props := [
    { requires := "For every two agents among those compared, which are the agent that learns \
        and every agent whose memory after each answer does not depend on what it was given, and \
        for every attempt of the first and every attempt of the second: the first earns more \
        reward across the counted members on its attempt than the second on its own exactly when \
        it solves more of the counted members on its attempt than the second on its own. What an \
        agent earns in a member on an attempt is the class's aggregate of the rewards the \
        member's world generates at the attempt's steps, and across the class it is the sum of \
        that over the counted members."
      rulesOut := "A class in which one of those agents earns more on an attempt than another on \
        an attempt without solving more counted members, or solves more without earning more: \
        such as a class whose members generate no reward at their goals, where two of those \
        agents solve different numbers of them."
      allows := "Any reward function, aggregation and attempt length under which the two orders \
        agree on those agents and attempts; and any disagreement between them on agents that \
        are not compared."
      freedom := "The reward function, the aggregation, the attempt length and the members \
        counted, as far as the two orders agree." },
    { requires := "There is an attempt, the n-th counted from zero, with n + lapses + 1 < \
        horizon, so that more attempts come after it and before the class's horizon than the \
        class's number of lapses, on which the agent earns more reward across the counted \
        members than each agent that keeps nothing of its experience earns on each of its own \
        attempts."
      rulesOut := "An agent with no such attempt: an agent that itself keeps nothing of its \
        experience; an agent whose only such attempts come at or after the horizon, or leave no \
        more later attempts before it than the lapses; and every agent in a class whose horizon \
        is at most its lapses and one."
      allows := "One such attempt and no other, as far as this property goes; no advantage on \
        the first attempt; and an advantage smaller than the best an agent could have."
      freedom := "Which attempt it is, and by how much the agent earns more." },
    { requires := "For each member of the class, counted or not, there is one list of at most \
        as many attempts as the class's number of lapses such that, for every attempt on which \
        the agent solves the member and every attempt no earlier than it and before the \
        horizon: if every attempt from the first of the two to the second starts, in the \
        agent's run in that member, from the state the first started from, and the second is \
        not in the list, then the agent solves the member on the second."
      rulesOut := "An agent that, having solved a member, misses it on more attempts before the \
        horizon than the lapses while the member's attempts go on starting from the same state; \
        with no lapse allowed, one such miss."
      allows := "For each member, misses on up to the stated number of attempts, the same list \
        whichever earlier attempt solved it; any miss at or after the horizon; a miss on an \
        attempt that starts from another state than every attempt on which the member was \
        solved; and never solving a member."
      freedom := "Which attempts are a member's lapses, and everything from the horizon on." },
    { requires := "For each member of the class, counted or not, each attempt n on which the \
        agent solves it, each later attempt g that starts, in the agent's run in that member, \
        from another state than attempt n started from, and each attempt n' later than g: if \
        every attempt from n' on, without end, starts from the state attempt n started from, \
        then the agent solves the member on some attempt after g. So after the last attempt \
        that starts from another state, the member is solved at least once."
      rulesOut := "An agent that, having solved a member whose attempts then left that state \
        and came back to it for good, solves it on no attempt after the last one that started \
        from another state."
      allows := "Missing the member on any number of attempts after it is back, and solving it \
        only once more, as far as this property goes; solving it again only after the horizon; \
        anything of a member whose attempts never leave the state of the solved attempt, which \
        is the third property's to say; and anything of a member whose attempts leave that \
        state and do not come back to it for good."
      freedom := "On which attempt the member is solved again, and how the agent comes to solve \
        it again." }]
  vocab := [
    { requires := "From every memory, the memory the agent's answer produces is the same \
        whatever observation and reward the agent is given."
      rulesOut := "An agent whose next memory depends, from some memory, on what it is given."
      allows := "An action that reads what the agent is given at that step, and a memory that \
        changes from step to step in a way fixed in advance, such as a clock or a script of \
        timed actions."
      freedom := "None of its own: it is a definition the properties are written in." },
    { requires := "At some step of the attempt, the run of the given agent in the given member, \
        from the member's start and the agent's initial memory, is in a state that meets the \
        member's goal; attempt n is the class's attempt length of steps, from the step that \
        length times n on."
      rulesOut := "An attempt at none of whose steps the member's goal is met, such as every \
        attempt of a class whose attempts last no step."
      allows := "Meeting the goal at any step of the attempt, the first included."
      freedom := "None of its own: it is a definition the properties are written in." }]
  restatement := .confirmed owner
  consequences := [
    ⟨learnerKeepsSomething, learnerKeepsSomething_holds,
      { requires := "From some memory, the memory the agent's answer produces depends on what \
          the agent is given."
        rulesOut := "An agent that keeps nothing of its experience, in every class: one that \
          always answers the same, a clock, a script of timed actions."
        allows := "Any way of keeping something of what the agent is given."
        freedom := "What the agent keeps, and how it uses it." }, .derived⟩,
    ⟨solvesMoreBeforeHorizon, solvesMoreBeforeHorizon_holds,
      { requires := "There is an attempt before the class's horizon on which the agent solves \
          more of the counted members than each agent that keeps nothing of its experience \
          solves on each of its own attempts."
        rulesOut := "An agent that on no attempt before the horizon solves more of the counted \
          members than every agent that keeps nothing solves on any attempt."
        allows := "Leaving some counted members unsolved on that attempt."
        freedom := "Which attempt it is, and how many more members the agent solves." },
      .derived⟩,
    ⟨advantageSolvedAgain, advantageSolvedAgain_holds,
      { requires := "There is an attempt on which the agent earns more reward across the \
          counted members than each agent that keeps nothing of its experience earns on each of \
          its own attempts, and such that each member the agent solves on that attempt, and \
          whose every later attempt starts in the agent's run from the state that attempt \
          started from, the agent solves again on some later attempt before the horizon."
        rulesOut := "An agent that, on every attempt of its advantage, solves a member whose \
          later attempts all start from that state and never solves it again before the horizon."
        allows := "Solving such a member again on one later attempt only; and never again a \
          member whose later attempts do not all start from that state."
        freedom := "On which later attempt each member is solved again." }, .derived⟩,
    ⟨actionReadsMemory, actionReadsMemory_holds,
      { requires := "From some two memories and something the agent may be given, the agent's \
          action differs: it is not the case that its action depends only on what it is given \
          at that step."
        rulesOut := "An agent that stores what it is given and never reads it, which acts as an \
          agent that keeps nothing of its experience acts."
        allows := "Any use of its memory in what it does."
        freedom := "How the agent's memory enters its action." }, .derived⟩,
    ⟨countsSomeMember, countsSomeMember_holds,
      { requires := "The list of members the comparison counts is not empty."
        rulesOut := "A class that counts no member, in which every agent earns nothing across \
          the class."
        allows := "Any list with at least one member."
        freedom := "Which members are counted." }, .derived⟩,
    ⟨rulesOutFixedAgent, rulesOutFixedAgent_holds,
      { requires := "The trial fixed, the two-door class base with an agent that tries the first \
        door on every attempt and so keeps nothing of its experience, does not meet the record."
        rulesOut := "That trial; base, whose agent remembers the door that worked, meets the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨rulesOutUnpaidGoals, rulesOutUnpaidGoals_holds,
      { requires := "The trial unpaid, the two-door class base whose members generate no reward \
        at their goals, does not meet the record: its agent solves more members on its second \
        attempt than an agent that always tries the first door, and earns no more."
        rulesOut := "That trial; base, whose members pay one at their goals, meets the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨rulesOutSolvingOnce, rulesOutSolvingOnce_holds,
      { requires := "The trial forgetful, the two-door class base with an agent that solves the \
        first member on its first attempt and on no later one, does not meet the record: the \
        class allows no lapse, its second attempt comes before the horizon, and every attempt \
        of a member starts from the same state."
        rulesOut := "That trial; base, whose agent solves again what it has solved, meets the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨rulesOutAdvantageOnce, rulesOutAdvantageOnce_holds,
      { requires := "The trial flashy, the two-door class base with an agent that solves both \
        members on its second attempt, earning more than every agent that keeps nothing, and \
        solves no member from its third attempt on, does not meet the record: the third attempt \
        comes before the horizon and the class allows no lapse."
        rulesOut := "That trial; base, whose agent goes on solving both members, meets the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨rulesOutLateAdvantage, rulesOutLateAdvantage_holds,
      { requires := "The trial hurried, the two-door class base with its horizon at the third \
        attempt in place of the fourth, does not meet the record: its agent first earns more \
        than every agent that keeps nothing on its second attempt, which no attempt follows \
        before the horizon."
        rulesOut := "That trial; base, whose horizon leaves one attempt after the second, meets the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨noFirstAttemptAdvantage, noFirstAttemptAdvantage_holds,
      { requires := "Nothing more: some trial that meets the record has an agent that earns, on \
          its first attempt, no more across the counted members than some agent that keeps \
          nothing of its experience earns on its first attempt."
        rulesOut := "Nothing."
        allows := "No advantage on a first attempt."
        freedom := "Whether the agent has an advantage on its first attempt." }, .derived⟩,
    ⟨firstAttemptMayFail, firstAttemptMayFail_holds,
      { requires := "Nothing more: some trial that meets the record has an agent that does not \
          solve one of the counted members on its first attempt."
        rulesOut := "Nothing."
        allows := "Failing a member on a first attempt."
        freedom := "Which members the agent solves on its first attempt." }, .derived⟩]

end AcornVerif.Intent.Postcondition
