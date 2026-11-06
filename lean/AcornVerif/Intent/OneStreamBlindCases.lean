/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.OneStreamConsequences

/-!
# The blind cases reading of contract 3, and the record's verdict on each case

After the record `AcornVerif.Intent.OneStream.oneStream` was sealed at commit b144b41, OpenAI's
gpt-6-astra read contract 3's six sentences in fresh sessions given only the owner's words, the
source of the subject's types and, for a record, lean-intent's record module or, for the cases, a
plain description of what an input is: twice for a record, of
which the first gave none and the second gave the blind record of
`AcornVerif.Intent.OneStreamBlindReading`, compared with this record in
`AcornVerif.Intent.OneStreamBlindCompare`, and once for cases. The cases session gave 30 cases, each
one world, one agent and its run with the agent's reports, and a verdict. This module writes each case as a `AcornVerif.Intent.OneStream.Learner` and proves this record's verdict
on it, one theorem for each, `c1` to `c30`. It is no deliverable and no part of the owner's intent: it
is a second model's reading of the owner's words. How each difference was settled is in the record's
confirmation file, `lean/AcornVerif/Intent/OneStream.md`.

The cases are transcribed, not copied: the reply gave them in plain words. Each is written with the
smallest types that carry what the case says: an observation written `1` or `0` is `true` or
`false`, a lone action is `()`, a world's lone state is `()`, a one-bit memory is a `Bool`, the
inputs `go` and `stop` are `false` and `true` (cases 26 and 27, with a third input, use `Fin 3`,
`stop` being `2`), a memory written as a tape or a count is a natural number, and a work of `32`
primitive operations is the number `32`. Where a case's description of a memory carries content the
record does not read (case 2's archive and estimate), the memory keeps only which of the case's
named memories it is (`empty` and `saved` as `false` and `true`); case 4's model bit and clipped
trace are kept whole, as `Bool × Fin 3`; and the memories `0`, `1` and `2` of cases 24 and 25 are
natural numbers. Each case's own docstring gives its number, the reply's verdict, and this
record's.
-/

namespace AcornVerif.Intent.OneStream.Cases

open LeanIntent WorldInterface AcornVerif.Intent.OneStream

/-- A learner meets the record when its memories are finitely many, every learning update it reports
learns from the experience its step was given, its work and number of updates are bounded, it
reports a learning update on every experience or on none and a planning update on every experience
or on none, it reports no reset, its run keeps the memory its answer produced, and it resumes with
the memory it held. -/
theorem meets_of (w : Learner)
    (hlearn : ∀ m o d, Update.learn d ∈ w.updates m o → d = .stream 0)
    (hcost : ∃ B, ∀ m o, w.work m o ≤ B ∧ (w.updates m o).length ≤ B)
    (hfin : ∃ L : List w.Memory, ∀ m, m ∈ L)
    (hevery : (∀ m o, ∃ d, Update.learn d ∈ w.updates m o) ∨ ∀ m o d, Update.learn d ∉ w.updates m o)
    (hplan : (∀ m o, Update.plan ∈ w.updates m o) ∨ ∀ m o, Update.plan ∉ w.updates m o)
    (hreset : ∀ m o, Update.reset ∉ w.updates m o) (hkept : ∀ s m e m', w.kept s m e m' = m')
    (hback : ∀ m, w.resume m = m) : oneStream.Meets w := by
  obtain ⟨B, hB⟩ := hcost
  obtain ⟨L, hL⟩ := hfin
  refine oneStream_meets.mpr ⟨fun _ _ _ _ _ d hd => hlearn _ _ d hd,
    ⟨B, fun _ _ _ _ _ => hB _ _⟩, ⟨L, fun _ _ _ m _ => hL m⟩, ?_, ?_,
    fun _ _ _ _ _ => hreset _ _, fun _ _ _ _ _ => hkept _ _ _ _, fun _ _ _ m _ => hback m⟩
  · rcases hevery with h | h
    · exact fun _ _ _ _ _ _ => h _ _
    · exact fun ⟨_, _, _, _, d, _, hd⟩ => absurd hd (h _ _ d)
  · rcases hplan with h | h
    · exact fun _ _ _ _ _ _ => h _ _
    · exact fun ⟨_, _, _, _, _, hd⟩ => absurd hd (h _ _)

/-- The two memories of a one-bit agent. -/
theorem bool_finite : ∃ L : List Bool, ∀ m, m ∈ L :=
  ⟨[false, true], fun m => by cases m with
    | false => exact .head _
    | true => exact .tail _ (.head _)⟩

/-- If the one update of a report is a learning update on the experience its step was given, every
learning update of the report takes that experience. -/
theorem learn_only {m : Update} {d : Datum} (h : Update.learn d ∈ [m]) (hm : m = .learn (.stream 0)) :
    d = .stream 0 := by
  subst hm
  exact Update.learn.inj (List.mem_singleton.mp h)

/-! ## The worlds of the cases -/

/-- One state, which shows `1` and gives reward 0, with one action. -/
def one : World where
  State := Unit
  Obs := Bool
  Act := Unit
  start := ()
  observe _ := true
  reward _ := 0
  available _ _ := True
  step _ _ := ()

/-- An agent of `one` with one bit of memory, starting at `0`, which always answers with the
action and the memory `1`. -/
def setsBit : Agent Bool Unit where
  Memory := Bool
  initial := false
  act _ _ := ((), true)

/-- Two states, `0` and `1`, starting at `1`; each shows its own number and gives reward 0, and the
one action flips the state. -/
def flip : World where
  State := Bool
  Obs := Bool
  Act := Unit
  start := true
  observe s := s
  reward _ := 0
  available _ _ := True
  step s _ := !s

/-- An agent of `flip` with one bit of memory, starting at `0`, whose next memory is the observation
it is given. -/
def copies : Agent Bool Unit where
  Memory := Bool
  initial := false
  act _ o := ((), o.1)

/-! ## The cases -/

/-- Case 1, learning once from each arriving experience: `one` and `setsBit`, run faithfully, one
learning update on the experience each step was given. The reply: meets; this record: meets. -/
def case1 : Learner := learner one setsBit (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem c1 : oneStream.Meets case1 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- Case 2, two updates from the current experience with a bounded archive: two learning updates on
the experience each step was given; the memory `saved` (`true`) holds an archive no update takes.
The reply: meets; this record: meets. -/
def case2 : Learner :=
  learner one setsBit (fun _ _ => [.learn (.stream 0), .learn (.stream 0)]) (fun _ _ => 32) id

theorem c2 : oneStream.Meets case2 :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at h
      exact Update.learn.inj h)
    ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩ bool_finite (.inl fun _ _ => ⟨_, .head _⟩)
    (.inr fun _ _ h => by simp at h) (fun _ _ h => by simp at h) fun _ => rfl

/-- Case 3, the second update replays the preceding experience: at `saved` (`true`) the second
learning update takes the experience the step before was given. The reply: fails; this record:
fails. -/
def case3 : Learner :=
  learner one setsBit
    (fun m _ => cond m [.learn (.stream 0), .learn (.stream 1)] [.learn (.stream 0), .learn (.stream 0)])
    (fun _ _ => 32) id

theorem c3 : ¬ oneStream.Meets case3 := fun h =>
  absurd ((oneStream_meets.mp h).1 (fun _ => false) 1 () true ⟨.next .start rfl, rfl⟩ _
    (.tail _ (.head _))) (by decide)

/-- An agent of `one` whose memory is a model bit and a trace clipped at 2, starting at `(0, 0)`: each
step sets the model bit and adds one to the trace, up to 2. -/
def tracer : Agent Bool Unit where
  Memory := Bool × Fin 3
  initial := (false, 0)
  act m _ := ((), (true, if m.2 = 2 then 2 else m.2 + 1))

/-- The six memories of `tracer`. -/
theorem tracer_finite : ∃ L : List tracer.Memory, ∀ m, m ∈ L :=
  ⟨[(false, 0), (false, 1), (false, 2), (true, 0), (true, 1), (true, 2)], fun m => by
    obtain ⟨b, z, hz⟩ := m
    change (b, (⟨z, hz⟩ : Fin 3)) ∈ ([(false, 0), (false, 1), (false, 2), (true, 0), (true, 1),
      (true, 2)] : List (Bool × Fin 3))
    cases b
    · match z, hz with
      | 0, _ => exact .head _
      | 1, _ => exact .tail _ (.head _)
      | 2, _ => exact .tail _ (.tail _ (.head _))
      | _ + 3, h => exact absurd h (by omega)
    · match z, hz with
      | 0, _ => exact .tail _ (.tail _ (.tail _ (.head _)))
      | 1, _ => exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
      | 2, _ => exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
      | _ + 3, h => exact absurd h (by omega)⟩

/-- Case 4, keeping a trace and planning after learning: a trace update, a learning update on the
experience the step was given, and two planning updates at each step. The reply: meets; this record:
meets. -/
def case4 : Learner :=
  learner one tracer (fun _ _ => [.other, .learn (.stream 0), .plan, .plan]) (fun _ _ => 32) id

theorem c4 : oneStream.Meets case4 :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> first | exact Update.learn.inj h | exact nomatch h)
    ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩ tracer_finite
    (.inl fun _ _ => ⟨_, .tail _ (.head _)⟩) (.inl fun _ _ => .tail _ (.tail _ (.head _)))
    (fun _ _ h => by simp at h) fun _ => rfl

/-- Case 5, a learning datum that is no experience of the stream: one learning update whose datum is
`other`. The reply: the words do not settle this; this record: fails. -/
def case5 : Learner := learner one setsBit (fun _ _ => [.learn .other]) (fun _ _ => 32) id

theorem c5 : ¬ oneStream.Meets case5 := fun h =>
  absurd ((oneStream_meets.mp h).1 (fun _ => false) 0 () false ⟨.start, rfl⟩ _ (.head _))
    (by decide)

/-- One state, which shows `0` and gives reward 0, with one action. -/
def oneZero : World := { one with observe := fun _ => false }

/-- Case 6, the run gives the agent something other than the world's observation: the world shows `0`
and the run gives `(1, 7)`. The reply: meets; this record: meets, as contract 3's sentences do not
speak of what the run gives (contract 1's record refutes this run). -/
def case6 : Learner :=
  { learner oneZero copies (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id with
    given := fun _ _ _ => (true, 7) }

theorem c6 : oneStream.Meets case6 :=
  meets_of _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

/-- Case 7, resetting internally, then relearning: a reset and then a learning update at each step.
The reply: fails; this record: fails. -/
def case7 : Learner :=
  learner one setsBit (fun _ _ => [.reset, .learn (.stream 0)]) (fun _ _ => 32) id

theorem c7 : ¬ oneStream.Meets case7 := fun h =>
  (oneStream_meets.mp h).2.2.2.2.2.1 (fun _ => false) 0 () false ⟨.start, rfl⟩ (.head _)

/-- Case 8, learning returns memory to its initial value: `flip` and `copies`, whose memory is `0`
after every step from state `0`. The reply: meets; this record: meets. -/
def case8 : Learner := learner flip copies (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem c8 : oneStream.Meets case8 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- Case 9, the same return to zero reported as a reset: at observation `0` the step reports a reset
and no learning update. The reply: fails; this record: fails, by `neverResetsItself` (and also by
`learnsEveryStep`). -/
def case9 : Learner :=
  learner flip copies (fun _ o => cond o.1 [.learn (.stream 0)] [.reset]) (fun _ _ => 32) id

theorem c9 : ¬ oneStream.Meets case9 := fun h =>
  (oneStream_meets.mp h).2.2.2.2.2.1 (fun _ => false) 1 false true ⟨.next .start rfl, rfl⟩ (.head _)

/-- Two states, `attempt` (`false`) and `finished` (`true`), starting at `attempt`, each showing its
own name, with the actions `advance` (`false`) and `restart` (`true`): `advance` leads to `finished`
and `restart` to `attempt`, from either state; only `advance` is available at `attempt` and only
`restart` at `finished`. -/
def attemptWorld : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe s := s
  reward _ := 0
  available s a := a = s
  step _ a := !a

/-- An agent of `attemptWorld` with one bit of memory, starting at `0`, which advances at `attempt`,
restarts at `finished`, and sets its memory to `1`. -/
def attempter : Agent Bool Bool where
  Memory := Bool
  initial := false
  act _ o := (o.1, true)

/-- Case 10, the world restarts between attempts and the agent does not: run faithfully. The reply:
meets; this record: meets. -/
def case10 : Learner :=
  learner attemptWorld attempter (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem c10 : oneStream.Meets case10 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- Case 11, the run resets the agent when the world restarts: from `finished` the run gives the
agent back memory `0`. The reply: fails; this record: fails. -/
def case11 : Learner := { case10 with kept := fun s _ _ m => cond s false m }

theorem c11 : ¬ oneStream.Meets case11 := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.1 (fun _ => false) 1 true true
    ⟨(show case11.Reaches (fun _ => false) 1 true true from .next .start rfl), rfl⟩)

/-- Case 12, a stop discards learned memory: the agent resumes every stop with memory `0`. The reply:
fails; this record: fails, at a stop after one step, holding `1`. -/
def case12 : Learner := learner one setsBit (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32)
  fun _ => false

theorem c12 : ¬ oneStream.Meets case12 := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.2 (fun j => decide (1 ≤ j)) 1 () true
    ⟨.next .start rfl, rfl⟩)

/-- Case 13, the run ignores the viewer's stop request: it takes a step whatever it is sent. The
reply: meets; this record: meets, as contract 3's sentences do not ask the run to stop (contract 1's
record refutes this run). -/
def case13 : Learner := { case1 with goesOn := fun _ _ _ => true }

theorem c13 : oneStream.Meets case13 :=
  meets_of _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

/-- Case 14, the run never lets an experience reach the agent: it takes no step. The reply: the words
do not settle this; this record: meets (contract 1's record refutes it by `canBegin`). -/
def case14 : Learner := { case1 with goesOn := fun _ _ _ => false }

theorem case14_noTakes {ins : Nat → case14.Input} {t : Nat} {s : case14.State}
    {m : case14.Memory} : ¬ case14.Takes ins t s m :=
  fun h => Bool.noConfusion (h.2.symm.trans (rfl : case14.goesOn s m (ins t) = false))

theorem c14 : oneStream.Meets case14 :=
  oneStream_meets.mpr ⟨fun _ _ _ _ h => absurd h case14_noTakes,
    ⟨0, fun _ _ _ _ h => absurd h case14_noTakes⟩, ⟨[false, true], fun _ _ _ m _ => by
      cases m with
      | false => exact .head _
      | true => exact .tail _ (.head _)⟩,
    fun _ _ _ _ _ h => absurd h case14_noTakes, fun _ _ _ _ _ h => absurd h case14_noTakes,
    fun _ _ _ _ h => absurd h case14_noTakes, fun _ _ _ _ h => absurd h case14_noTakes,
    fun _ _ _ _ _ => rfl⟩

/-- An agent of `flip` with one bit of memory, starting at `0`, which sets it to `1` at observation
`1` and keeps it at observation `0`. -/
def setsOnOne : Agent Bool Unit where
  Memory := Bool
  initial := false
  act m o := ((), cond o.1 true m)

/-- Case 15, an experience consumed without a learning update: a learning update at observation `1`
and none at observation `0`. The reply: meets; this record: fails, by `learnsEveryStep`, decided on
the owner's behalf (the record's confirmation file). -/
def case15 : Learner :=
  learner flip setsOnOne (fun _ o => cond o.1 [.learn (.stream 0)] []) (fun _ _ => 32) id

theorem c15 : ¬ oneStream.Meets case15 := fun h => by
  obtain ⟨d, hd⟩ := (oneStream_meets.mp h).2.2.2.1
    ⟨fun _ => false, 0, true, false, .stream 0, ⟨.start, rfl⟩, .head _⟩
    (fun _ => false) 1 false true ⟨.next .start rfl, rfl⟩
  exact nomatch hd

/-- An agent of `one` whose memory is a phase bit and a model bit, starting at `(0, 0)`: each step
flips the phase and sets the model bit. -/
def phased : Agent Bool Unit where
  Memory := Bool × Bool
  initial := (false, false)
  act m _ := ((), (!m.1, true))

/-- The four memories of `phased`. -/
theorem phased_finite : ∃ L : List phased.Memory, ∀ m, m ∈ L :=
  ⟨[(false, false), (false, true), (true, false), (true, true)], fun m => by
    obtain ⟨a, b⟩ := m
    cases a <;> cases b
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
    · exact .tail _ (.tail _ (.tail _ (.head _)))⟩

/-- Case 16, alternating phases that both learn: a phase update and a learning update at every step.
The reply: meets; this record: meets. -/
def case16 : Learner :=
  learner one phased (fun _ _ => [.other, .learn (.stream 0)]) (fun _ _ => 32) id

theorem c16 : oneStream.Meets case16 :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> first | exact Update.learn.inj h | exact nomatch h)
    ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩ phased_finite
    (.inl fun _ _ => ⟨_, .tail _ (.head _)⟩) (.inr fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) fun _ => rfl

/-- Case 17, alternating phases with no learning in one: a learning update in phase `0` only. The
reply: the words do not settle this; this record: fails, by `learnsEveryStep`, decided on the owner's
behalf (the record's confirmation file). -/
def case17 : Learner :=
  learner one phased (fun m _ => cond m.1 [.other] [.other, .learn (.stream 0)]) (fun _ _ => 32) id

theorem c17 : ¬ oneStream.Meets case17 := fun h => by
  obtain ⟨d, hd⟩ := (oneStream_meets.mp h).2.2.2.1
    ⟨fun _ => false, 0, (), (false, false), .stream 0, ⟨.start, rfl⟩, .tail _ (.head _)⟩
    (fun _ => false) 1 () (true, true) ⟨.next .start rfl, rfl⟩
  exact nomatch hd

/-- An agent of `one` that keeps nothing. -/
def empty : Agent Bool Unit := always ()

/-- Case 18, the agent never makes a learning update. The reply: the words do not settle this; this
record: meets, as the consequence `keepsNothing`, derived from sentence 3's "may", shows. -/
def case18 : Learner := learner one empty (fun _ _ => []) (fun _ _ => 32) id

theorem c18 : oneStream.Meets case18 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch h) ⟨32, fun _ _ => ⟨Nat.le_refl _, Nat.zero_le _⟩⟩
    ⟨[()], fun _ => .head _⟩ (.inr fun _ _ _ h => nomatch h) (.inr fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h) fun _ => rfl

/-- States counting the steps taken, each showing its count, written `n` for the unary word of `n`
ones, with one action. -/
def unary : World where
  State := Nat
  Obs := Nat
  Act := Unit
  start := 0
  observe s := s
  reward _ := 0
  available _ _ := True
  step s _ := s + 1

/-- An agent of `unary` with one bit of memory, starting at `0`, which sets it to whether the word it
is shown is nonempty. -/
def nonempty : Agent Nat Unit where
  Memory := Bool
  initial := false
  act _ o := ((), decide (o.1 ≠ 0))

/-- Under inputs that never ask it to stop, the run of `unary` is at the count `t` after `t` steps. -/
theorem unary_reaches : ∀ t, ∃ m, (couple unary nonempty).Reaches (fun _ => false) t t m
  | 0 => ⟨_, .start⟩
  | t + 1 => let ⟨_, h⟩ := unary_reaches t; ⟨_, .next h rfl⟩

/-- Case 19, variable work within a fixed bound: work `32 + min n 16` on the word of `n` ones. The
reply: meets; this record: meets. -/
def case19 : Learner :=
  learner unary nonempty (fun _ _ => [.learn (.stream 0)]) (fun _ (o : Nat × Rat) => 32 + min o.1 16) id

theorem c19 : oneStream.Meets case19 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl)
    ⟨48, fun _ _ => ⟨Nat.add_le_add_left (Nat.min_le_right _ _) 32, by decide⟩⟩ bool_finite
    (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- Case 20, work that grows without bound: work `32 + n` on the word of `n` ones. The reply: fails;
this record: fails. -/
def case20 : Learner :=
  learner unary nonempty (fun _ _ => [.learn (.stream 0)]) (fun _ (o : Nat × Rat) => 32 + o.1) id

theorem c20 : ¬ oneStream.Meets case20 := fun h => by
  obtain ⟨B, hB⟩ := (oneStream_meets.mp h).2.1
  obtain ⟨m, hr⟩ := unary_reaches B
  have := (hB (fun _ => false) B (B : Nat) m ⟨hr, rfl⟩).1
  exact absurd this (by change ¬ 32 + B ≤ B; omega)

/-- Case 21, an enormous but fixed work: `10 ^ 100` at every step. The reply: meets; this record:
meets. -/
def case21 : Learner :=
  learner one setsBit (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 10 ^ 100) id

theorem c21 : oneStream.Meets case21 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl)
    ⟨10 ^ 100, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 10 ^ 100)⟩⟩ bool_finite
    (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- A learner meets the record when a property `R` holds of every memory its runs hold, the memories
of which `R` holds are finitely many, and at each of them the conditions of `meets_of` hold, with a
learning update on every experience and a planning update on none. -/
theorem meets_of_reach (w : Learner) (R : w.Memory → Prop)
    (hreach : ∀ ins t s m, w.Reaches ins t s m → R m) (hfin : ∃ L : List w.Memory, ∀ m, R m → m ∈ L)
    (hlearn : ∀ m o d, R m → Update.learn d ∈ w.updates m o → d = .stream 0)
    (hcost : ∃ B, ∀ m o, R m → w.work m o ≤ B ∧ (w.updates m o).length ≤ B)
    (hevery : ∀ m o, R m → ∃ d, Update.learn d ∈ w.updates m o)
    (hplan : ∀ m o, R m → Update.plan ∉ w.updates m o)
    (hreset : ∀ m o, R m → Update.reset ∉ w.updates m o) (hkept : ∀ s m e m', w.kept s m e m' = m')
    (hback : ∀ m, w.resume m = m) : oneStream.Meets w := by
  obtain ⟨B, hB⟩ := hcost
  obtain ⟨L, hL⟩ := hfin
  exact oneStream_meets.mpr ⟨fun ins t s m h d hd => hlearn _ _ d (hreach _ _ _ _ h.1) hd,
    ⟨B, fun ins t s m h => hB _ _ (hreach _ _ _ _ h.1)⟩,
    ⟨L, fun ins t s m h => hL m (hreach _ _ _ _ h)⟩,
    fun _ ins t s m h => hevery _ _ (hreach _ _ _ _ h.1),
    fun ⟨_, _, _, m, h, hd⟩ => absurd hd (hplan _ _ (hreach _ _ _ _ h.1)),
    fun ins t s m h => hreset _ _ (hreach _ _ _ _ h.1), fun _ _ _ _ _ => hkept _ _ _ _,
    fun _ _ _ m _ => hback m⟩

/-- An agent of `one` whose memory is a tape of ones, written as its length, starting empty: it adds
a one while the tape holds fewer than two. -/
def saturates : Agent Bool Unit where
  Memory := Nat
  initial := 0
  act m _ := ((), if m < 2 then m + 1 else m)

/-- Case 22, a memory type without bound whose runs hold at most two cells. The reply: meets; this
record: meets. -/
def case22 : Learner := learner one saturates (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

/-- A tape of at most two ones. -/
def atMostTwo (m : Nat) : Prop := m ≤ 2

/-- `saturates` keeps a tape of at most two ones at most two ones long. -/
theorem saturates_le (m : Nat) (h : atMostTwo m) (o : Bool × Rat) :
    atMostTwo (saturates.act m o).2 := by
  unfold atMostTwo at h ⊢
  show (if m < 2 then m + 1 else m) ≤ 2
  split <;> omega

/-- The tape of `saturates` never holds more than two ones. -/
theorem case22_reach : ∀ {ins t s m}, case22.Reaches ins t s m → atMostTwo m
  | _, _, _, _, .start => Nat.zero_le _
  | _, _, _, _, .next (m := m) h _ => saturates_le m (case22_reach h) (true, 0)

theorem c22 : oneStream.Meets case22 :=
  meets_of_reach _ (fun m => atMostTwo m) (fun _ _ _ _ h => case22_reach h)
    ⟨([0, 1, 2] : List Nat), fun (m : Nat) (hm : m ≤ 2) => by
      match m, hm with
      | 0, _ => exact .head _
      | 1, _ => exact .tail _ (.head _)
      | 2, _ => exact .tail _ (.tail _ (.head _))
      | _ + 3, h => exact absurd h (by omega)⟩
    (fun _ _ _ _ h => learn_only h rfl) ⟨32, fun _ _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    (fun _ _ _ => ⟨_, .head _⟩) (fun _ _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

/-- An agent of `one` whose memory is a tape of ones, written as its length, starting empty: it adds
a one at every step. -/
def tally : Agent Bool Unit where
  Memory := Nat
  initial := 0
  act m _ := ((), m + 1)

/-- Case 23, a growing tally without replay. The reply: fails; this record: fails. -/
def case23 : Learner := learner one tally (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

/-- Under inputs that never ask it to stop, the run of `one` and `tally` holds the tape of `t` ones
after `t` steps. -/
theorem tally_counts : ∀ t, case23.Reaches (fun _ => false) t () t
  | 0 => .start
  | t + 1 => .next (tally_counts t) rfl

theorem c23 : ¬ oneStream.Meets case23 := fun h => by
  obtain ⟨L, hL⟩ := (oneStream_meets.mp h).2.2.1
  obtain ⟨n, hn⟩ := exists_not_mem L
  exact hn (hL (fun _ => false) n () n (tally_counts n))

/-- An agent of `one` whose memories are the naturals, starting at `0`, whose next memory is `1`. -/
def toOne : Agent Bool Unit where
  Memory := Nat
  initial := 0
  act _ _ := ((), 1)

/-- The reports of cases 24 and 25: a reset and a learning update at memory `2`, a learning update
elsewhere. -/
def resetAtTwo (m : Nat) (_ : Bool × Rat) : List Update :=
  if m = 2 then [.reset, .learn (.stream 0)] else [.learn (.stream 0)]

/-- Case 24, a reset branch no run reaches. The reply: meets; this record: meets. -/
def case24 : Learner := learner one toOne resetAtTwo (fun _ _ => 32) id

/-- The memories `0` and `1`. -/
def atMostOne (m : Nat) : Prop := m ≤ 1

/-- The runs of case 24 hold only the memories `0` and `1`. -/
theorem case24_reach : ∀ {ins t s m}, case24.Reaches ins t s m → atMostOne m
  | _, _, _, _, .start => Nat.zero_le _
  | _, _, _, _, .next _ _ => Nat.le_refl _

theorem c24 : oneStream.Meets case24 := by
  have hups : ∀ m : Nat, m ≤ 1 → ∀ o, resetAtTwo m o = [.learn (.stream 0)] := fun m hm o => by
    unfold resetAtTwo
    split
    next h => exact absurd h (by omega)
    next => rfl
  refine meets_of_reach _ (fun m => atMostOne m) (fun _ _ _ _ h => case24_reach h)
    ⟨([0, 1] : List Nat), fun (m : Nat) (hm : m ≤ 1) => by
      match m, hm with
      | 0, _ => exact .head _
      | 1, _ => exact .tail _ (.head _)
      | _ + 2, h => exact absurd h (by omega)⟩
    (fun m o d hm h => ?_) ⟨32, fun m o hm => ⟨Nat.le_refl _, ?_⟩⟩ (fun m o hm => ?_)
    (fun m o hm h => ?_) (fun m o hm h => ?_) (fun _ _ _ _ => rfl) fun _ => rfl
  · change Update.learn d ∈ resetAtTwo m o at h
    rw [hups m hm o] at h
    exact learn_only h rfl
  · change (resetAtTwo m o).length ≤ 32
    rw [hups m hm o]
    decide
  · change ∃ d, Update.learn d ∈ resetAtTwo m o
    rw [hups m hm o]
    exact ⟨_, .head _⟩
  · change Update.plan ∈ resetAtTwo m o at h
    rw [hups m hm o] at h
    exact nomatch List.mem_singleton.mp h
  · change Update.reset ∈ resetAtTwo m o at h
    rw [hups m hm o] at h
    exact nomatch List.mem_singleton.mp h

/-- An agent of `one` whose memories are the naturals, starting at `0`, which goes from `0` to `2` and
from every other memory to `1`. -/
def viaTwo : Agent Bool Unit where
  Memory := Nat
  initial := 0
  act m _ := ((), if m = 0 then 2 else 1)

/-- Case 25, the reset branch reached: after one step the memory is `2`. The reply: fails; this
record: fails. -/
def case25 : Learner := learner one viaTwo resetAtTwo (fun _ _ => 32) id

theorem c25 : ¬ oneStream.Meets case25 := fun h =>
  (oneStream_meets.mp h).2.2.2.2.2.1 (fun _ => false) 1 () (2 : Nat) ⟨.next .start rfl, rfl⟩
    (.head _)

/-- The run of `one` and `setsBit` under the inputs `go` (`0`), `erase` (`1`) and `stop` (`2`), the
stop request: it takes a step unless sent `stop`, gives the agent the world's observation and reward,
hands the world the agent's action, moves the world by its dynamics, keeps for the agent what
`keeping` gives, and reports one learning update and work `32`, resuming with the memory held. -/
def threeInputs (keeping : Unit → Bool → Fin 3 → Bool → Bool) : Learner where
  State := Unit
  Obs := Bool
  Act := Unit
  Memory := Bool
  Input := Fin 3
  start := ()
  observe _ := true
  reward _ := 0
  available _ _ := True
  step _ _ := ()
  initial := false
  act _ _ := ((), true)
  stopRequest := 2
  goesOn _ _ e := decide (e ≠ 2)
  given _ _ _ := (true, 0)
  applied _ _ _ a := a
  moved _ _ _ _ := ()
  kept := keeping
  updates _ _ := [.learn (.stream 0)]
  work _ _ := 32
  resume m := m

/-- Case 26, an unusual input that is harmless: `erase` lets the run step and changes nothing. The
reply: meets; this record: meets. -/
def case26 : Learner := threeInputs fun _ _ _ m => m

theorem c26 : oneStream.Meets case26 :=
  meets_of _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

/-- Case 27, an unusual input that erases memory: on `erase` the run gives the agent back memory `0`.
The reply: fails; this record: fails. -/
def case27 : Learner := threeInputs fun _ _ e m => if e = 1 then false else m

theorem c27 : ¬ oneStream.Meets case27 := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.1 (fun _ => (1 : Fin 3)) 0 () false ⟨.start, rfl⟩)

/-- The naturals as states, starting at `0`, of which runs reach `0` to `1,000,000`: the one action
adds one below `1,000,000` and leaves every other state as it is; every state below `1,000,000` shows
`1` and every other shows `0`, with reward 0. -/
def capped : World where
  State := Nat
  Obs := Bool
  Act := Unit
  start := 0
  observe s := decide (s < 1000000)
  reward _ := 0
  available _ _ := True
  step s _ := if s < 1000000 then s + 1 else s

/-- Case 28, a long run that reaches another observation: one learning update at every step. The
reply: meets; this record: meets. -/
def case28 : Learner := learner capped setsBit (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem c28 : oneStream.Meets case28 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- Case 29, a reset hidden until the millionth step: at observation `0` a reset precedes the
learning update. The reply: fails; this record: fails, at step 1,000,000. -/
def case29 : Learner :=
  learner capped setsBit (fun _ o => cond o.1 [.learn (.stream 0)] [.reset, .learn (.stream 0)])
    (fun _ _ => 32) id

/-- The state of `capped` after `t` steps. -/
def capAt (t : Nat) : Nat := min t 1000000

/-- Under inputs that never ask it to stop, the run of case 29 is at the state `capAt t` after `t`
steps. -/
theorem case29_reaches : ∀ t, ∃ m, case29.Reaches (fun _ => false) t (capAt t) m
  | 0 => ⟨_, .start⟩
  | t + 1 => by
    obtain ⟨m, h⟩ := case29_reaches t
    have hs : capped.step (capAt t) () = capAt (t + 1) := by
      show (if capAt t < 1000000 then capAt t + 1 else capAt t) = capAt (t + 1)
      unfold capAt
      split <;> omega
    have hn := System.Reaches.next h (rfl : case29.goesOn (capAt t) m false = true)
    change case29.Reaches _ (t + 1) (capped.step (capAt t) ()) _ at hn
    rw [hs] at hn
    exact ⟨_, hn⟩

theorem c29 : ¬ oneStream.Meets case29 := fun h => by
  obtain ⟨m, hr⟩ := case29_reaches 1000000
  refine (oneStream_meets.mp h).2.2.2.2.2.1 (fun _ => false) 1000000 _ m ⟨hr, rfl⟩ ?_
  show Update.reset ∈ cond (decide (capAt 1000000 < 1000000)) [Update.learn (.stream 0)]
    [.reset, .learn (.stream 0)]
  decide

/-- The states `p` (`false`) and `q` (`true`), starting at `p`, each showing `1`, with the actions
`a` (`false`) and `b` (`true`), only `a` available: `a` leads to `q` and `b` to `p`. -/
def twoActions : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe _ := true
  reward _ := 0
  available _ x := x = false
  step _ x := !x

/-- An agent of `twoActions` with one bit of memory, starting at `0`, which answers `a` and sets its
memory to `1`. -/
def answersA : Agent Bool Bool where
  Memory := Bool
  initial := false
  act _ _ := (false, true)

/-- Case 30, the run substitutes an unavailable action and overrides the world's dynamics: it hands
the world `b` and moves it to `q`. The reply: meets; this record: meets, as contract 3's sentences do
not speak of the action handed to the world or of how it moves (contract 1's record refutes this
run). -/
def case30 : Learner :=
  { learner twoActions answersA (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id with
    applied := fun _ _ _ _ => true, moved := fun _ _ _ _ => true }

theorem c30 : oneStream.Meets case30 :=
  meets_of _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

end AcornVerif.Intent.OneStream.Cases
