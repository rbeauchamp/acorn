/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.OneStream
import AcornVerif.Intent.WorldInterfaceConsequences

/-!
# The consequences of the record of learning from one stream

Each consequence of `AcornVerif.Intent.OneStream.oneStream` is proved here to hold of the record:
what it requires of every learner that meets it, the learners it rules out, each beside the learner
that differs from it only where it attacks and meets the record, and the learners it still allows.
-/

namespace AcornVerif.Intent.OneStream

open LeanIntent WorldInterface

/-! ## Resuming after a stop -/

namespace Learner

variable (w : Learner)

/-- The learner resumed after a stop at the state `s` with the memory `m`: the same world, agent, run
and reports, its run beginning at `s`, where the world waited, with the memory the agent resumes
with. -/
def resumedAt (s : w.State) (m : w.Memory) : Learner :=
  { w with start := s, initial := w.resume m }

end Learner

/-- The outside inputs `ins` before the time `t`, then, from `t` on, the inputs `ins'` from their
first: at the time `t + k` the input `ins' k`. -/
def splice {I : Type} (ins : Nat → I) (t : Nat) (ins' : Nat → I) : Nat → I :=
  fun j => if j < t then ins j else ins' (j - t)

theorem splice_after {I : Type} (ins : Nat → I) (t : Nat) (ins' : Nat → I) (k : Nat) :
    splice ins t ins' (t + k) = ins' k := by
  have : ¬ t + k < t := by omega
  simp only [splice, this, ite_false, Nat.add_sub_cancel_left]

/-- A run that has taken no step is at the world's start with the agent's initial memory. -/
theorem reaches_zero {v : WorldInterface.System} {ins : Nat → v.Input} {s : v.State}
    {m : v.Memory} (h : v.Reaches ins 0 s m) : s = v.start ∧ m = v.initial := by
  cases h
  exact ⟨rfl, rfl⟩

/-- A run that has taken `k + 1` steps took its last from what it reached after `k`. -/
theorem reaches_succ {v : WorldInterface.System} {ins : Nat → v.Input} {k : Nat} {s' : v.State}
    {m' : v.Memory} (h : v.Reaches ins (k + 1) s' m') :
    ∃ s m, v.Reaches ins k s m ∧ v.goesOn s m (ins k) = true ∧
      s' = v.moved s m (ins k) (v.applied s m (ins k) (v.answer s m (ins k)).1) ∧
      m' = v.kept s m (ins k) (v.answer s m (ins k)).2 := by
  cases h with
  | next h hgo => exact ⟨_, _, h, hgo, rfl, rfl⟩

/-- A run reaches the same state and memory after `t` steps under two sequences of outside inputs
that agree before `t`. -/
theorem reaches_congr {v : WorldInterface.System} {ins ins' : Nat → v.Input} :
    ∀ {t s m}, (∀ j, j < t → ins j = ins' j) → v.Reaches ins t s m → v.Reaches ins' t s m
  | 0, _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := reaches_zero h
    exact .start
  | t + 1, _, _, hagree, h => by
    obtain ⟨_, _, hr, hgo, rfl, rfl⟩ := reaches_succ h
    have he := hagree t (Nat.lt_succ_self t)
    have h' := reaches_congr (fun j hj => hagree j (Nat.lt_succ_of_lt hj)) hr
    rw [he] at hgo ⊢
    exact .next h' hgo

/-- Under the outside inputs `ins` up to a stop at the time `t` and `ins'` after it, the run reaches
the stop's state and memory at `t`. -/
theorem stop_reaches_splice {w : Learner} {ins : Nat → w.Input} {t : Nat} {s : w.State}
    {m : w.Memory} (h : w.Stops ins t s m) (ins' : Nat → w.Input) :
    w.Reaches (splice ins t ins') t s m :=
  reaches_congr (fun j hj => by simp [splice, hj]) h.1

/-- What a run resumed after a stop reaches, with the agent resuming with the memory it held, the
run that did not stop reaches at the same time after the stop, and conversely. -/
theorem resumed_reaches_iff {w : Learner} {ins : Nat → w.Input} {t : Nat} {s : w.State}
    {m : w.Memory} (h : w.Stops ins t s m) (hback : w.resume m = m) (ins' : Nat → w.Input) :
    ∀ k s' m', (w.resumedAt s m).Reaches ins' k s' m' ↔
      w.Reaches (splice ins t ins') (t + k) s' m'
  | 0, s', m' => by
    constructor
    · intro hr
      obtain ⟨hs, hm⟩ := reaches_zero hr
      rw [hs, hm]
      change w.Reaches (splice ins t ins') t s (w.resume m)
      rw [hback]
      exact stop_reaches_splice h ins'
    · intro hr
      obtain ⟨hs, hm⟩ := System.Reaches.unique (t := t) hr (stop_reaches_splice h ins')
      have hstart : (w.resumedAt s m).Reaches ins' 0 (w.resumedAt s m).start
          (w.resumedAt s m).initial := .start
      change (w.resumedAt s m).Reaches ins' 0 s (w.resume m) at hstart
      rw [hback] at hstart
      cases hs
      cases hm
      exact hstart
  | k + 1, s', m' => by
    constructor
    · intro hr
      obtain ⟨s1, m1, hr', hgo, rfl, rfl⟩ := reaches_succ hr
      have ih := (resumed_reaches_iff h hback ins' k s1 m1).mp hr'
      have hgo' : w.goesOn s1 m1 (splice ins t ins' (t + k)) = true := by
        rw [splice_after]; exact hgo
      have hn := System.Reaches.next ih hgo'
      rw [splice_after] at hn
      exact hn
    · intro hr
      obtain ⟨s1, m1, hr', hgo, rfl, rfl⟩ := reaches_succ (k := t + k) hr
      have ih := (resumed_reaches_iff h hback ins' k s1 m1).mpr hr'
      rw [splice_after] at hgo ⊢
      exact .next ih hgo

/-- **A stopped agent resumes where it stopped, and afterwards acts and learns as without the
stop.** After every stop a run makes, the run resumed in the world that waited, under any outside
inputs, reaches at each time after the stop exactly what the run that did not stop reaches then
under those inputs, and at each state, memory and input it answers and makes the internal updates
the agent would without the stop. -/
def resumesAsWithoutStop : Consequence Learner :=
  ⟨"a stopped agent resumes where it stopped, and afterwards acts and learns as it would have \
    without the stop, in a world that waited for it", .entailment, fun w =>
    ∀ ins t s m, w.Stops ins t s m → ∀ ins' : Nat → w.Input,
      (∀ k s' m', (w.resumedAt s m).Reaches ins' k s' m' ↔
        w.Reaches (splice ins t ins') (t + k) s' m') ∧
      ∀ s' m' e, (w.resumedAt s m).answer s' m' e = w.answer s' m' e ∧
        (w.resumedAt s m).stepUpdates s' m' e = w.stepUpdates s' m' e⟩

theorem resumesAsWithoutStop_holds : resumesAsWithoutStop.HoldsOf oneStream :=
  fun _ hw _ _ _ _ h ins' =>
    ⟨resumed_reaches_iff h ((oneStream_meets.mp hw).2.2.2.2.2.2.2 _ _ _ _ h) ins',
      fun _ _ _ => ⟨rfl, rfl⟩⟩

/-- What holds of the input the run that did not stop is sent at the time `t + k` holds of the
input the resumed run is sent at its time `k`. -/
theorem of_splice {I : Type} {ins : Nat → I} {t : Nat} {ins' : Nat → I} {k : Nat} (P : I → Prop)
    (h : P (splice ins t ins' (t + k))) : P (ins' k) := by
  rw [splice_after] at h
  exact h

/-- What holds of the input the resumed run is sent at its time `k` holds of the input the run that
did not stop is sent at the time `t + k`. -/
theorem to_splice {I : Type} {ins : Nat → I} {t : Nat} {ins' : Nat → I} {k : Nat} (P : I → Prop)
    (h : P (ins' k)) : P (splice ins t ins' (t + k)) := by
  rw [splice_after]
  exact h

/-- A step the resumed run takes is a step the run that did not stop takes. -/
theorem resumed_takes {w : Learner} {ins : Nat → w.Input} {t : Nat} {s : w.State} {m : w.Memory}
    (h : w.Stops ins t s m) (hback : w.resume m = m) {ins' : Nat → w.Input} {k : Nat}
    {s' : w.State} {m' : w.Memory} (hk : (w.resumedAt s m).Takes ins' k s' m') :
    w.Takes (splice ins t ins') (t + k) s' m' :=
  ⟨(resumed_reaches_iff h hback ins' k s' m').mp hk.1, by rw [splice_after]; exact hk.2⟩

/-- A stop the resumed run makes is a stop the run that did not stop makes. -/
theorem resumed_stops {w : Learner} {ins : Nat → w.Input} {t : Nat} {s : w.State} {m : w.Memory}
    (h : w.Stops ins t s m) (hback : w.resume m = m) {ins' : Nat → w.Input} {k : Nat}
    {s' : w.State} {m' : w.Memory} (hk : (w.resumedAt s m).Stops ins' k s' m') :
    w.Stops (splice ins t ins') (t + k) s' m' :=
  ⟨(resumed_reaches_iff h hback ins' k s' m').mp hk.1, by rw [splice_after]; exact hk.2⟩

/-- **Every run, the runs resumed after a stop included.** After every stop a run makes, the learner
resumed in the world that waited meets the record too. -/
def resumedMeets : Consequence Learner :=
  ⟨"a run resumed after a stop meets the record too", .entailment, fun w =>
    ∀ ins t s m, w.Stops ins t s m → oneStream.Meets (w.resumedAt s m)⟩

theorem resumedMeets_holds : resumedMeets.HoldsOf oneStream := by
  intro w hw ins t s m h
  obtain ⟨h1, ⟨B, hB⟩, ⟨L, hL⟩, h4, h5, h6, h7, h8⟩ := oneStream_meets.mp hw
  have hback := h8 _ _ _ _ h
  refine oneStream_meets.mpr ⟨fun ins' k s' m' hk => ?_, ⟨B, fun ins' k s' m' hk => ?_⟩,
    ⟨L, fun ins' k s' m' hr => hL _ _ _ _ ((resumed_reaches_iff h hback ins' k s' m').mp hr)⟩,
    fun ⟨ins', k, s', m', d, hk, hd⟩ ins'' k' s'' m'' hk' => ?_,
    fun ⟨ins', k, s', m', hk, hd⟩ ins'' k' s'' m'' hk' => ?_,
    fun ins' k s' m' hk => ?_, fun ins' k s' m' hk => ?_,
    fun ins' k s' m' hk => h8 _ _ _ _ (resumed_stops h hback hk)⟩
  · exact of_splice (fun e => ∀ d, Update.learn d ∈ w.stepUpdates s' m' e → d = .stream 0)
      (h1 (splice ins t ins') (t + k) s' m' (resumed_takes h hback hk))
  · exact of_splice (fun e => w.stepWork s' m' e ≤ B ∧ (w.stepUpdates s' m' e).length ≤ B)
      (hB (splice ins t ins') (t + k) s' m' (resumed_takes h hback hk))
  · exact of_splice (fun e => ∃ d, Update.learn d ∈ w.stepUpdates s'' m'' e)
      (h4 ⟨splice ins t ins', t + k, s', m', d, resumed_takes h hback hk,
        to_splice (fun e => Update.learn d ∈ w.stepUpdates s' m' e) hd⟩
        (splice ins t ins'') (t + k') s'' m'' (resumed_takes h hback hk'))
  · exact of_splice (fun e => Update.plan ∈ w.stepUpdates s'' m'' e)
      (h5 ⟨splice ins t ins', t + k, s', m', resumed_takes h hback hk,
        to_splice (fun e => Update.plan ∈ w.stepUpdates s' m' e) hd⟩
        (splice ins t ins'') (t + k') s'' m'' (resumed_takes h hback hk'))
  · exact of_splice (fun e => Update.reset ∉ w.stepUpdates s' m' e)
      (h6 (splice ins t ins') (t + k) s' m' (resumed_takes h hback hk))
  · exact of_splice (fun e => w.kept s' m' e (w.answer s' m' e).2 = (w.answer s' m' e).2)
      (h7 (splice ins t ins') (t + k) s' m' (resumed_takes h hback hk))

/-! ## Learning on arrival -/

/-- **A learner learns from each experience as it arrives.** If the agent learns on some step a run
takes, then at every step every run takes it makes a learning update on the experience that step
was given, and no learning update on anything else. -/
def learnsEachOnArrival : Consequence Learner :=
  ⟨"an agent that learns on some step learns, on every step, from the experience that step was \
    given and from nothing else", .entailment, fun w =>
    (∃ ins t s m d, w.Takes ins t s m ∧ Update.learn d ∈ w.stepUpdates s m (ins t)) →
      ∀ ins t s m, w.Takes ins t s m →
        Update.learn (.stream 0) ∈ w.stepUpdates s m (ins t) ∧
          ∀ d, Update.learn d ∈ w.stepUpdates s m (ins t) → d = .stream 0⟩

theorem learnsEachOnArrival_holds : learnsEachOnArrival.HoldsOf oneStream := by
  intro w hw hsome ins t s m h
  obtain ⟨h1, -, -, h4, -⟩ := oneStream_meets.mp hw
  obtain ⟨d, hd⟩ := h4 hsome ins t s m h
  exact ⟨h1 ins t s m h d hd ▸ hd, h1 ins t s m h⟩

/-! ## Learners the record rules out, each beside the learner that differs only where it attacks -/

/-- `base`, which also learns at each step from the experience the step before was given. -/
def replaysLast : Learner :=
  { base with updates := fun _ _ => [.learn (.stream 0), .learn (.stream 1)] }

/-- Under inputs that never ask it to stop, the run of `base` is at its start state with its initial
memory after one step. -/
theorem base_reaches_one : base.Reaches neverStop 1 false false := .next .start rfl

theorem replaysLast_fails : ¬ oneStream.Meets replaysLast := fun h =>
  absurd ((oneStream_meets.mp h).1 neverStop 1 _ _ ⟨base_reaches_one, rfl⟩ _ (.tail _ (.head _)))
    (by decide)

/-- **Replaying the last experience is ruled out**: the learner `replaysLast`, which at each step
learns from the experience that step was given and again from the one the step before was given.
Its neighbour is `base`. -/
def rulesOutReplay : Consequence Learner :=
  ⟨"the learner replaysLast, which learns again from the previous step's experience, is ruled out",
    .entailment, fun w => w ≠ replaysLast⟩

theorem rulesOutReplay_holds : rulesOutReplay.HoldsOf oneStream :=
  fun _ hw he => replaysLast_fails (he ▸ hw)

/-- `base`, which also learns at each step from data that is no experience of its own stream. -/
def learnsElsewhere : Learner :=
  { base with updates := fun _ _ => [.learn (.stream 0), .learn .other] }

theorem learnsElsewhere_fails : ¬ oneStream.Meets learnsElsewhere := fun h =>
  absurd ((oneStream_meets.mp h).1 neverStop 0 _ _ (takes_first (w := base.toSystem) rfl) _
    (.tail _ (.head _))) (by decide)

/-- **Learning from outside its one stream is ruled out**: the learner `learnsElsewhere`. Its
neighbour is `base`. -/
def rulesOutOtherStream : Consequence Learner :=
  ⟨"the learner learnsElsewhere, which learns from data that is no experience of its own stream, is \
    ruled out", .entailment, fun w => w ≠ learnsElsewhere⟩

theorem rulesOutOtherStream_holds : rulesOutOtherStream.HoldsOf oneStream :=
  fun _ hw he => learnsElsewhere_fails (he ▸ hw)

/-- An agent that answers with what it sees and stores every observation it has seen. -/
def hoarder : Agent Bool Bool where
  Memory := List Bool
  initial := []
  act m o := (o.1, o.1 :: m)

/-- The faithful run of `mirror` and `hoarder`, which learns from the experience each step was
given and replays none. -/
def storesStream : Learner :=
  learner mirror hoarder (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id

/-- Under inputs that never ask it to stop, the run of `mirror` and `hoarder` holds a memory of length
`t` after `t` steps. -/
theorem hoarder_grows : ∀ t, ∃ s m, (couple mirror hoarder).Reaches neverStop t s m ∧
    List.length (α := Bool) m = t
  | 0 => ⟨_, _, .start, rfl⟩
  | t + 1 =>
    let ⟨_, _, h, hl⟩ := hoarder_grows t
    ⟨_, _, .next h rfl, congrArg Nat.succ hl⟩

theorem storesStream_fails : ¬ oneStream.Meets storesStream := fun h => by
  obtain ⟨L, hL⟩ := (oneStream_meets.mp h).2.2.1
  obtain ⟨n, hn⟩ := exists_not_mem (L.map (List.length (α := Bool)))
  obtain ⟨_, m, hr, hl⟩ := hoarder_grows n
  exact hn (hl ▸ List.mem_map_of_mem (hL neverStop n _ m hr))

/-- **Storing the whole stream is ruled out, though nothing is replayed**: the learner
`storesStream`, whose agent keeps every observation it is given. Its neighbour is `base`, whose
agent keeps only the last. -/
def rulesOutStoringStream : Consequence Learner :=
  ⟨"the learner storesStream, which keeps every observation it is given though it replays none, is \
    ruled out", .entailment, fun w => w ≠ storesStream⟩

theorem rulesOutStoringStream_holds : rulesOutStoringStream.HoldsOf oneStream :=
  fun _ hw he => storesStream_fails (he ▸ hw)

/-- The neighbour of `growingWork`: the same world and agent, reporting no work. -/
theorem noWork_meets : oneStream.Meets (learner clock still (fun _ _ => []) (fun _ _ => 0) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch h) ⟨0, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
    ⟨[()], fun _ => .head _⟩ (.inr fun _ _ _ h => nomatch h) (.inr fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h) fun _ => rfl

theorem growingWork_fails : ¬ oneStream.Meets growingWork := fun h => by
  obtain ⟨B, hB⟩ := (oneStream_meets.mp h).2.1
  have := (hB neverStop (B + 1) _ _ ⟨clock_reaches (B + 1), rfl⟩).1
  exact absurd this (by change ¬ B + 1 ≤ B; omega)

/-- **Work that grows as the run goes on is ruled out**: the learner `growingWork`, whose step does
as much work as the number of steps taken before it. Its neighbour reports no work
(`noWork_meets`). -/
def rulesOutGrowingWork : Consequence Learner :=
  ⟨"the learner growingWork, whose work grows with the number of steps taken, is ruled out",
    .entailment, fun w => w ≠ growingWork⟩

theorem rulesOutGrowingWork_holds : rulesOutGrowingWork.HoldsOf oneStream :=
  fun _ hw he => growingWork_fails (he ▸ hw)

/-- The faithful run of `clock` and `still`, which plans once more at each step than at the step
before. -/
def plansMore : Learner :=
  learner clock still (fun _ (o : Nat × Rat) => List.replicate (o.1 + 1) .plan) (fun _ _ => 0) id

theorem plansMore_fails : ¬ oneStream.Meets plansMore := fun h => by
  obtain ⟨B, hB⟩ := (oneStream_meets.mp h).2.1
  have := (hB neverStop B _ _ ⟨clock_reaches B, rfl⟩).2
  exact absurd this (by change ¬ (List.replicate (B + 1) Update.plan).length ≤ B; simp)

/-- The neighbour of `plansMore`: the same world and agent, planning once at each step. -/
theorem plansOnceEach_meets :
    oneStream.Meets (learner clock still (fun _ _ => [.plan]) (fun _ _ => 0) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch List.mem_singleton.mp h)
    ⟨1, fun _ _ => ⟨Nat.zero_le _, Nat.le_refl _⟩⟩ ⟨[()], fun _ => .head _⟩
    (.inr fun _ _ _ h => nomatch List.mem_singleton.mp h) (.inl fun _ _ => .head _)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- **Internal updates that grow in number are ruled out**: the learner `plansMore`. Its neighbour
plans once at each step (`plansOnceEach_meets`). -/
def rulesOutGrowingUpdates : Consequence Learner :=
  ⟨"the learner plansMore, which makes one more planning update at each step, is ruled out",
    .entailment, fun w => w ≠ plansMore⟩

theorem rulesOutGrowingUpdates_holds : rulesOutGrowingUpdates.HoldsOf oneStream :=
  fun _ hw he => plansMore_fails (he ▸ hw)

/-- Every memory of `trained` is in the list of its two memories. -/
theorem trained_finite : ∃ L : List trained.Memory, ∀ m, m ∈ L :=
  ⟨[false, true], fun m => by cases m with
    | false => exact .head _
    | true => exact .tail _ (.head _)⟩

theorem learnsOnce_fails : ¬ oneStream.Meets learnsOnce := fun h => by
  obtain ⟨d, hd⟩ := (oneStream_meets.mp h).2.2.2.1 ⟨neverStop, 0, false, false, _,
    takes_first (w := learnsOnce.toSystem) rfl, List.mem_singleton_self _⟩ neverStop 1 false true
    ⟨trained_reaches_one, rfl⟩
  exact nomatch hd

/-- The neighbour of `learnsOnce`: the same world and agent, learning at every step. -/
theorem learnsAlways_meets :
    oneStream.Meets (learner mirror trained (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ trained_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- **A training period is ruled out**: the learner `learnsOnce`, which learns on its first step and
never after. Its neighbour learns at every step (`learnsAlways_meets`). -/
def rulesOutTrainingPeriod : Consequence Learner :=
  ⟨"the learner learnsOnce, which learns on its first step only, is ruled out", .entailment,
    fun w => w ≠ learnsOnce⟩

theorem rulesOutTrainingPeriod_holds : rulesOutTrainingPeriod.HoldsOf oneStream :=
  fun _ hw he => learnsOnce_fails (he ▸ hw)

theorem plansOnce_fails : ¬ oneStream.Meets plansOnce := fun h => by
  have hd := (oneStream_meets.mp h).2.2.2.2.1 ⟨neverStop, 0, false, false,
    takes_first (w := plansOnce.toSystem) rfl, List.mem_singleton_self _⟩ neverStop 1 false true
    ⟨trained_reaches_one, rfl⟩
  exact nomatch hd

/-- The neighbour of `plansOnce`: the same world and agent, planning at every step. -/
theorem plansAlways_meets :
    oneStream.Meets (learner mirror trained (fun _ _ => [.plan]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch List.mem_singleton.mp h)
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ trained_finite
    (.inr fun _ _ _ h => nomatch List.mem_singleton.mp h) (.inl fun _ _ => .head _)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- **A planning period is ruled out**: the learner `plansOnce`, which plans on its first step and
never after. Its neighbour plans at every step (`plansAlways_meets`). -/
def rulesOutPlanningPeriod : Consequence Learner :=
  ⟨"the learner plansOnce, which plans on its first step only, is ruled out", .entailment,
    fun w => w ≠ plansOnce⟩

theorem rulesOutPlanningPeriod_holds : rulesOutPlanningPeriod.HoldsOf oneStream :=
  fun _ hw he => plansOnce_fails (he ▸ hw)

/-- An agent of contract 1's world `attempts` that answers with what it sees and remembers whether it
has seen `false`, the world's start, since its life began. -/
def keeper : Agent Bool Bool where
  Memory := Bool
  initial := false
  act m o := (o.1, m || !o.1)

/-- An agent like `keeper` that, at each step where it sees `true`, the state from which `attempts`
restarts, sets its memory back to its initial value `false`, discarding what it remembered. -/
def resetter : Agent Bool Bool where
  Memory := Bool
  initial := false
  act m o := (o.1, cond o.1 false (m || !o.1))

/-- The faithful run of `attempts` and `resetter`, which reports a learning update at each step and
a reset at each step from which the world restarts. -/
def resetsAtRestart : Learner :=
  learner attempts resetter (fun _ o => cond o.1 [.learn (.stream 0), .reset] [.learn (.stream 0)])
    (fun _ _ => 1) id

/-- Under inputs that never ask it to stop, the run of `attempts` and `resetter` is, after one step,
at `true`, the state from which the world restarts, with the memory `true`, which its next step
discards. -/
theorem resetter_reaches_one : resetsAtRestart.Reaches neverStop 1 true true := .next .start rfl

theorem resetsAtRestart_fails : ¬ oneStream.Meets resetsAtRestart := fun h =>
  (oneStream_meets.mp h).2.2.2.2.2.1 neverStop 1 true true ⟨resetter_reaches_one, rfl⟩
    (.tail _ (.head _))

/-- The neighbour of `resetsAtRestart`: the same world with `keeper`, which keeps what it remembers
when the world restarts and reports no reset. -/
theorem attemptsKeeper_meets :
    oneStream.Meets (learner attempts keeper (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- The neighbour of the learners below that attack the run and the resumption: contract 1's world
`attempts` with `lastSeen`, run faithfully, resuming with the memory it held. -/
theorem attemptsLastSeen_meets :
    oneStream.Meets (learner attempts lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- **An agent that resets itself when the world restarts is ruled out**: the learner
`resetsAtRestart`, whose agent sets its memory back to its initial value at each step from which the
world `attempts` restarts and reports that reset. Its neighbour keeps its memory
(`attemptsKeeper_meets`). -/
def rulesOutSelfReset : Consequence Learner :=
  ⟨"the learner resetsAtRestart, whose agent resets its memory when the world restarts, is ruled out",
    .entailment, fun w => w ≠ resetsAtRestart⟩

theorem rulesOutSelfReset_holds : rulesOutSelfReset.HoldsOf oneStream :=
  fun _ hw he => resetsAtRestart_fails (he ▸ hw)

/-- The run of `attempts` and `lastSeen` in which the run gives the agent back its initial memory at
each step from which the world restarts, and is otherwise faithful. -/
def runResetsAtRestart : Learner :=
  { learner attempts lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id with
    kept := fun s _ _ m => cond s false m }

theorem runResetsAtRestart_fails : ¬ oneStream.Meets runResetsAtRestart := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.1 neverStop 1 _ _
    ⟨(show runResetsAtRestart.Reaches neverStop 1 true false from .next .start rfl), rfl⟩)

/-- **A run that resets the agent's memory when the world restarts is ruled out**: the learner
`runResetsAtRestart`. Its neighbour, run faithfully, meets the record (`attemptsLastSeen_meets`). -/
def rulesOutRunReset : Consequence Learner :=
  ⟨"the learner runResetsAtRestart, whose run resets the agent's memory when the world restarts, is \
    ruled out", .entailment, fun w => w ≠ runResetsAtRestart⟩

theorem rulesOutRunReset_holds : rulesOutRunReset.HoldsOf oneStream :=
  fun _ hw he => runResetsAtRestart_fails (he ▸ hw)

/-- The run of `attempts` and `lastSeen` in which the agent resumes every stop with its initial
memory. -/
def resumesFresh : Learner :=
  learner attempts lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) fun _ => false

/-- The outside inputs that let the run take its first two steps and then ask it to stop. -/
def stopAtTwo : Nat → Bool := fun j => decide (2 ≤ j)

/-- Under `stopAtTwo`, the run of `attempts` and `lastSeen` stops after two steps, having seen
`true` at its second. -/
theorem resumesFresh_stops : resumesFresh.Stops stopAtTwo 2 false true :=
  ⟨.next (.next .start rfl) rfl, rfl⟩

theorem resumesFresh_fails : ¬ oneStream.Meets resumesFresh := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.2 _ _ _ _ resumesFresh_stops)

/-- **Resuming with a fresh memory is ruled out**: the learner `resumesFresh`, whose agent resumes
every stop with its initial memory. Its neighbour resumes with the memory it held
(`attemptsLastSeen_meets`). -/
def rulesOutFreshResume : Consequence Learner :=
  ⟨"the learner resumesFresh, whose agent resumes a stop with its initial memory, is ruled out",
    .entailment, fun w => w ≠ resumesFresh⟩

theorem rulesOutFreshResume_holds : rulesOutFreshResume.HoldsOf oneStream :=
  fun _ hw he => resumesFresh_fails (he ▸ hw)

/-! ## What the record still allows -/

/-- `base` making two learning updates on the experience each step was given and a planning update,
with three units of work. -/
def severalAtOnce : Learner :=
  learner mirror lastSeen (fun _ _ => [.learn (.stream 0), .learn (.stream 0), .plan])
    (fun _ _ => 3) id

theorem severalAtOnce_meets : oneStream.Meets severalAtOnce :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> first | exact Update.learn.inj h | exact nomatch h)
    ⟨3, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, .head _⟩) (.inl fun _ _ => .tail _ (.tail _ (.head _)))
    (fun _ _ h => by simp at h) fun _ => rfl

/-- **Several internal updates per step**: some learner that meets the record makes, at a step a run
takes, two learning updates on the experience that step was given and a planning update. -/
def severalUpdates : Consequence Learner :=
  ⟨"an agent may make several internal updates in one step, learning more than once from the \
    experience that step was given and planning", .possibility, fun w =>
    ∃ ins t s m, w.Takes ins t s m ∧
      w.stepUpdates s m (ins t) = [.learn (.stream 0), .learn (.stream 0), .plan]⟩

theorem severalUpdates_holds : severalUpdates.HoldsOf oneStream :=
  ⟨severalAtOnce, severalAtOnce_meets, neverStop, 0, false, false,
    takes_first (w := severalAtOnce.toSystem) rfl, rfl⟩

/-- An agent that answers with what it sees and remembers the last two things it saw, a short-term
memory of its experience in the manner of an eligibility trace. -/
def lastTwo : Agent Bool Bool where
  Memory := Bool × Bool
  initial := (false, false)
  act m o := (o.1, (o.1, m.1))

/-- Every memory of `lastTwo` is in the list of its four memories. -/
theorem lastTwo_finite : ∃ L : List lastTwo.Memory, ∀ m, m ∈ L :=
  ⟨[(false, false), (false, true), (true, false), (true, true)], fun m => by
    obtain ⟨a, b⟩ := m
    cases a <;> cases b
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
    · exact .tail _ (.tail _ (.tail _ (.head _)))⟩

/-- The faithful run of `mirror` and `lastTwo`, which learns at each step from the experience that
step was given only. -/
def keepsShortTerm : Learner :=
  learner mirror lastTwo (fun _ _ => [.learn (.stream 0), .other]) (fun _ _ => 2) id

theorem keepsShortTerm_meets : oneStream.Meets keepsShortTerm :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> first | exact Update.learn.inj h | exact nomatch h)
    ⟨2, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
    lastTwo_finite
    (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) fun _ => rfl

/-- **Short-term memory of earlier experience, such as an eligibility trace**: some learner that
meets the record, and at every step a run takes learns only from the experience that step is given,
has an agent whose answer, applied twice from some memory, gives a memory that depends on the first
of the two experiences. -/
def keepsTrace : Consequence Learner :=
  ⟨"an agent may keep short-term memory of earlier experience, such as an eligibility trace, while \
    learning only from the experience each step is given", .possibility, fun w =>
    (∀ ins t s m, w.Takes ins t s m → ∀ d, Update.learn d ∈ w.stepUpdates s m (ins t) →
      d = .stream 0) ∧
    ∃ m o o' o'', (w.act (w.act m o).2 o'').2 ≠ (w.act (w.act m o').2 o'').2⟩

theorem keepsTrace_holds : keepsTrace.HoldsOf oneStream :=
  ⟨keepsShortTerm, keepsShortTerm_meets, (oneStream_meets.mp keepsShortTerm_meets).1,
    ((false, false) : Bool × Bool), ((true, 0) : Bool × Rat), ((false, 0) : Bool × Rat),
    ((false, 0) : Bool × Rat), show ((false, true) : Bool × Bool) ≠ (false, false) by decide⟩

/-- `base` learning and planning at each step, with two units of work. -/
def learnsAndPlans : Learner :=
  learner mirror lastSeen (fun _ _ => [.learn (.stream 0), .plan]) (fun _ _ => 2) id

theorem learnsAndPlans_meets : oneStream.Meets learnsAndPlans :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> first | exact Update.learn.inj h | exact nomatch h)
    ⟨2, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, .head _⟩) (.inl fun _ _ => .tail _ (.head _))
    (fun _ _ h => by simp at h) fun _ => rfl

/-- **Learning and planning on every step**: some learner that meets the record takes a step, and
at every step every run takes it makes a learning update and a planning update. -/
def learnsAndPlansEveryStep : Consequence Learner :=
  ⟨"an agent may learn, and plan with a model it has learned, on every step", .possibility, fun w =>
    (∃ ins t s m, w.Takes ins t s m) ∧ ∀ ins t s m, w.Takes ins t s m →
      Update.learn (.stream 0) ∈ w.stepUpdates s m (ins t) ∧
        Update.plan ∈ w.stepUpdates s m (ins t)⟩

theorem learnsAndPlansEveryStep_holds : learnsAndPlansEveryStep.HoldsOf oneStream :=
  ⟨learnsAndPlans, learnsAndPlans_meets,
    ⟨neverStop, 0, false, false, takes_first (w := learnsAndPlans.toSystem) rfl⟩,
    fun _ _ _ _ _ => ⟨.head _, .tail _ (.head _)⟩⟩

/-- The faithful run of `mirror` and an agent that always answers `true` and keeps nothing,
reporting no update and no work. -/
def frozen : Learner := learner mirror (always true) (fun _ _ => []) (fun _ _ => 0) id

theorem frozen_meets : oneStream.Meets frozen :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch h) ⟨0, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
    ⟨[()], fun _ => .head _⟩ (.inr fun _ _ _ h => nomatch h) (.inr fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h) fun _ => rfl

/-- **An agent that keeps nothing of its experience**: some learner that meets the record has an
agent whose memory after an answer does not depend on what it was given, and makes no learning
update at any step. -/
def keepsNothing : Consequence Learner :=
  ⟨"an agent may keep nothing of its experience and never learn",
    .possibility, fun w => (∀ m o o', (w.act m o).2 = (w.act m o').2) ∧
      ∀ ins t s m d, w.Takes ins t s m → Update.learn d ∉ w.stepUpdates s m (ins t)⟩

theorem keepsNothing_holds : keepsNothing.HoldsOf oneStream :=
  ⟨frozen, frozen_meets, fun _ _ _ => rfl, fun _ _ _ _ _ _ h => nomatch h⟩

/-! ## Consequences decided on the owner's behalf

Their status, and the reason for each, is recorded in the record's confirmation file,
`lean/AcornVerif/Intent/OneStream.md`; the explanation does not show them. -/

/-- An agent that answers with what it sees and flips its memory at every step, so that in contract
1's world `attempts`, which restarts every two steps, its memory is back at its initial value at
every restart. -/
def parity : Agent Bool Bool where
  Memory := Bool
  initial := false
  act m o := (o.1, cond m false true)

/-- The faithful run of `attempts` and `parity`, reporting one update of another kind at each step
and no reset. -/
def returnsByItself : Learner :=
  learner attempts parity (fun _ _ => [.other]) (fun _ _ => 1) id

theorem returnsByItself_meets : oneStream.Meets returnsByItself :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch List.mem_singleton.mp h)
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inr fun _ _ _ h => nomatch List.mem_singleton.mp h)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- **A memory may return to its initial value by the agent's own step, without a reset**: some
learner that meets the record takes a step from a memory other than its initial one at which its
run moves the world to its start, the memory its own answer produces is its initial one, and its
step makes no reset. -/
def returnsToInitialWithoutReset : Consequence Learner :=
  ⟨"an agent's memory may return to its initial value by its own step when the world restarts, \
    without a reset", .possibility, fun w => ∃ ins t s m, w.Takes ins t s m ∧ m ≠ w.initial ∧
      w.moved s m (ins t) (w.applied s m (ins t) (w.answer s m (ins t)).1) = w.start ∧
      (w.answer s m (ins t)).2 = w.initial ∧ Update.reset ∉ w.stepUpdates s m (ins t)⟩

theorem returnsToInitialWithoutReset_holds : returnsToInitialWithoutReset.HoldsOf oneStream :=
  ⟨returnsByItself, returnsByItself_meets, neverStop, 1, true, true, ⟨.next .start rfl, rfl⟩,
    fun h => Bool.noConfusion h, rfl, rfl, fun h => nomatch List.mem_singleton.mp h⟩

/-- A world of two states that alternates between them whatever the action, shows its state, gives
reward 1 at `true` and 0 at `false`, and makes both actions available. -/
def blinker : World := { attempts with reward := fun s => cond s 1 0 }

/-- The faithful run of `blinker` and `lastSeen`, which reports a learning update only at the steps
where it is given a reward other than 0. -/
def learnsOnReward : Learner :=
  learner blinker lastSeen (fun _ o => if o.2 = 0 then [] else [.learn (.stream 0)]) (fun _ _ => 1) id

theorem learnsOnReward_fails : ¬ oneStream.Meets learnsOnReward := fun h => by
  obtain ⟨d, hd⟩ := (oneStream_meets.mp h).2.2.2.1
    ⟨neverStop, 1, true, false, .stream 0, ⟨.next .start rfl, rfl⟩, by decide⟩
    neverStop 0 false false (takes_first (w := learnsOnReward.toSystem) rfl)
  have hnone : learnsOnReward.stepUpdates false false (neverStop 0) = [] := by decide
  rw [hnone] at hd
  exact nomatch hd

/-- The neighbour of `learnsOnReward`: the same world and agent, reporting a learning update at
every step. -/
theorem blinkerLearns_meets :
    oneStream.Meets (learner blinker lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- **Learning only on some steps is ruled out**: the learner `learnsOnReward`, which learns at the
steps where it is given a reward other than 0 and at no other. Its neighbour learns at every step
(`blinkerLearns_meets`). -/
def rulesOutLearningOnSomeSteps : Consequence Learner :=
  ⟨"the learner learnsOnReward, which learns only at the steps where its reward is not 0, is ruled \
    out", .entailment, fun w => w ≠ learnsOnReward⟩

theorem rulesOutLearningOnSomeSteps_holds : rulesOutLearningOnSomeSteps.HoldsOf oneStream :=
  fun _ hw he => learnsOnReward_fails (he ▸ hw)

/-- `base` whose run takes no step, whatever it is sent. -/
def neverBegins : Learner := { base with goesOn := fun _ _ _ => false }

/-- The run of `neverBegins` takes no step. -/
theorem neverBegins_noTakes {ins : Nat → neverBegins.Input} {t : Nat} {s : neverBegins.State}
    {m : neverBegins.Memory} : ¬ neverBegins.Takes ins t s m :=
  fun h => Bool.noConfusion (h.2.symm.trans (rfl : neverBegins.goesOn s m (ins t) = false))

theorem neverBegins_meets : oneStream.Meets neverBegins := by
  have hr : ∀ {ins t s m}, neverBegins.Reaches ins t s m → m = false
    | _, 0, _, _, h => (reaches_zero h).2
    | _, _ + 1, _, _, h => by
      obtain ⟨_, _, hr, hgo, -⟩ := reaches_succ h
      exact absurd ⟨hr, hgo⟩ neverBegins_noTakes
  refine oneStream_meets.mpr ⟨fun _ _ _ _ h => absurd h neverBegins_noTakes,
    ⟨0, fun _ _ _ _ h => absurd h neverBegins_noTakes⟩,
    ⟨[false], fun _ _ _ _ h => (hr h) ▸ .head _⟩,
    fun _ _ _ _ _ h => absurd h neverBegins_noTakes,
    fun _ _ _ _ _ h => absurd h neverBegins_noTakes,
    fun _ _ _ _ h => absurd h neverBegins_noTakes, fun _ _ _ _ h => absurd h neverBegins_noTakes,
    fun _ _ _ _ _ => rfl⟩

/-- **Some learner whose run takes no step meets the record**: the properties of steps hold of it
emptily, it holds only its initial memory, and its stop before the first step asks only that it
resume with that memory. Contract 1's record refutes such a run by its property `canBegin`. -/
def neverBeginsMeets : Consequence Learner :=
  ⟨"some learner whose run takes no step meets the record", .possibility,
    fun w => ∀ ins t s m, ¬ w.Takes ins t s m⟩

theorem neverBeginsMeets_holds : neverBeginsMeets.HoldsOf oneStream :=
  ⟨neverBegins, neverBegins_meets, fun _ _ _ _ => neverBegins_noTakes⟩

/-! ## The explanation -/

/-- The record explained in plain words, with its restatement standing as confirmed by the owner: the
owner confirmed contract 3's six sentences, and that this revision carries them is the agents'
judgment, on which the owners' log attaches the owner's answer. Every consequence it shows is
recorded as derived from that restatement. The consequences decided on the owner's behalf are
recorded, with their reasons, in the record's confirmation file, `lean/AcornVerif/Intent/OneStream.md`,
and are not shown here. Each statement's freedom says what that statement leaves open on its own
subject; the shape's says what the whole record leaves open. -/
def oneStreamExplained : Explanation oneStream where
  shape :=
    { requires := "Nothing of its own: the subject is one world, one agent and the run that couples \
        them, over types each world chooses, with what the agent reports of its own steps and of how \
        it resumes, declared a plain value."
      rulesOut := "Nothing of its own."
      allows := "A world, an agent or a report that is constant, which a shape that asks every \
        function to vary with its input would not admit."
      freedom := "Two learners that meet the record may differ in everything the properties leave \
        open: the world, the agent's memories and answer, the run's parts, how many internal updates \
        a step makes and of which kinds within the bound, the bound on work, how many memories the \
        agent holds, whether it learns or plans at all, and what the reports give wherever no run \
        takes a step or stops." }
  dom := []
  props := [
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run takes a step, every learning update the agent's step makes there takes as its \
        training datum the experience that step was given."
      rulesOut := "A learner that, at a step a run takes, learns from an experience an earlier step \
        was given, replaying it, or from data that is no experience of its own stream."
      allows := "Several learning updates in one step on the experience that step was given; \
        planning updates and other updates, which take no training datum; and a memory that keeps \
        earlier experience, such as an eligibility trace, which no learning update takes as its \
        training datum."
      freedom := "How many learning updates a step makes, and what the agent would report at a step \
        no run takes." },
    { requires := "There is one number that bounds, at every step every run takes under every \
        sequence of outside inputs, both the work the agent's step does and the number of its \
        internal updates."
      rulesOut := "A learner whose work, or number of internal updates, at the steps its runs take \
        exceeds every bound, such as work that grows with the number of steps taken, in runs that \
        take unboundedly many steps."
      allows := "Any bound, however large, and work that varies from step to step within it."
      freedom := "The bound." },
    { requires := "There is one finite list of memories that holds, at every time of every run under \
        every sequence of outside inputs, the memory the agent then holds."
      rulesOut := "A learner whose runs reach infinitely many memories, such as an agent that counts \
        its steps or stores every observation it is given, in runs that take unboundedly many steps."
      allows := "Any finite number of memories, however large."
      freedom := "How many memories the agent holds, and which." },
    { requires := "If, at some step some run takes under some sequence of outside inputs, the \
        agent's step makes a learning update, then at every step every run takes, under every \
        sequence of outside inputs, its step makes a learning update."
      rulesOut := "A learner whose step makes a learning update on some steps and none on others, \
        whether it learns during a first training period and then stops, learns in some phases \
        only, or makes a learning update only on some experiences, such as only where it is given \
        a reward other than 0."
      allows := "An agent that never learns; and a learning update that changes nothing, so an \
        agent whose learning leaves what it has learned unchanged on some steps meets this \
        property when its step makes the update on every step. What the property rules out is \
        making the update on some steps only, not what an update changes."
      freedom := "Whether the agent learns at all, and what each learning update changes." },
    { requires := "If, at some step some run takes under some sequence of outside inputs, the \
        agent's step makes a planning update, then at every step every run takes, under every \
        sequence of outside inputs, its step makes a planning update."
      rulesOut := "A learner whose step makes a planning update on some steps and none on others, \
        whether it plans during a first period and then stops, plans in some phases only, or \
        plans only on some experiences."
      allows := "An agent that never plans; and a planning update that changes nothing, so an \
        agent whose planning leaves what it has learned unchanged on some steps meets this \
        property when its step makes the update on every step. What the property rules out is \
        making the update on some steps only, not what an update changes."
      freedom := "Whether the agent plans at all, and what each planning update changes." },
    { requires := "At every step every run takes, under every sequence of outside inputs, the \
        agent's step makes no reset."
      rulesOut := "An agent that, at a step a run takes, such as one at which the world restarts, \
        discards what some or all of its memory holds and sets it back to its value at the start of \
        its life."
      allows := "A memory that returns to its initial value by an update that is no reset."
      freedom := "Everything about how the agent's memory changes but a reset." },
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run takes a step, the memory the agent begins its next step with is the memory \
        its own answer produced."
      rulesOut := "A run in which, at a step it takes, a host, a tool, the viewer or a restart of \
        the world leaves the agent another memory than its own answer produced."
      allows := "Any memory the agent's own answer produces."
      freedom := "How the agent's own answer changes its memory." },
    { requires := "For every sequence of outside inputs, every time, and every state and memory at \
        which the run stops, the memory the agent resumes with is the memory it held there."
      rulesOut := "An agent that resumes a stop with another memory: its initial one, one with part \
        of it reset, or one changed while it was stopped."
      allows := "A stop at any time, the first step included."
      freedom := "What the agent would resume with from a memory at which no run stops." }]
  vocab := [
    { requires := "Under the given outside inputs, the run took each step before the given time, \
        holds the given state and memory at that time, and takes the next step."
      rulesOut := "A configuration the run does not reach, or one at which it does not go on."
      allows := "Every configuration the run reaches and goes on from."
      freedom := "None of its own: it is a definition the properties are written in." },
    { requires := "Under the given outside inputs, the run took each step before the given time, \
        holds the given state and memory at that time, and takes no step from them."
      rulesOut := "A configuration the run does not reach, or one from which it goes on."
      allows := "Every configuration the run reaches and does not go on from."
      freedom := "None of its own: it is a definition the properties are written in." }]
  restatement := .confirmed owner
  consequences := [
    ⟨resumesAsWithoutStop, resumesAsWithoutStop_holds,
      { requires := "After every stop a run makes, under every sequence of outside inputs, the run resumed in the world that waited, at the state where it stopped, reaches at each later time exactly the states and memories the run that did not stop reaches at the same time after the stop, and at each of them answers and makes the internal updates the agent would have."
        rulesOut := "A resumed agent whose actions or learning after the stop differ from what they would have been without it."
        allows := "Nothing more."
        freedom := "What happens to a world that did not wait." }, .derived⟩,
    ⟨resumedMeets, resumedMeets_holds,
      { requires := "After every stop a run makes, the learner resumed in the world that waited meets the record too: the run after a resumption has no exception."
        rulesOut := "A resumed run that breaks any property of the record."
        allows := "Nothing more."
        freedom := "Nothing of its own." }, .derived⟩,
    ⟨learnsEachOnArrival, learnsEachOnArrival_holds,
      { requires := "If the agent learns on some step a run takes, then at every step every run takes it makes a learning update on the experience that step was given, and no learning update on anything else: each experience is learned from at the step it arrives, in order, and at no later step."
        rulesOut := "A learning agent that, at some step, does not learn from the experience that step was given, or learns from another."
        allows := "An agent that never learns."
        freedom := "How many learning updates each step makes." }, .derived⟩,
    ⟨rulesOutReplay, rulesOutReplay_holds,
      { requires := "The learner replaysLast, of contract 1's world mirror and the agent lastSeen, which at each step learns from the experience that step was given and again from the one the step before was given, does not meet the record."
        rulesOut := "That learner; base, which learns only from the experience each step was given, meets the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutOtherStream, rulesOutOtherStream_holds,
      { requires := "The learner learnsElsewhere, which at each step also learns from data that is no experience of its own stream, does not meet the record."
        rulesOut := "That learner; base meets the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutStoringStream, rulesOutStoringStream_holds,
      { requires := "The learner storesStream, whose agent keeps every observation it is given, though it learns only from the experience each step was given and replays none, does not meet the record."
        rulesOut := "That learner; base, whose agent keeps only the last observation, meets the record (base_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutGrowingWork, rulesOutGrowingWork_holds,
      { requires := "The learner growingWork, of the world clock, which counts the steps taken, whose step does as much work as that count, does not meet the record."
        rulesOut := "That learner; the same world and agent reporting no work meet the record (noWork_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutGrowingUpdates, rulesOutGrowingUpdates_holds,
      { requires := "The learner plansMore, which makes one more planning update at each step than at the step before, does not meet the record."
        rulesOut := "That learner; the same world and agent planning once at each step meet the record (plansOnceEach_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutTrainingPeriod, rulesOutTrainingPeriod_holds,
      { requires := "The learner learnsOnce, which learns on its first step and never after, does not meet the record."
        rulesOut := "That learner; the same world and agent learning at every step meet the record (learnsAlways_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutPlanningPeriod, rulesOutPlanningPeriod_holds,
      { requires := "The learner plansOnce, which plans on its first step and never after, does not meet the record."
        rulesOut := "That learner; the same world and agent planning at every step meet the record (plansAlways_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutSelfReset, rulesOutSelfReset_holds,
      { requires := "The learner resetsAtRestart, of contract 1's world attempts, which restarts every two steps, whose agent sets its memory back to its initial value at each step from which the world restarts, discarding what it remembered, and reports that reset, does not meet the record."
        rulesOut := "That learner; the same world with an agent that keeps what it remembers and makes no reset meets the record (attemptsKeeper_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutRunReset, rulesOutRunReset_holds,
      { requires := "The learner runResetsAtRestart, whose run gives the agent back its initial memory at each step from which the world attempts restarts, does not meet the record."
        rulesOut := "That learner; the same world and agent run faithfully meet the record (attemptsLastSeen_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨rulesOutFreshResume, rulesOutFreshResume_holds,
      { requires := "The learner resumesFresh, whose agent resumes every stop with its initial memory, does not meet the record; it stops after two steps holding another memory."
        rulesOut := "That learner; the same world and agent resuming with the memory held meet the record (attemptsLastSeen_meets)."
        allows := "Nothing more."
        freedom := "Everything but being that one learner." }, .derived⟩,
    ⟨severalUpdates, severalUpdates_holds,
      { requires := "Nothing more: some learner that meets the record makes, at a step a run takes, two learning updates on the experience that step was given and a planning update."
        rulesOut := "Nothing."
        allows := "Several internal updates in one step."
        freedom := "How many updates a step makes, within the bound." }, .derived⟩,
    ⟨keepsTrace, keepsTrace_holds,
      { requires := "Nothing more: some learner that meets the record learns only from the experience each step is given at every step a run takes, while its agent's answer, applied twice from some memory, gives a memory that depends on the first of the two experiences."
        rulesOut := "Nothing."
        allows := "Short-term memory of earlier experience, such as an eligibility trace, beside learning on arrival."
        freedom := "What the agent keeps of earlier experience, as long as no learning update takes it." }, .derived⟩,
    ⟨learnsAndPlansEveryStep, learnsAndPlansEveryStep_holds,
      { requires := "Nothing more: some learner that meets the record takes a step, and at every step every run takes it makes a learning update on the experience that step was given and a planning update."
        rulesOut := "Nothing."
        allows := "Learning, and planning with a model the agent has learned, on every step."
        freedom := "Whether the agent learns and plans." }, .derived⟩,
    ⟨keepsNothing, keepsNothing_holds,
      { requires := "Nothing more: some learner that meets the record has an agent whose memory after an answer does not depend on what it was given, and makes no learning update at any step."
        rulesOut := "Nothing."
        allows := "An agent that keeps nothing of its experience and never learns: the record states how an agent learns, not that it learns; such an agent still meets the record only within its bounds, its stops and its run's keeping of its memory."
        freedom := "Whether the agent learns at all." }, .derived⟩]

end AcornVerif.Intent.OneStream
