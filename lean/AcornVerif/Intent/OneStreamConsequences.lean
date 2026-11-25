import AcornVerif.Intent.OneStream
import AcornVerif.Intent.WorldInterfaceConsequences

namespace AcornVerif.Intent.OneStream

open LeanIntent WorldInterface

namespace Learner

variable (w : Learner)

def resumedAt (s : w.State) (m : w.Memory) : Learner :=
  { w with start := s, initial := w.resume m }

end Learner

def splice {I : Type} (ins : Nat → I) (t : Nat) (ins' : Nat → I) : Nat → I :=
  fun j => if j < t then ins j else ins' (j - t)

theorem splice_after {I : Type} (ins : Nat → I) (t : Nat) (ins' : Nat → I) (k : Nat) :
    splice ins t ins' (t + k) = ins' k := by
  have : ¬ t + k < t := by omega
  simp only [splice, this, ite_false, Nat.add_sub_cancel_left]

theorem reaches_zero {v : WorldInterface.System} {ins : Nat → v.Input} {s : v.State}
    {m : v.Memory} (h : v.Reaches ins 0 s m) : s = v.start ∧ m = v.initial := by
  cases h
  exact ⟨rfl, rfl⟩

theorem reaches_succ {v : WorldInterface.System} {ins : Nat → v.Input} {k : Nat} {s' : v.State}
    {m' : v.Memory} (h : v.Reaches ins (k + 1) s' m') :
    ∃ s m, v.Reaches ins k s m ∧ v.goesOn s m (ins k) = true ∧
      s' = v.moved s m (ins k) (v.applied s m (ins k) (v.answer s m (ins k)).1) ∧
      m' = v.kept s m (ins k) (v.answer s m (ins k)).2 := by
  cases h with
  | next h hgo => exact ⟨_, _, h, hgo, rfl, rfl⟩

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

theorem stop_reaches_splice {w : Learner} {ins : Nat → w.Input} {t : Nat} {s : w.State}
    {m : w.Memory} (h : w.Stops ins t s m) (ins' : Nat → w.Input) :
    w.Reaches (splice ins t ins') t s m :=
  reaches_congr (fun j hj => by simp [splice, hj]) h.1

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

theorem of_splice {I : Type} {ins : Nat → I} {t : Nat} {ins' : Nat → I} {k : Nat} (P : I → Prop)
    (h : P (splice ins t ins' (t + k))) : P (ins' k) := by
  rw [splice_after] at h
  exact h

theorem to_splice {I : Type} {ins : Nat → I} {t : Nat} {ins' : Nat → I} {k : Nat} (P : I → Prop)
    (h : P (ins' k)) : P (splice ins t ins' (t + k)) := by
  rw [splice_after]
  exact h

theorem resumed_takes {w : Learner} {ins : Nat → w.Input} {t : Nat} {s : w.State} {m : w.Memory}
    (h : w.Stops ins t s m) (hback : w.resume m = m) {ins' : Nat → w.Input} {k : Nat}
    {s' : w.State} {m' : w.Memory} (hk : (w.resumedAt s m).Takes ins' k s' m') :
    w.Takes (splice ins t ins') (t + k) s' m' :=
  ⟨(resumed_reaches_iff h hback ins' k s' m').mp hk.1, by rw [splice_after]; exact hk.2⟩

theorem resumed_stops {w : Learner} {ins : Nat → w.Input} {t : Nat} {s : w.State} {m : w.Memory}
    (h : w.Stops ins t s m) (hback : w.resume m = m) {ins' : Nat → w.Input} {k : Nat}
    {s' : w.State} {m' : w.Memory} (hk : (w.resumedAt s m).Stops ins' k s' m') :
    w.Stops (splice ins t ins') (t + k) s' m' :=
  ⟨(resumed_reaches_iff h hback ins' k s' m').mp hk.1, by rw [splice_after]; exact hk.2⟩

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

def boundedBits : Consequence Learner :=
  ⟨"the memories the agent holds fit in a fixed number of bits", .entailment, fun w =>
    ∃ (S : Nat) (code : w.Memory → List Bool),
      (∀ ins t s m, w.Reaches ins t s m → (code m).length ≤ S) ∧
      ∀ ins t s m ins' t' s' m', w.Reaches ins t s m → w.Reaches ins' t' s' m' →
        code m = code m' → m = m'⟩

theorem boundedBits_holds : boundedBits.HoldsOf oneStream := by
  intro w hw
  obtain ⟨L, hL⟩ := (oneStream_meets.mp hw).2.2.1
  let idx : w.Memory → Nat := fun m =>
    @dite _ (∃ i : Fin L.length, L.get i = m) (Classical.propDecidable _)
      (fun h => (Classical.choose h).val) fun _ => 0
  have hidx : ∀ m, m ∈ L → ∃ i : Fin L.length, idx m = i.val ∧ L.get i = m := fun m hm => by
    have he : ∃ i : Fin L.length, L.get i = m := by
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
      exact ⟨⟨i, hi⟩, he⟩
    refine ⟨Classical.choose he, ?_, Classical.choose_spec he⟩
    show @dite _ _ (Classical.propDecidable _) _ _ = _
    split
    · rfl
    · contradiction
  refine ⟨L.length, fun m => List.replicate (idx m) true, fun ins t s m h => ?_,
    fun ins t s m ins' t' s' m' h h' he => ?_⟩
  · obtain ⟨i, hi, -⟩ := hidx m (hL _ _ _ _ h)
    rw [List.length_replicate, hi]
    exact Nat.le_of_lt i.isLt
  · obtain ⟨i, hi, hm⟩ := hidx m (hL _ _ _ _ h)
    obtain ⟨i', hi', hm'⟩ := hidx m' (hL _ _ _ _ h')
    have hlen := congrArg List.length he
    simp only [List.length_replicate] at hlen
    have : i = i' := Fin.ext (hi.symm.trans (hlen.trans hi'))
    rw [← hm, ← hm', this]

def replaysLast : Learner :=
  { base with updates := fun _ _ => [.learn (.stream 0), .learn (.stream 1)] }

theorem base_reaches_one : base.Reaches neverStop 1 false false := .next .start rfl

theorem replaysLast_fails : ¬ oneStream.Meets replaysLast := fun h =>
  absurd ((oneStream_meets.mp h).1 neverStop 1 _ _ ⟨base_reaches_one, rfl⟩ _ (.tail _ (.head _)))
    (by decide)

def rulesOutReplay : Consequence Learner :=
  ⟨"the learner replaysLast, which learns again from the previous step's experience, is ruled out",
    .entailment, fun w => w ≠ replaysLast⟩

theorem rulesOutReplay_holds : rulesOutReplay.HoldsOf oneStream :=
  fun _ hw he => replaysLast_fails (he ▸ hw)

theorem replaysPrevious_fails : ¬ oneStream.Meets replaysPrevious := fun h =>
  absurd ((oneStream_meets.mp h).1 neverStop 1 _ _ ⟨base_reaches_one, rfl⟩ _ (.head _)) (by decide)

def rulesOutLateLearning : Consequence Learner :=
  ⟨"the learner replaysPrevious, whose one learning update takes the experience one step back instead \
    of its own, is ruled out", .entailment, fun w => w ≠ replaysPrevious⟩

theorem rulesOutLateLearning_holds : rulesOutLateLearning.HoldsOf oneStream :=
  fun _ hw he => replaysPrevious_fails (he ▸ hw)

def learnsElsewhere : Learner :=
  { base with updates := fun _ _ => [.learn (.stream 0), .learn .other] }

theorem learnsElsewhere_fails : ¬ oneStream.Meets learnsElsewhere := fun h =>
  absurd ((oneStream_meets.mp h).1 neverStop 0 _ _ (takes_first (w := base.toSystem) rfl) _
    (.tail _ (.head _))) (by decide)

def rulesOutOtherStream : Consequence Learner :=
  ⟨"the learner learnsElsewhere, which learns from data that is no experience of its own stream, is \
    ruled out", .entailment, fun w => w ≠ learnsElsewhere⟩

theorem rulesOutOtherStream_holds : rulesOutOtherStream.HoldsOf oneStream :=
  fun _ hw he => learnsElsewhere_fails (he ▸ hw)

def hoarder : Agent Bool Bool where
  Memory := List Bool
  initial := []
  act m o := (o.1, o.1 :: m)

def storesStream : Learner :=
  learner mirror hoarder (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id

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

def rulesOutStoringStream : Consequence Learner :=
  ⟨"the learner storesStream, which keeps every observation it is given though it replays none, is \
    ruled out", .entailment, fun w => w ≠ storesStream⟩

theorem rulesOutStoringStream_holds : rulesOutStoringStream.HoldsOf oneStream :=
  fun _ hw he => storesStream_fails (he ▸ hw)

theorem noWork_meets : oneStream.Meets (learner clock still (fun _ _ => []) (fun _ _ => 0) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch h) ⟨0, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
    ⟨[()], fun _ => .head _⟩ (.inr fun _ _ _ h => nomatch h) (.inr fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h) fun _ => rfl

theorem growingWork_fails : ¬ oneStream.Meets growingWork := fun h => by
  obtain ⟨B, hB⟩ := (oneStream_meets.mp h).2.1
  have := (hB neverStop (B + 1) _ _ ⟨clock_reaches (B + 1), rfl⟩).1
  exact absurd this (by change ¬ B + 1 ≤ B; omega)

def rulesOutGrowingWork : Consequence Learner :=
  ⟨"the learner growingWork, whose work grows with the number of steps taken, is ruled out",
    .entailment, fun w => w ≠ growingWork⟩

theorem rulesOutGrowingWork_holds : rulesOutGrowingWork.HoldsOf oneStream :=
  fun _ hw he => growingWork_fails (he ▸ hw)

def plansMore : Learner :=
  learner clock still (fun _ (o : Nat × Rat) => List.replicate (o.1 + 1) .plan) (fun _ _ => 0) id

theorem plansMore_fails : ¬ oneStream.Meets plansMore := fun h => by
  obtain ⟨B, hB⟩ := (oneStream_meets.mp h).2.1
  have := (hB neverStop B _ _ ⟨clock_reaches B, rfl⟩).2
  exact absurd this (by change ¬ (List.replicate (B + 1) Update.plan).length ≤ B; simp)

theorem plansOnceEach_meets :
    oneStream.Meets (learner clock still (fun _ _ => [.plan]) (fun _ _ => 0) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch List.mem_singleton.mp h)
    ⟨1, fun _ _ => ⟨Nat.zero_le _, Nat.le_refl _⟩⟩ ⟨[()], fun _ => .head _⟩
    (.inr fun _ _ _ h => nomatch List.mem_singleton.mp h) (.inl fun _ _ => .head _)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def rulesOutGrowingUpdates : Consequence Learner :=
  ⟨"the learner plansMore, which makes one more planning update at each step, is ruled out",
    .entailment, fun w => w ≠ plansMore⟩

theorem rulesOutGrowingUpdates_holds : rulesOutGrowingUpdates.HoldsOf oneStream :=
  fun _ hw he => plansMore_fails (he ▸ hw)

theorem trained_finite : ∃ L : List trained.Memory, ∀ m, m ∈ L :=
  ⟨[false, true], fun m => by cases m with
    | false => exact .head _
    | true => exact .tail _ (.head _)⟩

theorem learnsOnce_fails : ¬ oneStream.Meets learnsOnce := fun h => by
  obtain ⟨d, hd⟩ := (oneStream_meets.mp h).2.2.2.1 ⟨neverStop, 0, false, false, _,
    takes_first (w := learnsOnce.toSystem) rfl, List.mem_singleton_self _⟩ neverStop 1 false true
    ⟨trained_reaches_one, rfl⟩
  exact nomatch hd

theorem learnsAlways_meets :
    oneStream.Meets (learner mirror trained (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ trained_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

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

theorem plansAlways_meets :
    oneStream.Meets (learner mirror trained (fun _ _ => [.plan]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch List.mem_singleton.mp h)
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ trained_finite
    (.inr fun _ _ _ h => nomatch List.mem_singleton.mp h) (.inl fun _ _ => .head _)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def rulesOutPlanningPeriod : Consequence Learner :=
  ⟨"the learner plansOnce, which plans on its first step only, is ruled out", .entailment,
    fun w => w ≠ plansOnce⟩

theorem rulesOutPlanningPeriod_holds : rulesOutPlanningPeriod.HoldsOf oneStream :=
  fun _ hw he => plansOnce_fails (he ▸ hw)

def keeper : Agent Bool Bool where
  Memory := Bool
  initial := false
  act m o := (o.1, m || !o.1)

def resetter : Agent Bool Bool where
  Memory := Bool
  initial := false
  act m o := (o.1, cond o.1 false (m || !o.1))

def resetsAtRestart : Learner :=
  learner attempts resetter (fun _ o => cond o.1 [.learn (.stream 0), .reset] [.learn (.stream 0)])
    (fun _ _ => 1) id

theorem resetter_reaches_one : resetsAtRestart.Reaches neverStop 1 true true := .next .start rfl

theorem resetsAtRestart_fails : ¬ oneStream.Meets resetsAtRestart := fun h =>
  (oneStream_meets.mp h).2.2.2.2.2.1 neverStop 1 true true ⟨resetter_reaches_one, rfl⟩
    (.tail _ (.head _))

theorem attemptsKeeper_meets :
    oneStream.Meets (learner attempts keeper (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

theorem attemptsLastSeen_meets :
    oneStream.Meets (learner attempts lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def rulesOutSelfReset : Consequence Learner :=
  ⟨"the learner resetsAtRestart, whose agent resets its memory when the world restarts, is ruled out",
    .entailment, fun w => w ≠ resetsAtRestart⟩

theorem rulesOutSelfReset_holds : rulesOutSelfReset.HoldsOf oneStream :=
  fun _ hw he => resetsAtRestart_fails (he ▸ hw)

def runResetsAtRestart : Learner :=
  { learner attempts lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id with
    kept := fun s _ _ m => cond s false m }

theorem runResetsAtRestart_fails : ¬ oneStream.Meets runResetsAtRestart := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.1 neverStop 1 _ _
    ⟨(show runResetsAtRestart.Reaches neverStop 1 true false from .next .start rfl), rfl⟩)

def rulesOutRunReset : Consequence Learner :=
  ⟨"the learner runResetsAtRestart, whose run resets the agent's memory when the world restarts, is \
    ruled out", .entailment, fun w => w ≠ runResetsAtRestart⟩

theorem rulesOutRunReset_holds : rulesOutRunReset.HoldsOf oneStream :=
  fun _ hw he => runResetsAtRestart_fails (he ▸ hw)

def resumesFresh : Learner :=
  learner attempts lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) fun _ => false

def stopAtTwo : Nat → Bool := fun j => decide (2 ≤ j)

theorem resumesFresh_stops : resumesFresh.Stops stopAtTwo 2 false true :=
  ⟨.next (.next .start rfl) rfl, rfl⟩

theorem resumesFresh_fails : ¬ oneStream.Meets resumesFresh := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.2 _ _ _ _ resumesFresh_stops)

def rulesOutFreshResume : Consequence Learner :=
  ⟨"the learner resumesFresh, whose agent resumes a stop with its initial memory, is ruled out",
    .entailment, fun w => w ≠ resumesFresh⟩

theorem rulesOutFreshResume_holds : rulesOutFreshResume.HoldsOf oneStream :=
  fun _ hw he => resumesFresh_fails (he ▸ hw)

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

def severalUpdates : Consequence Learner :=
  ⟨"an agent may make several internal updates in one step, learning more than once from the \
    experience that step was given and planning", .possibility, fun w =>
    ∃ ins t s m, w.Takes ins t s m ∧
      w.stepUpdates s m (ins t) = [.learn (.stream 0), .learn (.stream 0), .plan]⟩

theorem severalUpdates_holds : severalUpdates.HoldsOf oneStream :=
  ⟨severalAtOnce, severalAtOnce_meets, neverStop, 0, false, false,
    takes_first (w := severalAtOnce.toSystem) rfl, rfl⟩

def lastTwo : Agent Bool Bool where
  Memory := Bool × Bool
  initial := (false, false)
  act m o := (o.1, (o.1, m.1))

theorem lastTwo_finite : ∃ L : List lastTwo.Memory, ∀ m, m ∈ L :=
  ⟨[(false, false), (false, true), (true, false), (true, true)], fun m => by
    obtain ⟨a, b⟩ := m
    cases a <;> cases b
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
    · exact .tail _ (.tail _ (.tail _ (.head _)))⟩

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

def learnsAndPlansEveryStep : Consequence Learner :=
  ⟨"an agent may learn, and plan with a model it has learned, on every step", .possibility, fun w =>
    (∃ ins t s m, w.Takes ins t s m) ∧ ∀ ins t s m, w.Takes ins t s m →
      Update.learn (.stream 0) ∈ w.stepUpdates s m (ins t) ∧
        Update.plan ∈ w.stepUpdates s m (ins t)⟩

theorem learnsAndPlansEveryStep_holds : learnsAndPlansEveryStep.HoldsOf oneStream :=
  ⟨learnsAndPlans, learnsAndPlans_meets,
    ⟨neverStop, 0, false, false, takes_first (w := learnsAndPlans.toSystem) rfl⟩,
    fun _ _ _ _ _ => ⟨.head _, .tail _ (.head _)⟩⟩

def frozen : Learner := learner mirror (always true) (fun _ _ => []) (fun _ _ => 0) id

theorem frozen_meets : oneStream.Meets frozen :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch h) ⟨0, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
    ⟨[()], fun _ => .head _⟩ (.inr fun _ _ _ h => nomatch h) (.inr fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h) fun _ => rfl

def keepsNothing : Consequence Learner :=
  ⟨"an agent may keep nothing of its experience and never learn",
    .possibility, fun w => (∀ m o o', (w.act m o).2 = (w.act m o').2) ∧
      ∀ ins t s m d, w.Takes ins t s m → Update.learn d ∉ w.stepUpdates s m (ins t)⟩

theorem keepsNothing_holds : keepsNothing.HoldsOf oneStream :=
  ⟨frozen, frozen_meets, fun _ _ _ => rfl, fun _ _ _ _ _ _ h => nomatch h⟩

def parity : Agent Bool Bool where
  Memory := Bool
  initial := false
  act m o := (o.1, cond m false true)

def returnsByItself : Learner :=
  learner attempts parity (fun _ _ => [.other]) (fun _ _ => 1) id

theorem returnsByItself_meets : oneStream.Meets returnsByItself :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch List.mem_singleton.mp h)
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inr fun _ _ _ h => nomatch List.mem_singleton.mp h)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def returnsToInitialWithoutReset : Consequence Learner :=
  ⟨"an agent's memory may return to its initial value by its own step when the world restarts, \
    without a reset", .possibility, fun w => ∃ ins t s m, w.Takes ins t s m ∧ m ≠ w.initial ∧
      w.moved s m (ins t) (w.applied s m (ins t) (w.answer s m (ins t)).1) = w.start ∧
      (w.answer s m (ins t)).2 = w.initial ∧ Update.reset ∉ w.stepUpdates s m (ins t)⟩

theorem returnsToInitialWithoutReset_holds : returnsToInitialWithoutReset.HoldsOf oneStream :=
  ⟨returnsByItself, returnsByItself_meets, neverStop, 1, true, true, ⟨.next .start rfl, rfl⟩,
    fun h => Bool.noConfusion h, rfl, rfl, fun h => nomatch List.mem_singleton.mp h⟩

def blinker : World := { attempts with reward := fun s => cond s 1 0 }

def learnsOnReward : Learner :=
  learner blinker lastSeen (fun _ o => if o.2 = 0 then [] else [.learn (.stream 0)]) (fun _ _ => 1) id

theorem learnsOnReward_fails : ¬ oneStream.Meets learnsOnReward := fun h => by
  obtain ⟨d, hd⟩ := (oneStream_meets.mp h).2.2.2.1
    ⟨neverStop, 1, true, false, .stream 0, ⟨.next .start rfl, rfl⟩, by decide⟩
    neverStop 0 false false (takes_first (w := learnsOnReward.toSystem) rfl)
  have hnone : learnsOnReward.stepUpdates false false (neverStop 0) = [] := by decide
  rw [hnone] at hd
  exact nomatch hd

theorem blinkerLearns_meets :
    oneStream.Meets (learner blinker lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id) :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def rulesOutLearningOnSomeSteps : Consequence Learner :=
  ⟨"the learner learnsOnReward, which learns only at the steps where its reward is not 0, is ruled \
    out", .entailment, fun w => w ≠ learnsOnReward⟩

theorem rulesOutLearningOnSomeSteps_holds : rulesOutLearningOnSomeSteps.HoldsOf oneStream :=
  fun _ hw he => learnsOnReward_fails (he ▸ hw)

def neverBegins : Learner := { base with goesOn := fun _ _ _ => false }

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

def neverBeginsMeets : Consequence Learner :=
  ⟨"some learner whose run takes no step meets the record", .possibility,
    fun w => ∀ ins t s m, ¬ w.Takes ins t s m⟩

theorem neverBeginsMeets_holds : neverBeginsMeets.HoldsOf oneStream :=
  ⟨neverBegins, neverBegins_meets, fun _ _ _ _ => neverBegins_noTakes⟩

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
    ⟨boundedBits, boundedBits_holds,
      { requires := "There is a number S and a code of the agent's memories as strings of bits such that every memory any run holds, under every sequence of outside inputs and at every time, is coded in at most S bits, and two different memories that runs hold have different codes."
        rulesOut := "A learner whose runs hold more memories than any fixed number of bits can tell apart, that is, infinitely many."
        allows := "Any fixed number of bits, however large."
        freedom := "The number of bits and the code." }, .derived⟩,
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
    ⟨rulesOutLateLearning, rulesOutLateLearning_holds,
      { requires := "The learner replaysPrevious, of contract 1's world mirror and the agent lastSeen, whose one learning update at every step is reported as taking the experience one step back rather than its own (from the second step on, the experience the step before was given), does not meet the record."
        rulesOut := "That learner; base, which learns from the experience each step was given, meets the record (base_meets)."
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
