import AcornVerif.Intent.WorldInterface

namespace AcornVerif.Intent.OneStream

open LeanIntent WorldInterface

inductive Datum where
  | stream (age : Nat)
  | other
  deriving DecidableEq

inductive Update where
  | learn (datum : Datum)
  | plan
  | reset
  | other
  deriving DecidableEq

structure Learner extends WorldInterface.System where
  updates : Memory → Obs × Rat → List Update
  work : Memory → Obs × Rat → Nat
  resume : Memory → Memory

namespace Learner

variable (w : Learner)

def stepUpdates (s : w.State) (m : w.Memory) (e : w.Input) : List Update :=
  w.updates m (w.given s m e)

def stepWork (s : w.State) (m : w.Memory) (e : w.Input) : Nat :=
  w.work m (w.given s m e)

def Stops (ins : Nat → w.Input) (t : Nat) (s : w.State) (m : w.Memory) : Prop :=
  w.Reaches ins t s m ∧ w.goesOn s m (ins t) = false

end Learner

def learnsOnArrival : Clause Learner :=
  ⟨"each step, every learning update learns from the experience that step was given", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      ∀ d, Update.learn d ∈ w.stepUpdates s m (ins t) → d = .stream 0⟩

def boundedWork : Clause Learner :=
  ⟨"the work of each step, and the number of its internal updates, stay within one bound", fun w =>
    ∃ W : Nat, ∀ ins t s m, w.Takes ins t s m →
      w.stepWork s m (ins t) ≤ W ∧ (w.stepUpdates s m (ins t)).length ≤ W⟩

def boundedMemory : Clause Learner :=
  ⟨"the agent holds one of finitely many memories at every time of every run", fun w =>
    ∃ L : List w.Memory, ∀ ins t s m, w.Reaches ins t s m → m ∈ L⟩

def learnsEveryStep : Clause Learner :=
  ⟨"an agent that learns on some step learns on every step", fun w =>
    (∃ ins t s m d, w.Takes ins t s m ∧ Update.learn d ∈ w.stepUpdates s m (ins t)) →
      ∀ ins t s m, w.Takes ins t s m → ∃ d, Update.learn d ∈ w.stepUpdates s m (ins t)⟩

def plansEveryStep : Clause Learner :=
  ⟨"an agent that plans on some step plans on every step", fun w =>
    (∃ ins t s m, w.Takes ins t s m ∧ Update.plan ∈ w.stepUpdates s m (ins t)) →
      ∀ ins t s m, w.Takes ins t s m → Update.plan ∈ w.stepUpdates s m (ins t)⟩

def neverResetsItself : Clause Learner :=
  ⟨"no step of the agent makes a reset", fun w =>
    ∀ ins t s m, w.Takes ins t s m → Update.reset ∉ w.stepUpdates s m (ins t)⟩

def keepsItsMemory : Clause Learner :=
  ⟨"each step, the agent keeps the memory its own answer produced", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      w.kept s m (ins t) (w.answer s m (ins t)).2 = (w.answer s m (ins t)).2⟩

def resumesWhereStopped : Clause Learner :=
  ⟨"after every stop, the agent resumes with the memory it held when it stopped", fun w =>
    ∀ ins t s m, w.Stops ins t s m → w.resume m = m⟩

abbrev Configuration : Type 1 :=
  (w : Learner) × (Nat → w.Input) × Nat × w.State × w.Memory

def oneStream : IntentRecord Learner where
  shape := .value _
  dom := []
  props := [learnsOnArrival, boundedWork, boundedMemory, learnsEveryStep, plansEveryStep,
    neverResetsItself, keepsItsMemory, resumesWhereStopped]
  vocab := [
    ⟨"the run takes a step", Configuration,
      fun c => c.1.Takes c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2⟩,
    ⟨"the run stops", Configuration, fun c => c.1.Stops c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2⟩]

theorem oneStream_meets {w : Learner} :
    oneStream.Meets w ↔
      learnsOnArrival.holds w ∧ boundedWork.holds w ∧ boundedMemory.holds w ∧
        learnsEveryStep.holds w ∧ plansEveryStep.holds w ∧ neverResetsItself.holds w ∧
          keepsItsMemory.holds w ∧ resumesWhereStopped.holds w := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [oneStream]), h _ (by simp [oneStream]), h _ (by simp [oneStream]),
      h _ (by simp [oneStream]), h _ (by simp [oneStream]), h _ (by simp [oneStream]),
      h _ (by simp [oneStream]), h _ (by simp [oneStream])⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [oneStream, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8

def learner (W : World) (A : Agent W.Obs W.Act) (ups : A.Memory → W.Obs × Rat → List Update)
    (cost : A.Memory → W.Obs × Rat → Nat) (back : A.Memory → A.Memory) : Learner :=
  { toSystem := couple W A, updates := ups, work := cost, resume := back }

theorem learner_meets (W : World) (A : Agent W.Obs W.Act)
    (ups : A.Memory → W.Obs × Rat → List Update) (cost : A.Memory → W.Obs × Rat → Nat)
    (back : A.Memory → A.Memory)
    (hlearn : ∀ m o d, Update.learn d ∈ ups m o → d = .stream 0)
    (hcost : ∃ B, ∀ m o, cost m o ≤ B ∧ (ups m o).length ≤ B)
    (hfin : ∃ L : List A.Memory, ∀ m, m ∈ L)
    (hevery : (∀ m o, ∃ d, Update.learn d ∈ ups m o) ∨ ∀ m o d, Update.learn d ∉ ups m o)
    (hplan : (∀ m o, Update.plan ∈ ups m o) ∨ ∀ m o, Update.plan ∉ ups m o)
    (hreset : ∀ m o, Update.reset ∉ ups m o) (hback : ∀ m, back m = m) :
    oneStream.Meets (learner W A ups cost back) := by
  obtain ⟨B, hB⟩ := hcost
  obtain ⟨L, hL⟩ := hfin
  refine oneStream_meets.mpr ⟨fun _ _ _ _ _ d hd => hlearn _ _ d hd,
    ⟨B, fun _ _ _ _ _ => hB _ _⟩, ⟨L, fun _ _ _ m _ => hL m⟩, ?_, ?_,
    fun _ _ _ _ _ => hreset _ _, fun _ _ _ _ _ => rfl, fun _ _ _ m _ => hback m⟩
  · rcases hevery with h | h
    · exact fun _ _ _ _ _ _ => h _ _
    · exact fun ⟨_, _, _, _, d, _, hd⟩ => absurd hd (h _ _ d)
  · rcases hplan with h | h
    · exact fun _ _ _ _ _ _ => h _ _
    · exact fun ⟨_, _, _, _, _, hd⟩ => absurd hd (h _ _)

def lastSeen : Agent Bool Bool where
  Memory := Bool
  initial := false
  act _ o := (o.1, o.1)

def base : Learner :=
  learner mirror lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id

theorem lastSeen_finite : ∃ L : List lastSeen.Memory, ∀ m, m ∈ L :=
  ⟨[false, true], fun m => by cases m with
    | false => exact .head _
    | true => exact .tail _ (.head _)⟩

theorem base_meets : oneStream.Meets base :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def stopAtOnce : Nat → Bool := fun _ => true

theorem oneStream_o2 : O2 oneStream := by
  refine (o2_correct _).mpr ⟨⟨base, fun _ h => nomatch h⟩, fun p hp => ?_⟩
  simp only [oneStream, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨base, neverStop, 0, false, false⟩, takes_first (w := base.toSystem) rfl⟩
  · exact ⟨⟨base, stopAtOnce, 0, false, false⟩, .start, rfl⟩

theorem oneStream_o2Run : O2Run oneStream :=
  (o2Run_correct _).mpr ⟨base, base_meets.1, base_meets.2⟩

def replaysPrevious : Learner := { base with updates := fun _ _ => [.learn (.stream 1)] }

def clock : World where
  State := Nat
  Obs := Nat
  Act := Bool
  start := 0
  observe s := s
  reward _ := 0
  available _ _ := True
  step s _ := s + 1

def still : Agent Nat Bool := always true

def growingWork : Learner := learner clock still (fun _ _ => []) (fun _ o => o.1) id

theorem clock_reaches : ∀ t, (couple clock still).Reaches neverStop t t ()
  | 0 => .start
  | t + 1 => .next (clock_reaches t) rfl

def counting : Learner :=
  learner mirror echo (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id

theorem echo_counts : ∀ t, ∃ s, (couple mirror echo).Reaches neverStop t s t
  | 0 => ⟨_, .start⟩
  | t + 1 =>
    let ⟨_, h⟩ := echo_counts t
    ⟨_, .next h rfl⟩

theorem le_sum_of_mem : ∀ {L : List Nat} {n : Nat}, n ∈ L → n ≤ L.sum
  | _ :: _, _, .head _ => by simp only [List.sum_cons]; omega
  | a :: _, _, .tail _ h => by have := le_sum_of_mem h; simp only [List.sum_cons]; omega

theorem exists_not_mem (L : List Nat) : ∃ n, n ∉ L :=
  ⟨L.sum + 1, fun h => absurd (le_sum_of_mem h) (by omega)⟩

def trained : Agent Bool Bool where
  Memory := Bool
  initial := false
  act _ o := (o.1, true)

def learnsOnce : Learner :=
  learner mirror trained (fun m _ => cond m [] [.learn (.stream 0)]) (fun _ _ => 1) id

def plansOnce : Learner := learner mirror trained (fun m _ => cond m [] [.plan]) (fun _ _ => 1) id

theorem trained_reaches_one : (couple mirror trained).Reaches neverStop 1 false true :=
  .next .start rfl

def resetsItself : Learner := { base with updates := fun _ _ => [.learn (.stream 0), .reset] }

def runFlipsMemory : Learner := { base with kept := fun _ _ _ m => cond m false true }

def resumesOther : Learner := { base with resume := fun m => cond m false true }

theorem oneStream_o3 : O3 oneStream := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [oneStream, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨replaysPrevious, fun h => absurd (h neverStop 0 _ _ (takes_first (w := base.toSystem) rfl)
      _ (List.mem_singleton_self _)) (by decide)⟩
  · refine ⟨growingWork, fun ⟨B, hB⟩ => ?_⟩
    have := (hB neverStop (B + 1) _ _ ⟨clock_reaches (B + 1), rfl⟩).1
    exact absurd this (by change ¬ B + 1 ≤ B; omega)
  · refine ⟨counting, fun ⟨L, hL⟩ => ?_⟩
    obtain ⟨n, hn⟩ := exists_not_mem L
    obtain ⟨_, hr⟩ := echo_counts n
    exact hn (hL neverStop n _ _ hr)
  · refine ⟨learnsOnce, fun h => ?_⟩
    obtain ⟨d, hd⟩ := h ⟨neverStop, 0, false, false, _, takes_first (w := learnsOnce.toSystem) rfl,
      List.mem_singleton_self _⟩ neverStop 1 false true ⟨trained_reaches_one, rfl⟩
    exact nomatch hd
  · refine ⟨plansOnce, fun h => ?_⟩
    have hd := h ⟨neverStop, 0, false, false, takes_first (w := plansOnce.toSystem) rfl,
      List.mem_singleton_self _⟩ neverStop 1 false true ⟨trained_reaches_one, rfl⟩
    exact nomatch hd
  · exact ⟨resetsItself, fun h => h neverStop 0 _ _ (takes_first (w := base.toSystem) rfl)
      (.tail _ (.head _))⟩
  · exact ⟨runFlipsMemory, fun h => Bool.noConfusion
      (h neverStop 0 _ _ (takes_first (w := runFlipsMemory.toSystem) rfl))⟩
  · exact ⟨resumesOther, fun h => Bool.noConfusion (h stopAtOnce 0 _ _ ⟨.start, rfl⟩)⟩

theorem oneStream_o4 : O4 oneStream := (o4_correct _).mpr trivial

theorem oneStream_o5_widest : O5 oneStream .widest := o5_widest _

def baseWorkTwo : Learner :=
  learner mirror lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 2) id

theorem baseWorkTwo_meets : oneStream.Meets baseWorkTwo :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨2, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

theorem oneStream_not_o5_eq : ¬ O5 oneStream .eq := by
  refine not_o5_eq base_meets baseWorkTwo_meets fun h => ?_
  have hw : ∀ e : baseWorkTwo.Input, baseWorkTwo.stepWork baseWorkTwo.start baseWorkTwo.initial e = 1 :=
    h ▸ fun _ => rfl
  exact absurd (hw false) (by decide)

theorem oneStream_pairs :
    ∀ c ∈ oneStream.props, OPair (Pair.whole oneStream c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨base, trivial, fun _ => base_meets.2 c hc⟩

theorem every_world_served (W : World) (a₀ : W.Act) :
    ∃ A : Agent W.Obs W.Act, ∃ ups cost back, oneStream.Meets (learner W A ups cost back) :=
  ⟨always a₀, fun _ _ => [], fun _ _ => 0, id,
    learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch h) ⟨0, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
      ⟨[()], fun _ => .head _⟩ (.inr fun _ _ _ h => nomatch h) (.inr fun _ _ h => nomatch h)
      (fun _ _ h => nomatch h) fun _ => rfl⟩

end AcornVerif.Intent.OneStream
