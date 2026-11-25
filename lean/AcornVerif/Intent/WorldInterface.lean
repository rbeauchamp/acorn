import AcornVerif.LeanIntentBridge

namespace AcornVerif.Intent.WorldInterface

open LeanIntent

structure System where
  State : Type
  Obs : Type
  Act : Type
  Memory : Type
  Input : Type
  start : State
  observe : State → Obs
  reward : State → Rat
  available : State → Act → Prop
  step : State → Act → State
  initial : Memory
  act : Memory → Obs × Rat → Act × Memory
  stopRequest : Input
  goesOn : State → Memory → Input → Bool
  given : State → Memory → Input → Obs × Rat
  applied : State → Memory → Input → Act → Act
  moved : State → Memory → Input → Act → State
  kept : State → Memory → Input → Memory → Memory

namespace System

variable (w : System)

def answer (s : w.State) (m : w.Memory) (e : w.Input) : w.Act × w.Memory :=
  w.act m (w.given s m e)

inductive Reaches (ins : Nat → w.Input) : Nat → w.State → w.Memory → Prop where
  | start : Reaches ins 0 w.start w.initial
  | next {t : Nat} {s : w.State} {m : w.Memory} :
      Reaches ins t s m → w.goesOn s m (ins t) = true →
      Reaches ins (t + 1) (w.moved s m (ins t) (w.applied s m (ins t) (w.answer s m (ins t)).1))
        (w.kept s m (ins t) (w.answer s m (ins t)).2)

def Takes (ins : Nat → w.Input) (t : Nat) (s : w.State) (m : w.Memory) : Prop :=
  w.Reaches ins t s m ∧ w.goesOn s m (ins t) = true

end System

def seesObservation : Clause System :=
  ⟨"each step, the agent is given the world's observation of its current state", fun w =>
    ∀ ins t s m, w.Takes ins t s m → (w.given s m (ins t)).1 = w.observe s⟩

def getsWorldReward : Clause System :=
  ⟨"each step, the agent is given the reward the world generates at its current state", fun w =>
    ∀ ins t s m, w.Takes ins t s m → (w.given s m (ins t)).2 = w.reward s⟩

def answersAvailable : Clause System :=
  ⟨"each step, the agent answers with an action the world makes available", fun w =>
    ∀ ins t s m, w.Takes ins t s m → w.available s (w.answer s m (ins t)).1⟩

def fixedActions : Clause System :=
  ⟨"the world makes the same actions available at every one of its states", fun w =>
    ∀ s s' a, w.available s a ↔ w.available s' a⟩

def worldGetsAnswer : Clause System :=
  ⟨"each step, the world is handed the action the agent answered", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      w.applied s m (ins t) (w.answer s m (ins t)).1 = (w.answer s m (ins t)).1⟩

def worldMovesByItself : Clause System :=
  ⟨"each step, the world moves by its own dynamics", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      w.moved s m (ins t) (w.applied s m (ins t) (w.answer s m (ins t)).1) =
        w.step s (w.applied s m (ins t) (w.answer s m (ins t)).1)⟩

def keepsOwnMemory : Clause System :=
  ⟨"each step, the agent keeps the memory its own answer produced", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      w.kept s m (ins t) (w.answer s m (ins t)).2 = (w.answer s m (ins t)).2⟩

def viewerCanStop : Clause System :=
  ⟨"a run the viewer keeps asking to stop stops", fun w =>
    ∀ ins t₀, (∀ t, t₀ ≤ t → ins t = w.stopRequest) →
      ∃ t, t₀ ≤ t ∧ ∀ s m, ¬ w.Takes ins t s m⟩

def canBegin : Clause System :=
  ⟨"the run can take its first step", fun w => ∃ e, w.goesOn w.start w.initial e = true⟩

abbrev Configuration : Type 1 :=
  (w : System) × (Nat → w.Input) × Nat × w.State × w.Memory

def worldInterface : IntentRecord System where
  shape := .value _
  dom := []
  props := [seesObservation, getsWorldReward, answersAvailable, fixedActions, worldGetsAnswer,
    worldMovesByItself, keepsOwnMemory, viewerCanStop, canBegin]
  vocab := [⟨"the run takes a step", Configuration, fun c => c.1.Takes c.2.1 c.2.2.1 c.2.2.2.1
    c.2.2.2.2⟩]

theorem worldInterface_meets {w : System} :
    worldInterface.Meets w ↔
      seesObservation.holds w ∧ getsWorldReward.holds w ∧ answersAvailable.holds w ∧
        fixedActions.holds w ∧ worldGetsAnswer.holds w ∧ worldMovesByItself.holds w ∧
          keepsOwnMemory.holds w ∧ viewerCanStop.holds w ∧ canBegin.holds w := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [worldInterface]), h _ (by simp [worldInterface]),
      h _ (by simp [worldInterface]), h _ (by simp [worldInterface]),
      h _ (by simp [worldInterface]), h _ (by simp [worldInterface]),
      h _ (by simp [worldInterface]), h _ (by simp [worldInterface]),
      h _ (by simp [worldInterface])⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [worldInterface, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9

structure World where
  State : Type
  Obs : Type
  Act : Type
  start : State
  observe : State → Obs
  reward : State → Rat
  available : State → Act → Prop
  step : State → Act → State

structure Agent (Obs Act : Type) where
  Memory : Type
  initial : Memory
  act : Memory → Obs × Rat → Act × Memory

def couple (W : World) (A : Agent W.Obs W.Act) : System where
  State := W.State
  Obs := W.Obs
  Act := W.Act
  Memory := A.Memory
  Input := Bool
  start := W.start
  observe := W.observe
  reward := W.reward
  available := W.available
  step := W.step
  initial := A.initial
  act := A.act
  stopRequest := true
  goesOn _ _ e := !e
  given s _ _ := (W.observe s, W.reward s)
  applied _ _ _ a := a
  moved s _ _ a := W.step s a
  kept _ _ _ m := m

theorem couple_meets (W : World) (A : Agent W.Obs W.Act)
    (hfixed : ∀ s s' a, W.available s a ↔ W.available s' a)
    (hanswer : ∀ s m o, W.available s (A.act m o).1) : worldInterface.Meets (couple W A) := by
  refine worldInterface_meets.mpr ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ s m _ => hanswer s m _, hfixed, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun ins t₀ hstop => ⟨t₀, Nat.le_refl _, fun s m h => ?_⟩,
    ⟨false, rfl⟩⟩
  have hgo : (couple W A).goesOn s m (ins t₀) = true := h.2
  rw [hstop t₀ (Nat.le_refl _)] at hgo
  exact Bool.noConfusion hgo

def mirror : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe s := s
  reward _ := 0
  available _ _ := True
  step _ a := a

def echo : Agent Bool Bool where
  Memory := Nat
  initial := 0
  act m o := (o.1, m + 1)

def base : System := couple mirror echo

theorem base_meets : worldInterface.Meets base :=
  couple_meets mirror echo (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial)

def neverStop : Nat → Bool := fun _ => false

theorem takes_first {w : System} {ins : Nat → w.Input}
    (hgo : w.goesOn w.start w.initial (ins 0) = true) :
    w.Takes ins 0 w.start w.initial :=
  ⟨.start, hgo⟩

theorem worldInterface_o2 : O2 worldInterface := by
  refine (o2_correct _).mpr ⟨⟨base, fun _ h => nomatch h⟩, fun p hp => ?_⟩
  simp only [worldInterface, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨⟨base, neverStop, 0, false, (0 : Nat)⟩, takes_first (w := base) rfl⟩

theorem worldInterface_o2Run : O2Run worldInterface :=
  (o2Run_correct _).mpr ⟨base, base_meets.1, base_meets.2⟩

def showsOther : System := { base with given := fun s _ _ => (!s, 0) }

def otherReward : System := { base with given := fun s _ _ => (s, 1) }

def nothingAvailable : System := { base with available := fun _ _ => False }

def availableAtTrue : System := { base with available := fun s _ => s = true }

def overridesAction : System := { base with applied := fun _ _ _ a => !a }

def movesOtherwise : System := { base with moved := fun _ _ _ a => !a }

def resetsMemory : System := { base with kept := fun _ _ _ _ => (0 : Nat) }

def neverStops : System := { base with goesOn := fun _ _ _ => true }

def neverBegins : System := { base with goesOn := fun _ _ _ => false }

theorem neverStops_reaches (ins : Nat → Bool) : ∀ t, ∃ s m, neverStops.Reaches ins t s m
  | 0 => ⟨_, _, .start⟩
  | t + 1 =>
    let ⟨_, _, h⟩ := neverStops_reaches ins t
    ⟨_, _, .next h rfl⟩

theorem worldInterface_o3 : O3 worldInterface := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [worldInterface, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨showsOther, fun h => Bool.noConfusion (h neverStop 0 _ _ (takes_first rfl))⟩
  · exact ⟨otherReward, fun h => absurd (h neverStop 0 _ _ (takes_first rfl)) (by decide)⟩
  · exact ⟨nothingAvailable, fun h => h neverStop 0 _ _ (takes_first rfl)⟩
  · exact ⟨availableAtTrue, fun h => Bool.noConfusion ((h false true false).mpr rfl)⟩
  · exact ⟨overridesAction, fun h => Bool.noConfusion (h neverStop 0 _ _ (takes_first rfl))⟩
  · exact ⟨movesOtherwise, fun h => Bool.noConfusion (h neverStop 0 _ _ (takes_first rfl))⟩
  · exact ⟨resetsMemory, fun h => Nat.noConfusion (h neverStop 0 _ _ (takes_first rfl))⟩
  · refine ⟨neverStops, fun h => ?_⟩
    obtain ⟨t, -, ht⟩ := h (fun _ => true) 0 (fun _ _ => rfl)
    obtain ⟨s, m, hr⟩ := neverStops_reaches (fun _ => true) t
    exact ht s m ⟨hr, rfl⟩
  · exact ⟨neverBegins, fun ⟨_, h⟩ => Bool.noConfusion h⟩

theorem worldInterface_o4 : O4 worldInterface := (o4_correct _).mpr trivial

theorem worldInterface_o5_widest : O5 worldInterface .widest := o5_widest _

def mirrorRewardOne : World := { mirror with reward := fun _ => 1 }

def baseRewardOne : System := couple mirrorRewardOne echo

theorem worldInterface_pairs :
    ∀ c ∈ worldInterface.props, OPair (Pair.whole worldInterface c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨base, trivial, fun _ => base_meets.2 c hc⟩

def always {Obs Act : Type} (a : Act) : Agent Obs Act where
  Memory := Unit
  initial := ()
  act _ _ := (a, ())

theorem every_world_served (W : World) (hfixed : ∀ s s' a, W.available s a ↔ W.available s' a)
    (a₀ : W.Act) (ha₀ : ∀ s, W.available s a₀) :
    ∃ A : Agent W.Obs W.Act, worldInterface.Meets (couple W A) :=
  ⟨always a₀, couple_meets W _ hfixed fun s _ _ => ha₀ s⟩

theorem worldInterface_not_o5_eq : ¬ O5 worldInterface .eq := by
  refine not_o5_eq base_meets
    (couple_meets mirrorRewardOne echo (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial)) fun h => ?_
  have hr : HEq base.reward baseRewardOne.reward := by rw [h]; rfl
  have hr' : base.reward = baseRewardOne.reward := eq_of_heq hr
  exact absurd (congrFun hr' false) (by decide)

end AcornVerif.Intent.WorldInterface
