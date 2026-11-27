import AcornVerif.Intent.WorldInterface
import AcornVerif.Intent.WorldInterfaceConsequences

namespace AcornVerif.Intent.WorldInterface.OwnerIntent

def answer (s : System) (q : s.State) (m : s.Memory)
    (i : s.Input) : s.Act × s.Memory :=
  s.act m (s.given q m i)

def outcome (s : System) (q : s.State) (m : s.Memory)
    (i : s.Input) : s.Act × s.Memory :=
  let r := answer s q m i
  (s.applied q m i r.1, s.kept q m i r.2)

def CanBegin (s : System) : Prop :=
  ∃ i, s.goesOn s.start s.initial i = true

def FixedActionSet (s : System) : Prop :=
  ∀ q a, s.available q a ↔ s.available s.start a

def ReceivesWorldSignals (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    s.given q m i = (s.observe q, s.reward q)

def AnswersWithAvailableAction (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    s.available q (answer s q m i).1

def AgentChoosesAction (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    (outcome s q m i).1 = (answer s q m i).1

def WorldFollowsOwnDynamics (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    s.moved q m i (outcome s q m i).1 =
      s.step q (outcome s q m i).1

def AgentKeepsOwnUpdatedMemory (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    (outcome s q m i).2 = (answer s q m i).2

def OnlySignalsInformAgent (s : System) : Prop :=
  ∀ q₁ q₂ m i₁ i₂,
    s.goesOn q₁ m i₁ = true →
    s.goesOn q₂ m i₂ = true →
    (s.observe q₁, s.reward q₁) =
      (s.observe q₂, s.reward q₂) →
    outcome s q₁ m i₁ = outcome s q₂ m i₂

def ViewerCanStop (s : System) : Prop :=
  ∀ q m, s.goesOn q m s.stopRequest = false

structure PlainData where
  State : Type
  Obs : Type
  Act : Type
  Memory : Type
  Input : Type
  start : State
  initial : Memory
  stopRequest : Input

private def member
    (name : String)
    (A B : System → Type)
    (f : (s : System) → A s → B s) :
    LeanIntent.Member System where
  name := name
  In := (s : System) → A s
  Out := Sigma B
  get := fun s probe => ⟨s, f s (probe s)⟩

private def systemShape : LeanIntent.Shape System :=
  .bundle
    (fun s =>
      ({ State := s.State
         Obs := s.Obs
         Act := s.Act
         Memory := s.Memory
         Input := s.Input
         start := s.start
         initial := s.initial
         stopRequest := s.stopRequest } : PlainData))
    (member "World observation"
      (fun s => s.State) (fun s => s.Obs)
      (fun s => s.observe))
    [
      member "World reward"
        (fun s => s.State) (fun _ => Rat)
        (fun s => s.reward),
      member "Available actions"
        (fun s => s.State × s.Act) (fun _ => Prop)
        (fun s x => s.available x.1 x.2),
      member "World dynamics, including restarts"
        (fun s => s.State × s.Act) (fun s => s.State)
        (fun s x => s.step x.1 x.2),
      member "Agent answer"
        (fun s => s.Memory × (s.Obs × Rat))
        (fun s => s.Act × s.Memory)
        (fun s x => s.act x.1 x.2),
      member "Whether the run takes a step"
        (fun s => s.State × s.Memory × s.Input)
        (fun _ => Bool)
        (fun s x => s.goesOn x.1 x.2.1 x.2.2),
      member "Signals delivered to the agent"
        (fun s => s.State × s.Memory × s.Input)
        (fun s => s.Obs × Rat)
        (fun s x => s.given x.1 x.2.1 x.2.2),
      member "Action handed to the world"
        (fun s => s.State × s.Memory × s.Input × s.Act)
        (fun s => s.Act)
        (fun s x => s.applied x.1 x.2.1 x.2.2.1 x.2.2.2),
      member "World state after a step"
        (fun s => s.State × s.Memory × s.Input × s.Act)
        (fun s => s.State)
        (fun s x => s.moved x.1 x.2.1 x.2.2.1 x.2.2.2),
      member "Memory retained for the next step"
        (fun s => s.State × s.Memory × s.Input × s.Memory)
        (fun s => s.Memory)
        (fun s x => s.kept x.1 x.2.1 x.2.2.1 x.2.2.2)
    ]

private def requirements : List (LeanIntent.Clause System) :=
  [
    ⟨"The run can begin taking steps", CanBegin⟩,
    ⟨"The world's available action set is fixed", FixedActionSet⟩,
    ⟨"Each step delivers the world's observation and reward",
      ReceivesWorldSignals⟩,
    ⟨"The agent answers with an available action",
      AnswersWithAvailableAction⟩,
    ⟨"The agent's chosen action is handed to the world unchanged",
      AgentChoosesAction⟩,
    ⟨"The world moves and restarts through its own dynamics",
      WorldFollowsOwnDynamics⟩,
    ⟨"The agent keeps its own updated memory, including at world restarts",
      AgentKeepsOwnUpdatedMemory⟩,
    ⟨"Only the observation and reward inform learning and decisions",
      OnlySignalsInformAgent⟩,
    ⟨"The viewer's stop request stops the run", ViewerCanStop⟩
  ]

def worldInterfaceIntent : LeanIntent.IntentRecord System where
  shape := systemShape
  dom := []
  props := requirements
  vocab := requirements.map fun c =>
    ({ name := c.name
       Arg := System
       holds := c.holds } : LeanIntent.Pred.{1})

def EveryWorldAcornRunsMeetsTheInterface
    (acornRuns : System → Prop) : Prop :=
  ∀ s, acornRuns s → worldInterfaceIntent.Meets s

end AcornVerif.Intent.WorldInterface.OwnerIntent

namespace AcornVerif.Intent.WorldInterface.Compare

open LeanIntent AcornVerif.Intent.WorldInterface OwnerIntent

theorem theirs_mine (w : System) (h : worldInterfaceIntent.Meets w) : worldInterface.Meets w := by
  have hp := h.2
  have g : ∀ c ∈ requirements, c.holds w := hp
  have hBegin : CanBegin w := g requirements[0] (List.getElem_mem (by decide))
  have hFixed : FixedActionSet w := g requirements[1] (List.getElem_mem (by decide))
  have hSig : ReceivesWorldSignals w := g requirements[2] (List.getElem_mem (by decide))
  have hAvail : AnswersWithAvailableAction w := g requirements[3] (List.getElem_mem (by decide))
  have hChoose : AgentChoosesAction w := g requirements[4] (List.getElem_mem (by decide))
  have hDyn : WorldFollowsOwnDynamics w := g requirements[5] (List.getElem_mem (by decide))
  have hKeep : AgentKeepsOwnUpdatedMemory w := g requirements[6] (List.getElem_mem (by decide))
  have hStop : ViewerCanStop w := g requirements[8] (List.getElem_mem (by decide))
  refine worldInterface_meets.mpr ⟨fun ins t s m h => ?_, fun ins t s m h => ?_,
    fun ins t s m h => hAvail s m (ins t) h.2, fun s s' a => ?_,
    fun ins t s m h => hChoose s m _ h.2,
    fun ins t s m h => ?_, fun ins t s m h => hKeep s m _ h.2, fun ins t₀ hs => ?_, hBegin⟩
  · exact congrArg Prod.fst (hSig s m (ins t) h.2)
  · exact congrArg Prod.snd (hSig s m (ins t) h.2)
  · exact (hFixed s a).trans (hFixed s' a).symm
  · have := hDyn s m (ins t) h.2
    simpa [outcome, answer, System.answer] using this
  · refine ⟨t₀, Nat.le_refl _, fun s m ht => ?_⟩
    have := ht.2
    rw [hs t₀ (Nat.le_refl _), hStop s m] at this
    exact Bool.noConfusion this

def deferredStop : System :=
  runOf attempts echo (fun s _ e => !e || s) (fun s _ _ => (s, 0)) (fun _ _ _ a => a)
    (fun s _ _ _ => !s) (fun _ _ _ m => m)

theorem deferredStop_meets_mine : worldInterface.Meets deferredStop := by
  refine worldInterface_meets.mpr ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => trivial, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun ins t₀ hs => ⟨t₀ + 1, Nat.le_succ _, ?_⟩,
    ⟨false, rfl⟩⟩
  intro s m ht
  have hr := ht.1
  cases hr with
  | next hr0 hgo0 =>
    rename_i s0 m0
    have e0 : ins t₀ = true := hs t₀ (Nat.le_refl _)
    have e1 : ins (t₀ + 1) = true := hs (t₀ + 1) (Nat.le_succ _)
    have h0 : (!(ins t₀) || (s0 : Bool)) = true := hgo0
    rw [e0] at h0
    have h1 : (!(ins (t₀ + 1)) || !(s0 : Bool)) = true := ht.2
    rw [e1] at h1
    revert h0 h1
    match s0 with
    | true => exact fun _ h1 => Bool.noConfusion h1
    | false => exact fun h0 _ => Bool.noConfusion h0

theorem deferredStop_fails_theirs : ¬ worldInterfaceIntent.Meets deferredStop := fun h => by
  have hStop : ViewerCanStop deferredStop := h.2 requirements[8] (List.getElem_mem (by decide))
  have := hStop (true : Bool) (0 : Nat)
  change (!true || true) = false at this
  exact Bool.noConfusion this

def wrongOffRun : System :=
  runOf mirror echo (fun _ _ e => !e) (fun _ _ _ => (false, 0)) (fun _ _ _ a => a)
    (fun _ _ _ a => a) (fun _ _ _ m => m)

theorem wrongOffRun_states {ins : Nat → wrongOffRun.Input} {t : Nat} {s : wrongOffRun.State}
    {m : wrongOffRun.Memory} (h : wrongOffRun.Reaches ins t s m) : s = (false : Bool) := by
  cases h <;> rfl

theorem wrongOffRun_meets_mine : worldInterface.Meets wrongOffRun := by
  refine worldInterface_meets.mpr ⟨fun ins t s m h => ?_, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => trivial, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun ins t₀ hs => ⟨t₀, Nat.le_refl _, fun s m ht => ?_⟩, ⟨false, rfl⟩⟩
  · have := wrongOffRun_states h.1
    subst this
    rfl
  · have := ht.2
    change (!(ins t₀)) = true at this
    rw [hs t₀ (Nat.le_refl _)] at this
    exact Bool.noConfusion this

theorem wrongOffRun_fails_theirs : ¬ worldInterfaceIntent.Meets wrongOffRun := fun h => by
  have hSig : ReceivesWorldSignals wrongOffRun := h.2 requirements[2] (List.getElem_mem (by decide))
  have := congrArg Prod.fst (hSig (true : Bool) (0 : Nat) false rfl)
  change false = true at this
  exact Bool.noConfusion this

theorem mine_not_theirs : ¬ ∀ w, worldInterface.Meets w → worldInterfaceIntent.Meets w :=
  fun h => deferredStop_fails_theirs (h _ deferredStop_meets_mine)

end AcornVerif.Intent.WorldInterface.Compare
