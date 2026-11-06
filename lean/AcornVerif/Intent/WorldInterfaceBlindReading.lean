/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.WorldInterface
import AcornVerif.Intent.WorldInterfaceConsequences

/-!
# The blind record reading of contract 1, and its comparison with the record

This module holds the second, blind reading of contract 1's eight sentences that OpenAI's
gpt-6-astra made for a record over the subject's type, after the record
`AcornVerif.Intent.WorldInterface.worldInterface` was sealed at commit f6c9c73, and the comparison
of that reading with the record as revised after it. It is no deliverable and no part of the
owner's intent: it is a second model's reading of the owner's words. How each difference it found
was settled is in the record's confirmation file, `lean/AcornVerif/Intent/WorldInterface.md`.

## The blind record

The namespace `AcornVerif.Intent.WorldInterface.OwnerIntent` is the blind reader's own name, kept
as returned. It declares exactly the declarations of the Lean file in the blind reader's reply,
with the same names, statements, definition bodies and proofs. Its text differs from that file
only in these ways:

* The import of `types`, the file the session was given, is replaced by the import of
  `AcornVerif.Intent.WorldInterface`, the module that declares `System`.
* The import of `LeanIntent.Record` is removed: the merge gate's boundary audit admits an import
  of lean-intent in `AcornVerif.LeanIntentBridge` alone, and `AcornVerif.Intent.WorldInterface`
  reaches lean-intent's record module through it.
* `AcornVerif.Intent.WorldInterfaceConsequences` is imported, for the comparison.
* This copyright header and this module docstring are added.
* A docstring is added to each declaration the missing-docs linter flags: the nine properties
  `CanBegin`, `FixedActionSet`, `ReceivesWorldSignals`, `AnswersWithAvailableAction`,
  `AgentChoosesAction`, `WorldFollowsOwnDynamics`, `AgentKeepsOwnUpdatedMemory`,
  `OnlySignalsInformAgent` and `ViewerCanStop`, the eight fields of `PlainData`, and the record
  `worldInterfaceIntent`.

No linter flags the blind text otherwise, so no option is set before any of its declarations.

## The comparison

`AcornVerif.Intent.WorldInterface.Compare.theirs_mine` proves that every system that meets the
blind record meets the record, and `AcornVerif.Intent.WorldInterface.Compare.mine_not_theirs` that
some system meets the record and not the blind one, so the two differ only where the record allows
more. Two systems show where: `AcornVerif.Intent.WorldInterface.Compare.deferredStop`, whose host
lets one more step happen when the viewer asks the run to stop, and
`AcornVerif.Intent.WorldInterface.Compare.wrongOffRun`, which gives a wrong observation at a state
no run reaches. The comparison shares this module with the blind record because `theirs_mine`
reads the blind record's private list of requirements.
-/

namespace AcornVerif.Intent.WorldInterface.OwnerIntent

/-- The agent's answer to what the run actually supplies. -/
def answer (s : System) (q : s.State) (m : s.Memory)
    (i : s.Input) : s.Act × s.Memory :=
  s.act m (s.given q m i)

/-- The action actually handed over and the memory actually retained. -/
def outcome (s : System) (q : s.State) (m : s.Memory)
    (i : s.Input) : s.Act × s.Memory :=
  let r := answer s q m i
  (s.applied q m i r.1, s.kept q m i r.2)

/-- Some outside input lets the run take a step from the world's start and the agent's initial
memory. -/
def CanBegin (s : System) : Prop :=
  ∃ i, s.goesOn s.start s.initial i = true

/-- The actions available at every state of the world are those available at its start. -/
def FixedActionSet (s : System) : Prop :=
  ∀ q a, s.available q a ↔ s.available s.start a

/-- At every state, memory and input from which the run goes on, the agent is given the world's
observation and reward at that state. -/
def ReceivesWorldSignals (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    s.given q m i = (s.observe q, s.reward q)

/-- At every state, memory and input from which the run goes on, the agent's answer is an action
available at that state. -/
def AnswersWithAvailableAction (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    s.available q (answer s q m i).1

/-- At every state, memory and input from which the run goes on, the action handed to the world
is the agent's answer. -/
def AgentChoosesAction (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    (outcome s q m i).1 = (answer s q m i).1

/-- At every state, memory and input from which the run goes on, the world moves by its own
dynamics on the action handed to it. -/
def WorldFollowsOwnDynamics (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    s.moved q m i (outcome s q m i).1 =
      s.step q (outcome s q m i).1

/-- At every state, memory and input from which the run goes on, the memory kept for the next
step is the one the agent's answer produced. -/
def AgentKeepsOwnUpdatedMemory (s : System) : Prop :=
  ∀ q m i, s.goesOn q m i = true →
    (outcome s q m i).2 = (answer s q m i).2

/-- Two steps the run takes from the same memory, at states whose observation and reward agree,
hand the world the same action and keep the same memory. -/
def OnlySignalsInformAgent (s : System) : Prop :=
  ∀ q₁ q₂ m i₁ i₂,
    s.goesOn q₁ m i₁ = true →
    s.goesOn q₂ m i₂ = true →
    (s.observe q₁, s.reward q₁) =
      (s.observe q₂, s.reward q₂) →
    outcome s q₁ m i₁ = outcome s q₂ m i₂

/-- The run goes on from no state and memory when the viewer's stop request arrives. -/
def ViewerCanStop (s : System) : Prop :=
  ∀ q m, s.goesOn q m s.stopRequest = false

/-- Exactly the non-function fields of System. -/
structure PlainData where
  /-- The world's states. -/
  State : Type
  /-- What the world shows the agent. -/
  Obs : Type
  /-- The actions. -/
  Act : Type
  /-- The agent's memories. -/
  Memory : Type
  /-- What hosts, viewers and tools may send the run at a step. -/
  Input : Type
  /-- The world's state when the run begins. -/
  start : State
  /-- The agent's memory when the run begins. -/
  initial : Memory
  /-- What the viewer sends to ask the run to stop. -/
  stopRequest : Input

/--
Member requires fixed input and output types, whereas System's fields
have subject-dependent types. A probe supplies a typed argument for
each subject; the result retains its subject index.
-/
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

/-- The blind reading's record: the subject's shape, no domain hypothesis, and the nine
requirements, which are also its vocabulary. -/
def worldInterfaceIntent : LeanIntent.IntentRecord System where
  shape := systemShape
  dom := []
  props := requirements
  vocab := requirements.map fun c =>
    ({ name := c.name
       Arg := System
       holds := c.holds } : LeanIntent.Pred.{1})

/--
Requirement 8, once the actual collection of worlds Acorn runs is supplied.
That collection must include the tile world, every ARC-AGI-3 game Acorn
runs, and the Microduck.
-/
def EveryWorldAcornRunsMeetsTheInterface
    (acornRuns : System → Prop) : Prop :=
  ∀ s, acornRuns s → worldInterfaceIntent.Meets s

end AcornVerif.Intent.WorldInterface.OwnerIntent

namespace AcornVerif.Intent.WorldInterface.Compare

open LeanIntent AcornVerif.Intent.WorldInterface OwnerIntent

/-- Every system meeting the blind record meets Acorn's. -/
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

/-- A world of attempts of two steps with `echo`, whose host lets one more step happen when the
stop request arrives at the world's second state: it meets Acorn's record and not the blind one,
which asks the stop to take effect at once at every state. -/
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

/-- `base` with a wrong observation given at the state `true`, which no run of it reaches: it
meets Acorn's record and not the blind one, which asks the signals to be faithful at every state
from which the run would go on. -/
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

/-- The records are not equivalent: some system meets Acorn's and not the blind one. -/
theorem mine_not_theirs : ¬ ∀ w, worldInterface.Meets w → worldInterfaceIntent.Meets w :=
  fun h => deferredStop_fails_theirs (h _ deferredStop_meets_mine)

end AcornVerif.Intent.WorldInterface.Compare
