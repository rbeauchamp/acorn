/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.OneStream

/-!
# The blind record reading of contract 3

This module holds the second, blind reading of contract 3's six sentences that OpenAI's
gpt-6-astra made for a record over the subject's type, in a fresh session after the record
`AcornVerif.Intent.OneStream.oneStream` was sealed at commit b144b41 and after an earlier session
had answered with no record. It is no deliverable and no part of the owner's intent: it is a second
model's reading of the owner's words. Its comparison with the record is in
`AcornVerif.Intent.OneStreamBlindCompare`, and how each difference was settled is in the record's
confirmation file, `lean/AcornVerif/Intent/OneStream.md`.

The namespace `AcornVerif.Intent.OneStream.OwnerRecord` is the blind reader's own name, kept as
returned. It declares exactly the declarations of the Lean file in the blind reader's reply, with the
same names, statements, definition bodies and proofs. Its text differs from that file only in these
ways:

* The import of `types`, the file the session was given, is replaced by the import of
  `AcornVerif.Intent.OneStream`, the module that declares `Learner`, `Update` and `Datum` and imports
  the module that declares `System`.
* The import of `LeanIntent.Record` is removed: the merge gate's boundary audit admits an import
  of lean-intent in `AcornVerif.LeanIntentBridge` alone, and `AcornVerif.Intent.OneStream` reaches
  lean-intent's record module through it.
* This copyright header and this module docstring are added.
* A docstring is added to each declaration the missing-docs linter flags: the four fields of
  `Point`, `Reached`, `Taken`, `experience`, `stepUpdates`, `OnlyCurrentExperience`,
  `ContainsNoReset`, the five properties `LearnsOnlyFromTheExperienceOfThisStep`,
  `WorkHasAFixedLifetimeBound`, `NoInternalUpdateResetsMemory`, `TheRunCarriesTheAgentsNextMemory`
  and `ResumptionPreservesTheStoppedMemory`, the eight fields of `FixedData`, `fixedData`,
  `learnerShape`, `requirements` and the record `oneStreamIntent`.

No linter flags the blind text otherwise, so no option is set before any of its declarations.
-/

namespace AcornVerif.Intent.OneStream.OwnerRecord

open LeanIntent

/-- A boundary in one possible run. -/
structure Point (w : Learner) where
  /-- The outside inputs of the run, one per step. -/
  inputs : Nat → w.Input
  /-- The number of steps taken before the boundary. -/
  time : Nat
  /-- The world's state at the boundary. -/
  state : w.State
  /-- The agent's memory at the boundary. -/
  memory : w.Memory

/-- The run reaches the point's state and memory after its number of steps, under its inputs. -/
def Reached {w : Learner} (p : Point w) : Prop :=
  w.toSystem.Reaches p.inputs p.time p.state p.memory

/-- The run reaches the point and takes the next step from it. -/
def Taken {w : Learner} (p : Point w) : Prop :=
  w.toSystem.Takes p.inputs p.time p.state p.memory

/-- What the run gives the agent at the point. -/
def experience {w : Learner} (p : Point w) : w.Obs × Rat :=
  w.given p.state p.memory (p.inputs p.time)

/-- The internal updates the agent reports on the experience the run gives it at the point. -/
def stepUpdates {w : Learner} (p : Point w) : List Update :=
  w.updates p.memory (experience p)

/-- Every learning update in the list takes the experience its step was given. -/
def OnlyCurrentExperience (us : List Update) : Prop :=
  ∀ datum : Datum,
    Update.learn datum ∈ us → datum = Datum.stream 0

/-- The list holds no reset. -/
def ContainsNoReset (us : List Update) : Prop :=
  Update.reset ∉ us

/-- At every point at which the run takes a step, every learning update the agent reports takes the
experience that step was given. -/
def LearnsOnlyFromTheExperienceOfThisStep (w : Learner) : Prop :=
  ∀ p : Point w, Taken p →
    OnlyCurrentExperience (stepUpdates p)

/-- One bound covers the work the agent reports at every point at which the run takes a step. -/
def WorkHasAFixedLifetimeBound (w : Learner) : Prop :=
  ∃ bound : Nat, ∀ p : Point w, Taken p →
    w.work p.memory (experience p) ≤ bound

/-- At every point at which the run takes a step, the agent's reported updates hold no reset. -/
def NoInternalUpdateResetsMemory (w : Learner) : Prop :=
  ∀ p : Point w, Taken p →
    ContainsNoReset (stepUpdates p)

/-- At every point at which the run takes a step, the run keeps the memory the agent's answer
produced. -/
def TheRunCarriesTheAgentsNextMemory (w : Learner) : Prop :=
  ∀ p : Point w, Taken p →
    let nextMemory := (w.act p.memory (experience p)).2
    w.kept p.state p.memory (p.inputs p.time) nextMemory =
      nextMemory

/-- At every point the run reaches, stopped there or not, the memory the agent would resume with
after a stop there is the memory it held there. -/
def ResumptionPreservesTheStoppedMemory (w : Learner) : Prop :=
  ∀ p : Point w, Reached p →
    w.resume p.memory = p.memory

/--
A finite continuation computed directly from the supplied system functions.

Each entry records the agent's chosen action, the action handed to the
world, and the internal updates. A refusal to take a step ends this
continuation. The horizon limits this observation, not the agent's life.
-/
def continuation (w : Learner) :
    Nat → (Nat → w.Input) → w.State → w.Memory →
      List (w.Act × w.Act × List Update)
  | 0, _, _, _ => []
  | n + 1, inputs, state, memory =>
      let input := inputs 0
      if w.goesOn state memory input = true then
        let datum := w.given state memory input
        let answer := w.act memory datum
        let action := w.applied state memory input answer.1
        (answer.1, action, w.updates memory datum) ::
          continuation w n
            (fun k => inputs (k + 1))
            (w.moved state memory input action)
            (w.kept state memory input answer.2)
      else
        []

/--
Compare resumption with uninterrupted execution from the same world state
and with the same subsequent outside inputs.
-/
def AfterwardsActsAndLearnsAsWithoutTheStop (w : Learner) : Prop :=
  ∀ p : Point w, Reached p →
    ∀ horizon : Nat, ∀ inputs : Nat → w.Input,
      continuation w horizon inputs p.state (w.resume p.memory) =
        continuation w horizon inputs p.state p.memory

/-- Exact memory restoration suffices for every such continuation. -/
theorem exact_memory_preserves_continuations {w : Learner}
    (h : ResumptionPreservesTheStoppedMemory w) :
    AfterwardsActsAndLearnsAsWithoutTheStop w :=
  fun p hp horizon inputs =>
    congrArg
      (fun memory => continuation w horizon inputs p.state memory)
      (h p hp)

/-- The non-function fields of the description. -/
structure FixedData where
  /-- The world's states. -/
  State : Type
  /-- What the world shows. -/
  Obs : Type
  /-- The actions. -/
  Act : Type
  /-- The agent's memories. -/
  Memory : Type
  /-- The run's outside inputs. -/
  Input : Type
  /-- The world's start. -/
  start : State
  /-- The agent's initial memory. -/
  initial : Memory
  /-- The viewer's stop request. -/
  stopRequest : Input

/-- The fields of a learner that are no functions. -/
def fixedData (w : Learner) : FixedData :=
  {
    State := w.State
    Obs := w.Obs
    Act := w.Act
    Memory := w.Memory
    Input := w.Input
    start := w.start
    initial := w.initial
    stopRequest := w.stopRequest
  }

/--
Member requires input and output types fixed across all subjects.
Select the correctly typed argument at the subject, and return the result
tagged with that subject. This accommodates Learner's dependent carriers.
-/
def functionMember
    (name : String)
    (Input Output : Learner → Type)
    (f : (w : Learner) → Input w → Output w) :
    Member Learner :=
  {
    name := name
    In := (w : Learner) → Input w
    Out := Sigma Output
    get := fun w arguments => ⟨w, f w (arguments w)⟩
  }

/-- The subject declared a description made of functions: its fixed data and each of its functions. -/
def learnerShape : Shape Learner :=
  Shape.bundle fixedData
    (functionMember "World observation"
      (fun w => w.State) (fun w => w.Obs)
      (fun w state => w.observe state))
    [
      functionMember "World reward"
        (fun w => w.State) (fun _ => Rat)
        (fun w state => w.reward state),

      functionMember "Available actions"
        (fun w => w.State × w.Act) (fun _ => Prop)
        (fun w x => w.available x.1 x.2),

      functionMember "World dynamics"
        (fun w => w.State × w.Act) (fun w => w.State)
        (fun w x => w.step x.1 x.2),

      functionMember "Agent action and next memory"
        (fun w => w.Memory × (w.Obs × Rat))
        (fun w => w.Act × w.Memory)
        (fun w x => w.act x.1 x.2),

      functionMember "Whether the run takes a step"
        (fun w => w.State × w.Memory × w.Input)
        (fun _ => Bool)
        (fun w x => w.goesOn x.1 x.2.1 x.2.2),

      functionMember "Experience given to the agent"
        (fun w => w.State × w.Memory × w.Input)
        (fun w => w.Obs × Rat)
        (fun w x => w.given x.1 x.2.1 x.2.2),

      functionMember "Action handed to the world"
        (fun w => w.State × w.Memory × w.Input × w.Act)
        (fun w => w.Act)
        (fun w x => w.applied x.1 x.2.1 x.2.2.1 x.2.2.2),

      functionMember "World state after a step"
        (fun w => w.State × w.Memory × w.Input × w.Act)
        (fun w => w.State)
        (fun w x => w.moved x.1 x.2.1 x.2.2.1 x.2.2.2),

      functionMember "Memory carried into the next step"
        (fun w => w.State × w.Memory × w.Input × w.Memory)
        (fun w => w.Memory)
        (fun w x => w.kept x.1 x.2.1 x.2.2.1 x.2.2.2),

      functionMember "Internal updates"
        (fun w => w.Memory × (w.Obs × Rat))
        (fun _ => List Update)
        (fun w x => w.updates x.1 x.2),

      functionMember "Work of a step"
        (fun w => w.Memory × (w.Obs × Rat))
        (fun _ => Nat)
        (fun w x => w.work x.1 x.2),

      functionMember "Memory after resumption"
        (fun w => w.Memory) (fun w => w.Memory)
        (fun w memory => w.resume memory)
    ]

/-- The six properties of the blind record. -/
def requirements : List (Clause Learner) :=
  [
    {
      name := "Learning uses only this step's own-stream experience"
      holds := LearnsOnlyFromTheExperienceOfThisStep
    },
    {
      name := "Step work has a fixed bound throughout every run"
      holds := WorkHasAFixedLifetimeBound
    },
    {
      name := "No internal update resets any memory"
      holds := NoInternalUpdateResetsMemory
    },
    {
      name := "The run carries the agent's next memory forward"
      holds := TheRunCarriesTheAgentsNextMemory
    },
    {
      name := "Resumption preserves exactly the stopped memory"
      holds := ResumptionPreservesTheStoppedMemory
    },
    {
      name := "With the world waiting, subsequent actions and learning agree"
      holds := AfterwardsActsAndLearnsAsWithoutTheStop
    }
  ]

/-- The blind record of the invariants of learning from one stream. -/
def oneStreamIntent : IntentRecord Learner :=
  {
    shape := learnerShape
    dom := []
    props := requirements
    vocab :=
      [
        {
          name := "A boundary reached in a run"
          Arg := Sigma Point
          holds := fun p => Reached p.2
        },
        {
          name := "A step actually taken in a run"
          Arg := Sigma Point
          holds := fun p => Taken p.2
        },
        {
          name := "Every learning datum is this step's experience"
          Arg := ULift.{1} (List Update)
          holds := fun us => OnlyCurrentExperience us.down
        },
        {
          name := "The update sequence contains no reset"
          Arg := ULift.{1} (List Update)
          holds := fun us => ContainsNoReset us.down
        }
      ] ++
      requirements.map (fun c =>
        {
          name := c.name
          Arg := Learner
          holds := c.holds
        })
  }

end AcornVerif.Intent.OneStream.OwnerRecord
