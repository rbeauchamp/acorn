import AcornVerif.Intent.OneStream

namespace AcornVerif.Intent.OneStream.OwnerRecord

open LeanIntent

structure Point (w : Learner) where
  inputs : Nat → w.Input
  time : Nat
  state : w.State
  memory : w.Memory

def Reached {w : Learner} (p : Point w) : Prop :=
  w.toSystem.Reaches p.inputs p.time p.state p.memory

def Taken {w : Learner} (p : Point w) : Prop :=
  w.toSystem.Takes p.inputs p.time p.state p.memory

def experience {w : Learner} (p : Point w) : w.Obs × Rat :=
  w.given p.state p.memory (p.inputs p.time)

def stepUpdates {w : Learner} (p : Point w) : List Update :=
  w.updates p.memory (experience p)

def OnlyCurrentExperience (us : List Update) : Prop :=
  ∀ datum : Datum,
    Update.learn datum ∈ us → datum = Datum.stream 0

def ContainsNoReset (us : List Update) : Prop :=
  Update.reset ∉ us

def LearnsOnlyFromTheExperienceOfThisStep (w : Learner) : Prop :=
  ∀ p : Point w, Taken p →
    OnlyCurrentExperience (stepUpdates p)

def WorkHasAFixedLifetimeBound (w : Learner) : Prop :=
  ∃ bound : Nat, ∀ p : Point w, Taken p →
    w.work p.memory (experience p) ≤ bound

def NoInternalUpdateResetsMemory (w : Learner) : Prop :=
  ∀ p : Point w, Taken p →
    ContainsNoReset (stepUpdates p)

def TheRunCarriesTheAgentsNextMemory (w : Learner) : Prop :=
  ∀ p : Point w, Taken p →
    let nextMemory := (w.act p.memory (experience p)).2
    w.kept p.state p.memory (p.inputs p.time) nextMemory =
      nextMemory

def ResumptionPreservesTheStoppedMemory (w : Learner) : Prop :=
  ∀ p : Point w, Reached p →
    w.resume p.memory = p.memory

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

def AfterwardsActsAndLearnsAsWithoutTheStop (w : Learner) : Prop :=
  ∀ p : Point w, Reached p →
    ∀ horizon : Nat, ∀ inputs : Nat → w.Input,
      continuation w horizon inputs p.state (w.resume p.memory) =
        continuation w horizon inputs p.state p.memory

theorem exact_memory_preserves_continuations {w : Learner}
    (h : ResumptionPreservesTheStoppedMemory w) :
    AfterwardsActsAndLearnsAsWithoutTheStop w :=
  fun p hp horizon inputs =>
    congrArg
      (fun memory => continuation w horizon inputs p.state memory)
      (h p hp)

structure FixedData where
  State : Type
  Obs : Type
  Act : Type
  Memory : Type
  Input : Type
  start : State
  initial : Memory
  stopRequest : Input

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
