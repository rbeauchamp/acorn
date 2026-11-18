/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.Postcondition

/-!
# The blind record reading of contract 2

PROVISIONAL HEADER
-/

namespace AcornVerif.Intent.BigClassBlind

open WorldInterface (Agent)
open Postcondition (Member)

/-- A class of worlds with an agent. -/
structure ClassWithAgent where
  /-- What the worlds of the class show an agent. -/
  Obs : Type
  /-- The actions of the class. -/
  Act : Type
  /-- The names of the class's members. -/
  Index : Type
  /-- Each member: its world, its reward function and its goal. -/
  member : Index → Member Obs Act
  /-- How long an attempt lasts, in steps. -/
  length : Nat
  /-- The agent. -/
  agent : Agent Obs Act

namespace AcornOwnerIntent

/-- What a member of the class gives the agent at a step: an observation with a reward. -/
abbrev Percept (c : ClassWithAgent) := c.Obs × Rat

/-- Follow a finite sequence of actions, using the world's actual dynamics. -/
def follow {Obs Act : Type} (w : Member Obs Act)
    (s : w.State) : List Act → w.State
  | [] => s
  | a :: actions => follow w (w.step s a) actions

/-- Reachability from the specified starting state; no recoverability
    from subsequent states is required. -/
def goalReachable (c : ClassWithAgent) (i : c.Index) : Prop :=
  ∃ actions : List c.Act,
    (c.member i).goal
      (follow (c.member i) (c.member i).start actions) = true

/-- Every member's goal is reachable from the member's start. -/
def everyGoalReachable (c : ClassWithAgent) : Prop :=
  ∀ i : c.Index, goalReachable c i

/-- A memoryless agent uses its current observation and actual reward,
    without retaining experience. -/
def memorylessState (c : ClassWithAgent)
    (answer : Percept c → c.Act) (i : c.Index) :
    Nat → (c.member i).State
  | 0 => (c.member i).start
  | n + 1 =>
      let s := memorylessState c answer i n
      (c.member i).step s
        (answer ((c.member i).observe s, (c.member i).reward s))

/-- The memoryless rule brings the member to its goal within the attempt's length of steps from
the member's start. -/
def memorylessSolves (c : ClassWithAgent)
    (answer : Percept c → c.Act) (i : c.Index) : Prop :=
  ∃ n : Nat,
    n ≤ c.length ∧
    (c.member i).goal (memorylessState c answer i n) = true

/-- The broader world-agent pairs referred to by "any big world".
    This does not define general bigness by Acorn's four conditions. -/
structure WorldWithAgent where
  /-- The world's observations. -/
  Obs : Type
  /-- The world's actions. -/
  Act : Type
  /-- The world. -/
  world : Member Obs Act
  /-- The agent. -/
  agent : Agent Obs Act

/--
Interpretations of the owner's qualitative vocabulary.

These fields supply meanings, not proofs that a subject meets them.
All resource and representability predicates concern the paired agent
and the resources needed for its task.
-/
structure Meaning where
  /-- The agent is far smaller in the resources its task needs. -/
  farSmallerInTaskResources : ClassWithAgent → Prop
  /-- The agent can fully perceive the world's state. -/
  canFullyPerceiveState : ClassWithAgent → Prop
  /-- The agent can represent values for every state. -/
  canRepresentValuesEverywhere : ClassWithAgent → Prop
  /-- The agent can represent a best action for every state. -/
  canRepresentBestActionsEverywhere : ClassWithAgent → Prop

  /-- Under every interaction, perceptions, including actual rewards,
      give no information about the goal before its first achievement. -/
  noGoalInformationBeforeFirstSuccess : ClassWithAgent → Prop

  /-- The supplied subset constitutes a small share of this class.
      No counting convention, distribution, or threshold is invented here. -/
  smallShare : (c : ClassWithAgent) → (c.Index → Prop) → Prop

  /-- There are more separate solution demands than the paired agent
      can retain solutions to simultaneously. This is not a comparison
      between the number of members and the number of memory states. -/
  moreSeparateProblemsThanSolutionsFit : ClassWithAgent → Prop

  /-- Maintaining the intended success requires continued learning
      and relinquishing solutions or information no longer needed. -/
  continuedLearningAndGivingUpUnneededSolutionsRequired :
    ClassWithAgent → Prop

  /-- Success is recognizable to the paired agent through its perceptions,
      including reward. -/
  successPerceptible : ClassWithAgent → Prop

  /-- Experience has enough temporal coherence for continued learning
      to pay under the intended performance comparison. -/
  temporallyCoherentEnoughForLearning : ClassWithAgent → Prop

  /-- Feasible continuing learning processes for the paired agent,
      respecting its resource limits. -/
  ContinuingLearning : ClassWithAgent → Type

  /-- Fixed solutions admissible under those same resource limits. -/
  FixedSolution : ClassWithAgent → Type

  /-- The intended comparison of task performance over experience. -/
  doesBetter :
    (c : ClassWithAgent) →
    ContinuingLearning c → FixedSolution c → Prop

  /-- The class contributes toward any big world. -/
  contributesTowardAnyBigWorld : ClassWithAgent → Prop
  /-- A world is generally big relative to its agent. -/
  generallyBig : WorldWithAgent → Prop
  /-- A world-agent pair remains in a class's long-term aim. -/
  includedInLongTermAim : ClassWithAgent → WorldWithAgent → Prop

/-- Every memoryless rule solves only a small share of the class on an attempt, under the given
meaning of a small share. -/
def memorylessSolvesOnlySmallShare
    (meaning : Meaning) (c : ClassWithAgent) : Prop :=
  ∀ answer : Percept c → c.Act,
    meaning.smallShare c (memorylessSolves c answer)

/-- Some continuing learning process does better than every fixed solution, under the given
meanings. -/
def continuingLearningCanBeatEveryFixedSolution
    (meaning : Meaning) (c : ClassWithAgent) : Prop :=
  ∃ learning : meaning.ContinuingLearning c,
    ∀ fixed : meaning.FixedSolution c,
      meaning.doesBetter c learning fixed

/-- Every generally big world-agent pair remains in the class's long-term aim, under the given
meanings. -/
def aimIncludesEveryBigWorld
    (meaning : Meaning) (c : ClassWithAgent) : Prop :=
  ∀ pair : WorldWithAgent,
    meaning.generallyBig pair →
    meaning.includedInLongTermAim c pair

/-- The reply's fourteen properties, under the given meanings. -/
def requirements (meaning : Meaning) :
    List (LeanIntent.Clause ClassWithAgent) :=
  [
    ⟨"The agent is far smaller in the resources its task needs",
      meaning.farSmallerInTaskResources⟩,
    ⟨"The agent cannot fully perceive the world's state",
      fun c => ¬ meaning.canFullyPerceiveState c⟩,
    ⟨"The agent cannot represent values for every state",
      fun c => ¬ meaning.canRepresentValuesEverywhere c⟩,
    ⟨"The agent cannot represent a best action for every state",
      fun c => ¬ meaning.canRepresentBestActionsEverywhere c⟩,
    ⟨"Every goal is reachable from its attempt's start",
      everyGoalReachable⟩,
    ⟨"Perceptions reveal no goal information before first success",
      meaning.noGoalInformationBeforeFirstSuccess⟩,
    ⟨"Every memoryless agent solves only a small share on an attempt",
      memorylessSolvesOnlySmallShare meaning⟩,
    ⟨"More separate problems are posed than solutions fit at once",
      meaning.moreSeparateProblemsThanSolutionsFit⟩,
    ⟨"Continued success requires learning and giving up unneeded solutions",
      meaning.continuedLearningAndGivingUpUnneededSolutionsRequired⟩,
    ⟨"Success is perceptible to the agent",
      meaning.successPerceptible⟩,
    ⟨"Experience is temporally coherent enough for learning to pay",
      meaning.temporallyCoherentEnoughForLearning⟩,
    ⟨"Continuing learning can do better than every fixed solution",
      continuingLearningCanBeatEveryFixedSolution meaning⟩,
    ⟨"The class contributes toward any big world",
      meaning.contributesTowardAnyBigWorld⟩,
    ⟨"The long-term aim still includes every big world",
      aimIncludesEveryBigWorld meaning⟩
  ]

/-- The non-behavioural data of the description, including its carriers
    and initial configurations. -/
structure DescriptionData where
  /-- The observations. -/
  Obs : Type
  /-- The actions. -/
  Act : Type
  /-- The members' names. -/
  Index : Type
  /-- Each member's states. -/
  State : Index → Type
  /-- Each member's start state. -/
  start : (i : Index) → State i
  /-- The attempt's length. -/
  length : Nat
  /-- The agent's memories. -/
  Memory : Type
  /-- The agent's initial memory. -/
  initial : Memory

/-- The non-behavioural data of a class with an agent. -/
def descriptionData (c : ClassWithAgent) : DescriptionData :=
  {
    Obs := c.Obs
    Act := c.Act
    Index := c.Index
    State := fun i => (c.member i).State
    start := fun i => (c.member i).start
    length := c.length
    Memory := c.agent.Memory
    initial := c.agent.initial
  }

/--
The component functions have subject-dependent input and output types.
Typed packages give Shape.bundle fixed carrier types while preserving
the original functions on correctly typed inputs.
-/
abbrev TypedValue := Sigma (fun T : Type => T)

/-- A function applied to a typed value of its input type, and nothing for a value of another
type. -/
noncomputable def typedApply {A B : Type}
    (f : A → B) (input : TypedValue) : Option TypedValue := by
  classical
  exact
    if h : input.1 = A then
      some ⟨B, f (cast h input.2)⟩
    else
      none

/-- A member's name with one of its states. -/
abbrev WorldState (c : ClassWithAgent) :=
  Sigma (fun i : c.Index => (c.member i).State)

/-- A member's name with one of its states and an action. -/
abbrev WorldStepInput (c : ClassWithAgent) :=
  Sigma (fun i : c.Index => (c.member i).State × c.Act)

/-- The shape the reply declares: a bundle of the functions of a class with an agent. -/
noncomputable def subjectShape : LeanIntent.Shape ClassWithAgent :=
  .bundle descriptionData
    {
      name := "World observations"
      In := TypedValue
      Out := Option TypedValue
      get := fun c => typedApply
        (fun p : WorldState c => (c.member p.1).observe p.2)
    }
    [
      {
        name := "World rewards"
        In := TypedValue
        Out := Option TypedValue
        get := fun c => typedApply
          (fun p : WorldState c => (c.member p.1).reward p.2)
      },
      {
        name := "World dynamics, including restarts"
        In := TypedValue
        Out := Option TypedValue
        get := fun c => typedApply
          (fun p : WorldStepInput c =>
            (⟨p.1, (c.member p.1).step p.2.1 p.2.2⟩ :
              WorldState c))
      },
      {
        name := "World goals"
        In := TypedValue
        Out := Option TypedValue
        get := fun c => typedApply
          (fun p : WorldState c => (c.member p.1).goal p.2)
      },
      {
        name := "Agent answers and memory updates"
        In := TypedValue
        Out := Option TypedValue
        get := fun c => typedApply
          (fun p : c.agent.Memory × Percept c =>
            c.agent.act p.1 p.2)
      }
    ]

/-- A named predicate of a class with an agent. -/
def classPredicate (name : String)
    (holds : ClassWithAgent → Prop) : LeanIntent.Pred.{1} :=
  { name := name, Arg := ClassWithAgent, holds := holds }

/-- The reply's vocabulary, under the given meanings. -/
def vocabulary (meaning : Meaning) : List LeanIntent.Pred.{1} :=
  (requirements meaning).map
    (fun clause => classPredicate clause.name clause.holds)
  ++
  [
    classPredicate "Can fully perceive the world's state"
      meaning.canFullyPerceiveState,
    classPredicate "Can represent values everywhere"
      meaning.canRepresentValuesEverywhere,
    classPredicate "Can represent best actions everywhere"
      meaning.canRepresentBestActionsEverywhere,
    {
      name := "A member's goal is reachable from its start"
      Arg := Sigma (fun c : ClassWithAgent => c.Index)
      holds := fun p => goalReachable p.1 p.2
    },
    {
      name := "A memoryless rule solves a member within an attempt"
      Arg := Sigma (fun c : ClassWithAgent =>
        (Percept c → c.Act) × c.Index)
      holds := fun p => memorylessSolves p.1 p.2.1 p.2.2
    },
    {
      name := "A subset is a small share of its class"
      Arg := Sigma (fun c : ClassWithAgent => c.Index → Prop)
      holds := fun p => meaning.smallShare p.1 p.2
    },
    {
      name := "Continuing learning does better than a fixed solution"
      Arg := Sigma (fun c : ClassWithAgent =>
        meaning.ContinuingLearning c × meaning.FixedSolution c)
      holds := fun p => meaning.doesBetter p.1 p.2.1 p.2.2
    },
    {
      name := "A world is generally big relative to its agent"
      Arg := WorldWithAgent
      holds := meaning.generallyBig
    },
    {
      name := "A world-agent pair remains in a class's long-term aim"
      Arg := ClassWithAgent × WorldWithAgent
      holds := fun p => meaning.includedInLongTermAim p.1 p.2
    }
  ]

/-- The blind record: the reply's record, one for each meaning of its qualitative vocabulary. -/
noncomputable def ownerIntent (meaning : Meaning) :
    LeanIntent.IntentRecord ClassWithAgent :=
  {
    shape := subjectShape
    dom := []
    props := requirements meaning
    vocab := vocabulary meaning
  }

end AcornOwnerIntent

end AcornVerif.Intent.BigClassBlind
