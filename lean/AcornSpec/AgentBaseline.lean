/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.World
import AcornSpec.Agent
import AcornSpec.StudySchema

/-!
# Executable specification: the agent-baseline protocol

Discounted evaluator for five arms with a shared opportunity loop. `StudySchema`
owns the row types and fixed protocol constants used by the analysis definitions.
This evaluator specifies its own transitions; correspondence to any observed
execution requires separate evidence.

The loop carries one world/agent stream per (seed, arm), carries inventory across
attempts, goals and cycles, sets a goal once per occurrence, and ends an attempt
at 4,000 steps or achievement. Its action fold uses the
`Constants.Compatibility.Domain.actionFold` identity. Fold equality is a lossy
observation and cannot establish transition equivalence.
-/

namespace AcornSpec

/-! ## Arms and policy -/

/-- The evaluator mode of an agent-backed arm (`AgentBaselineArm::evaluation_mode`). -/
def Arm.mode : Arm → Option Agent.Mode
  | .final => some .final
  | .random => none
  | .frozen => some .frozen
  | .ablatedGoalRelation => some .withoutReachRelation
  | .ablatedTemporalAbstraction => some .primitiveOnly

/-- `agent_baseline::AGENT_SEED`, generated from its sealed historical domain. -/
def agentSeed : UInt64 := Constants.Compatibility.Domain.agentBaselineInitialization.value

/-- The random arm's dedicated stream key at its sealed historical domain. -/
def randomArmKey : UInt64 :=
  Xoshiro256.streamKey agentSeed (Constants.Compatibility.Domain.agentBaselineRandom.value)

/-- `agent_baseline::ArmPolicySpec` — one executable arm lowered to the shared
stream loop's ingredients. -/
structure ArmSpec where
  /-- Agent-backed evaluator mode, absent for a pseudorandom comparator. -/
  mode : Option Agent.Mode
  /-- Primitive-controller credit policy for agent-backed arms. -/
  credit : ControlCredit
  /-- Where every ε-consumer's exploration rate comes from. -/
  rate : RatePolicy
  /-- Agent initialization / random base seed. -/
  agentSeed : UInt64
  /-- The pseudorandom comparator's dedicated stream key. -/
  randomKey : UInt64

/-- `AgentBaselineArm::spec` — the agent-baseline arms in the retained evaluator. -/
def Arm.spec (arm : Arm) : ArmSpec :=
  { mode := arm.mode, credit := .perStep, rate := .perLearner
    agentSeed := agentSeed, randomKey := randomArmKey }

/-- `intra_option_credit::AGENT_SEED`. -/
def intraOptionCreditAgentSeed : UInt64 := Constants.Compatibility.Domain.intraOptionCreditInitialization.value

/-- The intra-option-credit comparator's dedicated stream key. -/
def intraOptionCreditRandomArmKey : UInt64 :=
  Xoshiro256.streamKey intraOptionCreditAgentSeed (Constants.Compatibility.Domain.intraOptionCreditRandom.value)

/-- `intra_option_credit::IntraOptionCreditArm` — the five frozen intra-option-credit arms. -/
inductive IntraOptionCreditArm where
  /-- The deployed hierarchical learner (PAR-9 per-step credit). -/
  | final
  /-- Deterministic pseudorandom primitive comparator. -/
  | random
  /-- Identically initialized hierarchy with learner updates off. -/
  | frozen
  /-- The pre-PAR-9 incumbent credit path (skip + SMDP catch-up). -/
  | ablatedIntraOption
  /-- No span compensation at all (the pre-G12 shape). -/
  | ablatedSpanCredit
  deriving DecidableEq, Repr

/-- `IntraOptionCreditArm::spec`. -/
def IntraOptionCreditArm.spec : IntraOptionCreditArm → ArmSpec
  | .final => { mode := some .final, credit := .perStep, rate := .perLearner
                agentSeed := intraOptionCreditAgentSeed, randomKey := intraOptionCreditRandomArmKey }
  | .random => { mode := none, credit := .perStep, rate := .perLearner
                 agentSeed := intraOptionCreditAgentSeed, randomKey := intraOptionCreditRandomArmKey }
  | .frozen => { mode := some .frozen, credit := .perStep, rate := .perLearner
                 agentSeed := intraOptionCreditAgentSeed, randomKey := intraOptionCreditRandomArmKey }
  | .ablatedIntraOption =>
    { mode := some .final, credit := .smdpCatchUp 0 0, rate := .perLearner
      agentSeed := intraOptionCreditAgentSeed, randomKey := intraOptionCreditRandomArmKey }
  | .ablatedSpanCredit =>
    { mode := some .final, credit := .noSpanCredit, rate := .perLearner
      agentSeed := intraOptionCreditAgentSeed, randomKey := intraOptionCreditRandomArmKey }

/-- `derived_exploration_rate::AGENT_SEED`. -/
def derivedExplorationRateAgentSeed : UInt64 := Constants.Compatibility.Domain.derivedExplorationRateInitialization.value

/-- The derived-exploration-rate comparator's dedicated stream key. -/
def derivedExplorationRateRandomArmKey : UInt64 :=
  Xoshiro256.streamKey derivedExplorationRateAgentSeed (Constants.Compatibility.Domain.derivedExplorationRateRandom.value)

/-- `derived_exploration_rate::DerivedExplorationRateArm` — the five frozen derived-exploration-rate arms. -/
inductive DerivedExplorationRateArm where
  /-- The deployed learner: one derived rate per ε-consumer (PAR-10). -/
  | final
  /-- Deterministic pseudorandom primitive comparator. -/
  | random
  /-- Identically initialized hierarchy with learner updates off. -/
  | frozen
  /-- The incumbent hand-set schedule — the primary ablation. -/
  | ablatedAnnealedSchedule
  /-- One derived rate shared by every consumer — the attribution arm. -/
  | ablatedSharedRate
  deriving DecidableEq, Repr

/-- `DerivedExplorationRateArm::spec`. -/
def DerivedExplorationRateArm.spec : DerivedExplorationRateArm → ArmSpec
  | .final => { mode := some .final, credit := .perStep, rate := .perLearner
                agentSeed := derivedExplorationRateAgentSeed, randomKey := derivedExplorationRateRandomArmKey }
  | .random => { mode := none, credit := .perStep, rate := .perLearner
                 agentSeed := derivedExplorationRateAgentSeed, randomKey := derivedExplorationRateRandomArmKey }
  | .frozen => { mode := some .frozen, credit := .perStep, rate := .perLearner
                 agentSeed := derivedExplorationRateAgentSeed, randomKey := derivedExplorationRateRandomArmKey }
  | .ablatedAnnealedSchedule =>
    { mode := some .final, credit := .perStep
      rate := .annealed EpsilonSchedule.incumbent
      agentSeed := derivedExplorationRateAgentSeed, randomKey := derivedExplorationRateRandomArmKey }
  | .ablatedSharedRate =>
    { mode := some .final, credit := .perStep, rate := .shared
      agentSeed := derivedExplorationRateAgentSeed, randomKey := derivedExplorationRateRandomArmKey }

/-- `agent_baseline::StudyPolicy` — an agent-backed evaluator or the pseudorandom
comparator. -/
inductive Policy where
  /-- Agent-backed arm; its evaluator mode is bound into the agent at
  construction. -/
  | agent (a : Agent)
  /-- The comparator's dedicated generator. -/
  | random (rng : Xoshiro256)

/-- `StudyPolicy::new` over the lowered spec. -/
def Policy.ofSpec (spec : ArmSpec) : Policy :=
  match spec.mode with
  | some mode => .agent (Agent.withArm spec.agentSeed mode spec.credit spec.rate)
  | none => .random (Xoshiro256.new spec.randomKey)

/-- `StudyPolicy::new` for an agent-baseline protocol arm. -/
def Policy.new (arm : Arm) : Policy :=
  Policy.ofSpec arm.spec

/-- `StudyPolicy::action` — the random arm draws blind; agent arms observe
and act under their own arm. -/
def Policy.action (p : Policy) (w : World) (carried : StepRes) : Policy × Action :=
  match p with
  | .agent a =>
    let obs := w.observe
    let (a, act) := a.act obs carried
    (.agent a, act)
  | .random rng =>
    let (d, rng) := rng.nextBelow 9
    (.random rng, Action.fromIndex d.toNat)

/-- The binding fold's initial value, generated from its sealed historical domain. -/
def foldInit : UInt64 := Constants.Compatibility.Domain.actionFold.value

/-- Fold one action index into the transcript
(`fold · 0x100000001B3 + index + 1`, the `observe_action` recurrence). -/
@[inline]
def foldAction (fold : UInt64) (a : Action) : UInt64 :=
  fold * 0x00000100000001B3 + (a.index.toUInt64 + 1)

/-- The inner attempt loop: act, step, accumulate, stop at the cap or on
achievement. Returns world, policy, carried result, fold, steps and reward. -/
def runAttempt (w : World) (p : Policy) (carried : StepRes) (fold : UInt64) :
    World × Policy × StepRes × UInt64 × UInt64 × Float32 :=
  let rec
    go (w : World) (p : Policy) (carried : StepRes) (fold : UInt64)
        (steps : UInt64) (reward : Float32) : Nat →
        World × Policy × StepRes × UInt64 × UInt64 × Float32
      | 0 => (w, p, carried, fold, steps, reward)
      | fuel + 1 =>
        let (p, action) := p.action w carried
        let fold := foldAction fold action
        let (w, res) := w.step action
        let reward := reward + res.reward
        let steps := steps + 1
        if res.done then (w, p, res, fold, steps, reward)
        else go w p res fold steps reward fuel
  go w p carried fold 0 f32zero stepsPerAttempt.toNat

/-- `agent_baseline::run_arm_folded` at the frozen protocol — one lowered arm through
the single opportunity loop, plus the action-transcript fold. -/
def runSpec (seed : UInt64) (spec : ArmSpec) : Shard :=
  let w := World.new seed studyWorldSide
  let curriculum := standardCurriculum seed studyWorldSide
  let p := Policy.ofSpec spec
  Id.run do
    let mut w := w
    let mut p := p
    let mut carried := StepRes.default
    let mut fold := foldInit
    let mut rows : Array Row := Array.emptyWithCapacity (studyCycles * studyGoals * attemptsPerGoal)
    for cycle in [0:studyCycles] do
      for goalIndex in [0:studyGoals] do
        let goal := curriculum[goalIndex]!
        w := w.setGoal goal
        let initiallySatisfied := w.goalAchieved
        let mut occurrenceDone := false
        for attempt in [0:attemptsPerGoal] do
          if !occurrenceDone then
            let (w', p', carried', fold', steps, reward) := runAttempt w p carried fold
            w := w'
            p := p'
            carried := carried'
            fold := fold'
            rows := rows.push
              { cycle := cycle.toUInt64, goalIndex, goal
                tier := curriculumTiers[goalIndex]!
                family := goal.family, attempt, initiallySatisfied
                steps, achieved := carried.done, reward := reward.toBits }
            if carried.done then
              occurrenceDone := true
    pure { rows, actionFold := fold }

/-- `agent_baseline::run_arm` — one agent-baseline protocol arm. -/
def runArm (seed : UInt64) (arm : Arm) : Shard :=
  runSpec seed arm.spec

/-- `intra_option_credit::run` for one intra-option-credit arm. -/
def runIntraOptionCreditArm (seed : UInt64) (arm : IntraOptionCreditArm) : Shard :=
  runSpec seed arm.spec

/-- `derived_exploration_rate::run` for one derived-exploration-rate arm. -/
def runDerivedExplorationRateArm (seed : UInt64) (arm : DerivedExplorationRateArm) : Shard :=
  runSpec seed arm.spec

end AcornSpec
