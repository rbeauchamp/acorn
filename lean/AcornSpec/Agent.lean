/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Sarsa
import AcornSpec.HistoricalEncoding
import AcornSpec.Exploration

/-!
# Executable specification: the agent

Models the retained discounted, hand-authored-subtask evaluator construction
from `src/agent/agent.rs` (the orchestrator: gaps, exploration
preemption, the option lifecycle, the meta-controller, `act` under the
`EvaluationMode` bound at construction), `src/agent/options.rs` (potential-shaped
reward-respecting skills with interruption), `src/agent/demon.rs` +
`src/handcrafted/cumulants.rs` (the 11-demon Horde), and
`src/handcrafted/subtasks.rs` (the three skill potentials).

Observational state (the decision trace, lifetime statistics) never feeds a
decision, the RNG, or a learner in the Rust source, and is omitted here;
the historical evaluator carries its decision state here. This executable
specification and the `agent-baseline` probe do not establish refinement of
the current learned-subtask default or the differential research hierarchy.
Their maintained local contracts live in `AcornVerif` and the Rust/Kani owners.
-/

namespace AcornSpec

open AcornSpec.Constants

/-! ## Cumulants (the Horde's 11 signals) -/

/-- Tail-recursive window scan for a tile kind. -/
def anyKindGo (obs : Obs) (code : UInt8) (i : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if obs.tiles.get! i &&& 0x7 == code then true
    else anyKindGo obs code (i + 1) fuel

/-- Whether any window tile has the given kind code. -/
@[inline]
def anyKind (obs : Obs) (code : UInt8) : Bool :=
  anyKindGo obs code 0 121

/-- Tail-recursive window scan for the food flag. -/
def anyFoodGo (obs : Obs) (i : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if obs.tiles.get! i &&& 0x08 != 0 then true
    else anyFoodGo obs (i + 1) fuel

/-- Whether any window tile carries food. -/
@[inline]
def anyFood (obs : Obs) : Bool :=
  anyFoodGo obs 0 121

/-- `Cumulant::eval` for the demon at index `d` (in `Cumulant::ALL` order:
goal reward, near tree/stone/ore/water/food, energy low, night, has
wood/stone/axe). -/
def cumulantEval (d : Nat) (obs : Obs) (res : StepRes) : Float32 :=
  let flag (b : Bool) : Float32 := if b then natF32 1 else f32zero
  match d with
  | 0 => if f32zero < res.reward then natF32 1 else f32zero
  | 1 => flag (anyKind obs 4)   -- Tree
  | 2 => flag (anyKind obs 6)   -- Stone
  | 3 => flag (anyKind obs 7)   -- Ore
  | 4 => flag (anyKind obs 0)   -- Water
  | 5 => flag (anyFood obs)
  | 6 => flag (obs.energyBucket ≤ 3)
  | 7 => flag (4 ≤ obs.dayPhase)
  | 8 => flag (1 ≤ obs.invWood)
  | 9 => flag (1 ≤ obs.invStone)
  | _ => flag obs.invAxe

/-! ## Skills (options) -/

/-- `agent::SkillId` — the closed skill set. -/
inductive SkillId where
  /-- Tree-visible shaping potential. -/
  | wood
  /-- Rock-or-ore-visible shaping potential. -/
  | mine
  /-- Food-visible shaping potential. -/
  | forage
  deriving DecidableEq, Repr

/-- `SkillInterest::potential` — the indicator potential (`Potential` is
`{0, 1}` by construction, so a `Bool` carries it exactly). -/
def SkillId.potential (s : SkillId) (obs : Obs) : Bool :=
  match s with
  | .wood => anyKind obs 4
  | .mine => anyKind obs 7 || anyKind obs 6
  | .forage => anyFood obs

/-- `SkillInterest::stopping_value` — each variant owns its `z`. The
content of a derived bonus is not instantiated: each arm returns the
agent's estimate at zero bonus. -/
def SkillId.stoppingValue (s : SkillId) (agentEstimate : Float32) : Float32 :=
  match s with
  | .wood => agentEstimate
  | .mine => agentEstimate
  | .forage => agentEstimate

/-- `Potential::get` of an indicator. -/
@[inline]
def potentialGet (p : Bool) : Float32 := if p then natF32 1 else f32zero

/-- `options::OPTION_MAX_DURATION`. -/
def optionMaxDuration : UInt32 := 128

/-- Streaming option model predicting reward and continuation (STOMP-M, PAR-13). -/
structure OptionModel where
  /-- Expected cumulative host task reward predictor. -/
  reward : SwiftTd
  /-- Expected continuation state-value predictor. -/
  continuation : SwiftTd

namespace OptionModel

/-- `OptionModel::new` — fresh model with controller discount (g99). -/
def new : OptionModel :=
  let cfg := SwiftCfg.demon .g99
  ⟨SwiftTd.new cfg, SwiftTd.new cfg⟩

/-- `OptionModel::begin` — begin a new trajectory at `features`. -/
def begin (m : OptionModel) (features : Array UInt32) : OptionModel :=
  ⟨m.reward.begin features, m.continuation.begin features⟩

/-- `OptionModel::step` — intra-option transition step. -/
def step (m : OptionModel) (features : Array UInt32) (taskReward : Float32) : OptionModel :=
  let (r, _, _) := m.reward.step features taskReward
  let (c, _, _) := m.continuation.step features f32zero
  ⟨r, c⟩

/-- `OptionModel::terminate` — terminal transition step. -/
def terminate (m : OptionModel) (taskReward : Float32) (agentEstimate : Float32) : OptionModel :=
  let (r, _) := m.reward.terminalStep taskReward
  let gamma := m.continuation.cfg.gamma
  let boundedEst := projectNonneg agentEstimate m.continuation.cfg.discount.horizon
  let (c, _) := m.continuation.terminalStep (gamma * boundedEst)
  ⟨r, c⟩

/-- `OptionModel::predict` backed up value: `r̂(s, o) + ĉ_v(s, o)` (STOMP eq. 19). -/
def backedUpValue (m : OptionModel) (features : Array UInt32) : Float32 :=
  let rRaw := m.reward.predict features
  let cRaw := m.continuation.predict features
  let rHorizon := m.reward.cfg.discount.horizon
  let cHorizon := m.continuation.cfg.discount.horizon
  let rPred := projectNonneg rRaw rHorizon
  let cPred := projectNonneg cRaw cHorizon
  projectNonneg (rPred + cPred) rHorizon

/-- `OptionModel::clear_transient`. -/
def clearTransient (m : OptionModel) : OptionModel :=
  ⟨m.reward.clearTransient, m.continuation.clearTransient⟩

/-- `OptionModel::retire_feature`. -/
def retireIndex (m : OptionModel) (idx : Nat) : OptionModel :=
  ⟨m.reward.retireIndex idx, m.continuation.retireIndex idx⟩

end OptionModel

/-- One learned skill: its interest, primitive controller, and option model. -/
structure Skill where
  /-- The skill's identity (its potential). -/
  interest : SkillId
  /-- The intra-option Swift-Sarsa controller over the 9 primitives. -/
  sarsa : Sarsa
  /-- Streaming option model (STOMP-M, PAR-13). -/
  model : OptionModel

/-- Take-out placeholder; never observed. -/
instance : Inhabited Skill := ⟨⟨.wood, Sarsa.dummySarsa, OptionModel.new⟩⟩

/-- `options::OptionActivation` — trajectory-local state of one live
invocation. `learning = false` is the frozen activation mode. -/
structure Activation where
  /-- Whether the activation may update its learner. -/
  learning : Bool
  /-- Transitions executed. -/
  stepsRun : UInt32
  /-- Previous shaping potential. -/
  prevPotential : Bool

/-- `options::OptionEnd` — why a live option ends. -/
inductive OptionEnd where
  /-- The host task produced its terminal result. -/
  | goal
  /-- The activation reached its fixed work bound. -/
  | duration
  /-- The stopping value became strictly larger. -/
  | interrupted
  deriving DecidableEq

/-- `OptionSkill::begin` — clear transient state for a learning invocation,
begin option model trajectory, and issue the first potential. Returns the skill,
the activation, and the continuation potential. -/
def Skill.begin (sk : Skill) (features : Array UInt32) (obs : Obs) (learning : Bool) :
    Skill × Activation × Bool :=
  let sk :=
    if learning then
      { sk with sarsa := sk.sarsa.clearTransient, model := sk.model.begin features }
    else sk
  let potential := sk.interest.potential obs
  (sk, ⟨learning, 0, potential⟩, potential)

/-- `OptionSkill::decide` — terminate on the host terminal, the duration
bound, or strict interruption; otherwise continue with the current
potential. `agentEstimate` is the input to this skill's `stoppingValue`,
not a shared `z`. -/
def Skill.decide (sk : Skill) (act : Activation) (features : Array UInt32)
    (obs : Obs) (res : StepRes) (agentEstimate : Float32) :
    Sum Bool OptionEnd :=
  if res.done then .inr .goal
  else if optionMaxDuration ≤ act.stepsRun then .inr .duration
  else
    let potential := sk.interest.potential obs
    let vals := sk.sarsa.predictAll features
    let shaped := vals.foldl (fun m v => rustMax32 m v) f32NegInf
    let continuing := shaped + potentialGet potential
    let stoppingValue := sk.interest.stoppingValue agentEstimate
    if continuing < stoppingValue then .inr .interrupted
    else .inl potential

/-- `options::shaped_cumulant`. -/
@[inline]
def shapedCumulant (reward gamma : Float32) (next previous : Bool) : Float32 :=
  reward + gamma * potentialGet next - potentialGet previous

/-- `options::terminal_cumulant` — the subtask rule's `c + z` at `β = 1`,
shaped: the stopping value is bootstrapped undiscounted (G31).
Sutton, Machado et al., arXiv:2202.03466v4, eq. (5) printed p. 9. -/
@[inline]
def terminalCumulant (reward stopping : Float32) (previous : Bool) : Float32 :=
  reward + stopping - potentialGet previous

/-- `OptionSkill::step` — select the primitive action (ε-greedy at the rate
this skill's arm leaves it, its own derivation by default), learn from the
shaped cumulant when the activation is a learning one, step option model,
and age the activation. -/
def Skill.step (sk : Skill) (act : Activation) (continuation : Bool)
    (features : Array UInt32) (res : StepRes) (rng : Xoshiro256)
    (rate : ConsumerRate) : Skill × Activation × Nat × Xoshiro256 :=
  let vals := sk.sarsa.predictAll features
  let (action, rng) :=
    Sarsa.epsilonGreedyChoice vals (rate.resolve sk.sarsa.exploreRate) rng
  let sk :=
    if act.learning then
      let gamma := sk.sarsa.cfg.gamma
      let cumulant := shapedCumulant res.reward gamma continuation act.prevPotential
      let ⟨interest, sarsa, model⟩ := sk
      let sarsa' := (sarsa.step features action cumulant).1
      let model' := if 0 < act.stepsRun then model.step features res.reward else model
      ⟨interest, sarsa', model'⟩
    else sk
  let act := { act with prevPotential := continuation,
                        stepsRun := act.stepsRun + min 1 (0xFFFFFFFF - act.stepsRun) }
  (sk, act, action, rng)

/-- `OptionSkill::terminate` — the one closing update of a learning
activation. -/
def Skill.terminate (sk : Skill) (act : Activation) (res : StepRes)
    (agentEstimate : Float32) : Skill :=
  if act.learning then
    let stopping := sk.interest.stoppingValue agentEstimate
    let cumulant := terminalCumulant res.reward stopping act.prevPotential
    { sk with
      sarsa := sk.sarsa.terminalStep cumulant,
      model := sk.model.terminate res.reward agentEstimate }
  else sk

/-! ## The agent -/

/-- `agent::ControlCredit` — the primitive controller's credit policy, fixed
at construction. `perStep` is the retained evaluator credit policy (PAR-9); the other two are
the intra-option-credit evaluator ablation arms, each carrying its own span state. -/
inductive ControlCredit where
  /-- Intra-option learning: the ordinary executed-action update every
  learning step (PAR-9). -/
  | perStep
  /-- The pre-PAR-9 incumbent: skip under options, one SMDP catch-up at the
  next own action (gap steps and discounted owed-reward bits). -/
  | smdpCatchUp (steps : UInt32) (rewardBits : UInt32)
  /-- No span compensation at all (the pre-G12 shape). -/
  | noSpanCredit
  deriving Repr

/-- `agent::Phase` — exclusive occupancy of the action-selection path.
A term with exploring remaining *and* an active option is a type error. -/
inductive Phase where
  /-- No exploratory run and no option: the meta-controller may act. -/
  | idle
  /-- A committed εz-greedy run is being served. Preempts skills and meta. -/
  | exploring (remaining : UInt32) (action : Nat)
  /-- Exactly one skill invocation owns the next option update. -/
  | option (skill : Nat) (activation : Activation)

/-- `agent::EvaluationMode`. -/
inductive Agent.Mode where
  /-- Final hierarchical learner. -/
  | final
  /-- Learning disabled, initialization and exploration identical. -/
  | frozen
  /-- Reach relation removed from the feature stream. -/
  | withoutReachRelation
  /-- Option/meta control disabled. -/
  | primitiveOnly
  deriving DecidableEq

/-- `agent::Agent` at the study shape: featurizer, 11 demons, primitive and
meta controllers, 3 skills, the evaluator arm, the control-credit policy,
exclusive `Phase` occupancy, RNG and the step counter. -/
structure Agent where
  /-- The featurizer. -/
  featurizer : Featurizer
  /-- The 11 demon learners, in `Cumulant::ALL` order. -/
  demons : Array SwiftTd
  /-- Previous step's demon predictions (f32 bits), the features-as-state. -/
  demonPreds : Array UInt32
  /-- Primitive controller (9 actions). -/
  control : Sarsa
  /-- The three skills. -/
  skills : Array Skill
  /-- Meta-controller (4 actions). -/
  metaCtl : Sarsa
  /-- The evaluator arm, fixed at construction: an agent acts under one arm
  for its whole stream, so an arm without temporal abstraction never holds an
  option occupancy a later primitive-only step could overwrite. -/
  mode : Agent.Mode
  /-- Exclusive occupancy: idle, exploring, or one option. -/
  phase : Phase
  /-- Primitive-controller credit policy, fixed at construction. -/
  controlCredit : ControlCredit
  /-- Where every ε-consumer's rate comes from, fixed at construction. -/
  rate : RatePolicy
  /-- Meta controller's gap: skipped steps. -/
  metaGapSteps : UInt32
  /-- Meta controller's gap: discounted owed reward (bits). -/
  metaGapReward : UInt32
  /-- Exploration/action RNG stream. -/
  rng : Xoshiro256
  /-- Lifetime step count. -/
  steps : UInt64
  /-- Imprint units retired so far: the length of `RetirementProgress`. The
  tester is inert once this reaches the bank size (one event per slot). -/
  retired : Nat

namespace Agent

/-- `EvaluationMode::learns`. Exhaustive: a new variant is a type error
rather than inheriting learning-on from `_ => true`. -/
@[inline]
def Mode.learns : Mode → Bool
  | .final | .withoutReachRelation | .primitiveOnly => true
  | .frozen => false

/-- `EvaluationMode::uses_reach_relation`. Exhaustive. -/
@[inline]
def Mode.usesReach : Mode → Bool
  | .final | .frozen | .primitiveOnly => true
  | .withoutReachRelation => false

/-- `EvaluationMode::uses_temporal_abstraction`. Exhaustive. -/
@[inline]
def Mode.usesTemporalAbstraction : Mode → Bool
  | .final | .frozen | .withoutReachRelation => true
  | .primitiveOnly => false

/-- `EvaluationMode::task_features`. -/
@[inline]
def Mode.taskFeatures (m : Mode) : TaskFeatureMode :=
  if m.usesReach then .complete else .withoutReachRelation

/-- `Agent::with_arm` — every learner from zero knowledge, at one evaluator
arm's construction-fixed mode, credit and rate policies. -/
def withArm (seed : UInt64) (mode : Mode) (credit : ControlCredit) (rate : RatePolicy) :
    Agent :=
  { featurizer := Featurizer.new seed
    demons := Array.ofFn (n := 11) fun d => SwiftTd.new (SwiftCfg.demon (cumulantDiscount d.val))
    demonPreds := Array.replicate 11 0
    control := Sarsa.new 9 (SwiftCfg.control .g99)
    skills := #[⟨.wood, Sarsa.new 9 (SwiftCfg.optionSkill .g99), OptionModel.new⟩,
                ⟨.mine, Sarsa.new 9 (SwiftCfg.optionSkill .g99), OptionModel.new⟩,
                ⟨.forage, Sarsa.new 9 (SwiftCfg.optionSkill .g99), OptionModel.new⟩]
    metaCtl := Sarsa.new 4 (SwiftCfg.control .g99)
    mode
    phase := .idle
    controlCredit := credit
    rate
    metaGapSteps := 0, metaGapReward := 0
    rng := Xoshiro256.new (Xoshiro256.streamKey seed 0xA6E0000000000001)
    steps := 0
    retired := 0 }

/-- Historical evaluator default: discounted control and hand-authored subtasks. -/
def new (seed : UInt64) : Agent := withArm seed .final .perStep .perLearner

/-- `Agent::controller_rate` — the rate one controller (primitive or meta)
explores at under this agent's arm. -/
def controllerRate (a : Agent) (own : Float32) : Float32 :=
  match a.rate with
  | .perLearner => own
  | .shared => a.control.exploreRate
  | .annealed s => s.rate

/-- `Agent::skill_rate` — what this agent's arm imposes on an option skill,
if anything. -/
def skillRate (a : Agent) : ConsumerRate :=
  match a.rate with
  | .perLearner => .ownLearner
  | .shared => .imposed a.control.exploreRate
  | .annealed _ =>
    .imposed (saturate (Float32.ofBits Constants.optionEpsilonBits) f32zero (natF32 1))

/-- `Gap::accumulate` — add this step's reward at the accrued discount. -/
@[inline]
def gapAccumulate (steps : UInt32) (rewardBits : UInt32) (stepReward gamma : Float32) :
    UInt32 :=
  (Float32.ofBits rewardBits + stepReward * pow32 gamma steps).toBits

/-- `Gap::close` — the owed reward and covered span. -/
@[inline]
def gapClose (steps : UInt32) (rewardBits : UInt32) : Float32 × UInt32 :=
  (Float32.ofBits rewardBits, steps + min 1 (0xFFFFFFFF - steps))

/-- Whether imprint index `idx` is negligible in every learner this agent
owns — the every-consumer conjunct of PAR-11. -/
def unitNegligibleEverywhere (a : Agent) (idx : UInt32) : Bool :=
  let i := idx.toNat
  a.control.learners.all (fun l => l.unitIsNegligible i) &&
    a.metaCtl.learners.all (fun l => l.unitIsNegligible i) &&
    a.skills.all (fun sk => sk.sarsa.learners.all (fun l => l.unitIsNegligible i)) &&
    a.demons.all (fun l => l.unitIsNegligible i)

/-- `SwiftSarsa::retire_feature` — `retireIndex` in every action learner,
then the wrapper's shared `v_old`/`v_delta` cleared. -/
def retireOnSarsa (s : Sarsa) (idx : UInt32) : Sarsa :=
  { s with
    learners := s.learners.map (fun l => l.retireIndex idx.toNat)
    vOld := 0
    vDelta := 0 }

/-- `Agent::maybe_retire` — while the transcript has room (fewer retirements
than bank slots), the first imprint unit that is negligible in every learner
is replaced in place and the retirement counted; at most one per step. -/
def maybeRetire (a : Agent) : Agent :=
  let rec go (u : Nat) : Nat → Agent
    | 0 => a
    | fuel + 1 =>
      let feat := a.featurizer.imprintFeat u.toUInt64
      if a.unitNegligibleEverywhere feat then
        { a with
          featurizer := a.featurizer.replaceUnit u
          control := retireOnSarsa a.control feat
          metaCtl := retireOnSarsa a.metaCtl feat
          skills := a.skills.map (fun sk => { sk with
            sarsa := retireOnSarsa sk.sarsa feat
            model := sk.model.retireIndex feat.toNat })
          demons := a.demons.map (fun l => l.retireIndex feat.toNat)
          retired := a.retired + 1 }
      else
        go (u + 1) fuel
  if a.retired < imprintUnits then go 0 imprintUnits else a

/-- `Agent::update_demons` — one Horde sweep; every demon learns and its
projected prediction becomes next step's feature channel. -/
def updateDemons (a : Agent) (features : Array UInt32) (obs : Obs) (res : StepRes) :
    Agent :=
  let ⟨featurizer, demons, demonPreds, control, skills, metaCtl, mode, phase,
       credit, rate, mgs, mgr, rng, steps, retired⟩ := a
  let n := demons.size
  let (demons, demonPreds) := Id.run do
    let mut ds := demons
    let mut preds := demonPreds
    for d in [0:n] do
      let r := cumulantEval d obs res
      let l := ds[d]!
      let ds' := ds.set! d Sarsa.dummySwift
      let (l, v, _) := l.step features r
      ds := ds'.set! d l
      let horizon := (cumulantDiscount d).horizon
      preds := preds.set! d (projectNonneg v horizon).toBits
    pure (ds, preds)
  let a : Agent :=
    ⟨featurizer, demons, demonPreds, control, skills, metaCtl, mode, phase,
      credit, rate, mgs, mgr, rng, steps, retired⟩
  a.maybeRetire

/-- `Agent::credit_control_option_step` — credit for a step an option
executed, per the constructed policy. -/
def creditControlOption (a : Agent) (features : Array UInt32) (executed : Nat)
    (reward : Float32) : Agent :=
  match a.controlCredit with
  | .perStep =>
    let control := a.control
    let a := { a with control := Sarsa.dummySarsa }
    { a with control := (control.step features executed reward).1 }
  | .smdpCatchUp steps rewardBits =>
    let gamma := a.control.cfg.gamma
    let rewardBits := gapAccumulate steps rewardBits reward gamma
    { a with controlCredit := .smdpCatchUp (steps + 1) rewardBits }
  | .noSpanCredit => a

/-- `Agent::credit_control_own_step` — credit at a step where the primitive
controller supplied the action, per the constructed policy. -/
def creditControlOwn (a : Agent) (features : Array UInt32) (action : Nat)
    (reward : Float32) : Agent :=
  match a.controlCredit with
  | .perStep | .noSpanCredit =>
    let control := a.control
    let a := { a with control := Sarsa.dummySarsa }
    { a with control := (control.step features action reward).1 }
  | .smdpCatchUp steps rewardBits =>
    let gamma := a.control.cfg.gamma
    let rewardBits := gapAccumulate steps rewardBits reward gamma
    let (owed, k) := gapClose steps rewardBits
    let control := a.control
    let a := { a with control := Sarsa.dummySarsa,
                      controlCredit := .smdpCatchUp 0 0 }
    { a with control := (control.smdpStep features action owed k).1 }

/-- `Agent::learn_meta`. -/
def learnMeta (a : Agent) (features : Array UInt32) (ma : Nat) : Agent :=
  let (owed, k) := gapClose a.metaGapSteps a.metaGapReward
  let metaCtl := a.metaCtl
  let a := { a with metaCtl := Sarsa.dummySarsa,
                    metaGapSteps := 0, metaGapReward := 0 }
  { a with metaCtl := (metaCtl.smdpStep features ma owed k).1 }

/-- Serve the next committed explore action, or spend a finished run. -/
def serveExploring (a : Agent) : Option Nat × Agent :=
  match a.phase with
  | .exploring remaining action =>
    if 0 < remaining then
      (some action, { a with phase := .exploring (remaining - 1) action })
    else
      (none, { a with phase := .idle })
  | .idle | .option _ _ => (none, a)

/-- Begin an exploratory run at a primitive decision; occupancy is `Phase`. -/
def beginExploring (a : Agent) (rate : Float32) : Option Nat × Agent :=
  let (begun, rng) := EzGreedy.begin rate a.rng
  match begun with
  | some (x, remaining) =>
    let phase := if 0 < remaining then Phase.exploring remaining x else Phase.idle
    (some x, { a with rng := rng, phase })
  | none => (none, { a with rng := rng })

/-- `Agent::act_primitive_only` — the temporal-abstraction ablation: the
final observation and exploration, no option or meta selection. Learning
follows `Mode.learns`, not an implicit always-on. -/
def actPrimitiveOnly (a : Agent) (obs : Obs) (res : StepRes) (learning : Bool) :
    Agent × Action :=
  let features := encodeObservation a.featurizer obs a.demonPreds .complete
  let vals := a.control.predictAll features
  let (served, a) := a.serveExploring
  let (choice, a) :=
    match served with
    | some x => (some x, a)
    | none => a.beginExploring (a.controllerRate a.control.exploreRate)
  let (action, a) :=
    match choice with
    | some x => (x, a)
    | none =>
      let (g, rng) := Sarsa.greedy vals a.rng
      (g, { a with rng })
  let a :=
    if learning then
      let a := a.creditControlOwn features action res.reward
      a.updateDemons features obs res
    else a
  (a, Action.fromIndex action)

/-- `Planner::plan` (PAR-14) — background planning backups over option models. -/
def plan (metaCtl : Sarsa) (skills : Array Skill) (features : Array UInt32) : Sarsa :=
  let n := skills.size
  Id.run do
    let mut m := metaCtl
    for i in [0:n] do
      let ma := 1 + i
      let target := skills[i]!.model.backedUpValue features
      let (mNext, _) := m.planStep ma features target
      m := mNext
    pure m

/-- `Agent::act_in_mode` — one decision of the full hierarchy under `mode`,
the agent's own arm, in the exact priority order of the Rust orchestrator:
exploration run in progress, active option, meta-controller, then the
primitive layer. -/
def actInMode (a : Agent) (obs : Obs) (res : StepRes) (mode : Mode) :
    Agent × Action :=
    let learning := mode.learns
    -- Charge the meta gap before any branch; the primitive controller has no
    -- gap — every learning branch hands it this step's reward directly.
    let a :=
      if learning then
        let mg := a.metaCtl.cfg.gamma
        { a with
          metaGapReward := gapAccumulate a.metaGapSteps a.metaGapReward res.reward mg }
      else a
    let features := encodeObservation a.featurizer obs a.demonPreds mode.taskFeatures
    -- Exploratory run in progress preempts everything.
    let (served, a) := a.serveExploring
    match served with
    | some x =>
      let a :=
        if learning then
          let a := a.creditControlOwn features x res.reward
          let a := { a with metaGapSteps := a.metaGapSteps + 1 }
          a.updateDemons features obs res
        else a
      (a, Action.fromIndex x)
    | none =>
      -- Skills layer: an active option decides, continues or terminates.
      let phase := a.phase
      let a := { a with phase := .idle }
      let (a, continueData) :=
        match phase with
        | .option si act =>
          let agentEstimate := (a.metaCtl.predictAll features).foldl
            (fun m v => rustMax32 m v) f32NegInf
          let sk := a.skills[si]!
          match sk.decide act features obs res agentEstimate with
          | .inl continuation =>
            (a, some (si, act, continuation))
          | .inr _ =>
            let skills := a.skills.set! si (sk.terminate act res agentEstimate)
            ({ a with skills }, none)
        | .idle | .exploring _ _ => (a, none)
      match continueData with
      | some (si, act, continuation) =>
        -- Continue the active option.
        let sk := a.skills[si]!
        let skills0 := a.skills.set! si ⟨SkillId.wood, Sarsa.dummySarsa, OptionModel.new⟩
        let skillRate := a.skillRate
        let (sk, act, action, rng) := sk.step act continuation features res a.rng skillRate
        let skills := skills0.set! si sk
        let a := { a with skills := skills, rng := rng, phase := .option si act }
        let a :=
          if learning then
            let a := a.creditControlOption features action res.reward
            let a := { a with metaGapSteps := a.metaGapSteps + 1 }
            a.updateDemons features obs res
          else a
        (a, Action.fromIndex action)
      | none =>
        -- Meta-controller layer.
        let a := if learning then { a with metaCtl := plan a.metaCtl a.skills features } else a
        let metaVals := a.metaCtl.predictAll features
        let (ma, rng) :=
          Sarsa.epsilonGreedyChoice metaVals (a.controllerRate a.metaCtl.exploreRate) a.rng
        let a := { a with rng }
        let a := if learning then a.learnMeta features ma else a
        if 1 ≤ ma then
          -- Invoke a skill; it acts immediately.
          let si := ma - 1
          let sk := a.skills[si]!
          let skills0 := a.skills.set! si ⟨SkillId.wood, Sarsa.dummySarsa, OptionModel.new⟩
          let skillRate := a.skillRate
          let (sk, act, cont) := sk.begin features obs learning
          let (sk, act, action, rng) := sk.step act cont features res a.rng skillRate
          let skills := skills0.set! si sk
          let a := { a with skills := skills, rng := rng, phase := .option si act }
          let a :=
            if learning then
              let a := a.creditControlOption features action res.reward
              a.updateDemons features obs res
            else a
          (a, Action.fromIndex action)
        else
          -- Primitive control layer with εz-greedy.
          let vals := a.control.predictAll features
          let (choice, a) := a.beginExploring (a.controllerRate a.control.exploreRate)
          let (action, a) :=
            match choice with
            | some x => (x, a)
            | none =>
              let (g, rng) := Sarsa.greedy vals a.rng
              (g, { a with rng })
          let a :=
            if learning then
              let a := a.creditControlOwn features action res.reward
              a.updateDemons features obs res
            else a
          (a, Action.fromIndex action)

/-- `Agent::act` — the step count and rate clock advance once per step, then
the arm bound at construction dispatches: the primitive-only arm never
reaches the hierarchy, so it never holds an option occupancy to overwrite. -/
def act (a : Agent) (obs : Obs) (res : StepRes) : Agent × Action :=
  let a := { a with steps := a.steps + 1, rate := a.rate.advance }
  let mode := a.mode
  if !mode.usesTemporalAbstraction then a.actPrimitiveOnly obs res mode.learns
  else a.actInMode obs res mode

end Agent

end AcornSpec
