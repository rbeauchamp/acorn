/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Rng
import Acorn.State

/-!
# The complete current SwiftTD learner

Executable implementation of **Algorithm 1** of

Javed, Sharifnassab & Sutton (2024), *SwiftTD: A Fast and Robust Algorithm for
Temporal Difference Learning*, Reinforcement Learning Journal, vol. 2,
pp. 840–863 / RLC 2024 — Algorithm 1 printed page 9 (RLJ vol. 2 p. 848),
equation (7) p. 845, equation (32) printed page 18, §6 p. 849.

Trajectory entries follow Sutton, Machado et al., *Reward-Respecting Subtasks
for Model-Based Reinforcement Learning*, Artificial Intelligence 324 (2023)
104001, eq. (5) at β = 1 and eq. (17) (PAR-13); the planning entry follows
Sutton, *Dyna, an Integrated Architecture for Learning, Planning, and
Reacting*, SIGART Bulletin 2(4):160–163 (1991), STOMP eq. (19), and Wan,
Zaheer, White, White & Sutton, *Planning with Expectation Models*, IJCAI 2019,
pp. 3649–3655 (PAR-14).

The three corrections of the source named in PAR-1 are part of this
definition: eligible-set pruning at `z ≤ ε·lastAlpha` (a deliberate
subtraction for cost), the total `Weight` / `LogStepSize` projections on every
knowledge write, and re-anchoring of the adaptation state when the weight
projection binds. Pruning clears the meta-gradient registers with the traces,
so a dormant feature carries no selective-credit state.

Features are binary by argument type: `ActiveSet` carries first-occurrence
uniqueness as a field, so every `φ[i]` and `φ[i]²` factor of the listing is 1
on the active set and drops out. The eligible list admits arbitrary raw public
loop arguments; its uniqueness and length properties are proved from the
actual transitions in `AcornVerif.CurrentLearner`, not assumed here.

Every per-index trace and meta-gradient register remains a raw word by design:
weight/beta projection does not bound traces or meta-gradients. Ordered sums
and comparisons keep their machine rounding; reassociation is not part of any
definition. The audit checksum's multiplicative and rotation words are learner-local
mixing constants.
-/

namespace Acorn

namespace Binary32

/-- IEEE numeric equality on raw words: NaN is unordered, the two zero
encodings compare equal. This is the `==` the learner's clip and push checks
perform, computed on storage without crossing the native boundary. -/
def numericallyEqual (left right : Binary32) : Bool :=
  let lm := left.bits &&& 0x7fffffff
  let rm := right.bits &&& 0x7fffffff
  !left.isNaN && !right.isNaN &&
    ((lm == rm) && (left.negative == right.negative || lm == 0))

/-- Word equality with a zero-sign exception is exactly signed-key equality. -/
theorem numericallyEqual_eq_key (left right : Binary32) :
    left.numericallyEqual right = (!left.isNaN && !right.isNaN && decide (left.key = right.key)) := by
  unfold numericallyEqual
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  unfold key
  split <;> split <;> simp_all [magnitude, ← UInt32.toNat_inj] <;> omega

/-- IEEE non-strict order uses reversed strict word order after NaN exclusion. -/
def lessOrEqual (left right : Binary32) : Bool :=
  !left.isNaN && !right.isNaN && !right.less left

/-- Non-strict word order has the same signed-key contract over every encoding. -/
theorem lessOrEqual_eq_key (left right : Binary32) :
    left.lessOrEqual right = (!left.isNaN && !right.isNaN && decide (left.key ≤ right.key)) := by
  by_cases hl : left.isNaN = true
  · simp [lessOrEqual, hl]
  by_cases hr : right.isNaN = true
  · simp [lessOrEqual, hr]
  have hlf : left.isNaN = false := Bool.eq_false_iff.mpr hl
  have hrf : right.isNaN = false := Bool.eq_false_iff.mpr hr
  by_cases h : left.key ≤ right.key
  · have hn : ¬right.key < left.key := by omega
    simp [lessOrEqual, less_eq_key, hlf, hrf, h, hn]
  · have hy : right.key < left.key := by omega
    simp [lessOrEqual, less_eq_key, hlf, hrf, h, hy]

/-- Zero classification reads only the magnitude field, identifying both signs. -/
def isZero (value : Binary32) : Bool := value.bits &&& 0x7fffffff == 0

/-- Exactly the zero magnitude has signed key zero, independently of sign. -/
theorem isZero_eq_key (value : Binary32) : value.isZero = decide (value.key = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [isZero, beq_iff_eq, decide_eq_true_eq, ← UInt32.toNat_inj]
  unfold key
  split <;> simp_all [magnitude] <;> omega

/-- Sign clearing on raw storage, the `f32::abs` word. -/
def abs (value : Binary32) : Binary32 := ⟨value.bits &&& 0x7fffffff⟩

/-- The multiplicative identity encoding. -/
def one : Binary32 := ⟨0x3f800000⟩

end Binary32

/-- Swap-remove position `pos` of an array, matching `Vec::swap_remove`: the
last element moves into `pos` and the tail shortens by one. -/
def SwiftTd.swapRemove {α : Type} (items : Array α) (pos : Nat) (inRange : pos < items.size) :
    Array α :=
  (items.set pos items[items.size - 1]).pop

/-- A first-occurrence-unique active-feature list over one weight space, the
argument every learner entry takes. Uniqueness is carried as a field, so the
binary-feature specialization of Algorithm 1 is a fact of the argument. -/
structure SwiftTd.ActiveSet (dimension : Dimension) where
  /-- Active indices in first-occurrence order. -/
  indices : List (FeatIdx dimension)
  /-- Each index occurs at most once. -/
  nodup : indices.Nodup

namespace SwiftTd

/-- Project the zipped prefix of a dimension-indexed vector and raw input,
leaving every untouched suffix word alone. The raw tail decreases structurally;
the position guard also stops traversal at capacity. -/
def restorePrefix {α : Type} {capacity : Nat} (project : Binary32 → α)
    (values : Vector α capacity) (raw : List Binary32) (pos : Nat := 0) : Vector α capacity :=
  match raw with
  | [] => values
  | word :: rest =>
    if inRange : pos < capacity then
      restorePrefix project (values.set pos (project word) inRange) rest (pos + 1)
    else values

/-- The empty active set; no feature is active. -/
def ActiveSet.empty (dimension : Dimension) : ActiveSet dimension := ⟨[], List.nodup_nil⟩

variable {config : Config} {dimension : Dimension}

/-- The pruning negligibility `θ = ε · bound` of this learner's immutable
criterion: the instantaneous prediction change admitted by retiring a unit
whose weight is below it (PAR-11). -/
def disruptionBound (config : Config) : Binary32 := config.epsilon.mul config.rule.bound

/-- The two words the retirement predicate reads at every slot of one learner:
its θ and its step-size floor, both functions of the configuration alone. -/
structure Negligibility {config : Config} (rails : StepSizeRails config) where
  /-- The direct-term bound `ε · ValueRule.bound`. -/
  theta : Binary32
  /-- The rail a finished unit's step size sits on. -/
  floor : LogStepSize rails

/-- An exploration rate is a probability: inside `[0, 1]` at storage. The
interval words are the reward interval's; the role is distinct. -/
def exploreRange : Interval32 where
  lower := .zero
  upper := Binary32.one
  lowerFinite := by decide
  upperFinite := by decide
  ordered := by decide

/-- A stored exploration rate, projected at construction. -/
abbrev ExploreRate := Bounded32 exploreRange

/-- Never explore. -/
def ExploreRate.never : ExploreRate := Bounded32.project exploreRange .zero

/-- The only constructor: project into `[0, 1]`, mapping NaN to the low
endpoint — "do not explore" rather than propagation. -/
def ExploreRate.project (raw : Binary32) : ExploreRate := Bounded32.project exploreRange raw

/-- One ε-consumer's rate after its arm has been consulted: derived from the
consumer's own step sizes, or imposed by the arm. -/
inductive ConsumerRate where
  /-- Derive from the consumer's own step sizes (PAR-10). -/
  | ownLearner
  /-- The arm imposes this rate. -/
  | imposed (rate : ExploreRate)

/-- Resolve, evaluating the consumer's own derivation only when the arm did
not impose one. -/
def ConsumerRate.resolve (rate : ConsumerRate) (own : Unit → ExploreRate) : ExploreRate :=
  match rate with
  | .ownLearner => own ()
  | .imposed imposedRate => imposedRate

/-- What one learner step produced: the prediction and its TD error. The value
carries the ordered-sum envelope only as a proof-layer fact
(`AcornVerif.CurrentPrediction`), matching the `LinearPrediction` owner. -/
structure TdStep where
  /-- The prediction `v = Σ_{i∈F} w[i]` for the features presented. -/
  value : Binary32
  /-- The TD error `δ' = r + γ·v − v_old`. -/
  error : Binary32

end SwiftTd

namespace NumericState

open SwiftTd (ActiveSet swapRemove disruptionBound Negligibility TdStep)

variable {config : Config} {dimension : Dimension}

/-- Write one raw eligibility-trace word. -/
def writeZ (state : NumericState config dimension) (idx : FeatIdx dimension) (word : Binary32) :
    NumericState config dimension :=
  { state with transient := { state.transient with
      z := state.transient.z.set idx.val ⟨word⟩ idx.isLt } }

/-- Write one raw trace-increment word. -/
def writeZDelta (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      zDelta := state.transient.zDelta.set idx.val ⟨word⟩ idx.isLt } }

/-- Write one raw Dutch-trace word. -/
def writeZBar (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      zBar := state.transient.zBar.set idx.val ⟨word⟩ idx.isLt } }

/-- Write one raw pruning-reference word. -/
def writeLastAlpha (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      lastAlpha := state.transient.lastAlpha.set idx.val ⟨word⟩ idx.isLt } }

/-- Write one raw per-weight-update word. -/
def writeDeltaWeight (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      deltaWeight := state.transient.deltaWeight.set idx.val ⟨word⟩ idx.isLt } }

/-- Write one raw Dutch-trace auxiliary word. -/
def writeH (state : NumericState config dimension) (idx : FeatIdx dimension) (word : Binary32) :
    NumericState config dimension :=
  { state with transient := { state.transient with
      h := state.transient.h.set idx.val ⟨word⟩ idx.isLt } }

/-- Write one raw previous-auxiliary word. -/
def writeHOld (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      hOld := state.transient.hOld.set idx.val ⟨word⟩ idx.isLt } }

/-- Write one raw accumulating-auxiliary word. -/
def writeHTemp (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      hTemp := state.transient.hTemp.set idx.val ⟨word⟩ idx.isLt } }

/-- Write one raw meta-trace word. -/
def writeP (state : NumericState config dimension) (idx : FeatIdx dimension) (word : Binary32) :
    NumericState config dimension :=
  { state with transient := { state.transient with
      p := state.transient.p.set idx.val ⟨word⟩ idx.isLt } }

/-- Install an already-legal log step size without a further projection: the
re-anchor word read from the learner's own rails. -/
def writeBetaValue (state : NumericState config dimension) (idx : FeatIdx dimension)
    (value : LogStepSize state.rails) : NumericState config dimension :=
  { state with beta := state.beta.set idx.val value idx.isLt }

/-- Zero every per-index transient register at `idx`, leaving the knowledge
slots alone: the register half of the PAR-1 drop path. -/
def clearFeatureRegisters (state : NumericState config dimension) (idx : FeatIdx dimension) :
    NumericState config dimension :=
  let state := state.writeZ idx .zero
  let state := state.writeP idx .zero
  let state := state.writeZBar idx .zero
  let state := state.writeDeltaWeight idx .zero
  let state := state.writeZDelta idx .zero
  let state := state.writeH idx .zero
  let state := state.writeHOld idx .zero
  let state := state.writeHTemp idx .zero
  state.writeLastAlpha idx .zero

/-- Remove the eligible entry at `pos` by swap-remove. -/
def removeEligibleAt (state : NumericState config dimension) (pos : Nat)
    (inRange : pos < state.transient.eligible.size) : NumericState config dimension :=
  { state with transient := { state.transient with
      eligible := swapRemove state.transient.eligible pos inRange } }

/-- Drop every trace and adaptation scratch, keeping the knowledge arrays.
Eligibility traces refer to a specific recent trajectory and do not survive a
checkpoint restore or a trajectory boundary. -/
def clearTransient (state : NumericState config dimension) : NumericState config dimension :=
  { state with transient := TransientState.zero dimension }

/-- Raw ordered prediction `Σ_{i∈F} w[i]` over the unique active features, in
first-occurrence order; no output projection is applied. -/
def linearPrediction (state : NumericState config dimension) (features : ActiveSet dimension) :
    Binary32 :=
  Binary32.sumMap .zero features.indices (fun idx => (state.weights.get idx).value)

/-- The executing prediction retains the exact ordered machine-word sum. -/
theorem linearPrediction_eq_sumFrom (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    state.linearPrediction features = Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.weights.get idx).value) := by
  simp only [linearPrediction, Binary32.sumMap_eq]

/-- Predict: the ordered weight sum over the active set. -/
def predict (state : NumericState config dimension) (features : ActiveSet dimension) : Binary32 :=
  state.linearPrediction features

/-- One element of the first loop (Algorithm 1, RLJ vol. 2 p. 848:
`δw[i] ← δ′ z[i] − zδ[i] vδ; w[i] ← w[i] + δw[i]; β[i] ← β[i] + (θ/e^{β[i]})
(δ′ − vδ) p[i]`), with the corrections of the source: the weight write
projects through the immutable criterion and re-anchors the adaptation state
when the projection binds; the β write saturates through one total
`LogStepSize` projection; the `h` register lags so the accumulating `hTemp`
stays the eq. (32) h_t. Returns the updated state and whether the decayed
trace fell to `ε · lastAlpha`, the pruning condition. The element never
touches the eligible list. -/
def firstLoopElement (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta traceDecay : Binary32) : NumericState config dimension × Bool :=
  let dw := (delta.mul (state.transient.z.get idx).value).sub
    ((state.transient.zDelta.get idx).value.mul vDelta)
  let raw := (state.weights.get idx).value.add dw
  let weight := Weight.project config.rule raw
  let clipped := !(weight.value.numericallyEqual raw)
  let beta := if clipped then state.rails.initial else state.beta.get idx
  let p := if clipped then Binary32.zero else (state.transient.p.get idx).value
  let zBar := if clipped then Binary32.zero else (state.transient.zBar.get idx).value
  let h := if clipped then Binary32.zero else (state.transient.h.get idx).value
  let hTemp := if clipped then Binary32.zero else (state.transient.hTemp.get idx).value
  let stepped := beta.value.add
    (((config.metaStep.div beta.alpha).mul (delta.sub vDelta)).mul p)
  let nextH := (hTemp.add (delta.mul zBar)).sub
    ((state.transient.zDelta.get idx).value.mul vDelta)
  let z := (state.transient.z.get idx).value.mul traceDecay
  let next : NumericState config dimension := {
    state with
    weights := state.weights.set idx.val weight idx.isLt
    beta := state.beta.set idx.val (LogStepSize.project state.rails stepped) idx.isLt
    transient := {
      state.transient with
      z := state.transient.z.set idx.val ⟨z⟩ idx.isLt
      zDelta := state.transient.zDelta.set idx.val ⟨.zero⟩ idx.isLt
      zBar := state.transient.zBar.set idx.val ⟨zBar.mul traceDecay⟩ idx.isLt
      p := state.transient.p.set idx.val ⟨p.mul traceDecay⟩ idx.isLt
      hOld := state.transient.hOld.set idx.val ⟨h⟩ idx.isLt
      h := state.transient.h.set idx.val ⟨hTemp⟩ idx.isLt
      hTemp := state.transient.hTemp.set idx.val ⟨nextH⟩ idx.isLt
      deltaWeight := state.transient.deltaWeight.set idx.val
        ⟨if clipped then .zero else dw⟩ idx.isLt } }
  (next, z.lessOrEqual ((state.transient.lastAlpha.get idx).value.mul config.epsilon))

/-- The first-loop traversal: trace-eligible weights in eligible order with
swap-remove pruning. The worklist is the state's eligible list at entry; each
visit either advances the position or swap-removes the pruned index, so the
measure drops on every step. The final eligible list is the pruned worklist,
in the order the swap-removes left it. -/
def learnFirstLoopGo (config : Config) (delta vDelta traceDecay : Binary32) :
    NumericState config dimension → Array (FeatIdx dimension) → Nat → NumericState config dimension
  | state, work, pos =>
    if inRange : pos < work.size then
      let idx := work[pos]
      let (state, prune) := state.firstLoopElement idx delta vDelta traceDecay
      if prune then
        learnFirstLoopGo config delta vDelta traceDecay (state.clearFeatureRegisters idx)
          (swapRemove work pos inRange) pos
      else learnFirstLoopGo config delta vDelta traceDecay state work (pos + 1)
    else { state with transient := { state.transient with eligible := work } }
  termination_by _state work pos => work.size - pos
  decreasing_by
    · simp only [swapRemove, Array.size_pop, Array.size_set]
      omega
    · omega

/-- The first loop of the update over the learner's eligible list. `delta`,
`vDelta` and `traceDecay` are raw public arguments; no hypothesis about a
normal stream is part of this definition. -/
def learnFirstLoop (config : Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) : NumericState config dimension :=
  let work := state.transient.eligible
  let state := { state with transient := { state.transient with eligible := #[] } }
  learnFirstLoopGo config delta vDelta traceDecay state work 0

/-- One element of the second loop (Algorithm 1, p. 848: `zδ[i] ←
min(1, η/τ) e^{β[i]}`, `p[i] ← p[i] + h[i]`, and the eq. (32) `hTemp`
correction), with the overshoot step-size decay applied after this step's
trace and meta-gradient updates. A zero trace joins the eligible list, the
only admission; the check reads the entry trace, before this element's writes.
Returns the updated state and shared update accumulator. -/
def secondLoopElement (config : Config) (overshoot : Bool) (e t : Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) (idx : FeatIdx dimension) :
    NumericState config dimension × Binary32 :=
  let eligible := if (state.transient.z.get idx).value.isZero then
    state.transient.eligible.push idx else state.transient.eligible
  let vDelta := vDelta.add (state.transient.deltaWeight.get idx).value
  let zd := (config.eta.div e).mul (state.beta.get idx).alpha
  let oneSubT := Binary32.one.sub t
  let z := (state.transient.z.get idx).value.add (zd.mul oneSubT)
  let p := (state.transient.p.get idx).value.add (state.transient.h.get idx).value
  let zBar := (state.transient.zBar.get idx).value.add
    (zd.mul (oneSubT.sub (state.transient.zBar.get idx).value))
  let hTemp := (((state.transient.hTemp.get idx).value.sub
    ((state.transient.hOld.get idx).value.mul (z.sub zd))).sub
      ((state.transient.h.get idx).value.mul zd))
  let beta := if overshoot then
    state.beta.set idx.val
      (LogStepSize.project state.rails ((state.beta.get idx).value.add state.rails.decay)) idx.isLt
    else state.beta
  let h := if overshoot then state.transient.h.set idx.val ⟨.zero⟩ idx.isLt else state.transient.h
  let next : NumericState config dimension := {
    state with
    beta := beta
    transient := {
      state.transient with
      eligible := eligible
      z := state.transient.z.set idx.val ⟨z⟩ idx.isLt
      zDelta := state.transient.zDelta.set idx.val ⟨zd⟩ idx.isLt
      lastAlpha := state.transient.lastAlpha.set idx.val ⟨zd⟩ idx.isLt
      p := state.transient.p.set idx.val ⟨p⟩ idx.isLt
      zBar := state.transient.zBar.set idx.val ⟨if overshoot then .zero else zBar⟩ idx.isLt
      hTemp := state.transient.hTemp.set idx.val ⟨if overshoot then .zero else hTemp⟩ idx.isLt
      h := h } }
  (next, vDelta)

/-- The second loop of the update: the active features in first-occurrence
order. `τ = Σ_{i∈F} e^{β[i]}` (eq. (7), p. 845), one overshoot binding for
both the trace scale and the step-size decay, and the shared `vDelta`
accumulator returned to the caller. -/
def learnSecondLoop (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    NumericState config dimension × Binary32 :=
  let rate := Binary32.sumMap .zero features.indices (fun idx => (state.beta.get idx).alpha)
  let overshoot := config.eta.less rate
  let e := if overshoot then rate else config.eta
  let t := Binary32.sumMap .zero features.indices (fun idx => (state.transient.z.get idx).value)
  features.indices.foldl
    (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
    (state, vDelta)

/-- Both executing pre-update sums preserve the complete ordered active loop,
for every receiving state, feature list and accumulator word. -/
theorem learnSecondLoop_eq_sumFrom (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    learnSecondLoop config state features vDelta =
      let rate := Binary32.sumFrom .zero
        (features.indices.map fun idx => (state.beta.get idx).alpha)
      let overshoot := config.eta.less rate
      let e := if overshoot then rate else config.eta
      let t := Binary32.sumFrom .zero
        (features.indices.map fun idx => (state.transient.z.get idx).value)
      features.indices.foldl
        (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
        (state, vDelta) := by
  simp only [learnSecondLoop, Binary32.sumMap_eq]

/-- One full single-learner update: predict, then the two loops with this
learner's own `vDelta` and `vOld`; the bootstrap multiplier and trace decay
derive from the immutable criterion. -/
def step (config : Config) (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) : NumericState config dimension × TdStep :=
  let v := state.linearPrediction features
  let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
  let state := state.learnFirstLoop config delta state.transient.vDelta
    (config.rule.gamma.mul config.lambda)
  let (state, vd) := state.learnSecondLoop config features .zero
  let state := { state with transient := { state.transient with vDelta := vd, vOld := v } }
  (state, ⟨v, delta⟩)

/-- Begin a new trajectory at `features` (STOMP eq. (17); Sutton, Precup &
Singh, AIJ 112 (1999), §5): clear transient registers, evaluate the anchor
prediction, and lay the initial traces. -/
def beginTrajectory (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) : NumericState config dimension :=
  let state := state.clearTransient
  let v := state.predict features
  let (state, vd) := state.learnSecondLoop config features .zero
  { state with transient := { state.transient with vOld := v, vDelta := vd } }

/-- Close the current trajectory with a terminal TD update (STOMP eq. (5) at
β = 1): loop 1 on existing traces, then transient registers clear. -/
def terminalStep (config : Config) (state : NumericState config dimension) (target : Binary32) :
    NumericState config dimension × Binary32 :=
  let delta := target.sub state.transient.vOld
  let state := state.learnFirstLoop config delta state.transient.vDelta
    (config.rule.gamma.mul config.lambda)
  (state.clearTransient, delta)

/-- A single background planning update toward `target` at `features` without
modifying eligibility traces or meta-gradient registers (PAR-14; Dyna 1991,
STOMP eq. (19)): `w[i] ← project (w[i] + (η/E)·α[i]·δ)`. A nonfinite or zero
error is no update. -/
def planStep (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    NumericState config dimension × Binary32 :=
  let v := state.predict features
  let delta := target.sub v
  if !decide delta.Finite || delta.numericallyEqual .zero then (state, .zero)
  else
    let rate := Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.beta.get idx).alpha)
    let e := if config.eta.less rate then rate else config.eta
    let scale := config.eta.div e
    let state := features.indices.foldl (fun state idx =>
      let stepSize := (scale.mul (state.beta.get idx).alpha).mul delta
      state.writeWeight idx ((state.weights.get idx).value.add stepSize)) state
    (state, delta)

/-- Replace one feature's knowledge and transients with a fresh unit's start
state: the first eligible occurrence removed (the whole membership under
uniqueness), every per-index register zero, weight
zeroed, step size re-anchored, and the representation-dependent aggregates
cleared so the next surviving update is not charged the retired feature's
residue. -/
def retireIndex (state : NumericState config dimension) (idx : FeatIdx dimension) :
    NumericState config dimension :=
  let state := match found : state.transient.eligible.findIdx? (· == idx) with
    | some pos =>
      state.removeEligibleAt pos (Array.findIdx?_eq_some_iff_getElem.mp found).1
    | none => state
  let state := state.clearFeatureRegisters idx
  let state := state.writeWeight idx .zero
  let state := state.writeBetaValue idx state.rails.initial
  { state with transient := { state.transient with vOld := .zero, vDelta := .zero } }

/-- Overwrite the learned weights from an untrusted source, projecting each
value through the immutable criterion. The traversal consumes only the zipped
prefix; untouched suffixes keep their prior legal words. -/
def restoreWeights (state : NumericState config dimension) (raw : List Binary32) :
    NumericState config dimension :=
  { state with weights := SwiftTd.restorePrefix (Weight.project config.rule) state.weights raw }

/-- Overwrite the learned log step sizes from an untrusted source, saturating
each through this learner's own rails; the same zipped-prefix traversal. -/
def restoreLogStepSizes (state : NumericState config dimension) (raw : List Binary32) :
    NumericState config dimension :=
  { state with beta := SwiftTd.restorePrefix (LogStepSize.project state.rails) state.beta raw }

/-- Exclusive restoration without learner or configuration replacement: both
knowledge arrays through their own refinements, then process-local registers
cleared, in that order. -/
def installRestored (state : NumericState config dimension) (weights logStepSizes : List Binary32) :
    NumericState config dimension :=
  (state.restoreWeights weights |>.restoreLogStepSizes logStepSizes).clearTransient

/-- This learner's own retirement words, derived once per scan. -/
def negligibility (state : NumericState config dimension) : Negligibility state.rails where
  theta := disruptionBound config
  floor := ⟨state.rails.range.lower, state.rails.range.lowerFinite,
    Int.le_refl _, state.rails.range.ordered⟩

/-- Whether `feat` is negligible under retirement words `theta` and `floor`:
weight magnitude below θ and the step size exactly on the floor. Both
conjuncts are required; a small weight still adapting has not finished being
tested. The words are consumed raw, as the every-consumer scan does. -/
def unitIsNegligibleUnder (state : NumericState config dimension) (theta floor : Binary32)
    (feat : FeatIdx dimension) : Bool :=
  ((state.weights.get feat).value.abs.less theta) &&
    ((state.beta.get feat).value.numericallyEqual floor)

/-- The single-reader negligibility predicate at this learner's own bounds. -/
def unitIsNegligible (state : NumericState config dimension) (feat : FeatIdx dimension) : Bool :=
  state.unitIsNegligibleUnder state.negligibility.theta state.negligibility.floor.value feat

/-- Mean step size `α = e^β` over all weights. -/
def meanAlpha (state : NumericState config dimension) : Binary32 :=
  (Binary32.sumFrom .zero (state.beta.toList.map (·.alpha))).div
    (Binary32.ofUInt64 dimension.capacity.toUInt64)

/-- Mean step size over the weights currently being adapted, or zero when
nothing is eligible. -/
def activeAlpha (state : NumericState config dimension) : Binary32 :=
  if state.transient.eligible.isEmpty then .zero
  else
    (Binary32.sumFrom .zero
      (state.transient.eligible.toList.map fun idx => (state.beta.get idx).alpha)).div
      (Binary32.ofUInt64 state.transient.eligible.size.toUInt64)

/-- Sum of the normalized log step sizes over the eligible set, with the count
of terms: `ν(β) = (β − ln η_min) / (ln η − ln η_min)` in the additive
β-coordinate the optimizer works in. The endpoints come from this learner's
own rails. -/
def normalizedStepSizeSum (state : NumericState config dimension) : Binary32 × Nat :=
  if state.transient.eligible.isEmpty then (.zero, 0)
  else
    let lo := state.rails.range.lower
    let span := state.rails.range.upper.sub lo
    (Binary32.sumFrom .zero (state.transient.eligible.toList.map fun idx =>
      ((state.beta.get idx).value.sub lo).div span), state.transient.eligible.size)

/-- The normalized log step size a fresh feature starts at, `ν(ln α_init)`,
recomputed from the configuration as the observer owner does. -/
def initialNormalizedStepSize (config : Config) (state : NumericState config dimension) :
    Binary32 :=
  let lo := state.rails.range.lower
  let span := state.rails.range.upper.sub lo
  ((Portable.ln config.alphaInitial).sub lo).div span

/-- Number of eligible entries, including multiplicity under raw repeated loop calls. -/
def eligibleCount (state : NumericState config dimension) : Nat := state.transient.eligible.size

/-- The audit mixing multiplier of the learner checksum. -/
def checksumMultiplier : UInt64 := 0x00000100000001b3

/-- The audit rotation: 64-bit left rotation by 13, expressed with shifts. -/
def checksumRotate (word : UInt64) : UInt64 := (word <<< 13) ||| (word >>> 51)

/-- A checksum of the learner knowledge state — the deterministic audit's raw
material: per slot, the weight word is folded, mixed, the step-size word
folded, and the accumulator rotated by 13, in index order. -/
def stateChecksum (state : NumericState config dimension) : UInt64 :=
  (state.weights.zip state.beta).foldl (fun hash (weight, beta) =>
    checksumRotate (((hash ^^^ weight.value.bits.toUInt64) * checksumMultiplier) ^^^
      beta.value.bits.toUInt64)) Acorn.Rng.fnvOffset

end NumericState

namespace SwiftTd

variable {config : Config} {dimension : Dimension}

/-- The complete state-changing learner interface. Raw machine arguments and
standalone loop calls retain their original domain. -/
inductive Entry (dimension : Dimension) where
  /-- First update loop with raw public arguments. -/
  | first (delta vDelta decay : Binary32)
  /-- Second update loop with a shared accumulator. -/
  | second (features : ActiveSet dimension) (vDelta : Binary32)
  /-- Single-learner TD update. -/
  | step (features : ActiveSet dimension) (reward : Binary32)
  /-- New trajectory boundary. -/
  | beginTrajectory (features : ActiveSet dimension)
  /-- Terminal trajectory boundary. -/
  | terminal (target : Binary32)
  /-- Background planning update. -/
  | plan (features : ActiveSet dimension) (target : Binary32)
  /-- Feature retirement boundary. -/
  | retire (idx : FeatIdx dimension)
  /-- Project an untrusted weight prefix. -/
  | restoreWeights (raw : List Binary32)
  /-- Saturate an untrusted beta prefix. -/
  | restoreBeta (raw : List Binary32)
  /-- Exclusive restoration followed by transient clearing. -/
  | install (weights beta : List Binary32)
  /-- Clear process-local state. -/
  | clear

/-- Execute one interface operation using the same definitions as the direct
methods. Their observation results remain available from those methods. -/
def Entry.apply (entry : Entry dimension) (state : NumericState config dimension) :
    NumericState config dimension :=
  match entry with
  | .first delta vDelta decay => state.learnFirstLoop config delta vDelta decay
  | .second features vDelta => (state.learnSecondLoop config features vDelta).1
  | .step features reward => (state.step config features reward).1
  | .beginTrajectory features => state.beginTrajectory config features
  | .terminal target => (state.terminalStep config target).1
  | .plan features target => (state.planStep config features target).1
  | .retire idx => state.retireIndex idx
  | .restoreWeights raw => state.restoreWeights raw
  | .restoreBeta raw => state.restoreLogStepSizes raw
  | .install weights beta => state.installRestored weights beta
  | .clear => state.clearTransient

/-- Phase after an entry: true permits a following standalone second loop.
This phase governs composed resource safety, not the standalone input domain. -/
def nextReady (entry : Entry dimension) (before : Bool) : Bool :=
  match entry with
  | .first .. | .terminal .. | .install .. | .clear => true
  | .second .. | .step .. | .beginTrajectory .. => false
  | .plan .. | .retire .. | .restoreWeights .. | .restoreBeta .. => before

/-- The resource contract requires readiness only for standalone loop two. -/
def Permitted (entry : Entry dimension) (ready : Bool) : Prop :=
  match entry with
  | .second .. => ready = true
  | _ => True

/-- Admission provenance of an executing state. The derivation is a `Prop`,
so no operation history or input stream is retained in native storage. -/
inductive Admitted (config : Config) (dimension : Dimension) : NumericState config dimension → Prop
  /-- Fresh initialized storage. -/
  | initial : Admitted config dimension (NumericState.initial config dimension)
  /-- Every supplied interface operation preserves admission provenance. -/
  | transition {state : NumericState config dimension} (entry : Entry dimension)
      (before : Admitted config dimension state) : Admitted config dimension (entry.apply state)

/-- The existing numeric state with an erased admission witness. A raw
register helper or caller-constructed record cannot bypass this boundary. -/
abbrev Learner (config : Config) (dimension : Dimension) :=
  { state : NumericState config dimension // Admitted config dimension state }

/-- Initialize admitted learner storage without an operation log. -/
def Learner.initial (config : Config) (dimension : Dimension) : Learner config dimension :=
  ⟨NumericState.initial config dimension, .initial⟩

/-- Advance admitted storage; the proof of provenance is erased at runtime. -/
def Learner.apply (learner : Learner config dimension) (entry : Entry dimension) :
    Learner config dimension := ⟨entry.apply learner.val, .transition entry learner.property⟩

/-- One reader of a feature slot, paired with the words its predicate reads.
Built once per learner per scan; `of` is the only intended constructor. -/
structure Consumer {config : Config} {dimension : Dimension} (rails : StepSizeRails config) where
  /-- The learner read. -/
  learner : NumericState config dimension
  /-- Its derived retirement words. -/
  bounds : Negligibility rails

/-- A learner under its own bounds. -/
def Consumer.of (state : NumericState config dimension) :
    Consumer (dimension := dimension) state.rails :=
  ⟨state, state.negligibility⟩

/-- Whether this reader treats `feat` as negligible. -/
def Consumer.negligible {config : Config} {dimension : Dimension} {rails : StepSizeRails config}
    (consumer : Consumer (dimension := dimension) rails) (feat : FeatIdx dimension) : Bool :=
  consumer.learner.unitIsNegligibleUnder consumer.bounds.theta consumer.bounds.floor.value feat

/-- Conjunction over every consumer of one feature slot: the unit is
negligible only when every reader says so. The reader vector is nonempty by
its type; a conjunction over no readers would retire every unit. Cross-config
composition of heterogeneous readers belongs to the checkpoint slice. -/
def unitNegligibleInEvery {config : Config} {dimension : Dimension}
    {rails : StepSizeRails config} {count : Nat}
    (consumers : Vector (Consumer (dimension := dimension) rails) (count + 1))
    (feat : FeatIdx dimension) : Bool :=
  consumers.toList.all (·.negligible feat)

end SwiftTd

end Acorn
