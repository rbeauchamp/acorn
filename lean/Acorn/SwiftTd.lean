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

open SwiftTd (ActiveSet swapRemove TdStep)

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

/-- Install an already-legal log step size without a further projection, beside
its portable exponential: the listed write of one log step size. -/
def writeBetaValue (state : NumericState config dimension) (idx : FeatIdx dimension)
    (value : LogStepSize state.rails) : NumericState config dimension :=
  state.writeStepSize idx value value.alpha rfl

/-- A step-size write stores the log step size it was given and that word's
portable exponential, whichever word the writer held: it is the listed write. -/
theorem writeStepSize_eq (state : NumericState config dimension) (idx : FeatIdx dimension)
    (value : LogStepSize state.rails) (word : Binary32) (same : word = value.alpha) :
    state.writeStepSize idx value word same = state.writeBetaValue idx value := by
  subst same
  rfl

/-- The step size the first loop adapts: the re-anchor word's when the weight
projection binds, the stored one otherwise. Either is the portable exponential of
the log step size the listed element reads. -/
theorem anchor_stepSize (state : NumericState config dimension) (idx : FeatIdx dimension)
    (clipped : Bool) :
    (if clipped then state.rails.initial.alpha else state.stepSize idx) =
      (if clipped then state.rails.initial else state.beta.get idx).alpha := by
  cases clipped
  · exact state.stepSize_eq idx
  · rfl

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

/-- Drop every eligible trace structurally: zero all nine registers of each
eligible index and empty the list. Knowledge, the previous prediction and the
weight-change aggregate are kept, and no arithmetic reads a trace. The work is
the eligible length, not the capacity. -/
def releaseEligible (state : NumericState config dimension) : NumericState config dimension :=
  let cleared := state.transient.eligible.foldl (fun next idx => next.clearFeatureRegisters idx)
    state
  { cleared with transient := { cleared.transient with eligible := #[] } }

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
stays the eq. (32) h_t. The step size `e^{β[i]}` is read from storage, and
the one stored for the adapted `β[i]` is that word again when the adaptation
leaves `β[i]` unchanged and its portable exponential otherwise;
`firstLoopElement_eq` equates the element with the listed one, whose every
exponential is evaluated. Returns the updated state and whether the decayed
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
  let alpha := if clipped then state.rails.initial.alpha else state.stepSize idx
  let p := if clipped then Binary32.zero else (state.transient.p.get idx).value
  let zBar := if clipped then Binary32.zero else (state.transient.zBar.get idx).value
  let h := if clipped then Binary32.zero else (state.transient.h.get idx).value
  let hTemp := if clipped then Binary32.zero else (state.transient.hTemp.get idx).value
  let stepped := beta.value.add
    (((config.metaStep.div alpha).mul (delta.sub vDelta)).mul p)
  let adapted := LogStepSize.project state.rails stepped
  let nextH := (hTemp.add (delta.mul zBar)).sub
    ((state.transient.zDelta.get idx).value.mul vDelta)
  let z := (state.transient.z.get idx).value.mul traceDecay
  let next : NumericState config dimension := {
    state with
    weights := state.weights.set idx.val weight idx.isLt
    beta := state.beta.set idx.val adapted idx.isLt
    alpha := state.alpha.set idx.val (beta.alphaAfter alpha adapted) idx.isLt
    evaluated := state.evaluated.set idx.val idx.isLt adapted (beta.alphaAfter alpha adapted)
      (beta.alphaAfter_eq alpha adapted (state.anchor_stepSize idx clipped))
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

/-- The executing first-loop element is the listed one: every word is the one
Algorithm 1 lists with `e^{β[i]}` the portable exponential of the log step size it
adapts, the re-anchor word when the weight projection binds and the stored one
otherwise, and the adapted log step size is stored beside its own exponential.
Reading the stored step size and keeping it for an unchanged word change nothing.
This holds for every state, index and raw argument word. -/
theorem firstLoopElement_eq (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta traceDecay : Binary32) :
    state.firstLoopElement idx delta vDelta traceDecay =
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
      (next.writeBetaValue idx (LogStepSize.project state.rails stepped),
        z.lessOrEqual ((state.transient.lastAlpha.get idx).value.mul config.epsilon)) := by
  simp only [firstLoopElement, anchor_stepSize, LogStepSize.alphaAfter_self, writeBetaValue,
    NumericState.writeStepSize]

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
The caller supplies the three words no visit changes for a later one: the
trace scale `scale = η/e`, the complement `oneSubT = 1 − t` of the trace
total, and this feature's step size `alpha = e^{β[i]}`. The decayed log step
size is stored beside its own portable exponential. Returns the updated state
and shared update accumulator. -/
def secondLoopElementAt (overshoot : Bool) (scale oneSubT alpha : Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) (idx : FeatIdx dimension) :
    NumericState config dimension × Binary32 :=
  let eligible := if (state.transient.z.get idx).value.isZero then
    state.transient.eligible.push idx else state.transient.eligible
  let vDelta := vDelta.add (state.transient.deltaWeight.get idx).value
  let zd := scale.mul alpha
  let z := (state.transient.z.get idx).value.add (zd.mul oneSubT)
  let p := (state.transient.p.get idx).value.add (state.transient.h.get idx).value
  let zBar := (state.transient.zBar.get idx).value.add
    (zd.mul (oneSubT.sub (state.transient.zBar.get idx).value))
  let hTemp := (((state.transient.hTemp.get idx).value.sub
    ((state.transient.hOld.get idx).value.mul (z.sub zd))).sub
      ((state.transient.h.get idx).value.mul zd))
  let h := if overshoot then state.transient.h.set idx.val ⟨.zero⟩ idx.isLt else state.transient.h
  let next : NumericState config dimension := {
    state with
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
  (match overshoot with
    | true => next.writeBetaValue idx
        (LogStepSize.project next.rails ((next.beta.get idx).value.add next.rails.decay))
    | false => next, vDelta)

/-- The second-loop element as Algorithm 1 lists it: the scale `η/e` and
complement `1 − t` come from its arguments, and its step size `e^{β[i]}` is the
portable exponential of the log step size in the state it receives. The learner
contracts are stated about this element. The executing traversal computes the
scale and complement once and reads each step size from storage, and
`learnSecondLoop_eq_sumFrom` proves it equal to the fold of this element. -/
def secondLoopElement (config : Config) (overshoot : Bool) (e t : Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) (idx : FeatIdx dimension) :
    NumericState config dimension × Binary32 :=
  secondLoopElementAt overshoot (config.eta.div e) (Binary32.one.sub t)
    (state.beta.get idx).alpha state vDelta idx

/-- A second-loop visit changes no other feature's step size: its only
step-size write is the overshoot decay at its own index. -/
theorem secondLoopElementAt_alpha (overshoot : Bool) (scale oneSubT alpha : Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) (idx other : FeatIdx dimension)
    (different : idx ≠ other) :
    ((secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx).1.beta.get other).alpha =
      (state.beta.get other).alpha := by
  have distinct : idx.val ≠ other.val := fun same => different (Fin.ext same)
  have read : ∀ {α : Type} (values : Vector α dimension.capacity),
      values.get other = values[other.val] := fun _ => rfl
  unfold LogStepSize.alpha
  congr 1
  cases overshoot
  · rfl
  · simp only [secondLoopElementAt, writeBetaValue, NumericState.writeStepSize, read,
      Vector.getElem_set, distinct, ite_false]

/-- The stored step sizes of a feature list are the portable exponentials of its
stored log step sizes, in order, for every state and list. -/
theorem stepSizes_eq (state : NumericState config dimension)
    (indices : List (FeatIdx dimension)) :
    indices.map state.stepSize = indices.map fun idx => (state.beta.get idx).alpha :=
  List.map_congr_left fun idx _ => state.stepSize_eq idx

/-- The second-loop traversal: the active features in first-occurrence order,
each visit receiving its step size from the list read at loop entry. The
two lists advance together and a visit needs an entry of each, so traversal
ends with the shorter; `learnSecondLoop` supplies one step size per index. -/
def learnSecondLoopGo (overshoot : Bool) (scale oneSubT : Binary32) :
    List (FeatIdx dimension) → List Binary32 → NumericState config dimension → Binary32 →
      NumericState config dimension × Binary32
  | idx :: indices, alpha :: alphas, state, vDelta =>
    let next := secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx
    learnSecondLoopGo overshoot scale oneSubT indices alphas next.1 next.2
  | _, _, state, vDelta => (state, vDelta)

/-- Step sizes read once at loop entry are the step sizes each visit would
read from the state it receives, so the traversal is the fold of the listed
element. Unique indices are the hypothesis: an earlier visit writes only its
own step size, and every later index differs from it. -/
theorem learnSecondLoopGo_eq_foldl (config : Config) (overshoot : Bool) (e t : Binary32)
    (indices : List (FeatIdx dimension)) (unique : indices.Nodup)
    (state : NumericState config dimension) (vDelta : Binary32) :
    learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) indices
        (indices.map fun idx => (state.beta.get idx).alpha) state vDelta =
      indices.foldl
        (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
        (state, vDelta) := by
  induction indices generalizing state vDelta with
  | nil => rfl
  | cons idx rest ih =>
    have fresh := (List.nodup_cons.mp unique).1
    have restUnique := (List.nodup_cons.mp unique).2
    let next := secondLoopElement config overshoot e t state vDelta idx
    have same : (rest.map fun other => (state.beta.get other).alpha) =
        rest.map fun other => (next.1.beta.get other).alpha := by
      apply List.map_congr_left
      intro other member
      exact (secondLoopElementAt_alpha overshoot _ _ _ state vDelta idx other
        (fun equal => fresh (equal ▸ member))).symm
    calc learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) (idx :: rest)
          ((idx :: rest).map fun other => (state.beta.get other).alpha) state vDelta
        = learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) rest
            (rest.map fun other => (state.beta.get other).alpha) next.1 next.2 := rfl
      _ = learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) rest
            (rest.map fun other => (next.1.beta.get other).alpha) next.1 next.2 := by rw [same]
      _ = rest.foldl
            (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
            (next.1, next.2) := ih restUnique next.1 next.2
      _ = (idx :: rest).foldl
            (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
            (state, vDelta) := rfl

/-- The second loop of the update: the active features in first-occurrence
order. `τ = Σ_{i∈F} e^{β[i]}` (eq. (7), p. 845), one overshoot binding for
both the trace scale and the step-size decay, and the shared `vDelta`
accumulator returned to the caller. Each step size `e^{β[i]}` is read once
from storage, for both `τ` and its feature's trace increment. -/
def learnSecondLoop (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    NumericState config dimension × Binary32 :=
  let alphas := features.indices.map state.stepSize
  let rate := Binary32.sumFrom .zero alphas
  let overshoot := config.eta.less rate
  let e := if overshoot then rate else config.eta
  let t := Binary32.sumMap .zero features.indices (fun idx => (state.transient.z.get idx).value)
  learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) features.indices alphas
    state vDelta

/-- The executing second loop is the listed one: both pre-update sums keep
the complete ordered active loop, and every visit's step size, scale and
trace complement are the words the listed element computes for itself. This
holds for every receiving state, feature list and accumulator word. -/
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
  simp only [learnSecondLoop, Binary32.sumMap_eq, stepSizes_eq]
  exact learnSecondLoopGo_eq_foldl config _ _ _ features.indices features.nodup state vDelta

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

/-- The planning weight traversal: the active features in first-occurrence
order, each visit receiving its step size from the list read at entry.
The two lists advance together and a visit needs an entry of each, so
traversal ends with the shorter; `planStep` supplies one step size per index. -/
def planWeightsGo (scale delta : Binary32) :
    List (FeatIdx dimension) → List Binary32 → NumericState config dimension →
      NumericState config dimension
  | idx :: indices, alpha :: alphas, state =>
    planWeightsGo scale delta indices alphas
      (state.writeWeight idx ((state.weights.get idx).value.add ((scale.mul alpha).mul delta)))
  | _, _, state => state

/-- Step sizes read once at entry are the step sizes each planning visit
would read from the state it receives: a visit writes one weight and no step
size. No uniqueness hypothesis is needed. -/
theorem planWeightsGo_eq_foldl (scale delta : Binary32) (indices : List (FeatIdx dimension))
    (state : NumericState config dimension) :
    planWeightsGo scale delta indices (indices.map fun idx => (state.beta.get idx).alpha) state =
      indices.foldl (fun state idx =>
        let stepSize := (scale.mul (state.beta.get idx).alpha).mul delta
        state.writeWeight idx ((state.weights.get idx).value.add stepSize)) state := by
  induction indices generalizing state with
  | nil => rfl
  | cons idx rest ih =>
    exact ih (state.writeWeight idx
      ((state.weights.get idx).value.add ((scale.mul (state.beta.get idx).alpha).mul delta)))

/-- A single background planning update toward `target` at `features` without
modifying eligibility traces or meta-gradient registers (PAR-14; Dyna 1991,
STOMP eq. (19)): `w[i] ← project (w[i] + (η/E)·α[i]·δ)`. A nonfinite or zero
error is no update. Each step size `α[i]` is read once from storage, for both
`E` and its feature's weight write. -/
def planStep (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    NumericState config dimension × Binary32 :=
  let v := state.predict features
  let delta := target.sub v
  if !decide delta.Finite || delta.numericallyEqual .zero then (state, .zero)
  else
    let alphas := features.indices.map state.stepSize
    let rate := Binary32.sumFrom .zero alphas
    let e := if config.eta.less rate then rate else config.eta
    (planWeightsGo (config.eta.div e) delta features.indices alphas state, delta)

/-- The executing planning update is the fold whose every visit reads its own
step size from the state it receives, for every state, feature list and
target word. -/
theorem planStep_eq_foldl (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    state.planStep config features target =
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
        (state, delta) := by
  simp only [planStep, stepSizes_eq, planWeightsGo_eq_foldl]

/-- Replace one feature's knowledge and transients with a fresh unit's start
state: the first eligible occurrence removed (the whole membership under
uniqueness), every per-index register zero, weight zeroed and step size
re-anchored. Only the retired slot's own state changes: the shared previous
prediction and weight-change aggregate are kept, as generate-and-test resets
only the replaced unit (Dohare et al., arXiv:2306.13812v3, Algorithm 1, p. 23),
so the next TD error differs from the unreplaced one only through the retired
slot's weight. -/
def retireIndex (state : NumericState config dimension) (idx : FeatIdx dimension) :
    NumericState config dimension :=
  let state := match found : state.transient.eligible.findIdx? (· == idx) with
    | some pos =>
      state.removeEligibleAt pos (Array.findIdx?_eq_some_iff_getElem.mp found).1
    | none => state
  let state := state.clearFeatureRegisters idx
  let state := state.writeWeight idx .zero
  state.writeBetaValue idx state.rails.initial

/-- Overwrite the learned weights from an untrusted source, projecting each
value through the immutable criterion. The traversal consumes only the zipped
prefix; untouched suffixes keep their prior legal words. -/
def restoreWeights (state : NumericState config dimension) (raw : List Binary32) :
    NumericState config dimension :=
  { state with weights := SwiftTd.restorePrefix (Weight.project config.rule) state.weights raw }

/-- Overwrite the learned log step sizes from an untrusted source, saturating
each through this learner's own rails; the same zipped-prefix traversal. Every
step size is then evaluated from the restored log step sizes, so no stored step
size crosses the restore boundary. -/
def restoreLogStepSizes (state : NumericState config dimension) (raw : List Binary32) :
    NumericState config dimension :=
  let beta := SwiftTd.restorePrefix (LogStepSize.project state.rails) state.beta raw
  { state with
    beta := beta
    alpha := beta.map fun stored => stored.alpha
    evaluated := LogStepSize.Evaluated.map beta }

/-- Exclusive restoration without learner or configuration replacement: both
knowledge arrays through their own refinements, then process-local registers
cleared, in that order. -/
def installRestored (state : NumericState config dimension) (weights logStepSizes : List Binary32) :
    NumericState config dimension :=
  (state.restoreWeights weights |>.restoreLogStepSizes logStepSizes).clearTransient

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
  /-- Release every eligible trace, in work proportional to their number. -/
  | release

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
  | .release => state.releaseEligible

/-- Phase after an entry: true permits a following standalone second loop.
This phase governs composed resource safety, not the standalone input domain. -/
def nextReady (entry : Entry dimension) (before : Bool) : Bool :=
  match entry with
  | .first .. | .terminal .. | .install .. | .clear | .release => true
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

end SwiftTd

end Acorn
