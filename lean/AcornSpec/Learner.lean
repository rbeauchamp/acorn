/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Float
import AcornSpec.FeatureSpace

/-!
# Executable specification: SwiftTD

This model defines a closed discount set, total weight and log-step-size
projections, and the two SwiftTD update loops. Declared adaptations include
projection re-anchoring, total beta saturation and pruning that also clears
meta-gradient registers. Every modeled knowledge write uses its projection.

Learner arrays hold binary32 storage words (`Array UInt32`). Reads and writes
reinterpret these words with `ofBits` and `toBits`. Log-step-size admission
recomputes logarithmic bounds per call, and each step-size read computes the
local exponential. Current execution and its proof-bearing state live in
`Acorn.SwiftTd`; correspondence to this separate specification is not automatic.
-/

namespace AcornSpec

open AcornSpec.Constants

/-- `swifttd::Discount` — the closed discount set. -/
inductive Discount where
  /-- γ = 0.90. -/
  | g90
  /-- γ = 0.95. -/
  | g95
  /-- γ = 0.99. -/
  | g99
  deriving DecidableEq, Repr

/-- `Discount::gamma`. -/
@[inline]
def Discount.gamma : Discount → Float32
  | .g90 => Float32.ofBits gamma90Bits
  | .g95 => Float32.ofBits gamma95Bits
  | .g99 => Float32.ofBits gamma99Bits

/-- Discount horizon: `1.0 / (1.0 - gamma)` in binary32. -/
@[inline]
def Discount.horizon (d : Discount) : Float32 :=
  natF32 1 / (natF32 1 - d.gamma)

/-- `swifttd::project` — total projection into `[-bound, bound]`. -/
@[inline]
def project (v bound : Float32) : Float32 :=
  if v.isNaN then f32zero
  else if bound < v then bound
  else if v < Float32.neg bound then Float32.neg bound
  else v

/-- `swifttd::saturate` — total saturation into `[lo, hi]`. -/
@[inline]
def saturate (v lo hi : Float32) : Float32 :=
  if v.isNaN || v < lo then lo
  else if hi < v then hi
  else v

/-- `swifttd::project_nonneg` — total projection into `[0, bound]`. -/
@[inline]
def projectNonneg (v bound : Float32) : Float32 :=
  if v.isNaN || v < f32zero then f32zero
  else if bound < v then bound
  else v

/-- `swifttd::SwiftTdConfig` — hyperparameters as `f32` bit patterns plus the
closed discount. -/
structure SwiftCfg where
  /-- Trace-decay parameter λ (bits). -/
  lambda : UInt32
  /-- The discount. -/
  discount : Discount
  /-- Initial step size α₀ (bits). -/
  alphaInit : UInt32
  /-- Trace-pruning threshold ε (bits). -/
  epsilon : UInt32
  /-- Overshoot budget η (bits). -/
  eta : UInt32
  /-- Minimum step size (bits). -/
  etaMin : UInt32
  /-- Overshoot-triggered decay (bits). -/
  decay : UInt32
  /-- Meta step size θ (bits). -/
  metaStepSize : UInt32
  deriving Repr

namespace SwiftCfg

/-- `SwiftTdConfig::demon`. -/
def demon (d : Discount) : SwiftCfg :=
  { lambda := lambda095Bits, discount := d, alphaInit := alphaInit5e5Bits
    epsilon := epsilon1e5Bits, eta := eta01Bits, etaMin := etaMin1e10Bits
    decay := decay0999Bits, metaStepSize := meta1e3Bits }

/-- `SwiftTdConfig::control`. -/
def control (d : Discount) : SwiftCfg :=
  { lambda := lambda09Bits, discount := d, alphaInit := alphaInit5e5Bits
    epsilon := epsilon1e5Bits, eta := eta01Bits, etaMin := etaMin1e10Bits
    decay := decay0999Bits, metaStepSize := meta1e3Bits }

/-- `SwiftTdConfig::option_skill`. -/
def optionSkill (d : Discount) : SwiftCfg :=
  { lambda := lambda09Bits, discount := d, alphaInit := alphaInit1e4Bits
    epsilon := epsilon1e5Bits, eta := eta025Bits, etaMin := etaMin1e10Bits
    decay := decay0999Bits, metaStepSize := meta3e2Bits }

/-- γ as `f32`. -/
@[inline]
def gamma (c : SwiftCfg) : Float32 := c.discount.gamma

/-- The value bound `1/(1−γ)`. -/
@[inline]
def horizon (c : SwiftCfg) : Float32 := c.discount.horizon

/-- `LogStepSize::set` — saturate β into `[ln η_min, ln η]`, recomputing both
bounds per call. -/
@[inline]
def logStepSet (c : SwiftCfg) (beta : Float32) : Float32 :=
  let lo := ln32 (Float32.ofBits c.etaMin)
  let hi := ln32 (Float32.ofBits c.eta)
  saturate beta lo hi

/-- `LogStepSize::initial` — `set (ln α₀)`. -/
@[inline]
def logStepInitial (c : SwiftCfg) : Float32 :=
  c.logStepSet (ln32 (Float32.ofBits c.alphaInit))

/-- `Weight::set` — project through the discount's horizon. -/
@[inline]
def weightSet (c : SwiftCfg) (v : Float32) : Float32 :=
  project v c.horizon

/-- `SwiftTdConfig::disruption_bound` — `θ = ε · 1/(1−γ)`. -/
@[inline]
def disruptionBound (c : SwiftCfg) : Float32 :=
  Float32.ofBits c.epsilon * c.horizon

/-- `LogStepSize::at_floor` — β equals `ln η_min`, the word `logStepSet`
saturates to. -/
@[inline]
def atFloor (c : SwiftCfg) (beta : Float32) : Bool :=
  beta == ln32 (Float32.ofBits c.etaMin)

end SwiftCfg

/-- `swifttd::SwiftTd` — one learner. Arrays hold `f32` bits. -/
structure SwiftTd where
  /-- Hyperparameters. -/
  cfg : SwiftCfg
  /-- Weights (projected through the horizon on every write). -/
  w : Array UInt32
  /-- Log step sizes β (saturated on every write). -/
  beta : Array UInt32
  /-- Eligibility trace z. -/
  z : Array UInt32
  /-- Trace increment zδ. -/
  zDelta : Array UInt32
  /-- Per-weight update δw. -/
  deltaW : Array UInt32
  /-- Dutch-trace auxiliary h. -/
  h : Array UInt32
  /-- Previous h. -/
  hOld : Array UInt32
  /-- Accumulating h. -/
  hTemp : Array UInt32
  /-- Dutch trace z̄. -/
  zBar : Array UInt32
  /-- Meta-trace p. -/
  p : Array UInt32
  /-- Last trace increment (pruning reference). -/
  lastAlpha : Array UInt32
  /-- Active trace indices. -/
  eligible : Array UInt32
  /-- Accumulator of δw·φ over the previous step's active features (bits). -/
  vDelta : UInt32
  /-- Previous prediction (bits). -/
  vOld : UInt32

/-- The take-out placeholder default; never observed by any computation. -/
instance : Inhabited SwiftTd :=
  ⟨{ cfg := SwiftCfg.control .g99
     w := #[], beta := #[], z := #[], zDelta := #[], deltaW := #[]
     h := #[], hOld := #[], hTemp := #[], zBar := #[], p := #[], lastAlpha := #[]
     eligible := #[], vDelta := 0, vOld := 0 }⟩

namespace SwiftTd

/-- Read an `f32` slot. -/
@[inline]
def fget (a : Array UInt32) (i : Nat) : Float32 := Float32.ofBits a[i]!

/-- Write an `f32` slot. -/
@[inline]
def fset (a : Array UInt32) (i : Nat) (v : Float32) : Array UInt32 := a.set! i v.toBits

/-- `SwiftTd::new` — all-zero state, uniform initial log step sizes. -/
def new (cfg : SwiftCfg) : SwiftTd :=
  let zeros := Array.replicate weightSpace (0 : UInt32)
  { cfg
    w := zeros, beta := Array.replicate weightSpace (cfg.logStepInitial).toBits
    z := zeros, zDelta := zeros, deltaW := zeros
    h := zeros, hOld := zeros, hTemp := zeros
    zBar := zeros, p := zeros, lastAlpha := zeros
    eligible := #[]
    vDelta := 0, vOld := 0 }

/-- `SwiftTd::normalized_step_size_sum` — Σ ν(β) over the eligible set, with
the term count. `ν(β) = (β − ln η_min) / (ln η − ln η_min)`, endpoints from
this learner's own `cfg`. -/
def normalizedStepSizeSum (td : SwiftTd) : Float32 × Nat :=
  if td.eligible.isEmpty then (f32zero, 0)
  else
    let lo := ln32 (Float32.ofBits td.cfg.etaMin)
    let hi := ln32 (Float32.ofBits td.cfg.eta)
    let span := hi - lo
    let beta := td.beta
    let sum := td.eligible.foldl
      (fun s i => s + (fget beta i.toNat - lo) / span) f32zero
    (sum, td.eligible.size)

/-- `SwiftTd::initial_normalized_step_size` — ν(ln α_init). -/
def initialNormalizedStepSize (td : SwiftTd) : Float32 :=
  let lo := ln32 (Float32.ofBits td.cfg.etaMin)
  let hi := ln32 (Float32.ofBits td.cfg.eta)
  (ln32 (Float32.ofBits td.cfg.alphaInit) - lo) / (hi - lo)

/-- `SwiftTd::predict` — `Σ w[i]` over the active set, in feature order. -/
def predict (td : SwiftTd) (features : Array UInt32) : Float32 :=
  let w := td.w
  features.foldl (fun v i => v + fget w i.toNat) f32zero

/-- Absolute value that treats NaN as not-less-than-zero, matching
`f32::abs` on the comparison `abs(w) < θ` (NaN is not `< θ`). -/
@[inline]
def abs32 (x : Float32) : Float32 :=
  if x < f32zero then Float32.neg x else x

/-- `SwiftTd::unit_is_negligible`. -/
def unitIsNegligible (td : SwiftTd) (idx : Nat) : Bool :=
  abs32 (fget td.w idx) < td.cfg.disruptionBound && td.cfg.atFloor (fget td.beta idx)

/-- `SwiftTd::retire_index` — zero every register, drop from eligible,
install `w = 0` and `β = ln α_init`, and clear the representation-dependent
aggregates `v_old`/`v_delta` that fold the retired feature's contribution. -/
def retireIndex (td : SwiftTd) (idx : Nat) : SwiftTd :=
  let eligible :=
    match td.eligible.findIdx? (fun f => f.toNat == idx) with
    | none => td.eligible
    | some pos =>
      let last := td.eligible.size - 1
      (td.eligible.set! pos (td.eligible.getD last 0)).pop
  { td with
    eligible
    z := fset td.z idx f32zero
    p := fset td.p idx f32zero
    zBar := fset td.zBar idx f32zero
    deltaW := fset td.deltaW idx f32zero
    zDelta := fset td.zDelta idx f32zero
    h := fset td.h idx f32zero
    hOld := fset td.hOld idx f32zero
    hTemp := fset td.hTemp idx f32zero
    lastAlpha := fset td.lastAlpha idx f32zero
    w := fset td.w idx f32zero
    beta := fset td.beta idx td.cfg.logStepInitial
    vOld := 0
    vDelta := 0 }

/-- One iteration body plus loop of `SwiftTd::learn_first_loop`, destructured
for in-place array updates. `fuel` is `eligible.size - pos`, which strictly
decreases: an iteration either advances `pos` or shrinks the array. -/
private def firstLoopGo (delta vDeltaArg traceDecay : Float32)
    (metaStep epsilonF horizon lo hi betaInit : Float32)
    (w beta z zDelta deltaW h hOld hTemp zBar p lastAlpha : Array UInt32)
    (eligible : Array UInt32) (pos : Nat) : Nat →
    (Array UInt32 × Array UInt32 × Array UInt32 × Array UInt32 × Array UInt32 ×
     Array UInt32 × Array UInt32 × Array UInt32 × Array UInt32 × Array UInt32 ×
     Array UInt32 × Array UInt32)
  | 0 => (w, beta, z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha, eligible)
  | fuel + 1 =>
    if pos < eligible.size then
      let idx := eligible[pos]!.toNat
      let dwv := delta * fget z idx - fget zDelta idx * vDeltaArg
      let deltaW := fset deltaW idx dwv
      let raw := fget w idx + dwv
      let projected := project raw horizon
      let w := fset w idx projected
      let clipped := !(projected == raw)
      let (beta, zBar, p, h, hTemp, hOld, deltaW) :=
        if clipped then
          (fset beta idx betaInit, fset zBar idx f32zero, fset p idx f32zero,
           fset h idx f32zero, fset hTemp idx f32zero, fset hOld idx f32zero,
           fset deltaW idx f32zero)
        else (beta, zBar, p, h, hTemp, hOld, deltaW)
      let e := exp32 (fget beta idx)
      let stepped := fget beta idx +
        metaStep / e * (delta - vDeltaArg) * fget p idx
      let beta := fset beta idx (saturate stepped lo hi)
      let hOld := fset hOld idx (fget h idx)
      let h := fset h idx (fget hTemp idx)
      let hTemp := fset hTemp idx
        (fget h idx + delta * fget zBar idx - fget zDelta idx * vDeltaArg)
      let zDelta := fset zDelta idx f32zero
      let z := fset z idx (fget z idx * traceDecay)
      let p := fset p idx (fget p idx * traceDecay)
      let zBar := fset zBar idx (fget zBar idx * traceDecay)
      if fget z idx ≤ fget lastAlpha idx * epsilonF then
        -- `drop_from_eligible`: zero every register, swap-remove at `pos`.
        let z := fset z idx f32zero
        let p := fset p idx f32zero
        let zBar := fset zBar idx f32zero
        let deltaW := fset deltaW idx f32zero
        let zDelta := fset zDelta idx f32zero
        let h := fset h idx f32zero
        let hOld := fset hOld idx f32zero
        let hTemp := fset hTemp idx f32zero
        let lastAlpha := fset lastAlpha idx f32zero
        let last := eligible.size - 1
        let eligible := (eligible.set! pos eligible[last]!).pop
        firstLoopGo delta vDeltaArg traceDecay metaStep epsilonF horizon lo hi betaInit
          w beta z zDelta deltaW h hOld hTemp zBar p lastAlpha eligible pos fuel
      else
        firstLoopGo delta vDeltaArg traceDecay metaStep epsilonF horizon lo hi betaInit
          w beta z zDelta deltaW h hOld hTemp zBar p lastAlpha eligible (pos + 1) fuel
    else (w, beta, z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha, eligible)

/-- `SwiftTd::learn_first_loop`. The per-element pure constants — the meta
step size, pruning ε, projection horizon, β saturation bounds and the
re-anchor value — are computed once per invocation as pure functions of the
fixed configuration. -/
def learnFirstLoop (td : SwiftTd) (delta vDeltaArg traceDecay : Float32) : SwiftTd :=
  let ⟨cfg, w, beta, z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha,
       eligible, vD, vO⟩ := td
  let metaStep := Float32.ofBits cfg.metaStepSize
  let epsilonF := Float32.ofBits cfg.epsilon
  let horizon := cfg.horizon
  let lo := ln32 (Float32.ofBits cfg.etaMin)
  let hi := ln32 (Float32.ofBits cfg.eta)
  let betaInit := saturate (ln32 (Float32.ofBits cfg.alphaInit)) lo hi
  let fuel := eligible.size
  let (w, beta, z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha, eligible) :=
    firstLoopGo delta vDeltaArg traceDecay metaStep epsilonF horizon lo hi betaInit
      w beta z zDelta deltaW h hOld hTemp zBar p lastAlpha eligible 0 fuel
  ⟨cfg, w, beta, z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha,
   eligible, vD, vO⟩

/-- Loop body of `learn_second_loop`, tail-recursive over the feature list
with flat arguments (no per-feature tuple allocation). -/
private def secondLoopGo (features : Array UInt32)
    (overshoot : Bool) (e t one lnDecay etaF lo hi : Float32)
    (z zDelta deltaW h hOld hTemp zBar p lastAlpha beta : Array UInt32)
    (eligible : Array UInt32) (acc : Float32) (k : Nat) : Nat →
    (Array UInt32 × Array UInt32 × Array UInt32 × Array UInt32 × Array UInt32 ×
     Array UInt32 × Array UInt32 × Array UInt32 × Array UInt32 × Array UInt32 ×
     Array UInt32 × Float32)
  | 0 => (z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha, beta, eligible, acc)
  | fuel + 1 =>
    if k < features.size then
      let i := features[k]!
      let idx := i.toNat
      let eligible := if SwiftTd.fget z idx == f32zero then eligible.push i else eligible
      let acc := acc + SwiftTd.fget deltaW idx
      let zd := etaF / e * exp32 (SwiftTd.fget beta idx)
      let zDelta := SwiftTd.fset zDelta idx zd
      let lastAlpha := SwiftTd.fset lastAlpha idx zd
      let z := SwiftTd.fset z idx (SwiftTd.fget z idx + zd * (one - t))
      let p := SwiftTd.fset p idx (SwiftTd.fget p idx + SwiftTd.fget h idx)
      let zBar := SwiftTd.fset zBar idx
        (SwiftTd.fget zBar idx + zd * (one - t - SwiftTd.fget zBar idx))
      let hTemp := SwiftTd.fset hTemp idx
        (SwiftTd.fget hTemp idx - SwiftTd.fget hOld idx * (SwiftTd.fget z idx - zd) -
          SwiftTd.fget h idx * zd)
      if overshoot then
        let beta := SwiftTd.fset beta idx (saturate (SwiftTd.fget beta idx + lnDecay) lo hi)
        let hTemp := SwiftTd.fset hTemp idx f32zero
        let h := SwiftTd.fset h idx f32zero
        let zBar := SwiftTd.fset zBar idx f32zero
        secondLoopGo features overshoot e t one lnDecay etaF lo hi z zDelta deltaW h hOld
          hTemp zBar p lastAlpha beta eligible acc (k + 1) fuel
      else
        secondLoopGo features overshoot e t one lnDecay etaF lo hi z zDelta deltaW h hOld
          hTemp zBar p lastAlpha beta eligible acc (k + 1) fuel
    else (z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha, beta, eligible, acc)

/-- `SwiftTd::learn_second_loop`. Returns the learner and the accumulated
`v_delta` (the caller's `&mut` accumulator). -/
def learnSecondLoop (td : SwiftTd) (features : Array UInt32) (vDeltaAcc : Float32) :
    SwiftTd × Float32 :=
  let ⟨cfg, w, beta, z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha,
       eligible, vD, vO⟩ := td
  let eta := Float32.ofBits cfg.eta
  let rate := features.foldl (fun r i => r + exp32 (fget beta i.toNat)) f32zero
  let overshoot := eta < rate
  let e := if overshoot then rate else eta
  let t := features.foldl (fun t i => t + fget z i.toNat) f32zero
  let one := natF32 1
  let lnDecay := ln32 (Float32.ofBits cfg.decay)
  let lo := ln32 (Float32.ofBits cfg.etaMin)
  let hi := ln32 (Float32.ofBits cfg.eta)
  let fuel := features.size
  let (z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha, beta, eligible, acc) :=
    secondLoopGo features overshoot e t one lnDecay eta lo hi z zDelta deltaW h hOld hTemp
      zBar p lastAlpha beta eligible vDeltaAcc 0 fuel
  (⟨cfg, w, beta, z, zDelta, deltaW, h, hOld, hTemp, zBar, p, lastAlpha,
    eligible, vD, vO⟩, acc)

/-- `SwiftTd::step` — one full single-learner update (the demons' path).
Returns the learner, the prediction `v` and the TD error. Field reads are
hoisted before the consuming calls so the learner stays uniquely referenced
(in-place array updates). -/
def step (td : SwiftTd) (features : Array UInt32) (reward : Float32) :
    SwiftTd × Float32 × Float32 :=
  let v := td.predict features
  let gamma := td.cfg.gamma
  let lambda := Float32.ofBits td.cfg.lambda
  let vOld := Float32.ofBits td.vOld
  let vDelta := Float32.ofBits td.vDelta
  let delta := reward + gamma * v - vOld
  let td := td.learnFirstLoop delta vDelta (gamma * lambda)
  let (td, vd) := td.learnSecondLoop features f32zero
  ({ td with vDelta := vd.toBits, vOld := v.toBits }, v, delta)

/-- `SwiftTd::clear_transient` — drop every trace and adaptation scratch,
keeping `w` and `beta`. -/
def clearTransient (td : SwiftTd) : SwiftTd :=
  let zeros := Array.replicate weightSpace (0 : UInt32)
  { td with
    z := zeros, zBar := zeros, zDelta := zeros, deltaW := zeros
    p := zeros, h := zeros, hTemp := zeros, hOld := zeros, lastAlpha := zeros
    eligible := #[], vDelta := 0, vOld := 0 }

/-- `SwiftTd::begin` (PAR-13) — clear transient, anchor prediction, and lay initial traces. -/
def begin (td : SwiftTd) (features : Array UInt32) : SwiftTd :=
  let td := td.clearTransient
  let v := td.predict features
  let (td, vd) := td.learnSecondLoop features f32zero
  { td with vOld := v.toBits, vDelta := vd.toBits }

/-- `SwiftTd::terminal_step` (PAR-13 / G31) — terminal update on existing traces,
then clear transient. -/
def terminalStep (td : SwiftTd) (target : Float32) : SwiftTd × Float32 :=
  let vOld := Float32.ofBits td.vOld
  let vDelta := Float32.ofBits td.vDelta
  let gamma := td.cfg.gamma
  let lambda := Float32.ofBits td.cfg.lambda
  let delta := target - vOld
  let td := td.learnFirstLoop delta vDelta (gamma * lambda)
  (td.clearTransient, delta)

/-- `SwiftTd::plan_step` (PAR-14) — single background planning update toward `target` at `features`
without modifying eligibility traces or meta-gradient registers. -/
def planStep (td : SwiftTd) (features : Array UInt32) (target : Float32) : SwiftTd × Float32 :=
  let v := td.predict features
  let delta := target - v
  if !isFinite32 delta || delta == f32zero then (td, f32zero)
  else
    let beta := td.beta
    let rate := features.foldl (fun r i => r + exp32 (fget beta i.toNat)) f32zero
    let etaF := Float32.ofBits td.cfg.eta
    let e := if etaF < rate then rate else etaF
    let scale := etaF / e
    let horizon := td.cfg.discount.horizon
    let w := features.foldl (fun w i =>
      let idx := i.toNat
      let step := scale * exp32 (fget beta idx) * delta
      let raw := fget w idx + step
      fset w idx (project raw horizon)) td.w
    ({ td with w }, delta)

end SwiftTd

end AcornSpec
