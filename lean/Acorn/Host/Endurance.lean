/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Observation
import Acorn.Host.Task
import Std.Data.TreeMap.Lemmas

/-! # Pure endurance observation reduction

This calculator folds admitted frames, including attempt-terminal captures when
supplied. It does not capture telemetry, read clocks/RSS, publish files or execute
an agent. The Rust observer remains the transition integration owner. Missing
historical telemetry cannot be recovered by running this calculator.

Counts and histogram ranks use unbounded naturals. Return/error accumulation is
ordered binary64 arithmetic, with the standard native float implementation as a
trusted boundary. The tail theorem concerns the corresponding real discounted
sum, not floating-point exactness or one-frame-per-transition correspondence.
-/
namespace Acorn.Host.Endurance

/-- Closed discount horizons, in frames; their rational tail bounds are proved in
`AcornVerif.Endurance`. No per-observer floating termination loop is required. -/
def horizon : Discount → Nat
  | .g90 => 200
  | .g95 => 400
  | .g99 => 2000

/-- Fixed maximum retained history is derived from the largest closed horizon. -/
def historyCapacity : Nat := horizon .g99

/-- Raw diagnostic values preserve nonfinite fields for explicit null accounting. -/
structure Frame where
  /-- Physical world counter supplied by capture. -/
  time : UInt64
  /-- Admitted world energy. -/
  energy : Energy
  /-- Exact world coordinate identity. -/
  position : Int × Int
  /-- The captured exhausted event. -/
  exhausted : Bool
  /-- The captured eating event. -/
  ate : Bool
  /-- Reward on this frame. -/
  reward : Float32
  /-- Aggregate optimizer rate used only for null accounting. -/
  meanAlpha : Float32
  /-- Active control rate. -/
  activeAlpha : Float32
  /-- Aggregate demon rate used only for null accounting. -/
  demonAlpha : Float32
  /-- Individual active demon rates. -/
  demonAlphas : List Float32
  /-- Exploration rate used only for null accounting. -/
  epsilon : Float32
  /-- Predictions; absent channels are zero, surplus channels are ignored by returns. -/
  predictions : List Float32
  /-- Cumulants in the same declared channel order. -/
  cumulants : List Float32

/-- Shared rate summary for either control or demon observations. -/
structure Rates where
  /-- Finite observations only. -/
  count : Nat := 0
  /-- Ordered binary64 sum. -/
  sum : Float := 0
  /-- Count at the upper rail. -/
  upper : Nat := 0
  /-- Count at the lower rail, mutually exclusive with upper. -/
  lower : Nat := 0

/-- The rail source is the same closed role configuration as the learner. -/
def Rates.note (r : Rates) (role : Role) (alpha : Float32) : Rates :=
  if alpha.isNaN || alpha.isInf then r else
  let config : Config := ⟨role, .discounted .g99⟩
  let a := alpha.toFloat
  let upper := (Float32.ofBits config.eta.bits).toFloat * 0.999
  let lower := (Float32.ofBits config.etaMin.bits).toFloat * 1.001
  { count := r.count + 1, sum := r.sum + a,
    upper := r.upper + if a ≥ upper then 1 else 0,
    lower := r.lower + if a < upper && a ≤ lower then 1 else 0 }

/-- One channel's sampled return/error totals. -/
structure ErrorStats where
  /-- Finite prediction samples. -/
  count : Nat := 0
  /-- Sum of absolute rounded errors. -/
  error : Float := 0
  /-- Sum of absolute rounded returns. -/
  returns : Float := 0
  /-- Sum of absolute predictions. -/
  predictions : Float := 0

/-- Statistics attached to a caller-selected wall-clock window. -/
structure Window where
  /-- Every supplied frame counts once. -/
  frames : Nat := 0
  /-- Total energy. -/
  energy : Nat := 0
  /-- Exhausted frames. -/
  exhausted : Nat := 0
  /-- Eating frames. -/
  eats : Nat := 0
  /-- Sum of finite rewards. -/
  reward : Float := 0
  /-- Coordinates first visited in this window. -/
  newTiles : Nat := 0
  /-- Control rate statistics. -/
  control : Rates := {}
  /-- Demon rate statistics. -/
  demons : Rates := {}
  /-- Aggregate error count. -/
  errorCount : Nat := 0
  /-- Aggregate error sum in sample/channel order. -/
  errorSum : Float := 0
  /-- Per-channel decomposition in the declared order. -/
  errors : Vector ErrorStats FeatureConstants.demonCount := Vector.replicate _ {}

/-- Only the two channel arrays are retained in the bounded return history. -/
structure Channels where
  /-- Raw predictions at the beginning of a sampled frame interval. -/
  predictions : Vector Float32 FeatureConstants.demonCount
  /-- Cumulants observed in that interval. -/
  cumulants : Vector Float32 FeatureConstants.demonCount

/-- Prefix projection exactly preserves the original zero-padding/truncation rule. -/
def Frame.channels (f : Frame) : Channels :=
  ⟨Vector.ofFn (fun i => f.predictions[i.val]?.getD 0),
    Vector.ofFn (fun i => f.cumulants[i.val]?.getD 0)⟩

/-- Fixed storage makes history growth beyond its horizon unrepresentable. -/
structure History where
  /-- Slots are addressed only with a finite index. -/
  slots : Vector Channels historyCapacity
  /-- Next slot to overwrite; after a full buffer, this is the oldest frame. -/
  next : Fin historyCapacity
  /-- Number of retained frames saturates at capacity. -/
  count : Fin (historyCapacity + 1)

/-- Empty history with all unused slots initialized. -/
def History.empty : History :=
  ⟨Vector.replicate _ ⟨Vector.replicate _ 0, Vector.replicate _ 0⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- Push one frame, replacing only the next slot and saturating the count. -/
def History.push (h : History) (frame : Channels) : History :=
  ⟨h.slots.set h.next frame,
    ⟨(h.next.val + 1) % historyCapacity, Nat.mod_lt _ (by decide)⟩,
    ⟨min (h.count.val + 1) historyCapacity, by have := Nat.min_le_right (h.count.val + 1) historyCapacity; omega⟩⟩

/-- Access a full history in chronological order, starting at the oldest slot. -/
def History.at (h : History) (offset : Nat) : Channels :=
  h.slots.get ⟨(h.next.val + offset) % historyCapacity, Nat.mod_lt _ (by decide)⟩

/-- Binary64 left fold of one finite frame interval; nonfinite cumulants are skipped. -/
def realizedReturn (h : History) (i : Fin FeatureConstants.demonCount) : Float := Id.run do
  let discount := Handcrafted.demonDiscount i
  let gamma := (Float32.ofBits discount.gamma.bits).toFloat
  let mut total : Float := 0
  let mut power : Float := 1
  for k in [:horizon discount] do
    let c := (h.at k).cumulants.get i
    unless c.isNaN || c.isInf do total := total + power * c.toFloat
    power := power * gamma
  return total

/-- Add each finite oldest prediction's rounded realized error exactly once. -/
def Window.sample (w : Window) (h : History) : Window := Id.run do
  let mut out := w
  for i in List.finRange FeatureConstants.demonCount do
    let prediction := (h.at 0).predictions.get i
    unless prediction.isNaN || prediction.isInf do
      let returned := realizedReturn h i
      let error := (prediction.toFloat - returned).abs
      let prior := out.errors.get i
      out := { out with
        errorCount := out.errorCount + 1, errorSum := out.errorSum + error,
        errors := out.errors.set i ⟨prior.count + 1, prior.error + error,
          prior.returns + returned.abs, prior.predictions + prediction.toFloat.abs⟩ }
  return out

/-- Reduced scientific values, independent of rendering and publication. -/
structure Reduction where
  private mk ::
  /-- A zero sampling period cannot be supplied. -/
  sampleEvery : {n : Nat // 0 < n}
  /-- All admitted frames, including terminal captures. -/
  frames : Nat := 0
  /-- Physical counter on the first frame. -/
  first : Option UInt64 := none
  /-- Physical counter on the last frame. -/
  last : Option UInt64 := none
  /-- Nonfinite scalar fields plus one marker for any nonfinite prediction/cumulant. -/
  nulls : Nat := 0
  /-- Exact bounded-energy histogram. -/
  energy : Vector Nat (FeatureConstants.energyMax + 1) := Vector.replicate _ 0
  /-- Distinct observed coordinates in the standard ordered map. -/
  visited : Std.TreeMap (Int × Int) Unit (@compare (Int × Int) lexOrd) := {}
  /-- Fixed return history. -/
  history : History := History.empty
  /-- Current reporting window. -/
  current : Window := {}
  /-- Closed windows in order. -/
  windows : Array Window := #[]

/-- Start an empty reduction with a positive sampling period. -/
def Reduction.start (sampleEvery : {n : Nat // 0 < n}) : Reduction := { sampleEvery := sampleEvery }

/-- Fold one frame before the caller closes a window or records attempt metadata. -/
def Reduction.ingest (r : Reduction) (f : Frame) : Reduction := Id.run do
  let finite := fun (x : Float32) => !x.isNaN && !x.isInf
  let nulls := ([f.meanAlpha, f.activeAlpha, f.demonAlpha, f.epsilon, f.reward].filter (fun x => !finite x)).length +
    if f.predictions.any (fun x => !finite x) || f.cumulants.any (fun x => !finite x) then 1 else 0
  let novel := !r.visited.contains f.position
  let history := r.history.push f.channels
  let window := { r.current with
    frames := r.current.frames + 1, energy := r.current.energy + f.energy.val,
    exhausted := r.current.exhausted + if f.exhausted then 1 else 0,
    eats := r.current.eats + if f.ate then 1 else 0,
    reward := if finite f.reward then r.current.reward + f.reward.toFloat else r.current.reward,
    newTiles := r.current.newTiles + if novel then 1 else 0,
    control := r.current.control.note .control f.activeAlpha,
    demons := f.demonAlphas.foldl (fun s a => s.note .demon a) r.current.demons }
  let window := if history.count.val == historyCapacity && (r.frames + 1) % r.sampleEvery.val == 0
    then window.sample history else window
  return { r with
    frames := r.frames + 1, first := r.first.or (some f.time), last := some f.time,
    nulls := r.nulls + nulls, energy := r.energy.set f.energy (r.energy.get f.energy + 1),
    visited := if novel then r.visited.insert f.position () else r.visited,
    history := history, current := window }

/-- Closing a reporting window is an explicit input from the clock owner. -/
def Reduction.closeWindow (r : Reduction) : Reduction :=
  { r with windows := r.windows.push r.current, current := {} }

/-- Histogram population is derived, so ranks cannot disagree with a separate count. -/
def histogramTotal (histogram : Vector Nat (FeatureConstants.energyMax + 1)) : Nat :=
  histogram.toList.sum

/-- First cumulative rank crossing, with one linear traversal and no floating ranks. -/
def rankIndex (target denominator seen : Nat) : List Nat → Option Nat
  | [] => none
  | count :: rest =>
    if denominator * (seen + count) ≥ target then some 0
    else Nat.succ <$> rankIndex target denominator (seen + count) rest

/-- A selected rank always names a histogram bin; callers need no fallback index. -/
theorem rankIndex_bound (target denominator seen : Nat) (counts : List Nat) (i : Nat)
    (h : rankIndex target denominator seen counts = some i) : i < counts.length := by
  induction counts generalizing seen i with
  | nil => simp [rankIndex] at h
  | cons count rest ih =>
    simp only [rankIndex] at h
    split at h
    · cases h; simp
    · cases hr : rankIndex target denominator (seen + count) rest with
      | none => simp [hr] at h
      | some j =>
        rw [hr] at h
        change some (Nat.succ j) = some i at h
        cases h
        exact Nat.succ_lt_succ (ih _ _ hr)

/-- Exact empirical quantile: least index whose cumulative count meets the
rational rank. Empty histograms return none; no float rank rounding is involved. -/
def energyQuantile (histogram : Vector Nat (FeatureConstants.energyMax + 1))
    (numerator denominator : Nat) : Option Energy :=
  let total := histogramTotal histogram
  if total == 0 || denominator == 0 || numerator > denominator then none else
  match h : rankIndex (numerator * total) denominator 0 histogram.toList with
  | none => none
  | some i => some ⟨i, by simpa using rankIndex_bound _ _ _ _ i h⟩

/-- No observation yields no mean, rather than an invented zero. -/
def mean (sum : Float) (count : Nat) : Option Float :=
  if count == 0 then none else some (sum / count.toFloat)

/-- Rate means and saturation fractions share the exact finite-sample denominator. -/
def Rates.summary (rates : Rates) : Option Float × Option Float × Option Float :=
  (mean rates.sum rates.count, mean rates.upper.toFloat rates.count,
    mean rates.lower.toFloat rates.count)

/-- Error, return and prediction means share the same admitted prediction samples. -/
def ErrorStats.summary (stats : ErrorStats) : Option Float × Option Float × Option Float :=
  (mean stats.error stats.count, mean stats.returns stats.count, mean stats.predictions stats.count)

/-- Aggregate energy values derive their population from the histogram itself.
The low threshold is generated from the current world owner, never a caller rail. -/
def Reduction.energySummary (r : Reduction) : Option Float × Option Float :=
  let histogram := r.energy.toList
  let weighted := ((List.range histogram.length).zip histogram).foldl
    (fun total pair => total + pair.1 * pair.2) 0
  let count := histogramTotal r.energy
  (mean weighted.toFloat count,
    mean (histogram.take FeatureConstants.energyLow).sum.toFloat count)

end Acorn.Host.Endurance
