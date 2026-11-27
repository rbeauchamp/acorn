import Acorn.Handcrafted.Observation
import Acorn.Host.Task
import Std.Data.TreeMap.Lemmas

namespace Acorn.Host.Endurance

def horizon : Discount → Nat
  | .g90 => 200
  | .g95 => 400
  | .g99 => 2000

def historyCapacity : Nat := horizon .g99

structure Frame where
  time : UInt64
  energy : Energy
  position : Int × Int
  exhausted : Bool
  ate : Bool
  reward : Float32
  meanAlpha : Float32
  activeAlpha : Float32
  demonAlpha : Float32
  demonAlphas : List Float32
  epsilon : Float32
  predictions : List Float32
  cumulants : List Float32

structure Rates where
  count : Nat := 0
  sum : Float := 0
  upper : Nat := 0
  lower : Nat := 0

def Rates.note (r : Rates) (role : Role) (alpha : Float32) : Rates :=
  if alpha.isNaN || alpha.isInf then r else
  let config : Config := ⟨role, .discounted .g99⟩
  let a := alpha.toFloat
  let upper := (Float32.ofBits config.eta.bits).toFloat * 0.999
  let lower := (Float32.ofBits config.etaMin.bits).toFloat * 1.001
  { count := r.count + 1, sum := r.sum + a,
    upper := r.upper + if a ≥ upper then 1 else 0,
    lower := r.lower + if a < upper && a ≤ lower then 1 else 0 }

structure ErrorStats where
  count : Nat := 0
  error : Float := 0
  returns : Float := 0
  predictions : Float := 0

structure Window where
  frames : Nat := 0
  energy : Nat := 0
  exhausted : Nat := 0
  eats : Nat := 0
  reward : Float := 0
  newTiles : Nat := 0
  control : Rates := {}
  demons : Rates := {}
  errorCount : Nat := 0
  errorSum : Float := 0
  errors : Vector ErrorStats FeatureConstants.demonCount := Vector.replicate _ {}

structure Channels where
  predictions : Vector Float32 FeatureConstants.demonCount
  cumulants : Vector Float32 FeatureConstants.demonCount

def Frame.channels (f : Frame) : Channels :=
  ⟨Vector.ofFn (fun i => f.predictions[i.val]?.getD 0),
    Vector.ofFn (fun i => f.cumulants[i.val]?.getD 0)⟩

structure History where
  slots : Vector Channels historyCapacity
  next : Fin historyCapacity
  count : Fin (historyCapacity + 1)

def History.empty : History :=
  ⟨Vector.replicate _ ⟨Vector.replicate _ 0, Vector.replicate _ 0⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩

def History.push (h : History) (frame : Channels) : History :=
  ⟨h.slots.set h.next frame,
    ⟨(h.next.val + 1) % historyCapacity, Nat.mod_lt _ (by decide)⟩,
    ⟨min (h.count.val + 1) historyCapacity, by have := Nat.min_le_right (h.count.val + 1) historyCapacity; omega⟩⟩

def History.at (h : History) (offset : Nat) : Channels :=
  h.slots.get ⟨(h.next.val + offset) % historyCapacity, Nat.mod_lt _ (by decide)⟩

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

structure Reduction where
  private mk ::
  sampleEvery : {n : Nat // 0 < n}
  frames : Nat := 0
  first : Option UInt64 := none
  last : Option UInt64 := none
  nulls : Nat := 0
  energy : Vector Nat (FeatureConstants.energyMax + 1) := Vector.replicate _ 0
  visited : Std.TreeMap (Int × Int) Unit (@compare (Int × Int) lexOrd) := {}
  history : History := History.empty
  current : Window := {}
  windows : Array Window := #[]

def Reduction.start (sampleEvery : {n : Nat // 0 < n}) : Reduction := { sampleEvery := sampleEvery }

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

def Reduction.closeWindow (r : Reduction) : Reduction :=
  { r with windows := r.windows.push r.current, current := {} }

def histogramTotal (histogram : Vector Nat (FeatureConstants.energyMax + 1)) : Nat :=
  histogram.toList.sum

def rankIndex (target denominator seen : Nat) : List Nat → Option Nat
  | [] => none
  | count :: rest =>
    if denominator * (seen + count) ≥ target then some 0
    else Nat.succ <$> rankIndex target denominator (seen + count) rest

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

def energyQuantile (histogram : Vector Nat (FeatureConstants.energyMax + 1))
    (numerator denominator : Nat) : Option Energy :=
  let total := histogramTotal histogram
  if total == 0 || denominator == 0 || numerator > denominator then none else
  match h : rankIndex (numerator * total) denominator 0 histogram.toList with
  | none => none
  | some i => some ⟨i, by simpa using rankIndex_bound _ _ _ _ i h⟩

def mean (sum : Float) (count : Nat) : Option Float :=
  if count == 0 then none else some (sum / count.toFloat)

def Rates.summary (rates : Rates) : Option Float × Option Float × Option Float :=
  (mean rates.sum rates.count, mean rates.upper.toFloat rates.count,
    mean rates.lower.toFloat rates.count)

def ErrorStats.summary (stats : ErrorStats) : Option Float × Option Float × Option Float :=
  (mean stats.error stats.count, mean stats.returns stats.count, mean stats.predictions stats.count)

def Reduction.energySummary (r : Reduction) : Option Float × Option Float :=
  let histogram := r.energy.toList
  let weighted := ((List.range histogram.length).zip histogram).foldl
    (fun total pair => total + pair.1 * pair.2) 0
  let count := histogramTotal r.energy
  (mean weighted.toFloat count,
    mean (histogram.take FeatureConstants.energyLow).sum.toFloat count)

end Acorn.Host.Endurance
