/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.SignalValues
import Acorn.SwiftTd

/-!
# Off-policy questions about each option's policy

Sutton, Modayil, Delp, Degris, Pilarski, White & Precup, *Horde: A Scalable
Real-time Architecture for Learning Knowledge from Unsupervised Sensorimotor
Interaction*, AAMAS 2011, §4, pp. 763–764, learns many predictions in parallel about
policies other than the one being followed, which "requires off-policy learning",
with the gradient-TD method GQ(λ). Each option keeps one question per prediction
signal about its own policy: that signal's discounted sum if the agent followed the
option's policy, as the option executes it, from here on.

**Which transitions.** A transition trains an option's questions exactly when its
action was selected with the option's own distribution: the option was executing,
or the masses the behaviour reported equal the option's own (PAR-17). The importance
ratio of such a transition is one for every action, so none is formed. Elsewhere the
transition is not used.

**Learner.** GTD2-MP of Liu, Liu, Ghavamzadeh, Mahadevan & Petrik, *Finite-Sample
Analysis of Proximal Gradient TD Algorithms*, UAI 2015 (arXiv:2006.14364v2, §5,
Algorithm 2, p. 7), at importance ratio one and trace parameter zero, over binary
features. It keeps main weights `w` and second weights `u`. For a transition from
active set `x` to active set `x'` with signal value `c` and discount `γ`, write
`a = x − γx'`, `p = Σ_x u` and `δ = c + γ·Σ_x' w − Σ_x w`. With step size `h`,
`τ = h·|x|` and `κ = h·|a|²`, the extragradient midpoint has the two inner products
`p_m = p + τ(δ − p)` and `δ_m = δ − κp`, and the step adds `h(δ_m − p_m)` to `u` at
every index of `x` and `h·p_m·a` to `w`. The midpoint vectors are never formed: the
two inner products are affine in `p` and `δ`. Plain GTD2 (Sutton, Maei, Precup,
Bhatnagar, Silver, Szepesvári & Wiewiora, ICML 2009, eqs. (8)–(9)) is the same step
with `δ − p` and `p` in place of `δ_m − p_m` and `p_m`.

**Step size.** `h = min(α, η/(|x| + |x'|))`, with the demons' initial step size α and
rate budget η, after SwiftTD's rate bound (Javed, Sharifnassab & Sutton, RLC 2024,
§5.2, eqs. (6)–(7)) applied to both active sets. It keeps `τ` and `κ` at most about η,
which the per-step energy inequality of `AcornVerif.CurrentOffPolicy` needs. No step
size is adapted.

The scalar sums are accumulated in binary64 from the stored binary32 words, reading
each main weight of `x ∪ x'` and each second weight of `x` once; each of the four
increments is narrowed once, and every write passes the weight projection. Each index
the step writes is written once.

**Silent questions.** Zero weights and a zero signal are a fixed point of Algorithm 2.
A question that has learned from no signal word other than zero holds only zero
weights, by a field of its type, and takes no step at a zero signal word.
-/
namespace Acorn.Features

/-- `setFlags` with its work: one write for each listed index, and the fold's control. -/
def setFlagsCosted {size : Nat} (indices : List (Fin size)) (value : Bool)
    (flags : Vector Bool size) : Costed (Vector Bool size) :=
  Costed.foldl (fun current index => Costed.op .write (current.set index.val value index.isLt))
    flags indices

/-- Set one flag at every listed index. -/
def setFlags {size : Nat} (indices : List (Fin size)) (value : Bool) (flags : Vector Bool size) :
    Vector Bool size :=
  (setFlagsCosted indices value flags).val

/-- A flag set writes the flag at each listed index, in list order. -/
theorem setFlags_def {size : Nat} (indices : List (Fin size)) (value : Bool)
    (flags : Vector Bool size) :
    setFlags indices value flags =
      indices.foldl (fun current index => current.set index.val value index.isLt) flags := rfl

/-- A flag set over a list holds the new value at every listed index and its old value
elsewhere, for every list and every vector. -/
theorem setFlags_get {size : Nat} (indices : List (Fin size)) (value : Bool)
    (flags : Vector Bool size) (query : Fin size) :
    (setFlags indices value flags)[query.val] =
      if query ∈ indices then value else flags[query.val] := by
  induction indices generalizing flags with
  | nil => simp [setFlags_def]
  | cons head tail ih =>
    have step : setFlags (head :: tail) value flags =
        setFlags tail value (flags.set head.val value head.isLt) := rfl
    rw [step, ih]
    by_cases inTail : query ∈ tail
    · simp [inTail]
    · by_cases same : query = head
      · subst same
        simp [inTail]
      · have different : head.val ≠ query.val := fun equal => same (Fin.ext equal).symm
        simp [inTail, same, Vector.getElem_set_ne head.isLt query.isLt different]

/-- The active set of the preceding frame when that frame's action was selected with
the option's own distribution, and the empty set otherwise, beside one membership
flag per feature slot. The flags agree with the set by a field, so every value of the
type has them right. -/
structure Preceding (dimension : Dimension) where
  /-- The preceding frame's active set, or the empty set. -/
  features : SwiftTd.ActiveSet dimension
  /-- One flag per feature slot. -/
  flags : Vector Bool dimension.capacity
  /-- A flag is set exactly at the slots of the set. -/
  agrees : ∀ index : FeatIdx dimension, flags[index.val] = decide (index ∈ features.indices)

/-- No preceding transition: the empty set and no flag set. -/
def Preceding.empty (dimension : Dimension) : Preceding dimension :=
  ⟨SwiftTd.ActiveSet.empty dimension, Vector.replicate _ false, by
    intro index
    simp [SwiftTd.ActiveSet.empty]⟩

/-- The step-size cap α: the demons' initial step size (D4). -/
def gradientAlpha : Binary32 := ⟨Acorn.Constants.alphaInit5e5Bits⟩

/-- The rate budget η: the demons' step-size budget (D4). -/
def gradientEta : Binary32 := ⟨Acorn.Constants.eta01Bits⟩

/-- The cap is the demon role's initial step size and the budget its rate budget. -/
theorem gradient_constants (discount : Discount) :
    gradientAlpha = (⟨.demon, .discounted discount⟩ : Acorn.Config).alphaInitial ∧
      gradientEta = (⟨.demon, .discounted discount⟩ : Acorn.Config).eta :=
  ⟨rfl, rfl⟩

/-- A count as a binary64 word. -/
def wideCount (count : Nat) : Binary64 := Binary64.ofUInt64 count.toUInt64

/-- `min(α, η/total)` for the total number of active slots of a transition. -/
def gradientStep (total : Nat) : Binary64 :=
  let budget := (Conversion.widen gradientEta).div (wideCount total)
  let cap := Conversion.widen gradientAlpha
  if budget.less cap then budget else cap

/-- The largest active set a question learns from: `2^16` slots. The rounding analysis of
the step (`AcornVerif.CurrentOffPolicy`) covers transitions between sets of at most this
size, in feature spaces of every admitted capacity. -/
def passageLimit : Nat := 65536

/-- One classified transition: the two active sets, their difference and overlap, and
the step size shared by every question that learns from it. Each derived field carries
its definition, so every value of the type is classified right, and neither set exceeds
`passageLimit`, so every value of the type is one the step's bounds cover. -/
structure Passage (dimension : Dimension) where
  /-- The earlier active set `x`. -/
  source : SwiftTd.ActiveSet dimension
  /-- The later active set `x'`. -/
  target : SwiftTd.ActiveSet dimension
  /-- The slots of `x` that are not in `x'`, in the order of `x`. -/
  onlySource : List (FeatIdx dimension)
  /-- The slots in both, in the order of `x'`. -/
  both : List (FeatIdx dimension)
  /-- The slots of `x'` that are not in `x`, in the order of `x'`. -/
  onlyTarget : List (FeatIdx dimension)
  /-- The step size `h = min(α, η/(|x| + |x'|))`. -/
  step : Binary64
  /-- `τ = h·|x|`. -/
  tau : Binary64
  /-- `|x \ x'|`. -/
  onlySourceCount : Binary64
  /-- `|x ∩ x'|`. -/
  bothCount : Binary64
  /-- `|x' \ x|`. -/
  onlyTargetCount : Binary64
  /-- The earlier set is not empty. -/
  nonempty : source.indices ≠ []
  /-- Neither set exceeds `passageLimit`. -/
  fits : source.indices.length ≤ passageLimit ∧ target.indices.length ≤ passageLimit
  /-- Definition of `onlySource`. -/
  onlySource_eq : onlySource = source.indices.filter fun index => decide (index ∉ target.indices)
  /-- Definition of `both`. -/
  both_eq : both = target.indices.filter fun index => decide (index ∈ source.indices)
  /-- Definition of `onlyTarget`. -/
  onlyTarget_eq : onlyTarget = target.indices.filter fun index => decide (index ∉ source.indices)
  /-- Definition of `step`. -/
  step_eq : step = gradientStep (source.indices.length + target.indices.length)
  /-- Definition of `tau`. -/
  tau_eq : tau = step.mul (wideCount source.indices.length)
  /-- Definition of `onlySourceCount`. -/
  onlySourceCount_eq : onlySourceCount = wideCount onlySource.length
  /-- Definition of `bothCount`. -/
  bothCount_eq : bothCount = wideCount both.length
  /-- Definition of `onlyTargetCount`. -/
  onlyTargetCount_eq : onlyTargetCount = wideCount onlyTarget.length

/-- `Preceding.advance` with its work. From a stored set: the current set's two filters by the
flags (`flagTest` for each slot), the flags cleared over the stored set and set over the current one
(`write` for each), the two sets' lengths and, for a transition the bounds cover, the stored set's
filter by the new flags and the three classes' lengths; then, when the frame is not armed, the flags
cleared over the current set, and the advance's record (`preceding`). From the empty set: the flags
set over the current set when armed, and the record. -/
def Preceding.advanceCosted {dimension : Dimension} (preceding : Preceding dimension)
    (current : SwiftTd.ActiveSet dimension) (armed : Bool) :
    Costed (Option (Passage dimension) × Preceding dimension) :=
  let ⟨source, flags, agrees⟩ := preceding
  match sourceIndices : source.indices with
  | [] =>
    have clear : ∀ index : FeatIdx dimension, flags[index.val] = false := by
      intro index
      rw [agrees, sourceIndices]
      simp
    Costed.ite (armed = true)
      (fun _ =>
        let passage : Option (Passage dimension) := none
        Costed.bind (Costed.attach (setFlagsCosted current.indices true flags))
        fun marked => Costed.op .preceding (passage, ⟨current, marked.val, by
          intro index
          have marks : marked.val = setFlags current.indices true flags := marked.property
          rw [marks, setFlags_get, clear]
          by_cases inside : index ∈ current.indices <;> simp [inside]⟩))
      fun _ => Costed.op .preceding (none, ⟨SwiftTd.ActiveSet.empty dimension, flags, by
        intro index
        rw [clear]
        simp [SwiftTd.ActiveSet.empty]⟩)
  | _ :: _ => do
    let both ← Costed.attach (Costed.filter (fun index => Costed.op .flagTest flags[index.val])
      current.indices)
    let onlyTarget ← Costed.attach (Costed.filter
      (fun index => Costed.op .flagTest (!flags[index.val])) current.indices)
    let cleared ← Costed.attach (setFlagsCosted source.indices false flags)
    let marked ← Costed.attach (setFlagsCosted current.indices true cleared.val)
    have markedAgrees : ∀ index : FeatIdx dimension,
        marked.val[index.val] = decide (index ∈ current.indices) := by
      intro index
      have marks : marked.val =
          setFlags current.indices true (setFlags source.indices false flags) :=
        marked.property.trans (congrArg (setFlags current.indices true) cleared.property)
      simp only [marks, setFlags_get, agrees]
      by_cases inCurrent : index ∈ current.indices <;>
        by_cases inSource : index ∈ source.indices <;> simp [inCurrent, inSource]
    let sourceLength ← Costed.attach (Costed.length source.indices)
    let currentLength ← Costed.attach (Costed.length current.indices)
    let passage ← Costed.dite (sourceLength.val ≤ passageLimit ∧ currentLength.val ≤ passageLimit)
      (fun fits => do
        let onlySource ← Costed.attach (Costed.filter
          (fun index => Costed.op .flagTest (!marked.val[index.val])) source.indices)
        let step := gradientStep (sourceLength.val + currentLength.val)
        let tau := step.mul (wideCount sourceLength.val)
        let onlySourceLength ← Costed.attach (Costed.length onlySource.val)
        let onlySourceCount := wideCount onlySourceLength.val
        let bothLength ← Costed.attach (Costed.length both.val)
        let bothCount := wideCount bothLength.val
        let onlyTargetLength ← Costed.attach (Costed.length onlyTarget.val)
        let onlyTargetCount := wideCount onlyTargetLength.val
        Costed.pure <| some
          { source, target := current, onlySource := onlySource.val, both := both.val,
            onlyTarget := onlyTarget.val, step, tau, onlySourceCount, bothCount, onlyTargetCount
            nonempty := by rw [sourceIndices]; exact List.cons_ne_nil _ _
            fits := by
              have lengths := fits
              rw [sourceLength.property, currentLength.property] at lengths
              exact lengths
            onlySource_eq := by
              rw [onlySource.property]
              exact List.filter_congr fun index _ => by simp [Costed.op_val, markedAgrees]
            both_eq := by
              rw [both.property]
              exact List.filter_congr fun index _ => by simp [Costed.op_val, agrees]
            onlyTarget_eq := by
              rw [onlyTarget.property]
              exact List.filter_congr fun index _ => by simp [Costed.op_val, agrees]
            step_eq := by
              show gradientStep (sourceLength.val + currentLength.val) = _
              rw [sourceLength.property, currentLength.property, Costed.length_val,
                Costed.length_val]
            tau_eq := by
              show step.mul (wideCount sourceLength.val) = _
              rw [sourceLength.property, Costed.length_val]
            onlySourceCount_eq := by
              show wideCount onlySourceLength.val = _
              rw [onlySourceLength.property, Costed.length_val]
            bothCount_eq := by
              show wideCount bothLength.val = _
              rw [bothLength.property, Costed.length_val]
            onlyTargetCount_eq := by
              show wideCount onlyTargetLength.val = _
              rw [onlyTargetLength.property, Costed.length_val] })
      fun _ => Costed.pure none
    Costed.ite (armed = true)
      (fun _ => Costed.op .preceding (passage, ⟨current, marked.val, markedAgrees⟩))
      fun _ => Costed.bind (Costed.attach (setFlagsCosted current.indices false marked.val))
        fun unmarked => Costed.op .preceding (passage,
          ⟨SwiftTd.ActiveSet.empty dimension, unmarked.val, by
            intro index
            have unmarks : unmarked.val = setFlags current.indices false marked.val :=
              unmarked.property
            rw [unmarks, setFlags_get, markedAgrees]
            by_cases inside : index ∈ current.indices <;>
              simp [inside, SwiftTd.ActiveSet.empty]⟩)

/-- Classify the transition from the stored set to the current one and store the
current set when its action was selected with the option's distribution. A transition
from the empty set, or between sets of which one exceeds `passageLimit`, is not
classified: no question learns from it. The flags are read before any is written, then
cleared over the stored set and set over the current one, so the work is at most
proportional to the two sets. -/
def Preceding.advance {dimension : Dimension} (preceding : Preceding dimension)
    (current : SwiftTd.ActiveSet dimension) (armed : Bool) :
    Option (Passage dimension) × Preceding dimension :=
  (preceding.advanceCosted current armed).val

/-- An advance from a stored set filters the current set by the flags, clears the flags over the
stored set, sets them over the current one, classifies a transition whose sets fit
`passageLimit`, and stores the current set when armed; from the empty set it stores the current set
when armed. -/
theorem Preceding.advance_def {dimension : Dimension} (preceding : Preceding dimension)
    (current : SwiftTd.ActiveSet dimension) (armed : Bool) :
    preceding.advance current armed =
      let ⟨source, flags, agrees⟩ := preceding
      match sourceIndices : source.indices with
      | [] =>
        have clear : ∀ index : FeatIdx dimension, flags[index.val] = false := by
          intro index
          rw [agrees, sourceIndices]
          simp
        if armed then
          (none, ⟨current, setFlags current.indices true flags, by
            intro index
            rw [setFlags_get, clear]
            by_cases inside : index ∈ current.indices <;> simp [inside]⟩)
        else
          (none, ⟨SwiftTd.ActiveSet.empty dimension, flags, by
            intro index
            rw [clear]
            simp [SwiftTd.ActiveSet.empty]⟩)
      | _ :: _ =>
        let both := current.indices.filter fun index => flags[index.val]
        let onlyTarget := current.indices.filter fun index => !flags[index.val]
        let cleared := setFlags source.indices false flags
        let marked := setFlags current.indices true cleared
        have markedAgrees : ∀ index : FeatIdx dimension,
            marked[index.val] = decide (index ∈ current.indices) := by
          intro index
          simp only [marked, cleared, setFlags_get, agrees]
          by_cases inCurrent : index ∈ current.indices <;>
            by_cases inSource : index ∈ source.indices <;> simp [inCurrent, inSource]
        let onlySource := source.indices.filter fun index => !marked[index.val]
        let step := gradientStep (source.indices.length + current.indices.length)
        let passage : Option (Passage dimension) :=
          if fits : source.indices.length ≤ passageLimit ∧
              current.indices.length ≤ passageLimit then
            some { source, target := current, onlySource, both, onlyTarget, step
                   tau := step.mul (wideCount source.indices.length)
                   onlySourceCount := wideCount onlySource.length
                   bothCount := wideCount both.length
                   onlyTargetCount := wideCount onlyTarget.length
                   nonempty := by rw [sourceIndices]; exact List.cons_ne_nil _ _
                   fits
                   onlySource_eq := List.filter_congr fun index _ => by simp [markedAgrees]
                   both_eq := List.filter_congr fun index _ => by simp [agrees]
                   onlyTarget_eq := List.filter_congr fun index _ => by simp [agrees]
                   step_eq := rfl
                   tau_eq := rfl
                   onlySourceCount_eq := rfl
                   bothCount_eq := rfl
                   onlyTargetCount_eq := rfl }
          else none
        if armed then
          (passage, ⟨current, marked, markedAgrees⟩)
        else
          (passage, ⟨SwiftTd.ActiveSet.empty dimension, setFlags current.indices false marked, by
            intro index
            rw [setFlags_get, markedAgrees]
            by_cases inside : index ∈ current.indices <;>
              simp [inside, SwiftTd.ActiveSet.empty]⟩) := by
  rcases preceding with ⟨⟨indices, nodup⟩, flags, agrees⟩
  cases indices <;> cases armed <;> rfl

/-- Remove a retired slot from the stored set and clear its flag. -/
def Preceding.retire {dimension : Dimension} (preceding : Preceding dimension)
    (feature : FeatIdx dimension) : Preceding dimension :=
  let ⟨features, flags, agrees⟩ := preceding
  ⟨⟨features.indices.filter (· != feature), features.nodup.sublist List.filter_sublist⟩,
    flags.set feature.val false feature.isLt, by
      intro index
      by_cases same : index = feature
      · subst same
        simp
      · have different : feature.val ≠ index.val := fun equal => same (Fin.ext equal).symm
        rw [Vector.getElem_set_ne feature.isLt index.isLt different, agrees]
        simp [same]⟩

/-- One GTD2-MP learner: main weights, whose sum over an active set is the prediction,
and second weights, whose sum estimates the expected TD error there. Both live in the
discount's weight domain. -/
structure GradientLearner (discount : Discount) (dimension : Dimension) where
  /-- Main weights `w`. -/
  main : WeightArray (.discounted discount) dimension
  /-- Second weights `u`. -/
  second : WeightArray (.discounted discount) dimension

/-- Zero main and second weights, built as two vectors. Two equal `Vector.replicate`
terms compile to one array referenced twice, and the first write to either would then
copy every slot of the space; the second vector is therefore built slot by slot. The
native route of this definition requires both constructions in the compiled code. That
the two vectors are separate storage is a property of that code, not of these values. -/
def GradientLearner.initial (discount : Discount) (dimension : Dimension) :
    GradientLearner discount dimension :=
  ⟨Vector.replicate _ (Weight.project _ .zero), Vector.ofFn fun _ => Weight.project _ .zero⟩

/-- `wideSum` with its work: one addition (`sumTerm`) for each listed slot, and the fold's
control. -/
def wideSumCosted {rule : ValueRule} {dimension : Dimension} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (total : Binary64 := ⟨0⟩) : Costed Binary64 :=
  Costed.foldl (fun total index =>
    Costed.op .sumTerm (total.add (Conversion.widen (weights.get index).value))) total indices

/-- The binary64 sum of the widened stored words at the listed slots, in list order,
continued from `total`. -/
def wideSum {rule : ValueRule} {dimension : Dimension} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (total : Binary64 := ⟨0⟩) : Binary64 :=
  (wideSumCosted weights indices total).val

/-- A wide sum adds each listed slot's widened word to the total, in list order. -/
theorem wideSum_def {rule : ValueRule} {dimension : Dimension}
    (weights : WeightArray rule dimension) (indices : List (FeatIdx dimension)) (total : Binary64) :
    wideSum weights indices total =
      indices.foldl (fun total index => total.add (Conversion.widen (weights.get index).value))
        total := rfl

/-- `addAll` with its work: one weight write (`gradientWrite`) for each listed slot, and the
fold's control. -/
def addAllCosted {rule : ValueRule} {dimension : Dimension} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (delta : Binary32) : Costed (WeightArray rule dimension) :=
  Costed.foldl (fun current index => Costed.op .gradientWrite
    (current.set index.val (Weight.project rule ((current.get index).value.add delta)) index.isLt))
    weights indices

/-- Add one increment at every listed slot, through the weight projection. -/
def addAll {rule : ValueRule} {dimension : Dimension} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (delta : Binary32) : WeightArray rule dimension :=
  (addAllCosted weights indices delta).val

/-- An add fold writes each listed slot from the word it holds, in list order. -/
theorem addAll_def {rule : ValueRule} {dimension : Dimension} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (delta : Binary32) :
    addAll weights indices delta =
      indices.foldl (fun current index =>
        current.set index.val (Weight.project rule ((current.get index).value.add delta))
          index.isLt) weights := rfl

/-- `subAll` with its work: one weight write (`gradientWrite`) for each listed slot, and the
fold's control. -/
def subAllCosted {rule : ValueRule} {dimension : Dimension} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (delta : Binary32) : Costed (WeightArray rule dimension) :=
  Costed.foldl (fun current index => Costed.op .gradientWrite
    (current.set index.val (Weight.project rule ((current.get index).value.sub delta)) index.isLt))
    weights indices

/-- Subtract one decrement at every listed slot, through the weight projection. -/
def subAll {rule : ValueRule} {dimension : Dimension} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (delta : Binary32) : WeightArray rule dimension :=
  (subAllCosted weights indices delta).val

/-- A subtract fold writes each listed slot from the word it holds, in list order. -/
theorem subAll_def {rule : ValueRule} {dimension : Dimension} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (delta : Binary32) :
    subAll weights indices delta =
      indices.foldl (fun current index =>
        current.set index.val (Weight.project rule ((current.get index).value.sub delta))
          index.isLt) weights := rfl

/-- `GradientLearner.scalars` with its work: the four sums, then the two inner products from
them (`innerProducts`). -/
def GradientLearner.scalarsCosted {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : Costed (Binary64 × Binary64) := do
  let one := Binary64.ofUInt64 1
  let gamma := Conversion.widen discount.gamma
  let complement := one.sub gamma
  let shared ← wideSumCosted learner.main passage.both
  let earlier ← wideSumCosted learner.main passage.onlySource shared
  let later ← wideSumCosted learner.main passage.onlyTarget shared
  let expected ← wideSumCosted learner.second passage.source.indices
  let error := ((Conversion.widen cumulant).add (gamma.mul later)).sub earlier
  let gap := error.sub expected
  let curvature := passage.step.mul
    ((passage.onlySourceCount.add ((gamma.mul gamma).mul passage.onlyTargetCount)).add
      ((complement.mul complement).mul passage.bothCount))
  Costed.op .innerProducts (expected.add (passage.tau.mul gap),
    ((one.sub passage.tau).mul gap).sub (curvature.mul expected))

/-- The two inner products of the extragradient midpoint, from the stored words: the
midpoint's `p_m = p + τ(δ − p)` and its correction `δ_m − p_m = (1 − τ)(δ − p) − κp`. The
sums accumulate in binary64. The main weights of `x ∩ x'` are read once: their sum is
continued over `x \ x'` for `Σ_x w` and over `x' \ x` for `Σ_x' w`. -/
def GradientLearner.scalars {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : Binary64 × Binary64 :=
  (learner.scalarsCosted passage cumulant).val

/-- The inner products are formed from the sum over `x ∩ x'` continued over each class, and the
sum of the second weights over `x`. -/
theorem GradientLearner.scalars_def {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    learner.scalars passage cumulant =
      let one := Binary64.ofUInt64 1
      let gamma := Conversion.widen discount.gamma
      let complement := one.sub gamma
      let shared := wideSum learner.main passage.both
      let earlier := wideSum learner.main passage.onlySource shared
      let later := wideSum learner.main passage.onlyTarget shared
      let expected := wideSum learner.second passage.source.indices
      let error := ((Conversion.widen cumulant).add (gamma.mul later)).sub earlier
      let gap := error.sub expected
      let curvature := passage.step.mul
        ((passage.onlySourceCount.add ((gamma.mul gamma).mul passage.onlyTargetCount)).add
          ((complement.mul complement).mul passage.bothCount))
      (expected.add (passage.tau.mul gap),
        ((one.sub passage.tau).mul gap).sub (curvature.mul expected)) := rfl

/-- `GradientLearner.increments` with its work: the inner products, then the four increments
from them (`increments`). -/
def GradientLearner.incrementsCosted {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : Costed (Binary32 × Binary32 × Binary32 × Binary32) := do
  let scalars ← learner.scalarsCosted passage cumulant
  let gamma := Conversion.widen discount.gamma
  let mainStep := passage.step.mul scalars.1
  Costed.op .increments (Conversion.narrow (passage.step.mul scalars.2), Conversion.narrow mainStep,
    Conversion.narrow (((Binary64.ofUInt64 1).sub gamma).mul mainStep),
    Conversion.narrow (gamma.mul mainStep))

/-- The four increments of one step, each narrowed once: `h(δ_m − p_m)` for `u` on `x`,
and `h·p_m`, `(1 − γ)·h·p_m` and `γ·h·p_m` for `w` on `x \ x'`, `x ∩ x'` and `x' \ x`,
where the last is subtracted. -/
def GradientLearner.increments {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : Binary32 × Binary32 × Binary32 × Binary32 :=
  (learner.incrementsCosted passage cumulant).val

/-- The increments are the step size times each inner product, narrowed. -/
theorem GradientLearner.increments_def {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    learner.increments passage cumulant =
      let scalars := learner.scalars passage cumulant
      let gamma := Conversion.widen discount.gamma
      let mainStep := passage.step.mul scalars.1
      (Conversion.narrow (passage.step.mul scalars.2), Conversion.narrow mainStep,
        Conversion.narrow (((Binary64.ofUInt64 1).sub gamma).mul mainStep),
        Conversion.narrow (gamma.mul mainStep)) := rfl

/-- `GradientLearner.step` with its work: the increments, then the four write folds, three over
the classes of the main weights and one over `x` of the second weights. -/
def GradientLearner.stepCosted {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : Costed (GradientLearner discount dimension) := do
  let deltas ← learner.incrementsCosted passage cumulant
  let ⟨main, second⟩ := learner
  let main ← addAllCosted main passage.onlySource deltas.2.1
  let main ← addAllCosted main passage.both deltas.2.2.1
  let main ← subAllCosted main passage.onlyTarget deltas.2.2.2
  let second ← addAllCosted second passage.source.indices deltas.1
  Costed.pure ⟨main, second⟩

/-- One GTD2-MP step at importance ratio one (Liu et al., Algorithm 2): the increments are
computed from the weights before any write, and each slot of `x ∪ x'` is written once. -/
def GradientLearner.step {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : GradientLearner discount dimension :=
  (learner.stepCosted passage cumulant).val

/-- A step adds the increments over `x \ x'` and `x ∩ x'` and subtracts the last over `x' \ x` in
the main weights, and adds the first over `x` in the second weights. -/
theorem GradientLearner.step_def {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    learner.step passage cumulant =
      let deltas := learner.increments passage cumulant
      let ⟨main, second⟩ := learner
      ⟨subAll (addAll (addAll main passage.onlySource deltas.2.1) passage.both deltas.2.2.1)
          passage.onlyTarget deltas.2.2.2,
        addAll second passage.source.indices deltas.1⟩ := rfl

/-- Reset one retired slot's main and second weights to zero. -/
def GradientLearner.retire {discount : Discount} {dimension : Dimension}
    (learner : GradientLearner discount dimension) (feature : FeatIdx dimension) :
    GradientLearner discount dimension :=
  let ⟨main, second⟩ := learner
  ⟨main.set feature.val (Weight.project _ .zero) feature.isLt,
    second.set feature.val (Weight.project _ .zero) feature.isLt⟩

/-- One question: its learner, and whether its signal has been zero on every transition
it has learned from. Every weight of such a silent question is zero, by a field. -/
structure Question (discount : Discount) (dimension : Dimension) where
  /-- Main and second weights. -/
  learner : GradientLearner discount dimension
  /-- No learned transition has carried a signal word other than zero. -/
  silent : Bool
  /-- A silent question holds no knowledge. -/
  blank : silent = true → ∀ index : FeatIdx dimension,
    learner.main[index.val].value = .zero ∧ learner.second[index.val].value = .zero

/-- A fresh question is silent. -/
def Question.initial (discount : Discount) (dimension : Dimension) :
    Question discount dimension :=
  ⟨GradientLearner.initial discount dimension, true, fun _ index => by
    simp [GradientLearner.initial, Weight.project_zero]⟩

/-- `Question.step` with its work: the learner's step unless the question is silent at a zero
signal word, and the question's record (`question`). -/
def Question.stepCosted {discount : Discount} {dimension : Dimension}
    (question : Question discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : Costed (Question discount dimension) :=
  let ⟨learner, silent, blank⟩ := question
  Costed.ite ((silent && cumulant.bits == 0) = true)
    (fun _ => Costed.op .question ⟨learner, silent, blank⟩)
    fun _ => Costed.bind (learner.stepCosted passage cumulant) fun stepped =>
      Costed.op .question ⟨stepped, false, nofun⟩

/-- One step of a question. Zero weights and a zero signal word are a fixed point of
Algorithm 2: every sum and so every increment is zero. A silent question at a zero
signal word therefore takes no step and reads no weight. Any other step is the
learner's, and ends the silence. -/
def Question.step {discount : Discount} {dimension : Dimension}
    (question : Question discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : Question discount dimension :=
  (question.stepCosted passage cumulant).val

/-- A silent question at a zero signal word is kept; any other takes its learner's step and is no
longer silent. -/
theorem Question.step_def {discount : Discount} {dimension : Dimension}
    (question : Question discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    question.step passage cumulant =
      let ⟨learner, silent, blank⟩ := question
      if silent && cumulant.bits == 0 then ⟨learner, silent, blank⟩
      else ⟨learner.step passage cumulant, false, nofun⟩ := by
  rcases question with ⟨learner, silent, blank⟩
  cases silent <;> rfl

/-- Reset one retired slot. A silent question already holds zero there and is kept as it
is; any other question's learner resets the slot. -/
def Question.retire {discount : Discount} {dimension : Dimension}
    (question : Question discount dimension) (feature : FeatIdx dimension) :
    Question discount dimension :=
  let ⟨learner, silent, blank⟩ := question
  if quiet : silent = true then ⟨learner, silent, blank⟩
  else ⟨learner.retire feature, silent, fun impossible => absurd impossible quiet⟩

/-- One question per prediction signal, each under its signal's discount. -/
inductive GradientBank (dimension : Dimension) : List Discount → Type where
  /-- No further signals. -/
  | nil : GradientBank dimension []
  /-- One signal's question and the remaining signals. -/
  | cons {discount : Discount} {rest : List Discount}
      (question : Question discount dimension) (tail : GradientBank dimension rest) :
      GradientBank dimension (discount :: rest)

/-- Fresh questions for the supplied layout. -/
def GradientBank.initial (dimension : Dimension) :
    (discounts : List Discount) → GradientBank dimension discounts
  | [] => .nil
  | discount :: rest => .cons (Question.initial discount dimension)
      (GradientBank.initial dimension rest)

/-- `GradientBank.step` with its work: each question's step, the rest of the bank's step, then the
question put before the rest's (`questionBank`); the end of the bank is charged a visit. -/
def GradientBank.stepCosted {dimension : Dimension} {discounts : List Discount}
    (bank : GradientBank dimension discounts) (passage : Passage dimension)
    (cumulants : Cumulants discounts) : Costed (GradientBank dimension discounts) :=
  match bank, cumulants with
  | .nil, .nil => Costed.op .visit .nil
  | .cons question rest, .cons _origin value values => Costed.charge .visit do
    let stepped ← question.stepCosted passage value
    let next ← rest.stepCosted passage values
    Costed.op .questionBank (.cons stepped next)

/-- Each question takes one step from the same transition with its own signal value. -/
def GradientBank.step {dimension : Dimension} {discounts : List Discount}
    (bank : GradientBank dimension discounts) (passage : Passage dimension)
    (cumulants : Cumulants discounts) : GradientBank dimension discounts :=
  (bank.stepCosted passage cumulants).val

/-- A bank step steps each question with its own signal value and then the rest of the bank. -/
theorem GradientBank.step_def {dimension : Dimension} {discounts : List Discount}
    (bank : GradientBank dimension discounts) (passage : Passage dimension)
    (cumulants : Cumulants discounts) :
    bank.step passage cumulants =
      match bank, cumulants with
      | .nil, .nil => .nil
      | .cons question rest, .cons _origin value values =>
        .cons (question.step passage value) (rest.step passage values) := by
  cases bank <;> cases cumulants <;> rfl

/-- Every question resets the retired slot. -/
def GradientBank.retire {dimension : Dimension} {discounts : List Discount}
    (bank : GradientBank dimension discounts) (feature : FeatIdx dimension) :
    GradientBank dimension discounts :=
  match bank with
  | .nil => .nil
  | .cons question rest => .cons (question.retire feature) (rest.retire feature)

/-- The questions one option asks about its own policy, one per prediction signal, and
the preceding frame's active set when that frame's action was selected with the
option's distribution. -/
structure OptionQuestions (dimension : Dimension) (discounts : List Discount) where
  /-- One question per signal. -/
  learners : GradientBank dimension discounts
  /-- The preceding frame's active set, or the empty set. -/
  preceding : Preceding dimension

/-- Fresh learners and no preceding transition. -/
def OptionQuestions.initial (dimension : Dimension) (discounts : List Discount) :
    OptionQuestions dimension discounts :=
  ⟨GradientBank.initial dimension discounts, Preceding.empty dimension⟩

/-- `OptionQuestions.follow` with its work: the preceding set's advance, the bank's step when
the advance classifies a transition, and the questions' record (`follow`). -/
def OptionQuestions.followCosted {dimension : Dimension} {discounts : List Discount}
    (questions : OptionQuestions dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (cumulants : Cumulants discounts) (armed : Bool) :
    Costed (OptionQuestions dimension discounts) :=
  let ⟨learners, preceding⟩ := questions
  Costed.bind (preceding.advanceCosted features armed) fun
    | (none, next) => Costed.op .follow ⟨learners, next⟩
    | (some passage, next) => Costed.bind (learners.stepCosted passage cumulants) fun stepped =>
      Costed.op .follow ⟨stepped, next⟩

/-- One frame: learn from the transition into it when the preceding frame's action was
selected with the option's distribution, then store this frame's active set when its
own action was. -/
def OptionQuestions.follow {dimension : Dimension} {discounts : List Discount}
    (questions : OptionQuestions dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (cumulants : Cumulants discounts) (armed : Bool) : OptionQuestions dimension discounts :=
  (questions.followCosted features cumulants armed).val

/-- Following a frame steps the bank when the advance classifies a transition, and keeps the
advanced preceding set. -/
theorem OptionQuestions.follow_def {dimension : Dimension} {discounts : List Discount}
    (questions : OptionQuestions dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (cumulants : Cumulants discounts) (armed : Bool) :
    questions.follow features cumulants armed =
      let ⟨learners, preceding⟩ := questions
      match preceding.advance features armed with
      | (none, next) => ⟨learners, next⟩
      | (some passage, next) => ⟨learners.step passage cumulants, next⟩ := by
  rcases questions with ⟨learners, preceding⟩
  dsimp only [OptionQuestions.follow, OptionQuestions.followCosted, Preceding.advance, Costed.bind]
  rcases (preceding.advanceCosted features armed).val with ⟨_ | passage, next⟩ <;> rfl

/-- Reset the retired slot in every learner and drop it from the stored set. -/
def OptionQuestions.retire {dimension : Dimension} {discounts : List Discount}
    (questions : OptionQuestions dimension discounts) (feature : FeatIdx dimension) :
    OptionQuestions dimension discounts :=
  let ⟨learners, preceding⟩ := questions
  ⟨learners.retire feature, preceding.retire feature⟩

end Acorn.Features
