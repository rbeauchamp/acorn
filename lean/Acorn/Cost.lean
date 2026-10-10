/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# The work of an executed computation

A definition whose work Acorn bounds returns a `Costed` value: its result together with the
work of computing it. The work is a proposition about a cost model, so the compiler erases it:
a definition that returns `Costed α` compiles to the code of its result alone, and reading
`val` compiles to nothing. The definition that runs is the definition whose work the bounds
count, and a definition with the plain result type is the `val` of its costed definition.

**Sites.** A *site* (`Site`) is a stretch of executed code whose work is a constant of the
compiled code, together with every definition it calls. It contains no loop, or only loops whose
trip count is a constant of the code and whose bodies are such stretches: the three options,
the four meta actions, the 32 samples of a projection, the at most 15 doublings of the ranked
width's search and the at most 33 steps of `Portable.pow`. A cost model (`Costs`) assigns each
site a cost, and every work bound holds for every cost model. No theorem derives the cost of a
site in word operations; the scalar operations that the native resource audit bounds are the
operations with an extracted cost.

**Counting.** `op site value` is a stretch at the site's cost, `charge` puts a stretch before a
computation, and `bind` sequences two computations and adds their work. Each loop combinator
has as its value the library loop applied to its steps' values, and as its work the passes of
that loop's runtime implementation (`Library`, `Library.passes`): for each element, one `visit`
of the first pass and the work of the step, then one `visit` for each element of each further
pass, and one `visit` for each pass's end. `foldl`, `foldlArray`, `replicate` and `findIdx?` are
one pass (`Library.onePass`); `map` charges the further pass of `List.mapTR`'s reversal from the
table. Every function a combinator takes is costed: the steps of `foldl` and `foldlArray`, the
operation of `map`, the test of `findIdx?` and the continuation of `bind`. A loop's bound is
therefore its trip count times a bound of one visit, and a visit for each end. A recursion of
Acorn's own is a costed recursion whose every recursive call is under a charge and whose end is
charged a visit.

**Bounds.** `x.Within κ bound` states that under the cost model `κ` the work of `x` is at most
`bound`. Every `Costed` value is built here, and its work is one number under each cost model
(`single`), so a bound is never vacuous (`within_iff`).

**What is trusted.** That the counted work covers each operation of the compiled code rests on
the cost discipline of the costed definitions. A combinator counts the work of every function
it takes, but not the computation of a value it takes. The values a costed definition passes
in, which are all its uncosted entry points, are:

- the value of `pure`, the value of `op` and the element of `replicate`;
- the count of `replicate`, the initial accumulator and the collection of `foldl` and
  `foldlArray`, the collection of `map` and the array of `findIdx?`;
- the terms a costed definition evaluates in its own body between combinators: its `let`
  values, its branch conditions and the scrutinees of its matches.

Each must be computed by a stretch that runs no loop and calls no costed definition, a loop
must run only in a loop combinator or a costed definition, and each path to a recursive call
must pass a charge. The combinators cannot enforce it: `pure` accepts any value, so
`Costed.pure (state.step config features reward)` has work zero although its value runs the
learner. Lean's logic gives a pure term no operational meaning, so no theorem states the
discipline; it is a syntactic property, checked by reading until the cost-closed rule that
rbeauchamp/regula#333 proposes checks it. That a library loop makes the passes `Library.passes`
states is read once from the library's runtime implementation, which each row of `Library`
cites. That erasing the work leaves the compiled value code as written is checked by comparing
the generated C. That a site's stretch does at most its cost in word operations is the
hypothesis of each bound in word operations.

**What is not counted:** allocation and release of objects, reference counting, the copy of an
array that is shared when it is written (issue 84 of the repository), cache behaviour and time.
No unit here is a second, a byte or an instruction of a particular processor.
-/

namespace Acorn

/-- The constant stretches of the agent's step. -/
inductive Site where
  /-- The control of one visit of a loop: its test, its advance and its branch. -/
  | visit
  /-- One binary32 addition of an ordered sum, with the read of its term. -/
  | sumTerm
  /-- The read of one stored element into a list or vector being built. -/
  | read
  /-- The first SwiftTD loop's entry: the worklist is taken and the eligible list emptied. -/
  | firstOpen
  /-- One element of the first SwiftTD loop, with the read of its index and the prune test. -/
  | firstElement
  /-- A pruned first-loop index: its nine registers cleared and its entry swap-removed. -/
  | prune
  /-- The first SwiftTD loop's exit: the pruned worklist stored as the eligible list. -/
  | firstClose
  /-- The second SwiftTD loop's entry: the overshoot test, the scale and the complement. -/
  | secondOpen
  /-- One element of the second SwiftTD loop. -/
  | secondElement
  /-- The TD error of a SwiftTD step and the store of its prediction and accumulator. -/
  | stepClose
  /-- A fresh transient record apart from its nine register vectors. -/
  | zeroTransient
  /-- The store of a new trajectory's anchor prediction and accumulator. -/
  | beginClose
  /-- The terminal TD error and the result of a terminal step. -/
  | terminalClose
  /-- A planning step's error, its finiteness test and its scale. -/
  | planOpen
  /-- One planning weight write. -/
  | planElement
  /-- The nine registers of one eligible index cleared. -/
  | clearRegisters
  /-- The eligible list emptied after a release. -/
  | releaseClose
  /-- A retired index's registers cleared, its weight zeroed and its step size re-anchored. -/
  | retire
  /-- A shared-error update's store of the rows, the taken row and the lags. -/
  | creditClose
  /-- The on-policy error of a shared-error update. -/
  | valuesOpen
  /-- A controller record stored after its rows are updated. -/
  | controllerClose
  /-- The store of a planned row and the planning error. -/
  | planClose
  /-- One comparison of two values with the selection of one of them. -/
  | compare
  /-- One near-maximum test of an action's value against the tie threshold. -/
  | candidate
  /-- One reservoir step: a bounded draw and the selection of the pick. -/
  | reservoirDraw
  /-- One action's nominal mass. -/
  | probability
  /-- The exploration mass, the greedy mass and the tie threshold of a policy. -/
  | probabilitiesOpen
  /-- One uniform draw of an action. -/
  | uniform
  /-- The branch draw of a policy draw and the store of its decision. -/
  | drawClose
  /-- A persistent draw's branch, duration and action draws and the store of its decision. -/
  | explorationBegin
  /-- The two discount powers of a frozen-decision credit. -/
  | policyOpen
  /-- The store of a frozen policy snapshot. -/
  | snapshot
  /-- One learner's contribution to a derived exploration rate. -/
  | rateTerm
  /-- The projection of a derived exploration rate, with the fresh-feature fallback. -/
  | rateClose
  /-- A normalized step-size sum's emptiness test, its endpoints and its result. -/
  | normalizedOpen
  /-- One normalized log step size. -/
  | normalizedTerm
  /-- One term of a policy mean: the widened value added to the totals and the tie test. -/
  | expectedTerm
  /-- A policy mean's two weighted parts, its narrowing and its saturation. -/
  | expectedClose
  /-- One feedback word: a prediction's bucket at its horizon and its channel. -/
  | feedbackWord
  /-- One sample's term of a generated unit's projection. -/
  | sampleTerm
  /-- A generated unit's output from its projection. -/
  | activation
  /-- One sensor word hashed into a feature slot for one tiling. -/
  | hashFeature
  /-- One unit's output tested and its feature slot computed. -/
  | imprint
  /-- One raw feature's admission into the unique encoding. -/
  | uniqueAdd
  /-- The membership test and append of one absent index to an active set. -/
  | insert
  /-- One ranked position looked up for a feature slot. -/
  | position
  /-- One element written into a vector. -/
  | write
  /-- One product of a ranked value: a weight read times an expected value. -/
  | productTerm
  /-- One prediction admitted as an expected feature value. -/
  | project
  /-- One meta action's value of a predicted outcome. -/
  | outcomeValue
  /-- The record of an option model's prediction. -/
  | prediction
  /-- One meta action's discounted deviation of an outcome, with the outcome's residual. -/
  | deviation
  /-- The record of an option model after its learners are updated. -/
  | modelClose
  /-- An assignment's feature slot computed before its membership test. -/
  | assignmentPotential
  /-- A declared potential read from the frame's declared values. -/
  | declaredPotential
  /-- An option's termination tests: goal, duration and the stopping comparison. -/
  | decide
  /-- A started invocation's activation and continuation records. -/
  | beginOption
  /-- An option step's shaped cumulant, its activation advance and its records. -/
  | optionStep
  /-- An option's terminal cumulant and stopping value. -/
  | terminateOption
  /-- A stopped trajectory's stopping error and the skill record. -/
  | stopFollowing
  /-- A settled trajectory's shaped cumulant, its tree-backup error and the skill record. -/
  | settleFollowing
  /-- A planning look-ahead's backed-up target and its result record. -/
  | lookAhead
  /-- A backup's store of its prediction cache and planning error. -/
  | backupClose
  /-- A planning boundary's work count, its search-control advance and its result. -/
  | planBoundary
  /-- A fresh learner's rails and record, apart from its vectors. -/
  | initialState
  /-- One unit's Demon-0 weight tested for a ranking candidate. -/
  | rankCandidate
  /-- The ranked width's search, of at most 15 doublings. -/
  | rankWidth
  /-- One slot's objective installed, with the slot's cache and closing owner. -/
  | install
  /-- The slot-stable objective table: the kept objectives, the entrants and the open slots,
  over the three slots and the at most three ranked candidates. -/
  | assignmentTable
  /-- A rate schedule's advance and a credit gap's discounted reward. -/
  | prepare
  /-- A served step's run, interruption and decision record. -/
  | serve
  /-- A primitive draw's occupancy and decision record. -/
  | choosePrimitive
  /-- A free dispatch's records around the refresh. -/
  | refreshFree
  /-- A free boundary's planning state and its write-back. -/
  | planFree
  /-- A meta draw's generator write. -/
  | drawMeta
  /-- An ending option's slot and event record. -/
  | closeOption
  /-- The owed meta span and its write-back. -/
  | learnMeta
  /-- A dispatch's meta action mapped to an option, its value function and records. -/
  | dispatchMeta
  /-- A stepped option's occupancy and decision record. -/
  | stepOption
  /-- A free boundary's closing record and event. -/
  | atBoundary
  /-- Selection's branch tests, phase write and the stopping estimate. -/
  | select
  /-- The agent's clock advance and the chosen value's record. -/
  | choose

/-- A cost model: the cost of each site. -/
abbrev Costs := Site → Nat

/-- The library loops that costed code and the twins of `AcornVerif.Resource.Work` run. Each
is charged the passes of its runtime implementation over the collection it is charged for: the
compiler replacement that runs (a `csimp` theorem or an implementation attribute) and the loops
of that definition. `Library.passes` states each count once. -/
inductive Library where
  /-- `List.foldl`: one structural loop. -/
  | foldl
  /-- `Array.foldl`, implemented by `Array.foldlMUnsafe`: one loop. -/
  | foldlArray
  /-- `List.map`, replaced by `List.mapTR` (`List.map_eq_mapTR`): a loop, then `List.reverse`. -/
  | map
  /-- `Vector.replicate`, `Array.replicate`, implemented by the runtime's `lean_mk_array`: one
  loop. -/
  | replicate
  /-- `Array.findIdx?`: the loop `Array.findIdx?.loop`. -/
  | findIdx
  /-- `Vector.map`, `Array.map` by `Array.mapM`, implemented by `Array.mapMUnsafe`: one loop. -/
  | vectorMap
  /-- `Vector.ofFn`, `Array.ofFn` by its loop `Array.ofFn.go`: one loop. -/
  | ofFn
  /-- `Vector.mapFinIdx`, `Array.mapFinIdx`, implemented by `Array.mapFinIdxMUnsafe`: one loop. -/
  | mapFinIdx
  /-- `List.filter`, replaced by `List.filterTR` (`List.filter_eq_filterTR`): a loop, then
  `List.reverse`. -/
  | filter
  /-- `List.filterMap`, replaced by `List.filterMapTR` (`List.filterMap_eq_filterMapTR`): a loop,
  then `Array.toList` of the kept elements, at most one for each element. -/
  | filterMap
  /-- `List.flatMap`, replaced by `List.flatMapTR` (`List.flatMap_eq_flatMapTR`): one loop over
  the list; the elements of each result are counted by `flatMapResult`. -/
  | flatMap
  /-- The elements of one result of `List.flatMapTR`: `Array.appendList` pushes each one
  (`List.foldl`), and the final `Array.toList` reads each one. -/
  | flatMapResult
  /-- `List.length`, replaced by `List.lengthTR` (`List.length_eq_lengthTR`): one loop. -/
  | length
  /-- `List.contains` and the membership test of a list, `List.elem`: one loop. -/
  | contains
  /-- `List.range`, the loop `List.range.loop`: one loop. -/
  | range
  /-- `List.finRange`, `List.ofFn` by `Fin.foldr`: one loop. -/
  | finRange
  /-- `List.toArray`, implemented by `List.toArrayImpl`: `List.length`, then `List.toArrayAux`. -/
  | toArray
  /-- `Array.toList` and `Vector.toList`, implemented by `Array.toListImpl`, an `Array.foldr`: one
  loop. -/
  | toList
  /-- `List.reverse`, `List.reverseAux`: one loop. -/
  | reverse
  /-- The equality of two vectors, the equality of their arrays, replaced by
  `Array.instDecidableEqImpl` (`Array.instDecidableEq_csimp`), an `Array.isEqv`: one loop. -/
  | vectorEq
  /-- `++` on lists, replaced by `List.appendTR` (`List.append_eq_appendTR`): `List.reverse` of
  the first list, then `List.reverseAux` over it. -/
  | append
  /-- `List.dropLast`, replaced by `List.dropLastTR` (`List.dropLast_eq_dropLastTR`):
  `List.toArray` (two), `Array.pop`, then `Array.toList` (one). -/
  | dropLast
  /-- `List.zipIdx`, replaced by `List.zipIdxTR` (`List.zipIdx_eq_zipIdxTR`): `List.toArray`
  (two), then `Array.foldr` (one). -/
  | zipIdx
  /-- `List.sum`, a `List.foldr`, replaced by `List.foldrTR` (`List.foldr_eq_foldrTR`):
  `List.toArray` (two), then `Array.foldr` (one). -/
  | sum
  /-- Acorn's `fillVacant`, a structural recursion over the held positions: one loop. -/
  | fillVacant

/-- The passes of a library loop's runtime implementation over the collection it is charged
for. -/
def Library.passes : Library → Nat
  | .foldl => 1
  | .foldlArray => 1
  | .map => 2
  | .replicate => 1
  | .findIdx => 1
  | .vectorMap => 1
  | .ofFn => 1
  | .mapFinIdx => 1
  | .filter => 2
  | .filterMap => 2
  | .flatMap => 1
  | .flatMapResult => 2
  | .length => 1
  | .contains => 1
  | .range => 1
  | .finRange => 1
  | .toArray => 2
  | .toList => 1
  | .reverse => 1
  | .vectorEq => 1
  | .append => 2
  | .dropLast => 3
  | .zipIdx => 3
  | .sum => 3
  | .fillVacant => 1

/-- The loops whose combinators are written as one pass are one pass in the table. -/
theorem Library.onePass :
    Library.foldl.passes = 1 ∧ Library.foldlArray.passes = 1 ∧ Library.replicate.passes = 1 ∧
      Library.findIdx.passes = 1 ∧ Library.vectorMap.passes = 1 ∧ Library.ofFn.passes = 1 ∧
      Library.mapFinIdx.passes = 1 ∧ Library.flatMap.passes = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A result together with the work of computing it. The constructor is private, so every
`Costed` value is built by the combinators below. -/
structure Costed (α : Type) where
  private mk ::
  /-- The result. -/
  val : α
  /-- `work κ n`: under the cost model `κ`, computing the result does `n` work. A proposition,
  so the compiler erases it. -/
  work : Costs → Nat → Prop
  /-- Under each cost model the work is one number. -/
  single : ∀ κ, ∃ n, work κ n ∧ ∀ m, work κ m → m = n

namespace Costed

variable {α β : Type}

/-- Under the cost model `κ`, the work of `x` is at most `bound`. -/
def Within (x : Costed α) (κ : Costs) (bound : Nat) : Prop :=
  ∀ n, x.work κ n → n ≤ bound

/-- A bound holds exactly when the one work number is at most it. -/
theorem within_iff (x : Costed α) (κ : Costs) (bound : Nat) :
    x.Within κ bound ↔ ∃ n, x.work κ n ∧ n ≤ bound := by
  obtain ⟨n, holds, unique⟩ := x.single κ
  constructor
  · intro within
    exact ⟨n, holds, within n holds⟩
  · intro ⟨m, held, fits⟩ k work
    rw [unique k work, ← unique m held]
    exact fits

/-- A larger bound holds too. -/
theorem Within.mono {x : Costed α} {κ : Costs} {a b : Nat} (within : x.Within κ a)
    (fits : a ≤ b) : x.Within κ b :=
  fun n work => Nat.le_trans (within n work) fits

/-- A branch is bounded by a bound of each of its arms. -/
theorem within_ite {condition : Prop} [Decidable condition] {yes no : Costed α} {κ : Costs}
    {bound : Nat} (yesFits : yes.Within κ bound) (noFits : no.Within κ bound) :
    (if condition then yes else no).Within κ bound := by
  split
  · exact yesFits
  · exact noFits

/-- A value read without an operation of its own. -/
@[inline] def pure (value : α) : Costed α :=
  ⟨value, fun _ n => n = 0, fun _ => ⟨0, rfl, fun _ same => same⟩⟩

/-- A stretch of constant work at a site. -/
@[inline] def op (site : Site) (value : α) : Costed α :=
  ⟨value, fun κ n => n = κ site, fun κ => ⟨κ site, rfl, fun _ same => same⟩⟩

/-- A stretch at a site before a computation. -/
@[inline] def charge (site : Site) (rest : Costed α) : Costed α :=
  ⟨rest.val, fun κ n => ∃ later, rest.work κ later ∧ n = κ site + later, fun κ => by
    obtain ⟨later, held, unique⟩ := rest.single κ
    exact ⟨κ site + later, ⟨later, held, rfl⟩, fun m ⟨other, work, same⟩ => by
      rw [same, unique other work]⟩⟩

/-- Sequential composition: the continuation reads the first result, and the work of the two
parts adds. -/
@[inline] def bind (first : Costed α) (next : α → Costed β) : Costed β :=
  ⟨(next first.val).val,
    fun κ n => ∃ here later, first.work κ here ∧ (next first.val).work κ later ∧
      n = here + later, fun κ => by
    obtain ⟨here, firstHeld, firstUnique⟩ := first.single κ
    obtain ⟨later, nextHeld, nextUnique⟩ := (next first.val).single κ
    exact ⟨here + later, ⟨here, later, firstHeld, nextHeld, rfl⟩,
      fun m ⟨a, b, firstWork, nextWork, same⟩ => by
        rw [same, firstUnique a firstWork, nextUnique b nextWork]⟩⟩

instance : Monad Costed where
  pure := Costed.pure
  bind := Costed.bind

theorem pure_val (value : α) : (pure value).val = value := rfl

theorem op_val (site : Site) (value : α) : (op site value).val = value := rfl

theorem charge_val (site : Site) (rest : Costed α) : (charge site rest).val = rest.val := rfl

theorem bind_val (first : Costed α) (next : α → Costed β) :
    (first >>= next).val = (next first.val).val := rfl

theorem pure_eq (value : α) : (Pure.pure value : Costed α) = Costed.pure value := rfl

theorem bind_eq (first : Costed α) (next : α → Costed β) :
    first >>= next = Costed.bind first next := rfl

theorem pure_within (value : α) (κ : Costs) : (pure value).Within κ 0 :=
  fun _ same => Nat.le_of_eq same

theorem op_within (site : Site) (value : α) (κ : Costs) : (op site value).Within κ (κ site) :=
  fun _ same => Nat.le_of_eq same

theorem charge_within {site : Site} {rest : Costed α} {κ : Costs} {bound : Nat}
    (fits : rest.Within κ bound) : (charge site rest).Within κ (κ site + bound) :=
  fun _ ⟨later, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_left (fits later work) _

/-- A sequence is bounded by a bound of its first part and a bound of its continuation at the
first result. -/
theorem bind_within {first : Costed α} {next : α → Costed β} {κ : Costs} {a b : Nat}
    (firstFits : first.Within κ a) (nextFits : (next first.val).Within κ b) :
    (first >>= next).Within κ (a + b) :=
  fun _ ⟨here, later, firstWork, nextWork, same⟩ => by
    rw [same]
    exact Nat.add_le_add (firstFits here firstWork) (nextFits later nextWork)

/-- A sequence is bounded by a bound of its first part and a bound of its continuation at each
result. -/
theorem bind_within_all {first : Costed α} {next : α → Costed β} {κ : Costs} {a b : Nat}
    (firstFits : first.Within κ a) (nextFits : ∀ value, (next value).Within κ b) :
    (first >>= next).Within κ (a + b) :=
  bind_within firstFits (nextFits first.val)

/-! ## Loops -/

/-- The work of a left fold: for each visit, `visit` for the loop's control and the step's
work at the accumulator the fold reaches there, and `visit` for its end. -/
def foldlWork (step : β → α → Costed β) : β → List α → Costs → Nat → Prop
  | _, [], κ, n => n = κ .visit
  | acc, item :: rest, κ, n => ∃ here later, (step acc item).work κ here ∧
      foldlWork step (step acc item).val rest κ later ∧ n = κ .visit + here + later

theorem foldlWork_single (step : β → α → Costed β) (κ : Costs) (items : List α) :
    ∀ acc : β, ∃ n, foldlWork step acc items κ n ∧ ∀ m, foldlWork step acc items κ m → m = n := by
  induction items with
  | nil => exact fun _ => ⟨κ .visit, rfl, fun _ same => same⟩
  | cons item rest ih =>
    intro acc
    obtain ⟨here, stepHeld, stepUnique⟩ := (step acc item).single κ
    obtain ⟨later, restHeld, restUnique⟩ := ih (step acc item).val
    refine ⟨κ .visit + here + later, ⟨here, later, stepHeld, restHeld, rfl⟩, fun m work => ?_⟩
    obtain ⟨a, b, stepWork, restWork, same⟩ := work
    rw [same, stepUnique a stepWork, restUnique b restWork]

/-- A left fold over a list. Its value is the library fold of the steps' values. -/
@[inline] def foldl (step : β → α → Costed β) (init : β) (items : List α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init, fun κ => foldlWork step init items κ,
    fun κ => foldlWork_single step κ items init⟩

theorem foldl_val (step : β → α → Costed β) (init : β) (items : List α) :
    (foldl step init items).val = items.foldl (fun acc item => (step acc item).val) init := rfl

theorem foldlWork_within (step : β → α → Costed β) (κ : Costs) (bound : Nat)
    (items : List α) (each : ∀ acc, ∀ item ∈ items, (step acc item).Within κ bound) :
    ∀ acc n, foldlWork step acc items κ n →
      n ≤ items.length * (κ .visit + bound) + κ .visit := by
  induction items with
  | nil =>
    intro _ n work
    have same : n = κ .visit := work
    omega
  | cons item rest ih =>
    intro acc n work
    obtain ⟨here, later, stepWork, restWork, same⟩ := work
    have headFits := each acc item (List.mem_cons_self ..) here stepWork
    have restFits := ih (fun acc item member => each acc item (List.mem_cons_of_mem _ member))
      _ later restWork
    rw [same, List.length_cons, Nat.succ_mul]
    omega

/-- A fold whose every step is within `bound` is within its trip count times the visit and
that bound, and a visit for its end. The bound holds at every accumulator, so no reasoning about
the values the fold computes is needed. -/
theorem foldl_within {step : β → α → Costed β} {init : β} {items : List α} {κ : Costs}
    {bound : Nat} (each : ∀ acc, ∀ item ∈ items, (step acc item).Within κ bound) :
    (foldl step init items).Within κ (items.length * (κ .visit + bound) + κ .visit) :=
  foldlWork_within step κ bound items each init

/-- A left fold over an array, visiting its elements in order. -/
@[inline] def foldlArray (step : β → α → Costed β) (init : β) (items : Array α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    fun κ => foldlWork step init items.toList κ,
    fun κ => foldlWork_single step κ items.toList init⟩

theorem foldlArray_val (step : β → α → Costed β) (init : β) (items : Array α) :
    (foldlArray step init items).val = items.foldl (fun acc item => (step acc item).val) init :=
  rfl

theorem foldlArray_within {step : β → α → Costed β} {init : β} {items : Array α} {κ : Costs}
    {bound : Nat} (each : ∀ acc, ∀ item ∈ items.toList, (step acc item).Within κ bound) :
    (foldlArray step init items).Within κ (items.size * (κ .visit + bound) + κ .visit) := by
  have counted := foldlWork_within step κ bound items.toList each init
  rw [Array.length_toList] at counted
  exact counted

/-- The work of a mapping loop: for each visit, `visit` and the work of the mapped operation, and
`visit` for its end. -/
def mapWork (operation : α → Costed β) : List α → Costs → Nat → Prop
  | [], κ, n => n = κ .visit
  | item :: rest, κ, n => ∃ here later, (operation item).work κ here ∧
      mapWork operation rest κ later ∧ n = κ .visit + here + later

theorem mapWork_single (operation : α → Costed β) (κ : Costs) (items : List α) :
    ∃ n, mapWork operation items κ n ∧ ∀ m, mapWork operation items κ m → m = n := by
  induction items with
  | nil => exact ⟨κ .visit, rfl, fun _ same => same⟩
  | cons item rest ih =>
    obtain ⟨here, opHeld, opUnique⟩ := (operation item).single κ
    obtain ⟨later, restHeld, restUnique⟩ := ih
    refine ⟨κ .visit + here + later, ⟨here, later, opHeld, restHeld, rfl⟩, fun m work => ?_⟩
    obtain ⟨a, b, opWork, restWork, same⟩ := work
    rw [same, opUnique a opWork, restUnique b restWork]

/-- A mapping loop whose every operation is within `bound` is within its trip count times the
visit and that bound, and a visit for its end. -/
theorem mapWork_within {operation : α → Costed β} {κ : Costs} {bound : Nat} :
    ∀ items : List α, (∀ item ∈ items, (operation item).Within κ bound) →
      ∀ n, mapWork operation items κ n → n ≤ items.length * (κ .visit + bound) + κ .visit := by
  intro items
  induction items with
  | nil =>
    intro _ n work
    have same : n = κ .visit := work
    omega
  | cons item rest ih =>
    intro each n work
    obtain ⟨here, later, opWork, restWork, same⟩ := work
    have headFits := each item (List.mem_cons_self ..) here opWork
    have restFits := ih (fun item member => each item (List.mem_cons_of_mem _ member)) later
      restWork
    rw [same, List.length_cons, Nat.succ_mul]
    omega

/-- A map over a list: the loop of `List.mapTR`, then its further passes (`Library.map`), the
reversal of its result. -/
@[inline] def map (operation : α → Costed β) (items : List α) : Costed (List β) :=
  ⟨items.map fun item => (operation item).val,
    fun κ n => ∃ loop, mapWork operation items κ loop ∧
      n = loop + (Library.map.passes - 1) * (items.length * κ .visit + κ .visit),
    fun κ => by
      obtain ⟨loop, held, unique⟩ := mapWork_single operation κ items
      exact ⟨_, ⟨loop, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem map_val (operation : α → Costed β) (items : List α) :
    (map operation items).val = items.map fun item => (operation item).val := rfl

theorem map_within {operation : α → Costed β} {items : List α} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items, (operation item).Within κ bound) :
    (map operation items).Within κ (items.length * (κ .visit + bound) + κ .visit +
      (Library.map.passes - 1) * (items.length * κ .visit + κ .visit)) :=
  fun _ ⟨loop, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (mapWork_within items each loop work) _

/-- A vector of one repeated element: one visit for each element written, and one for the
pass's end. -/
@[inline] def replicate (count : Nat) (value : α) : Costed (Vector α count) :=
  ⟨Vector.replicate count value, fun κ n => n = count * κ .visit + κ .visit,
    fun κ => ⟨count * κ .visit + κ .visit, rfl, fun _ same => same⟩⟩

theorem replicate_val (count : Nat) (value : α) :
    (replicate count value).val = Vector.replicate count value := rfl

theorem replicate_within (count : Nat) (value : α) (κ : Costs) :
    (replicate count value).Within κ (count * κ .visit + κ .visit) :=
  fun _ same => Nat.le_of_eq same

/-- The index of the first element of `items` whose costed test holds, by the library search
`Array.findIdx?` (`Library.findIdx`), with the equation that names it: for each element a visit
and the work of its test, and a visit for the search's end, whether the search stops early or
not. -/
@[inline] def findIdx? (items : Array α) (test : α → Costed Bool) :
    Costed {found : Option Nat // items.findIdx? (fun item => (test item).val) = found} :=
  ⟨⟨items.findIdx? fun item => (test item).val, rfl⟩, fun κ => mapWork test items.toList κ,
    fun κ => mapWork_single test κ items.toList⟩

theorem findIdx?_val (items : Array α) (test : α → Costed Bool) :
    (findIdx? items test).val.val = items.findIdx? fun item => (test item).val := rfl

/-- A search whose every test is within `bound` is within its size times the visit and that
bound, and a visit for its end. -/
theorem findIdx?_within {items : Array α} {test : α → Costed Bool} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items.toList, (test item).Within κ bound) :
    (findIdx? items test).Within κ (items.size * (κ .visit + bound) + κ .visit) := by
  have counted := mapWork_within items.toList each
  rw [Array.length_toList] at counted
  exact counted

end Costed

end Acorn
