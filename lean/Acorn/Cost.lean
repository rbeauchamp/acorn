/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# The work of an executed computation

A definition whose work Acorn bounds returns a `Costed` value: its result together with the
work of computing it. The work is a type former and a proof about a cost model, which the
compiler erases, so a definition that returns `Costed α` compiles to the code of its result
alone, and reading `val` compiles to nothing (a trust assumption, below). The definition that
runs is the definition whose work the bounds count, and a definition with the plain result type
is the `val` of its costed definition.

**Sites.** A *site* (`Site`) is a kind of constant stretch of executed code, and its docstring names
the operations its charge marks. What a charge counts is its *segment*, defined here once:

- the *trace* is the word operations the compiled code runs during one call of a bounded part, as
  one flat sequence. The bounded part here is the first part, from the step's entry until the action
  is released, including the `Chosen` record built after selection's last charge. An operation
  inside a callee is itself an operation of the trace, at its own position;
- the *charge points* are an `op` at the value it charges, a `charge` before the computation it
  wraps, a loop combinator's visits at fixed points of each pass (each element's visit before that
  element's step, which is its callback in a pass that runs one, and the pass's end visit after its
  last element), and a costed recursion's charges where the recursion makes them;
- each operation belongs to the segment of the first charge point at or after it, and the operations
  after the part's last charge point belong to that last one, so the segments partition the trace.

The segment of an operation is decided by its position alone, so a site's segment can include
operations its docstring does not name, and a site's named operations can lie in another charge's
segment: after the site's own point, or before a charge stacked ahead of it. `words site` is the
largest number of word operations of a segment at a charge point of that site, and `SiteBounds`
(`AcornVerif.Resource.Twin.SiteBounds`) is the hypothesis `words site ≤ κ site`, so `κ site` must
cover the largest segment of that site. A `visit` segment of the SwiftTD loops
(`learnFirstLoopGoCosted`, `learnSecondLoopGoCosted`, `planWeightsGoCosted`) can include the work of
a whole element and, in the first loop, a prune, and the first visits of the second and planning
loops can include operations their opens name, so `κ visit` must cover the largest visit segment.

Every segment is bounded by a constant of the code: every loop whose trip count depends on the
configuration or the state runs in a loop combinator or a costed recursion, which has a charge point
on each iteration, so no segment contains one. The cost discipline below requires this of costed
definitions, and the one-time compiled-call inventory of one build observed it of the twins. The
loops left inside a segment have trip counts fixed by the code: the three options and their slots,
the four meta actions, the 32 samples of a projection, the at most 15 doublings of the ranked
width's search (`rankExponentFrom`) and the at most 33 steps of `Portable.pow`. A cost model
(`Costs`) assigns each site a cost, and every work bound holds for every cost model. No theorem
derives the cost of a site in word operations; the scalar operations that the native resource audit
bounds are the operations with an extracted cost.

**Counting.** `op site value` is a stretch at the site's cost, `charge` puts a stretch before a
computation, and `bind` sequences two computations and adds their work; `Pure` and `Bind` are the
only instances, so `do` blocks sequence costed computations and nothing maps an uncosted
callback. Each loop combinator has as its value the library loop applied to its callbacks'
values, and as its work each callback's work once and the control of its row of the table
(`Library`, `Library.control`): each of the row's passes, a `visit` for each element and one for
the pass's end. A loop's bound is therefore `Library.work`: its trip count times a bound of one
callback, and its row's control. Every function a combinator takes is costed: the steps of
`foldl` and `foldlArray`, the operation of `map`, the test of `findIdx?` and the continuation of
`bind`. A recursion of Acorn's own is a costed recursion whose every recursive call is under a
charge and whose end is charged a visit.

**Bounds.** `x.Within κ bound` states that under the cost model `κ` the work of `x` is at most
`bound`. Every `Costed` value is built here, and its work is one number under each cost model
(`single`), so a bound is never vacuous (`within_iff`).

**What is trusted.** That the counted work covers each operation of the compiled code rests on
the cost discipline of the costed definitions. A combinator counts the work of every function
it takes, but not the computation of a value it takes. The values a costed definition passes
in, which are all its uncosted entry points, are:

- the value parameters of the combinators: the value of `pure`; the site and value of `op`;
  the site of `charge`; the count and element of `replicate`; the initial accumulator and the
  collection of `foldl` and `foldlArray`; the collection of `map`; the array of `findIdx?`
  (`bind` takes none);
- the terms a costed definition evaluates in its own body between combinators: its `let`
  values, its branch conditions and the scrutinees of its matches.

The private constructor's work field is set only by the combinators here.

Each must be computed by a stretch that runs no loop and calls no costed definition, a loop
must run only in a loop combinator or a costed definition, and each path to a recursive call
must pass a charge. The combinators cannot enforce it: `pure` accepts any value, so
`Costed.pure (state.step config features reward)` has work zero although its value runs the
learner. Lean's logic gives a pure term no operational meaning, so no theorem states the
discipline; it is a syntactic property, checked by reading until the cost-closed rule that
rbeauchamp/regula#333 proposes checks it. That a library loop makes the passes `Library.passes`
states is read once from the library's runtime implementation, which each row of `Library`
cites. That the compiler erases the work, since `work` is a type former and `single` a proof,
and leaves the code of the value as written is a trust assumption on the compiler's erasure. A
comparison of the generated C of the costed learner with that of the same definitions written
without work found them equal up to renaming; it is an observation of one build, which no gate
repeats. That the segment of each charge of a site does at most the site's cost in word
operations is the hypothesis of each bound in word operations.

**What is not counted:** allocation and release of objects, reference counting, the copy of an
array that is shared when it is written (issue 84 of the repository), the one-time
initialization of a closed term, a value with no free variable that the compiled code builds
once for the process and then reads, cache behaviour and time.
No unit here is a second, a byte or an instruction of a particular processor.
-/

namespace Acorn

/-- The constant stretches of the agent's step. Each constructor names the operations its
charge marks; a charge counts its segment (the module's **Sites**). -/
inductive Site where
  /-- The control of one visit of a loop: its test, its advance and its branch. -/
  | visit
  /-- One binary32 addition of an ordered sum, with the read of its term. -/
  | sumTerm
  /-- The read of one stored element into a list or vector being built, or as the first
  accumulator of a fold. -/
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
  /-- A fresh transient record apart from its zero register vectors. -/
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
  /-- A managed learner's record after one entry: its next phase and the record itself. -/
  | managedEntry
  /-- A row credit's test of a pending restart. -/
  | creditRestart
  /-- The error or target a learner entry reads that its caller forms: a terminal credit's
  error and trace decay, a stopped trajectory's error, a ranked row's discounted target or a
  deviation learner's target. -/
  | learnerError
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
  /-- A policy's tie threshold: its maximum less the tie window. -/
  | tieThreshold
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
  /-- The projection of an exploration rate: a derived rate, with its fresh-feature fallback,
  or an annealed rate. -/
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
  /-- One word hashed into a feature slot: a sensor word for one tiling, a unit or a model
  age. -/
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
  /-- A fresh learner's rails and record, or a fresh question's projected zero weight, apart
  from their vectors. -/
  | initialState
  /-- One unit's Demon-0 weight tested for a ranking candidate, with its feature slot computed. -/
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
  /-- Selection's branch tests and phase write. -/
  | select
  /-- The agent's clock advance and the chosen value's record. -/
  | choose

/-- A cost model: the cost of each site, counted once for the segment of each charge of the
site. -/
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
  /-- `List.flatMap`, replaced by `List.flatMapTR` (`List.flatMap_eq_flatMapTR`): a loop over the
  list, then `Array.toList` of the results, whose end is charged as a second pass over the list
  and whose elements are counted by `flatMapResult`. -/
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
  /-- `List.drop` (`Init.Data.List.Basic`), which no `csimp` replaces: a structural recursion
  over the elements it drops, one loop. -/
  | drop
  /-- `List.dropLast`, replaced by `List.dropLastTR` (`List.dropLast_eq_dropLastTR`):
  `List.toArray` (two), `Array.pop`, then `Array.toList` (one). -/
  | dropLast
  /-- `List.zipIdx`, replaced by `List.zipIdxTR` (`List.zipIdx_eq_zipIdxTR`): `List.toArray`
  (two), then `Array.foldr` (one). -/
  | zipIdx
  /-- `List.sum` of integers, a `List.foldr`. The specialization that runs is the toolchain's
  `List.foldr` at `Lean.Omega.IntList.sum` (`Init.Omega.IntList`), whose compiled code is the
  structural recursion, not `List.foldrTR`: one loop. -/
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
  | .flatMap => 2
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
  | .drop => 1
  | .dropLast => 3
  | .zipIdx => 3
  | .sum => 1
  | .fillVacant => 1

/-- The loop control of the library loop `row` over `count` elements: each of its passes visits
each element once and ends with one visit. -/
abbrev Library.control (row : Library) (visit count : Nat) : Nat :=
  row.passes * (count * visit + visit)

/-- The work of the library loop `row` over `count` elements whose callback is within `bound` at
each element: the callback once for each element, and the loop's control. -/
abbrev Library.work (row : Library) (visit count bound : Nat) : Nat :=
  count * bound + row.control visit count

/-- A loop over more elements has more control. -/
theorem Library.control_mono (row : Library) {visit count limit : Nat} (fits : count ≤ limit) :
    row.control visit count ≤ row.control visit limit :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right visit fits) visit)

/-- A loop over more elements, each with a larger callback bound, does more work. -/
theorem Library.work_mono (row : Library) {visit count limit bound most : Nat}
    (fits : count ≤ limit) (within : bound ≤ most) :
    row.work visit count bound ≤ row.work visit limit most :=
  Nat.add_le_add (Nat.mul_le_mul fits within) (row.control_mono fits)

/-- A result together with the work of computing it. The constructor is private, so every
`Costed` value is built by the combinators below. -/
structure Costed (α : Type) where
  private mk ::
  /-- The result. -/
  val : α
  /-- `work κ n`: under the cost model `κ`, computing the result does `n` work. A type former,
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

/-- The `pure` of `do` blocks. There is no `Functor` or `Monad` instance, whose derived `map`
and `seq` would apply a callback that is not costed. -/
instance : Pure Costed := ⟨Costed.pure⟩

/-- The sequencing of `do` blocks. -/
instance : Bind Costed := ⟨Costed.bind⟩

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

/-- The work of the steps of a left fold: each step's work at the accumulator the fold reaches
there. The loop's control is charged from its row of `Library`. -/
def foldlSteps (step : β → α → Costed β) : β → List α → Costs → Nat → Prop
  | _, [], _, n => n = 0
  | acc, item :: rest, κ, n => ∃ here later, (step acc item).work κ here ∧
      foldlSteps step (step acc item).val rest κ later ∧ n = here + later

theorem foldlSteps_single (step : β → α → Costed β) (κ : Costs) (items : List α) :
    ∀ acc : β, ∃ n, foldlSteps step acc items κ n ∧ ∀ m, foldlSteps step acc items κ m → m = n := by
  induction items with
  | nil => exact fun _ => ⟨0, rfl, fun _ same => same⟩
  | cons item rest ih =>
    intro acc
    obtain ⟨here, stepHeld, stepUnique⟩ := (step acc item).single κ
    obtain ⟨later, restHeld, restUnique⟩ := ih (step acc item).val
    refine ⟨here + later, ⟨here, later, stepHeld, restHeld, rfl⟩, fun m work => ?_⟩
    obtain ⟨a, b, stepWork, restWork, same⟩ := work
    rw [same, stepUnique a stepWork, restUnique b restWork]

/-- The steps of a fold whose every step is within `bound` are within the trip count times that
bound. The bound holds at every accumulator, so no reasoning about the values the fold computes
is needed. -/
theorem foldlSteps_within (step : β → α → Costed β) (κ : Costs) (bound : Nat)
    (items : List α) (each : ∀ acc, ∀ item ∈ items, (step acc item).Within κ bound) :
    ∀ acc n, foldlSteps step acc items κ n → n ≤ items.length * bound := by
  induction items with
  | nil =>
    intro _ n work
    have same : n = 0 := work
    omega
  | cons item rest ih =>
    intro acc n work
    obtain ⟨here, later, stepWork, restWork, same⟩ := work
    have headFits := each acc item (List.mem_cons_self ..) here stepWork
    have restFits := ih (fun acc item member => each acc item (List.mem_cons_of_mem _ member))
      _ later restWork
    rw [same, List.length_cons, Nat.succ_mul]
    omega

/-- A left fold over a list (`Library.foldl`). Its value is the library fold of the steps'
values; its work is its steps' work and the control of its row. -/
@[inline] def foldl (step : β → α → Costed β) (init : β) (items : List α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    fun κ n => ∃ steps, foldlSteps step init items κ steps ∧
      n = steps + Library.foldl.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := foldlSteps_single step κ items init
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem foldl_val (step : β → α → Costed β) (init : β) (items : List α) :
    (foldl step init items).val = items.foldl (fun acc item => (step acc item).val) init := rfl

/-- A fold whose every step is within `bound` is within its row's work at that bound. -/
theorem foldl_within {step : β → α → Costed β} {init : β} {items : List α} {κ : Costs}
    {bound : Nat} (each : ∀ acc, ∀ item ∈ items, (step acc item).Within κ bound) :
    (foldl step init items).Within κ (Library.foldl.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (foldlSteps_within step κ bound items each init steps work) _

/-- A left fold over an array (`Library.foldlArray`), visiting its elements in order. -/
@[inline] def foldlArray (step : β → α → Costed β) (init : β) (items : Array α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    fun κ n => ∃ steps, foldlSteps step init items.toList κ steps ∧
      n = steps + Library.foldlArray.control (κ .visit) items.size,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := foldlSteps_single step κ items.toList init
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem foldlArray_val (step : β → α → Costed β) (init : β) (items : Array α) :
    (foldlArray step init items).val = items.foldl (fun acc item => (step acc item).val) init :=
  rfl

theorem foldlArray_within {step : β → α → Costed β} {init : β} {items : Array α} {κ : Costs}
    {bound : Nat} (each : ∀ acc, ∀ item ∈ items.toList, (step acc item).Within κ bound) :
    (foldlArray step init items).Within κ (Library.foldlArray.work (κ .visit) items.size bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := foldlSteps_within step κ bound items.toList each init steps work
    rw [Array.length_toList] at counted
    exact Nat.add_le_add_right counted _

/-- The work of the operations of a mapping loop: each operation's work. The loop's control is
charged from its row of `Library`. -/
def mapSteps (operation : α → Costed β) : List α → Costs → Nat → Prop
  | [], _, n => n = 0
  | item :: rest, κ, n => ∃ here later, (operation item).work κ here ∧
      mapSteps operation rest κ later ∧ n = here + later

theorem mapSteps_single (operation : α → Costed β) (κ : Costs) (items : List α) :
    ∃ n, mapSteps operation items κ n ∧ ∀ m, mapSteps operation items κ m → m = n := by
  induction items with
  | nil => exact ⟨0, rfl, fun _ same => same⟩
  | cons item rest ih =>
    obtain ⟨here, opHeld, opUnique⟩ := (operation item).single κ
    obtain ⟨later, restHeld, restUnique⟩ := ih
    refine ⟨here + later, ⟨here, later, opHeld, restHeld, rfl⟩, fun m work => ?_⟩
    obtain ⟨a, b, opWork, restWork, same⟩ := work
    rw [same, opUnique a opWork, restUnique b restWork]

/-- The operations of a mapping loop, each within `bound`, are within the trip count times that
bound. -/
theorem mapSteps_within {operation : α → Costed β} {κ : Costs} {bound : Nat} :
    ∀ items : List α, (∀ item ∈ items, (operation item).Within κ bound) →
      ∀ n, mapSteps operation items κ n → n ≤ items.length * bound := by
  intro items
  induction items with
  | nil =>
    intro _ n work
    have same : n = 0 := work
    omega
  | cons item rest ih =>
    intro each n work
    obtain ⟨here, later, opWork, restWork, same⟩ := work
    have headFits := each item (List.mem_cons_self ..) here opWork
    have restFits := ih (fun item member => each item (List.mem_cons_of_mem _ member)) later
      restWork
    rw [same, List.length_cons, Nat.succ_mul]
    omega

/-- A map over a list (`Library.map`): its operations' work and the control of its row, the loop
of `List.mapTR` and the reversal of its result. -/
@[inline] def map (operation : α → Costed β) (items : List α) : Costed (List β) :=
  ⟨items.map fun item => (operation item).val,
    fun κ n => ∃ steps, mapSteps operation items κ steps ∧
      n = steps + Library.map.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single operation κ items
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem map_val (operation : α → Costed β) (items : List α) :
    (map operation items).val = items.map fun item => (operation item).val := rfl

theorem map_within {operation : α → Costed β} {items : List α} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items, (operation item).Within κ bound) :
    (map operation items).Within κ (Library.map.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (mapSteps_within items each steps work) _

/-- A vector of one repeated element (`Library.replicate`): the control of its row. -/
@[inline] def replicate (count : Nat) (value : α) : Costed (Vector α count) :=
  ⟨Vector.replicate count value, fun κ n => n = Library.replicate.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem replicate_val (count : Nat) (value : α) :
    (replicate count value).val = Vector.replicate count value := rfl

theorem replicate_within (count : Nat) (value : α) (κ : Costs) :
    (replicate count value).Within κ (Library.replicate.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

/-- The index of the first element of `items` whose costed test holds, by the library search
`Array.findIdx?` (`Library.findIdx`), with the equation that names it: the work of each
element's test, whether the search stops early or not, and the control of its row. -/
@[inline] def findIdx? (items : Array α) (test : α → Costed Bool) :
    Costed {found : Option Nat // items.findIdx? (fun item => (test item).val) = found} :=
  ⟨⟨items.findIdx? fun item => (test item).val, rfl⟩,
    fun κ n => ∃ steps, mapSteps test items.toList κ steps ∧
      n = steps + Library.findIdx.control (κ .visit) items.size,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single test κ items.toList
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem findIdx?_val (items : Array α) (test : α → Costed Bool) :
    (findIdx? items test).val.val = items.findIdx? fun item => (test item).val := rfl

/-- A search whose every test is within `bound` is within its row's work at that bound. -/
theorem findIdx?_within {items : Array α} {test : α → Costed Bool} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items.toList, (test item).Within κ bound) :
    (findIdx? items test).Within κ (Library.findIdx.work (κ .visit) items.size bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within items.toList each steps work
    rw [Array.length_toList] at counted
    exact Nat.add_le_add_right counted _

end Costed

end Acorn
