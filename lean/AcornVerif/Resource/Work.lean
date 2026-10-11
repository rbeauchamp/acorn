/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Cost

/-!
# Work of the definitions not yet costed

The learner's executed definitions are the values of costed definitions (`Acorn.Costed`), so the
loops their bounds count are the loops that run. The other definitions of the agent's step are
not yet costed. For each of them a **twin** here is a `Costed` computation, a value with a `Nat`
of work, written beside the executed definition to follow its control flow. A twin's value
theorem states that its value is the executed definition's, by `rfl`, by induction on the same
recursion, or, through `via`, by reading.

**What a twin establishes.** A value theorem does not tie a twin's work to the executed code:
Lean's logic gives a pure term no operational meaning, and a twin of the same value with less
work would satisfy the same theorem. That a twin's loops and charges are those of the executed
definition is a correspondence by reading, so a bound proved here bounds the twin, and bounds
the executed code only through that reading. A definition that is the value of its costed
definition, as each of the learner's is, is bounded through that definition instead
(`AcornVerif.Resource.LearnerWork`).

**Loops.** Each loop combinator below has as its value the library loop applied to the values of
its parts, and as its work each part's work once and the control of the library loop's row of
`Acorn.Library` (`Acorn.Library.control`): each of the row's passes, a visit for each element and
one for the pass's end. A loop's bound is therefore `Acorn.Library.work`: its trip count times a
bound of one part, and its row's control (`foldl_work_le`, `mapSteps_le`, `ofFn_work_le`). A
recursion of Acorn's own is one pass of its own visits (`pass`).

**Scans.** A library function whose every visit is constant work is a **scan**, charged the
control of its row over the collection it names (`scanList`, `scanArray`, `scanVector`). Each
scan names its row where it is used, so each count is stated once, in the table.

**What is counted.** Each loop visit is charged `visit`, and each stretch of constant work is
charged where a twin says `Costed.op` or `Costed.charge`, at the cost a cost model assigns its
site (`Acorn.Site`). Every bound holds for every cost model.

**What is not counted:** allocation and release of objects, reference counting, the copy of
an array that is shared when it is written (issue 84 of the repository; the write itself is
charged as part of its stretch), cache behaviour and time. No unit here is a second, a byte
or an instruction of a particular processor. The work is a `Nat` of the proofs; nothing here
runs in the agent.
-/

namespace AcornVerif.Resource

/-- A value together with the work charged to the computation that produced it. -/
structure Costed (α : Type) where
  /-- The value; for a twin, definitionally the executed computation's. -/
  val : α
  /-- The work charged to the computation. -/
  work : Nat

/-! ## Passes -/

/-- The work of one pass of a recursion of Acorn's own over `count` elements: a visit for its
control and at most `bound` for each element, and one visit for its end. -/
abbrev pass (visit count bound : Nat) : Nat := count * (visit + bound) + visit

/-- A pass over more elements, each with a larger bound, does more work. -/
theorem pass_mono {visit count limit bound most : Nat} (fits : count ≤ limit)
    (within : bound ≤ most) : pass visit count bound ≤ pass visit limit most :=
  Nat.add_le_add_right (Nat.mul_le_mul fits (Nat.add_le_add_left within visit)) visit

namespace Costed

variable {α β : Type}

/-- A value read without an operation of its own. -/
@[reducible] def pure (value : α) : Costed α := ⟨value, 0⟩

/-- A stretch of constant work, at the given cost. -/
@[reducible] def op (cost : Nat) (value : α) : Costed α := ⟨value, cost⟩

/-- Sequential composition: the continuation reads the first value, and the work of
the two parts adds. -/
@[reducible] def bind (first : Costed α) (next : α → Costed β) : Costed β :=
  ⟨(next first.val).val, first.work + (next first.val).work⟩

/-- Charge an operation of the given cost before a computation. -/
@[reducible] def charge (cost : Nat) (rest : Costed α) : Costed α := ⟨rest.val, cost + rest.work⟩

/-- The executed value with the work of a twin of it. The twin's value theorem makes its
value the executed one; `via` is used where the executed value carries a proof that
names the executed expression, so the enclosing twin keeps that expression. -/
@[reducible] def via (value : α) (twin : Costed β) : Costed α := ⟨value, twin.work⟩

/-- The work of a twin whose value the enclosing computation does not read: the enclosing
twin follows the executed definition's control flow and reads the executed values. -/
@[reducible] def discard (twin : Costed α) : Costed Unit := ⟨(), twin.work⟩

/-- The `pure` of a twin's `do` blocks. There is no `Functor` or `Monad` instance, whose derived
`map` and `seq` would apply a callback without counting its work. -/
instance : Pure Costed := ⟨Costed.pure⟩

/-- The sequencing of a twin's `do` blocks. -/
instance : Bind Costed := ⟨Costed.bind⟩

/-- The value of a sequence is the continuation's value at the first value. -/
theorem bind_val (first : Costed α) (next : α → Costed β) :
    (first >>= next).val = (next first.val).val := rfl

/-- The work of a sequence is the sum of the work of its parts. -/
theorem bind_work (first : Costed α) (next : α → Costed β) :
    (first >>= next).work = first.work + (next first.val).work := rfl

/-- A sequence is bounded by a bound of its first part and a bound of its continuation
at every value. -/
theorem bind_work_le {first : Costed α} {next : α → Costed β} {a b : Nat}
    (firstFits : first.work ≤ a) (nextFits : ∀ value, (next value).work ≤ b) :
    (first >>= next).work ≤ a + b :=
  Nat.add_le_add firstFits (nextFits _)

/-- A sequence is bounded by a bound of its first part and a bound of its continuation
at the first part's value. -/
theorem bind_work_le_at {first : Costed α} {next : α → Costed β} {a b : Nat}
    (firstFits : first.work ≤ a) (nextFits : (next first.val).work ≤ b) :
    (first >>= next).work ≤ a + b :=
  Nat.add_le_add firstFits nextFits

/-- A charged computation is bounded by its charge and a bound of the rest. -/
theorem charge_work_le {cost bound : Nat} {rest : Costed α} (fits : rest.work ≤ bound) :
    (charge cost rest).work ≤ cost + bound :=
  Nat.add_le_add_left fits cost

/-- A discarded twin keeps its work. -/
theorem discard_work_le {twin : Costed α} {bound : Nat} (fits : twin.work ≤ bound) :
    (discard twin).work ≤ bound := fits

/-- A branch: the value and the work of the branch the condition selects. The
selection is an operation of the enclosing stretch. -/
@[reducible] def ite (condition : Prop) [Decidable condition] (yes no : Costed α) :
    Costed α :=
  ⟨if condition then yes.val else no.val, if condition then yes.work else no.work⟩

/-- A branch's work is at most the larger work of its two branches. -/
theorem ite_work_le (condition : Prop) [Decidable condition] (yes no : Costed α) :
    (ite condition yes no).work ≤ max yes.work no.work := by
  unfold ite
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

/-- A branch is bounded by a bound of both of its branches. -/
theorem ite_work_bound (condition : Prop) [Decidable condition] {yes no : Costed α} {bound : Nat}
    (yesFits : yes.work ≤ bound) (noFits : no.work ≤ bound) :
    (ite condition yes no).work ≤ bound := by
  unfold ite
  split
  · exact yesFits
  · exact noFits

/-- A branch whose arms read the decision. -/
@[reducible] def dite (condition : Prop) [Decidable condition]
    (yes : condition → Costed α) (no : ¬condition → Costed α) : Costed α :=
  ⟨if h : condition then (yes h).val else (no h).val,
    if h : condition then (yes h).work else (no h).work⟩

/-- A dependent branch's work is bounded by a bound of both arms. -/
theorem dite_work_le (condition : Prop) [Decidable condition]
    (yes : condition → Costed α) (no : ¬condition → Costed α) (bound : Nat)
    (yesBound : ∀ h, (yes h).work ≤ bound) (noBound : ∀ h, (no h).work ≤ bound) :
    (dite condition yes no).work ≤ bound := by
  unfold dite
  split
  · exact yesBound _
  · exact noBound _

/-- A partial step: the continuation runs only on a present value. -/
@[reducible] def optBind (first : Costed (Option α)) (next : α → Costed (Option β)) :
    Costed (Option β) :=
  ⟨first.val.bind fun value => (next value).val,
    first.work + match first.val with
      | none => 0
      | some value => (next value).work⟩

/-- A partial step's work is the first part's plus a bound of the continuation. -/
theorem optBind_work_le (first : Costed (Option α)) (next : α → Costed (Option β))
    (bound : Nat) (each : ∀ value, (next value).work ≤ bound) :
    (optBind first next).work ≤ first.work + bound := by
  unfold optBind
  dsimp only
  split
  · exact Nat.add_le_add_left (Nat.zero_le _) _
  · exact Nat.add_le_add_left (each _) _

/-! ## Arithmetic of bounds -/

/-- Larger bounds of both branches bound the larger branch. -/
theorem max_le_max {a b c d : Nat} (left : a ≤ c) (right : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr
    ⟨Nat.le_trans left (Nat.le_max_left _ _), Nat.le_trans right (Nat.le_max_right _ _)⟩

/-- One more visit of a loop: a visit within the per-visit bound followed by the rest. -/
theorem visit_le {visit rest count perVisit exit : Nat} (fits : visit ≤ perVisit)
    (restFits : rest ≤ count * perVisit + exit) :
    visit + rest ≤ (count + 1) * perVisit + exit := by
  rw [Nat.succ_mul]
  omega

/-! ## Sums of work over a collection -/

/-- A sum of terms each at most `bound` is at most the count times `bound`. -/
theorem sum_map_le (items : List α) (term : α → Nat) (bound : Nat)
    (each : ∀ item ∈ items, term item ≤ bound) :
    (items.map term).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons head rest ih =>
    have headBound := each head (List.mem_cons_self ..)
    have restBound := ih (fun item member => each item (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- A sum over a shorter collection with the same bound of each term is smaller. -/
theorem length_mul_le {count limit bound : Nat} (fits : count ≤ limit) :
    count * bound ≤ limit * bound :=
  Nat.mul_le_mul_right _ fits

/-! ## Loops -/

/-- The work of the steps of a left fold: each step's work at the accumulator the executed fold
reaches there. -/
def foldlSteps (step : β → α → Costed β) : β → List α → Nat
  | _, [] => 0
  | acc, item :: rest => (step acc item).work + foldlSteps step (step acc item).val rest

/-- A left fold over a list (`Acorn.Library.foldl`): its steps' work and its row's control. Its
value is the executed fold of the steps' values. -/
@[reducible] def foldl (visit : Nat) (step : β → α → Costed β) (init : β) (items : List α) :
    Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    foldlSteps step init items + Acorn.Library.foldl.control visit items.length⟩

/-- The steps of a fold, each at most `bound`, are at most the trip count times that bound. The
bound holds at every accumulator, so no reasoning about the values the fold computes is
needed. -/
theorem foldlSteps_le (bound : Nat) (step : β → α → Costed β)
    (items : List α) (each : ∀ acc, ∀ item ∈ items, (step acc item).work ≤ bound) :
    ∀ init, foldlSteps step init items ≤ items.length * bound := by
  induction items with
  | nil => intro init; simp [foldlSteps]
  | cons head rest ih =>
    intro init
    have headBound := each init head (List.mem_cons_self ..)
    have restBound := ih (fun acc item member => each acc item (List.mem_cons_of_mem _ member))
      (step init head).val
    simp only [foldlSteps, List.length_cons, Nat.succ_mul]
    omega

/-- A fold's work, by the bound of each step. -/
theorem foldl_work_le (visit bound : Nat) (step : β → α → Costed β) (init : β)
    (items : List α) (each : ∀ acc, ∀ item ∈ items, (step acc item).work ≤ bound) :
    (foldl visit step init items).work ≤ Acorn.Library.foldl.work visit items.length bound :=
  Nat.add_le_add_right (foldlSteps_le bound step items each init) _

/-- The work of the operations of a mapping loop: each operation's work. -/
@[reducible] def mapSteps (operation : α → Costed β) (items : List α) : Nat :=
  (items.map fun item => (operation item).work).sum

/-- The operations of a mapping loop, each at most `bound`, are at most the trip count times that
bound. -/
theorem mapSteps_le (bound : Nat) (operation : α → Costed β) (items : List α)
    (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    mapSteps operation items ≤ items.length * bound :=
  sum_map_le items _ _ each

/-- A map over a list (`Acorn.Library.map`): its operations' work and its row's control, the
loop of `List.mapTR` and its reversal. -/
@[reducible] def map (visit : Nat) (operation : α → Costed β) (items : List α) :
    Costed (List β) :=
  ⟨items.map fun item => (operation item).val,
    mapSteps operation items + Acorn.Library.map.control visit items.length⟩

/-- A map's work, by the bound of each operation. -/
theorem map_work_le (visit bound : Nat) (operation : α → Costed β) (items : List α)
    (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    (map visit operation items).work ≤ Acorn.Library.map.work visit items.length bound :=
  Nat.add_le_add_right (mapSteps_le bound operation items each) _

/-- The elements of a list that pass a costed test, as `List.filter` (`Acorn.Library.filter`):
each test's work and its row's control, the loop of `List.filterTR` and its reversal. -/
@[reducible] def filter (visit : Nat) (test : α → Costed Bool) (items : List α) :
    Costed (List α) :=
  ⟨items.filter fun item => (test item).val,
    mapSteps test items + Acorn.Library.filter.control visit items.length⟩

/-- A filter's work, by the bound of each test. -/
theorem filter_work_le (visit bound : Nat) (test : α → Costed Bool) (items : List α)
    (each : ∀ item ∈ items, (test item).work ≤ bound) :
    (filter visit test items).work ≤ Acorn.Library.filter.work visit items.length bound :=
  Nat.add_le_add_right (mapSteps_le bound test items each) _

/-- A map over a vector (`Acorn.Library.vectorMap`), visiting its elements in order. -/
@[reducible] def mapVector {count : Nat} (visit : Nat) (operation : α → Costed β)
    (items : Vector α count) : Costed (Vector β count) :=
  ⟨items.map fun item => (operation item).val,
    mapSteps operation items.toList + Acorn.Library.vectorMap.control visit count⟩

/-- A vector map's work, by the bound of each operation. -/
theorem mapVector_work_le {count : Nat} (visit bound : Nat) (operation : α → Costed β)
    (items : Vector α count) (each : ∀ item ∈ items.toList, (operation item).work ≤ bound) :
    (mapVector visit operation items).work ≤ Acorn.Library.vectorMap.work visit count bound := by
  have counted := mapSteps_le bound operation items.toList each
  rw [Vector.length_toList] at counted
  exact Nat.add_le_add_right counted _

/-- A vector built from its indices (`Acorn.Library.ofFn`), visiting each index in order. -/
@[reducible] def ofFn {count : Nat} (visit : Nat) (operation : Fin count → Costed β) :
    Costed (Vector β count) :=
  ⟨Vector.ofFn fun index => (operation index).val,
    mapSteps operation (List.finRange count) + Acorn.Library.ofFn.control visit count⟩

/-- A built vector's work, by the bound of each operation. -/
theorem ofFn_work_le {count : Nat} (visit bound : Nat) (operation : Fin count → Costed β)
    (each : ∀ index, (operation index).work ≤ bound) :
    (ofFn visit operation).work ≤ Acorn.Library.ofFn.work visit count bound := by
  have counted := mapSteps_le bound operation (List.finRange count) (fun index _ => each index)
  rw [List.length_finRange] at counted
  exact Nat.add_le_add_right counted _

/-- A map whose results are concatenated, as `List.flatMap` (`Acorn.Library.flatMap`): the
operations' work and its row's control over the list. The operation's work counts the elements
of its result (`Acorn.Library.flatMapResult`). -/
@[reducible] def flatMap (visit : Nat) (operation : α → Costed (List β)) (items : List α) :
    Costed (List β) :=
  ⟨items.flatMap fun item => (operation item).val,
    mapSteps operation items + Acorn.Library.flatMap.control visit items.length⟩

/-- A concatenating map's work, by the bound of each operation. -/
theorem flatMap_work_le (visit bound : Nat) (operation : α → Costed (List β)) (items : List α)
    (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    (flatMap visit operation items).work ≤ Acorn.Library.flatMap.work visit items.length bound :=
  Nat.add_le_add_right (mapSteps_le bound operation items each) _

/-- A map over a vector that reads each element's index, as `Vector.mapFinIdx`
(`Acorn.Library.mapFinIdx`). -/
@[reducible] def mapFinIdx {count : Nat} (visit : Nat)
    (operation : (index : Nat) → α → index < count → Costed β) (items : Vector α count) :
    Costed (Vector β count) :=
  ⟨items.mapFinIdx fun index item bound => (operation index item bound).val,
    ((List.finRange count).map fun index =>
      (operation index.val items[index.val] index.isLt).work).sum +
      Acorn.Library.mapFinIdx.control visit count⟩

/-- An indexed vector map's work, by the bound of each operation. -/
theorem mapFinIdx_work_le {count : Nat} (visit bound : Nat)
    (operation : (index : Nat) → α → index < count → Costed β) (items : Vector α count)
    (each : ∀ index item inside, (operation index item inside).work ≤ bound) :
    (mapFinIdx visit operation items).work ≤ Acorn.Library.mapFinIdx.work visit count bound := by
  have counted := sum_map_le (List.finRange count)
    (fun index : Fin count => (operation index.val items[index.val] index.isLt).work)
    bound (fun index _ => each _ _ _)
  rw [List.length_finRange] at counted
  exact Nat.add_le_add_right counted _

/-- A filtering map over a list (`Acorn.Library.filterMap`): its operations' work and its row's
control, the loop of `List.filterMapTR` and the `Array.toList` of the kept elements. -/
@[reducible] def filterMap (visit : Nat) (operation : α → Costed (Option β))
    (items : List α) : Costed (List β) :=
  ⟨items.filterMap fun item => (operation item).val,
    mapSteps operation items + Acorn.Library.filterMap.control visit items.length⟩

/-- A filtering map's work, by the bound of each operation. -/
theorem filterMap_work_le (visit bound : Nat) (operation : α → Costed (Option β))
    (items : List α) (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    (filterMap visit operation items).work ≤
      Acorn.Library.filterMap.work visit items.length bound :=
  Nat.add_le_add_right (mapSteps_le bound operation items each) _

/-- A left fold over an array (`Acorn.Library.foldlArray`), visiting its elements in order. -/
@[reducible] def foldlArray (visit : Nat) (step : β → α → Costed β) (init : β)
    (items : Array α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    foldlSteps step init items.toList + Acorn.Library.foldlArray.control visit items.size⟩

/-- An array fold's value is the list fold's value over the same elements. -/
theorem foldlArray_val (visit : Nat) (step : β → α → Costed β) (init : β) (items : Array α) :
    (foldlArray visit step init items).val = (foldl visit step init items.toList).val :=
  (Array.foldl_toList ..).symm

/-- An array fold's work, by the bound of each step. -/
theorem foldlArray_work_le (visit bound : Nat) (step : β → α → Costed β) (init : β)
    (items : Array α) (each : ∀ acc, ∀ item ∈ items.toList, (step acc item).work ≤ bound) :
    (foldlArray visit step init items).work ≤
      Acorn.Library.foldlArray.work visit items.size bound := by
  have counted := foldlSteps_le bound step items.toList each init
  rw [Array.length_toList] at counted
  exact Nat.add_le_add_right counted _

/-- A vector of one repeated element (`Acorn.Library.replicate`): its row's control. -/
@[reducible] def replicate (visit count : Nat) (value : α) : Costed (Vector α count) :=
  ⟨Vector.replicate count value, Acorn.Library.replicate.control visit count⟩

/-- A scan of a list by the library function `row`, whose every visit is one loop-free
comparison or copy, whatever the scan returns: its row's control. The value is the executed
expression; the list is the one that expression scans. -/
@[reducible] def scanList (row : Acorn.Library) (visit : Nat) (items : List α) (value : β) :
    Costed β :=
  ⟨value, row.control visit items.length⟩

/-- A scan of an array by the library function `row`. -/
@[reducible] def scanArray (row : Acorn.Library) (visit : Nat) (items : Array α) (value : β) :
    Costed β :=
  ⟨value, row.control visit items.size⟩

/-- A scan of a vector by the library function `row`. -/
@[reducible] def scanVector {count : Nat} (row : Acorn.Library) (visit : Nat)
    (_items : Vector α count) (value : β) : Costed β :=
  ⟨value, row.control visit count⟩

end Costed

end AcornVerif.Resource
