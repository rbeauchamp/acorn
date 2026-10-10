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
the executed code only through that reading. Each definition moves out of this accounting when
it becomes the value of its costed definition, as the learner did.

**Loops.** A **pass** over `count` elements is charged a visit for the loop's control and the
work of the visit's operation for each element, and one visit for its end, the final test and
branch (`pass`, `bare`). Each loop combinator below has as its value the library loop applied to
the values of its parts, and as its work the passes that loop's runtime implementation makes: one
for `List.foldl`, `Array.foldl`, `Vector.map`, `Vector.ofFn` and `Vector.mapFinIdx`; for
`List.map` a second for the reversal of `List.mapTR`; for `List.filterMap` a second for the
`Array.toList` of `List.filterMapTR`; for `List.flatMap` the end of the `Array.toList` of
`List.flatMapTR`, whose copies the operation's work counts. A loop's bound is therefore its trip
count times a bound of one visit, and one visit for each end (`foldl_work_le`, `mapWork_le`,
`ofFn_work_le`).

**Scans.** A library function whose every visit is constant work is a **scan**, charged its
number of passes over the collection it names (`scanList`, `scanArray`, `scanVector`). The
number is the passes of its runtime implementation, read from the library: one for
`List.length`, `List.contains`, `List.range`, `List.finRange`, `List.toArray`, `Array.toList`,
`Vector.toList`, `List.reverse` and the equality of vectors; two for `List.filter`
(`List.filterTR`: a loop and a reversal), `++` (`List.appendTR`: a reversal of the first list and
`List.reverseAux` over it), `List.dropLast` (`List.dropLastTR`: `List.toArray` and
`Array.toList`), `List.zipIdx` (`List.zipIdxTR`) and `List.sum` (`List.foldrTR`: `List.toArray`
and `Array.foldr`); three for `Features.insert` (a membership test and `++`). Each scan states
its passes where it is used, and a vector of one repeated element is one pass (`replicate`).

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

/-- The work of one pass of a loop over `count` elements: a visit for the loop's control and at
most `bound` for each element, and one visit for the pass's end. -/
abbrev pass (visit count bound : Nat) : Nat := count * (visit + bound) + visit

/-- The work of one pass whose visits do nothing beyond the loop's control. -/
abbrev bare (visit count : Nat) : Nat := count * visit + visit

/-- A pass over more elements, each with a larger bound, does more work. -/
theorem pass_mono {visit count limit bound most : Nat} (fits : count ≤ limit)
    (within : bound ≤ most) : pass visit count bound ≤ pass visit limit most :=
  Nat.add_le_add_right (Nat.mul_le_mul fits (Nat.add_le_add_left within visit)) visit

/-- A bare pass over more elements does more work. -/
theorem bare_mono {visit count limit : Nat} (fits : count ≤ limit) :
    bare visit count ≤ bare visit limit :=
  Nat.add_le_add_right (Nat.mul_le_mul_right visit fits) visit

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

instance : Monad Costed where
  pure := Costed.pure
  bind := Costed.bind

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

/-- The work of a left fold: for each visit, `visit` for the loop's control and the
step's work at the accumulator the executed fold reaches there, and `visit` for its end. -/
def foldlWork (visit : Nat) (step : β → α → Costed β) : β → List α → Nat
  | _, [] => visit
  | acc, item :: rest =>
    visit + (step acc item).work + foldlWork visit step (step acc item).val rest

/-- A left fold over a list. Its value is the executed fold of the steps' values. -/
@[reducible] def foldl (visit : Nat) (step : β → α → Costed β) (init : β) (items : List α) :
    Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init, foldlWork visit step init items⟩

/-- A fold whose every step is at most `bound` costs at most one pass with that bound. The
bound holds at every accumulator, so no reasoning about the values the fold computes is
needed. -/
theorem foldlWork_le (visit bound : Nat) (step : β → α → Costed β)
    (items : List α) (each : ∀ acc, ∀ item ∈ items, (step acc item).work ≤ bound) :
    ∀ init, foldlWork visit step init items ≤ pass visit items.length bound := by
  induction items with
  | nil => intro init; simp [foldlWork]
  | cons head rest ih =>
    intro init
    have headBound := each init head (List.mem_cons_self ..)
    have restBound := ih (fun acc item member => each acc item (List.mem_cons_of_mem _ member))
      (step init head).val
    simp only [foldlWork, pass, List.length_cons, Nat.succ_mul] at restBound ⊢
    omega

/-- A fold's work, by the bound of each step. -/
theorem foldl_work_le (visit bound : Nat) (step : β → α → Costed β) (init : β)
    (items : List α) (each : ∀ acc, ∀ item ∈ items, (step acc item).work ≤ bound) :
    (foldl visit step init items).work ≤ pass visit items.length bound :=
  foldlWork_le visit bound step items each init

/-- The work of one pass mapping an operation: for each visit, `visit` and the work of the
operation, and `visit` for the pass's end. -/
@[reducible] def mapWork (visit : Nat) (operation : α → Costed β) (items : List α) : Nat :=
  (items.map fun item => visit + (operation item).work).sum + visit

/-- A mapping pass's work, by the bound of each operation. -/
theorem mapWork_le (visit bound : Nat) (operation : α → Costed β) (items : List α)
    (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    mapWork visit operation items ≤ pass visit items.length bound :=
  Nat.add_le_add_right
    (sum_map_le items _ _ fun item member => Nat.add_le_add_left (each item member) _) visit

/-- A map over a list: the loop of `List.mapTR` and its reversal. -/
@[reducible] def map (visit : Nat) (operation : α → Costed β) (items : List α) :
    Costed (List β) :=
  ⟨items.map fun item => (operation item).val,
    mapWork visit operation items + bare visit items.length⟩

/-- A map's work, by the bound of each operation. -/
theorem map_work_le (visit bound : Nat) (operation : α → Costed β) (items : List α)
    (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    (map visit operation items).work ≤ pass visit items.length bound + bare visit items.length :=
  Nat.add_le_add_right (mapWork_le visit bound operation items each) _

/-- A map over a vector, visiting its elements in order in one pass. -/
@[reducible] def mapVector {count : Nat} (visit : Nat) (operation : α → Costed β)
    (items : Vector α count) : Costed (Vector β count) :=
  ⟨items.map fun item => (operation item).val, mapWork visit operation items.toList⟩

/-- A vector map's work, by the bound of each operation. -/
theorem mapVector_work_le {count : Nat} (visit bound : Nat) (operation : α → Costed β)
    (items : Vector α count) (each : ∀ item ∈ items.toList, (operation item).work ≤ bound) :
    (mapVector visit operation items).work ≤ pass visit count bound := by
  have counted := mapWork_le visit bound operation items.toList each
  simpa only [Vector.length_toList] using counted

/-- A vector built from its indices, visiting each index in order in one pass. -/
@[reducible] def ofFn {count : Nat} (visit : Nat) (operation : Fin count → Costed β) :
    Costed (Vector β count) :=
  ⟨Vector.ofFn fun index => (operation index).val,
    mapWork visit operation (List.finRange count)⟩

/-- A built vector's work, by the bound of each operation. -/
theorem ofFn_work_le {count : Nat} (visit bound : Nat) (operation : Fin count → Costed β)
    (each : ∀ index, (operation index).work ≤ bound) :
    (ofFn visit operation).work ≤ pass visit count bound := by
  have counted := mapWork_le visit bound operation (List.finRange count)
    (fun index _ => each index)
  simpa only [List.length_finRange] using counted

/-- A map whose results are concatenated, as `List.flatMap`: one pass, and the end of the
`Array.toList` of `List.flatMapTR`. The operation's work includes the copy of its result into
the concatenation and the read of each copied element into the result list. -/
@[reducible] def flatMap (visit : Nat) (operation : α → Costed (List β)) (items : List α) :
    Costed (List β) :=
  ⟨items.flatMap fun item => (operation item).val, mapWork visit operation items + visit⟩

/-- A map over a vector that reads each element's index, as `Vector.mapFinIdx`, in one pass. -/
@[reducible] def mapFinIdx {count : Nat} (visit : Nat)
    (operation : (index : Nat) → α → index < count → Costed β) (items : Vector α count) :
    Costed (Vector β count) :=
  ⟨items.mapFinIdx fun index item bound => (operation index item bound).val,
    ((List.finRange count).map fun index =>
      visit + (operation index.val items[index.val] index.isLt).work).sum + visit⟩

/-- An indexed vector map's work, by the bound of each operation. -/
theorem mapFinIdx_work_le {count : Nat} (visit bound : Nat)
    (operation : (index : Nat) → α → index < count → Costed β) (items : Vector α count)
    (each : ∀ index item inside, (operation index item inside).work ≤ bound) :
    (mapFinIdx visit operation items).work ≤ pass visit count bound := by
  have counted := sum_map_le (List.finRange count)
    (fun index : Fin count => visit + (operation index.val items[index.val] index.isLt).work)
    (visit + bound) (fun index _ => Nat.add_le_add_left (each _ _ _) _)
  simp only [List.length_finRange] at counted
  exact Nat.add_le_add_right counted visit

/-- A filtering map over a list: the loop of `List.filterMapTR` and the `Array.toList` of the
kept elements, at most one for each element. -/
@[reducible] def filterMap (visit : Nat) (operation : α → Costed (Option β))
    (items : List α) : Costed (List β) :=
  ⟨items.filterMap fun item => (operation item).val,
    mapWork visit operation items + bare visit items.length⟩

/-- A filtering map's work, by the bound of each operation. -/
theorem filterMap_work_le (visit bound : Nat) (operation : α → Costed (Option β))
    (items : List α) (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    (filterMap visit operation items).work ≤
      pass visit items.length bound + bare visit items.length :=
  Nat.add_le_add_right (mapWork_le visit bound operation items each) _

/-- A left fold over an array, visiting its elements in order in one pass. -/
@[reducible] def foldlArray (visit : Nat) (step : β → α → Costed β) (init : β)
    (items : Array α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    foldlWork visit step init items.toList⟩

/-- An array fold's value is the list fold's value over the same elements. -/
theorem foldlArray_val (visit : Nat) (step : β → α → Costed β) (init : β) (items : Array α) :
    (foldlArray visit step init items).val = (foldl visit step init items.toList).val :=
  (Array.foldl_toList ..).symm

/-- An array fold's work, by the bound of each step. -/
theorem foldlArray_work_le (visit bound : Nat) (step : β → α → Costed β) (init : β)
    (items : Array α) (each : ∀ acc, ∀ item ∈ items.toList, (step acc item).work ≤ bound) :
    (foldlArray visit step init items).work ≤ pass visit items.size bound := by
  have counted := foldlWork_le visit bound step items.toList each init
  simpa only [Array.length_toList] using counted

/-- A vector of one repeated element: one bare pass writing each element. -/
@[reducible] def replicate (visit count : Nat) (value : α) : Costed (Vector α count) :=
  ⟨Vector.replicate count value, bare visit count⟩

/-- A library scan of a list in `passes` passes whose every visit is one loop-free comparison or
copy, whatever the scan returns. The value is the executed expression; the list is the one that
expression scans. -/
@[reducible] def scanList (passes visit : Nat) (items : List α) (value : β) : Costed β :=
  ⟨value, passes * bare visit items.length⟩

/-- A library scan of an array in `passes` passes. -/
@[reducible] def scanArray (passes visit : Nat) (items : Array α) (value : β) : Costed β :=
  ⟨value, passes * bare visit items.size⟩

/-- A library scan of a vector in `passes` passes. -/
@[reducible] def scanVector {count : Nat} (passes visit : Nat) (_items : Vector α count)
    (value : β) : Costed β :=
  ⟨value, passes * bare visit count⟩

end Costed

end AcornVerif.Resource
