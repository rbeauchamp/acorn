import Acorn.Cost

namespace AcornVerif.Resource

structure Costed (α : Type) where
  val : α
  work : Nat

abbrev pass (visit count bound : Nat) : Nat := count * (visit + bound) + visit

theorem pass_mono {visit count limit bound most : Nat} (fits : count ≤ limit)
    (within : bound ≤ most) : pass visit count bound ≤ pass visit limit most :=
  Nat.add_le_add_right (Nat.mul_le_mul fits (Nat.add_le_add_left within visit)) visit

namespace Costed

variable {α β : Type}

@[reducible] def pure (value : α) : Costed α := ⟨value, 0⟩

@[reducible] def op (cost : Nat) (value : α) : Costed α := ⟨value, cost⟩

@[reducible] def bind (first : Costed α) (next : α → Costed β) : Costed β :=
  ⟨(next first.val).val, first.work + (next first.val).work⟩

@[reducible] def charge (cost : Nat) (rest : Costed α) : Costed α := ⟨rest.val, cost + rest.work⟩

@[reducible] def via (value : α) (twin : Costed β) : Costed α := ⟨value, twin.work⟩

@[reducible] def discard (twin : Costed α) : Costed Unit := ⟨(), twin.work⟩

instance : Pure Costed := ⟨Costed.pure⟩

instance : Bind Costed := ⟨Costed.bind⟩

theorem bind_val (first : Costed α) (next : α → Costed β) :
    (first >>= next).val = (next first.val).val := rfl

theorem bind_work (first : Costed α) (next : α → Costed β) :
    (first >>= next).work = first.work + (next first.val).work := rfl

theorem bind_work_le {first : Costed α} {next : α → Costed β} {a b : Nat}
    (firstFits : first.work ≤ a) (nextFits : ∀ value, (next value).work ≤ b) :
    (first >>= next).work ≤ a + b :=
  Nat.add_le_add firstFits (nextFits _)

theorem bind_work_le_at {first : Costed α} {next : α → Costed β} {a b : Nat}
    (firstFits : first.work ≤ a) (nextFits : (next first.val).work ≤ b) :
    (first >>= next).work ≤ a + b :=
  Nat.add_le_add firstFits nextFits

theorem charge_work_le {cost bound : Nat} {rest : Costed α} (fits : rest.work ≤ bound) :
    (charge cost rest).work ≤ cost + bound :=
  Nat.add_le_add_left fits cost

theorem discard_work_le {twin : Costed α} {bound : Nat} (fits : twin.work ≤ bound) :
    (discard twin).work ≤ bound := fits

@[reducible] def ite (condition : Prop) [Decidable condition] (yes no : Costed α) :
    Costed α :=
  ⟨if condition then yes.val else no.val, if condition then yes.work else no.work⟩

theorem ite_work_le (condition : Prop) [Decidable condition] (yes no : Costed α) :
    (ite condition yes no).work ≤ max yes.work no.work := by
  unfold ite
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

theorem ite_work_bound (condition : Prop) [Decidable condition] {yes no : Costed α} {bound : Nat}
    (yesFits : yes.work ≤ bound) (noFits : no.work ≤ bound) :
    (ite condition yes no).work ≤ bound := by
  unfold ite
  split
  · exact yesFits
  · exact noFits

@[reducible] def dite (condition : Prop) [Decidable condition]
    (yes : condition → Costed α) (no : ¬condition → Costed α) : Costed α :=
  ⟨if h : condition then (yes h).val else (no h).val,
    if h : condition then (yes h).work else (no h).work⟩

theorem dite_work_le (condition : Prop) [Decidable condition]
    (yes : condition → Costed α) (no : ¬condition → Costed α) (bound : Nat)
    (yesBound : ∀ h, (yes h).work ≤ bound) (noBound : ∀ h, (no h).work ≤ bound) :
    (dite condition yes no).work ≤ bound := by
  unfold dite
  split
  · exact yesBound _
  · exact noBound _

@[reducible] def optBind (first : Costed (Option α)) (next : α → Costed (Option β)) :
    Costed (Option β) :=
  ⟨first.val.bind fun value => (next value).val,
    first.work + match first.val with
      | none => 0
      | some value => (next value).work⟩

theorem optBind_work_le (first : Costed (Option α)) (next : α → Costed (Option β))
    (bound : Nat) (each : ∀ value, (next value).work ≤ bound) :
    (optBind first next).work ≤ first.work + bound := by
  unfold optBind
  dsimp only
  split
  · exact Nat.add_le_add_left (Nat.zero_le _) _
  · exact Nat.add_le_add_left (each _) _

theorem visit_le {visit rest count perVisit exit : Nat} (fits : visit ≤ perVisit)
    (restFits : rest ≤ count * perVisit + exit) :
    visit + rest ≤ (count + 1) * perVisit + exit := by
  rw [Nat.succ_mul]
  omega

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

theorem length_mul_le {count limit bound : Nat} (fits : count ≤ limit) :
    count * bound ≤ limit * bound :=
  Nat.mul_le_mul_right _ fits

def foldlSteps (step : β → α → Costed β) : β → List α → Nat
  | _, [] => 0
  | acc, item :: rest => (step acc item).work + foldlSteps step (step acc item).val rest

@[reducible] def foldl (visit : Nat) (step : β → α → Costed β) (init : β) (items : List α) :
    Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    foldlSteps step init items + Acorn.Library.foldl.control visit items.length⟩

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

theorem foldl_work_le (visit bound : Nat) (step : β → α → Costed β) (init : β)
    (items : List α) (each : ∀ acc, ∀ item ∈ items, (step acc item).work ≤ bound) :
    (foldl visit step init items).work ≤ Acorn.Library.foldl.work visit items.length bound :=
  Nat.add_le_add_right (foldlSteps_le bound step items each init) _

@[reducible] def mapSteps (operation : α → Costed β) (items : List α) : Nat :=
  (items.map fun item => (operation item).work).sum

theorem mapSteps_le (bound : Nat) (operation : α → Costed β) (items : List α)
    (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    mapSteps operation items ≤ items.length * bound :=
  sum_map_le items _ _ each

@[reducible] def map (visit : Nat) (operation : α → Costed β) (items : List α) :
    Costed (List β) :=
  ⟨items.map fun item => (operation item).val,
    mapSteps operation items + Acorn.Library.map.control visit items.length⟩

theorem map_work_le (visit bound : Nat) (operation : α → Costed β) (items : List α)
    (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    (map visit operation items).work ≤ Acorn.Library.map.work visit items.length bound :=
  Nat.add_le_add_right (mapSteps_le bound operation items each) _

@[reducible] def filter (visit : Nat) (test : α → Costed Bool) (items : List α) :
    Costed (List α) :=
  ⟨items.filter fun item => (test item).val,
    mapSteps test items + Acorn.Library.filter.control visit items.length⟩

theorem filter_work_le (visit bound : Nat) (test : α → Costed Bool) (items : List α)
    (each : ∀ item ∈ items, (test item).work ≤ bound) :
    (filter visit test items).work ≤ Acorn.Library.filter.work visit items.length bound :=
  Nat.add_le_add_right (mapSteps_le bound test items each) _

@[reducible] def mapVector {count : Nat} (visit : Nat) (operation : α → Costed β)
    (items : Vector α count) : Costed (Vector β count) :=
  ⟨items.map fun item => (operation item).val,
    mapSteps operation items.toList + Acorn.Library.vectorMap.control visit count⟩

theorem mapVector_work_le {count : Nat} (visit bound : Nat) (operation : α → Costed β)
    (items : Vector α count) (each : ∀ item ∈ items.toList, (operation item).work ≤ bound) :
    (mapVector visit operation items).work ≤ Acorn.Library.vectorMap.work visit count bound := by
  have counted := mapSteps_le bound operation items.toList each
  rw [Vector.length_toList] at counted
  exact Nat.add_le_add_right counted _

@[reducible] def ofFn {count : Nat} (visit : Nat) (operation : Fin count → Costed β) :
    Costed (Vector β count) :=
  ⟨Vector.ofFn fun index => (operation index).val,
    mapSteps operation (List.finRange count) + Acorn.Library.ofFn.control visit count⟩

theorem ofFn_work_le {count : Nat} (visit bound : Nat) (operation : Fin count → Costed β)
    (each : ∀ index, (operation index).work ≤ bound) :
    (ofFn visit operation).work ≤ Acorn.Library.ofFn.work visit count bound := by
  have counted := mapSteps_le bound operation (List.finRange count) (fun index _ => each index)
  rw [List.length_finRange] at counted
  exact Nat.add_le_add_right counted _

@[reducible] def flatMap (visit : Nat) (operation : α → Costed (List β)) (items : List α) :
    Costed (List β) :=
  ⟨items.flatMap fun item => (operation item).val,
    mapSteps operation items + Acorn.Library.flatMap.control visit items.length⟩

theorem flatMap_work_le (visit bound : Nat) (operation : α → Costed (List β)) (items : List α)
    (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    (flatMap visit operation items).work ≤ Acorn.Library.flatMap.work visit items.length bound :=
  Nat.add_le_add_right (mapSteps_le bound operation items each) _

@[reducible] def mapFinIdx {count : Nat} (visit : Nat)
    (operation : (index : Nat) → α → index < count → Costed β) (items : Vector α count) :
    Costed (Vector β count) :=
  ⟨items.mapFinIdx fun index item bound => (operation index item bound).val,
    ((List.finRange count).map fun index =>
      (operation index.val items[index.val] index.isLt).work).sum +
      Acorn.Library.mapFinIdx.control visit count⟩

theorem mapFinIdx_work_le {count : Nat} (visit bound : Nat)
    (operation : (index : Nat) → α → index < count → Costed β) (items : Vector α count)
    (each : ∀ index item inside, (operation index item inside).work ≤ bound) :
    (mapFinIdx visit operation items).work ≤ Acorn.Library.mapFinIdx.work visit count bound := by
  have counted := sum_map_le (List.finRange count)
    (fun index : Fin count => (operation index.val items[index.val] index.isLt).work)
    bound (fun index _ => each _ _ _)
  rw [List.length_finRange] at counted
  exact Nat.add_le_add_right counted _

@[reducible] def filterMap (visit : Nat) (operation : α → Costed (Option β))
    (items : List α) : Costed (List β) :=
  ⟨items.filterMap fun item => (operation item).val,
    mapSteps operation items + Acorn.Library.filterMap.control visit items.length⟩

theorem filterMap_work_le (visit bound : Nat) (operation : α → Costed (Option β))
    (items : List α) (each : ∀ item ∈ items, (operation item).work ≤ bound) :
    (filterMap visit operation items).work ≤
      Acorn.Library.filterMap.work visit items.length bound :=
  Nat.add_le_add_right (mapSteps_le bound operation items each) _

@[reducible] def foldlArray (visit : Nat) (step : β → α → Costed β) (init : β)
    (items : Array α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    foldlSteps step init items.toList + Acorn.Library.foldlArray.control visit items.size⟩

theorem foldlArray_val (visit : Nat) (step : β → α → Costed β) (init : β) (items : Array α) :
    (foldlArray visit step init items).val = (foldl visit step init items.toList).val :=
  (Array.foldl_toList ..).symm

theorem foldlArray_work_le (visit bound : Nat) (step : β → α → Costed β) (init : β)
    (items : Array α) (each : ∀ acc, ∀ item ∈ items.toList, (step acc item).work ≤ bound) :
    (foldlArray visit step init items).work ≤
      Acorn.Library.foldlArray.work visit items.size bound := by
  have counted := foldlSteps_le bound step items.toList each init
  rw [Array.length_toList] at counted
  exact Nat.add_le_add_right counted _

@[reducible] def replicate (visit count : Nat) (value : α) : Costed (Vector α count) :=
  ⟨Vector.replicate count value, Acorn.Library.replicate.control visit count⟩

@[reducible] def scanList (row : Acorn.Library) (visit : Nat) (items : List α) (value : β) :
    Costed β :=
  ⟨value, row.control visit items.length⟩

@[reducible] def scanArray (row : Acorn.Library) (visit : Nat) (items : Array α) (value : β) :
    Costed β :=
  ⟨value, row.control visit items.size⟩

@[reducible] def scanVector {count : Nat} (row : Acorn.Library) (visit : Nat)
    (_items : Vector α count) (value : β) : Costed β :=
  ⟨value, row.control visit count⟩

end Costed

end AcornVerif.Resource
