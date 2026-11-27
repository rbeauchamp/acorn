import Acorn.Encoding

namespace Acorn

inductive Site where
  | visit
  | sumTerm
  | read
  | firstOpen
  | firstElement
  | prune
  | firstClose
  | secondOpen
  | secondElement
  | stepClose
  | zeroTransient
  | beginClose
  | terminalClose
  | planOpen
  | planElement
  | clearRegisters
  | releaseClose
  | retire
  | managedEntry
  | creditRestart
  | learnerError
  | creditClose
  | valuesOpen
  | controllerClose
  | planClose
  | compare
  | candidate
  | tieThreshold
  | reservoirDraw
  | probability
  | probabilitiesOpen
  | uniform
  | drawClose
  | explorationBegin
  | policyOpen
  | snapshot
  | rateTerm
  | rateClose
  | normalizedOpen
  | normalizedTerm
  | expectedTerm
  | expectedClose
  | feedbackWord
  | sampleTerm
  | activation
  | hashFeature
  | imprint
  | uniqueAdd
  | insert
  | position
  | write
  | productTerm
  | project
  | outcomeValue
  | prediction
  | deviation
  | modelClose
  | demonOutput
  | demonClose
  | assignmentPotential
  | declaredPotential
  | decide
  | beginOption
  | optionStep
  | terminateOption
  | stopFollowing
  | settleFollowing
  | startFollowing
  | followStep
  | unlinkSlot
  | followTable
  | lookAhead
  | backupClose
  | planBoundary
  | initialState
  | rankCandidate
  | rankWidth
  | install
  | assignmentTable
  | prepare
  | serve
  | choosePrimitive
  | refreshFree
  | planFree
  | drawMeta
  | closeOption
  | learnMeta
  | dispatchMeta
  | stepOption
  | atBoundary
  | select
  | choose

abbrev Costs := Site → Nat

inductive Library where
  | foldl
  | foldlArray
  | map
  | replicate
  | findIdx
  | vectorMap
  | ofFn
  | mapFinIdx
  | filter
  | filterMap
  | flatMap
  | flatMapResult
  | length
  | contains
  | range
  | finRange
  | toArray
  | toList
  | reverse
  | vectorEq
  | append
  | vectorAppend
  | drop
  | dropLast
  | zipIdx
  | sum
  | fillVacant

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
  | .vectorAppend => 1
  | .drop => 1
  | .dropLast => 3
  | .zipIdx => 3
  | .sum => 1
  | .fillVacant => 2

abbrev Library.control (row : Library) (visit count : Nat) : Nat :=
  row.passes * (count * visit + visit)

abbrev Library.work (row : Library) (visit count bound : Nat) : Nat :=
  count * bound + row.control visit count

theorem Library.control_mono (row : Library) {visit count limit : Nat} (fits : count ≤ limit) :
    row.control visit count ≤ row.control visit limit :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right visit fits) visit)

theorem Library.work_mono (row : Library) {visit count limit bound most : Nat}
    (fits : count ≤ limit) (within : bound ≤ most) :
    row.work visit count bound ≤ row.work visit limit most :=
  Nat.add_le_add (Nat.mul_le_mul fits within) (row.control_mono fits)

structure Costed (α : Type) where
  private mk ::
  val : α
  work : Costs → Nat → Prop
  single : ∀ κ, ∃ n, work κ n ∧ ∀ m, work κ m → m = n

namespace Costed

variable {α β : Type}

def Within (x : Costed α) (κ : Costs) (bound : Nat) : Prop :=
  ∀ n, x.work κ n → n ≤ bound

theorem within_iff (x : Costed α) (κ : Costs) (bound : Nat) :
    x.Within κ bound ↔ ∃ n, x.work κ n ∧ n ≤ bound := by
  obtain ⟨n, holds, unique⟩ := x.single κ
  constructor
  · intro within
    exact ⟨n, holds, within n holds⟩
  · intro ⟨m, held, fits⟩ k work
    rw [unique k work, ← unique m held]
    exact fits

theorem Within.mono {x : Costed α} {κ : Costs} {a b : Nat} (within : x.Within κ a)
    (fits : a ≤ b) : x.Within κ b :=
  fun n work => Nat.le_trans (within n work) fits

theorem within_ite {condition : Prop} [Decidable condition] {yes no : Costed α} {κ : Costs}
    {bound : Nat} (yesFits : yes.Within κ bound) (noFits : no.Within κ bound) :
    (if condition then yes else no).Within κ bound := by
  split
  · exact yesFits
  · exact noFits

@[inline] def pure (value : α) : Costed α :=
  ⟨value, fun _ n => n = 0, fun _ => ⟨0, rfl, fun _ same => same⟩⟩

@[inline] def op (site : Site) (value : α) : Costed α :=
  ⟨value, fun κ n => n = κ site, fun κ => ⟨κ site, rfl, fun _ same => same⟩⟩

@[inline] def charge (site : Site) (rest : Costed α) : Costed α :=
  ⟨rest.val, fun κ n => ∃ later, rest.work κ later ∧ n = κ site + later, fun κ => by
    obtain ⟨later, held, unique⟩ := rest.single κ
    exact ⟨κ site + later, ⟨later, held, rfl⟩, fun m ⟨other, work, same⟩ => by
      rw [same, unique other work]⟩⟩

@[inline] def bind (first : Costed α) (next : α → Costed β) : Costed β :=
  ⟨(next first.val).val,
    fun κ n => ∃ here later, first.work κ here ∧ (next first.val).work κ later ∧
      n = here + later, fun κ => by
    obtain ⟨here, firstHeld, firstUnique⟩ := first.single κ
    obtain ⟨later, nextHeld, nextUnique⟩ := (next first.val).single κ
    exact ⟨here + later, ⟨here, later, firstHeld, nextHeld, rfl⟩,
      fun m ⟨a, b, firstWork, nextWork, same⟩ => by
        rw [same, firstUnique a firstWork, nextUnique b nextWork]⟩⟩

@[inline] def ite (condition : Prop) [Decidable condition] (yes no : Unit → Costed α) : Costed α :=
  ⟨if condition then (yes ()).val else (no ()).val,
    fun κ n => if condition then (yes ()).work κ n else (no ()).work κ n, fun κ => by
      by_cases holds : condition
      · simp only [holds, ↓reduceIte]
        exact (yes ()).single κ
      · simp only [holds, ↓reduceIte]
        exact (no ()).single κ⟩

instance : Pure Costed := ⟨Costed.pure⟩

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

theorem bind_within {first : Costed α} {next : α → Costed β} {κ : Costs} {a b : Nat}
    (firstFits : first.Within κ a) (nextFits : (next first.val).Within κ b) :
    (first >>= next).Within κ (a + b) :=
  fun _ ⟨here, later, firstWork, nextWork, same⟩ => by
    rw [same]
    exact Nat.add_le_add (firstFits here firstWork) (nextFits later nextWork)

theorem ite_val (condition : Prop) [Decidable condition] (yes no : Unit → Costed α) :
    (ite condition yes no).val = if condition then (yes ()).val else (no ()).val := rfl

theorem ite_within {condition : Prop} [Decidable condition] {yes no : Unit → Costed α}
    {κ : Costs} {bound : Nat} (yesFits : condition → (yes ()).Within κ bound)
    (noFits : ¬condition → (no ()).Within κ bound) : (ite condition yes no).Within κ bound := by
  intro n work
  change (if condition then (yes ()).work κ n else (no ()).work κ n) at work
  by_cases holds : condition
  · simp only [holds, ↓reduceIte] at work
    exact yesFits holds n work
  · simp only [holds, ↓reduceIte] at work
    exact noFits holds n work

@[inline] def dite (condition : Prop) [Decidable condition] (yes : condition → Costed α)
    (no : ¬condition → Costed α) : Costed α :=
  ⟨if holds : condition then (yes holds).val else (no holds).val,
    fun κ n => if holds : condition then (yes holds).work κ n else (no holds).work κ n,
    fun κ => by
      by_cases holds : condition
      · simp only [holds, ↓reduceDIte]
        exact (yes holds).single κ
      · simp only [holds, ↓reduceDIte]
        exact (no holds).single κ⟩

theorem dite_val (condition : Prop) [Decidable condition] (yes : condition → Costed α)
    (no : ¬condition → Costed α) :
    (dite condition yes no).val = if holds : condition then (yes holds).val else (no holds).val :=
  rfl

theorem dite_within {condition : Prop} [Decidable condition] {yes : condition → Costed α}
    {no : ¬condition → Costed α} {κ : Costs} {bound : Nat}
    (yesFits : ∀ holds, (yes holds).Within κ bound)
    (noFits : ∀ holds, (no holds).Within κ bound) :
    (dite condition yes no).Within κ bound := by
  intro n work
  change (if holds : condition then (yes holds).work κ n else (no holds).work κ n) at work
  by_cases holds : condition
  · simp only [holds, ↓reduceDIte] at work
    exact yesFits holds n work
  · simp only [holds, ↓reduceDIte] at work
    exact noFits holds n work

theorem bind_within_all {first : Costed α} {next : α → Costed β} {κ : Costs} {a b : Nat}
    (firstFits : first.Within κ a) (nextFits : ∀ value, (next value).Within κ b) :
    (first >>= next).Within κ (a + b) :=
  bind_within firstFits (nextFits first.val)

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

theorem foldl_within {step : β → α → Costed β} {init : β} {items : List α} {κ : Costs}
    {bound : Nat} (each : ∀ acc, ∀ item ∈ items, (step acc item).Within κ bound) :
    (foldl step init items).Within κ (Library.foldl.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (foldlSteps_within step κ bound items each init steps work) _

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

@[inline] def replicate (count : Nat) (value : α) : Costed (Vector α count) :=
  ⟨Vector.replicate count value, fun κ n => n = Library.replicate.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem replicate_val (count : Nat) (value : α) :
    (replicate count value).val = Vector.replicate count value := rfl

theorem replicate_within (count : Nat) (value : α) (κ : Costs) :
    (replicate count value).Within κ (Library.replicate.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

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

theorem findIdx?_within {items : Array α} {test : α → Costed Bool} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items.toList, (test item).Within κ bound) :
    (findIdx? items test).Within κ (Library.findIdx.work (κ .visit) items.size bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within items.toList each steps work
    rw [Array.length_toList] at counted
    exact Nat.add_le_add_right counted _

@[inline] def filter (test : α → Costed Bool) (items : List α) : Costed (List α) :=
  ⟨items.filter fun item => (test item).val,
    fun κ n => ∃ steps, mapSteps test items κ steps ∧
      n = steps + Library.filter.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single test κ items
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem filter_val (test : α → Costed Bool) (items : List α) :
    (filter test items).val = items.filter fun item => (test item).val := rfl

theorem filter_within {test : α → Costed Bool} {items : List α} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items, (test item).Within κ bound) :
    (filter test items).Within κ (Library.filter.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (mapSteps_within items each steps work) _

@[inline] def filterMap (operation : α → Costed (Option β)) (items : List α) :
    Costed (List β) :=
  ⟨items.filterMap fun item => (operation item).val,
    fun κ n => ∃ steps, mapSteps operation items κ steps ∧
      n = steps + Library.filterMap.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single operation κ items
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem filterMap_val (operation : α → Costed (Option β)) (items : List α) :
    (filterMap operation items).val = items.filterMap fun item => (operation item).val := rfl

theorem filterMap_within {operation : α → Costed (Option β)} {items : List α} {κ : Costs}
    {bound : Nat} (each : ∀ item ∈ items, (operation item).Within κ bound) :
    (filterMap operation items).Within κ (Library.filterMap.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (mapSteps_within items each steps work) _

def flatMapSteps (operation : α → Costed (List β)) : List α → Costs → Nat → Prop
  | [], _, n => n = 0
  | item :: rest, κ, n => ∃ here later, (operation item).work κ here ∧
      flatMapSteps operation rest κ later ∧
      n = here + Library.flatMapResult.control (κ .visit) (operation item).val.length + later

theorem flatMapSteps_single (operation : α → Costed (List β)) (κ : Costs) (items : List α) :
    ∃ n, flatMapSteps operation items κ n ∧
      ∀ m, flatMapSteps operation items κ m → m = n := by
  induction items with
  | nil => exact ⟨0, rfl, fun _ same => same⟩
  | cons item rest ih =>
    obtain ⟨here, opHeld, opUnique⟩ := (operation item).single κ
    obtain ⟨later, restHeld, restUnique⟩ := ih
    refine ⟨_, ⟨here, later, opHeld, restHeld, rfl⟩, fun m work => ?_⟩
    obtain ⟨a, b, opWork, restWork, same⟩ := work
    rw [same, opUnique a opWork, restUnique b restWork]

theorem flatMapSteps_within {operation : α → Costed (List β)} {κ : Costs} {bound size : Nat} :
    ∀ items : List α, (∀ item ∈ items, (operation item).Within κ bound) →
      (∀ item ∈ items, (operation item).val.length ≤ size) →
      ∀ n, flatMapSteps operation items κ n →
        n ≤ items.length * (bound + Library.flatMapResult.control (κ .visit) size) := by
  intro items
  induction items with
  | nil =>
    intro _ _ n work
    have same : n = 0 := work
    omega
  | cons item rest ih =>
    intro each sizes n work
    obtain ⟨here, later, opWork, restWork, same⟩ := work
    have headFits := each item (List.mem_cons_self ..) here opWork
    have headSize := Library.control_mono .flatMapResult (visit := κ .visit)
      (sizes item (List.mem_cons_self ..))
    have restFits := ih (fun item member => each item (List.mem_cons_of_mem _ member))
      (fun item member => sizes item (List.mem_cons_of_mem _ member)) later restWork
    rw [same, List.length_cons, Nat.succ_mul]
    omega

@[inline] def flatMap (operation : α → Costed (List β)) (items : List α) : Costed (List β) :=
  ⟨items.flatMap fun item => (operation item).val,
    fun κ n => ∃ steps, flatMapSteps operation items κ steps ∧
      n = steps + Library.flatMap.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := flatMapSteps_single operation κ items
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem flatMap_val (operation : α → Costed (List β)) (items : List α) :
    (flatMap operation items).val = items.flatMap fun item => (operation item).val := rfl

theorem flatMap_within {operation : α → Costed (List β)} {items : List α} {κ : Costs}
    {bound size : Nat} (each : ∀ item ∈ items, (operation item).Within κ bound)
    (sizes : ∀ item ∈ items, (operation item).val.length ≤ size) :
    (flatMap operation items).Within κ (Library.flatMap.work (κ .visit) items.length
      (bound + Library.flatMapResult.control (κ .visit) size)) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (flatMapSteps_within items each sizes steps work) _

@[inline] def mapVector {count : Nat} (operation : α → Costed β) (items : Vector α count) :
    Costed (Vector β count) :=
  ⟨items.map fun item => (operation item).val,
    fun κ n => ∃ steps, mapSteps operation items.toList κ steps ∧
      n = steps + Library.vectorMap.control (κ .visit) count,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single operation κ items.toList
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem mapVector_val {count : Nat} (operation : α → Costed β) (items : Vector α count) :
    (mapVector operation items).val = items.map fun item => (operation item).val := rfl

theorem mapVector_within {count : Nat} {operation : α → Costed β} {items : Vector α count}
    {κ : Costs} {bound : Nat} (each : ∀ item ∈ items.toList, (operation item).Within κ bound) :
    (mapVector operation items).Within κ (Library.vectorMap.work (κ .visit) count bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within items.toList each steps work
    rw [Vector.length_toList] at counted
    exact Nat.add_le_add_right counted _

@[inline] def mapFinIdx {count : Nat} (items : Vector α count)
    (operation : (index : Nat) → α → index < count → Costed β) : Costed (Vector β count) :=
  ⟨items.mapFinIdx fun index item bound => (operation index item bound).val,
    fun κ n => ∃ steps, mapSteps (fun index : Fin count =>
        operation index.val (items.get index) index.isLt) (List.finRange count) κ steps ∧
      n = steps + Library.mapFinIdx.control (κ .visit) count,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single (fun index : Fin count =>
        operation index.val (items.get index) index.isLt) κ (List.finRange count)
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem mapFinIdx_val {count : Nat} (items : Vector α count)
    (operation : (index : Nat) → α → index < count → Costed β) :
    (mapFinIdx items operation).val =
      items.mapFinIdx fun index item bound => (operation index item bound).val := rfl

theorem mapFinIdx_within {count : Nat} {items : Vector α count}
    {operation : (index : Nat) → α → index < count → Costed β} {κ : Costs} {bound : Nat}
    (each : ∀ index : Fin count, (operation index.val (items.get index) index.isLt).Within κ bound) :
    (mapFinIdx items operation).Within κ (Library.mapFinIdx.work (κ .visit) count bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within (List.finRange count) (fun index _ => each index) steps work
    rw [List.length_finRange] at counted
    exact Nat.add_le_add_right counted _

@[inline] def ofFn {count : Nat} (operation : Fin count → Costed β) : Costed (Vector β count) :=
  ⟨Vector.ofFn fun index => (operation index).val,
    fun κ n => ∃ steps, mapSteps operation (List.finRange count) κ steps ∧
      n = steps + Library.ofFn.control (κ .visit) count,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single operation κ (List.finRange count)
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem ofFn_val {count : Nat} (operation : Fin count → Costed β) :
    (ofFn operation).val = Vector.ofFn fun index => (operation index).val := rfl

theorem ofFn_within {count : Nat} {operation : Fin count → Costed β} {κ : Costs} {bound : Nat}
    (each : ∀ index, (operation index).Within κ bound) :
    (ofFn operation).Within κ (Library.ofFn.work (κ .visit) count bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within (List.finRange count) (fun index _ => each index) steps work
    rw [List.length_finRange] at counted
    exact Nat.add_le_add_right counted _

@[inline] def attach (x : Costed α) : Costed {value : α // value = x.val} :=
  ⟨⟨x.val, rfl⟩, x.work, x.single⟩

theorem attach_val (x : Costed α) : (attach x).val.val = x.val := rfl

theorem attach_within {x : Costed α} {κ : Costs} {bound : Nat} (fits : x.Within κ bound) :
    (attach x).Within κ bound := fits

@[inline] def toList {count : Nat} (items : Vector α count) : Costed (List α) :=
  ⟨items.toList, fun κ n => n = Library.toList.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem toList_val {count : Nat} (items : Vector α count) : (toList items).val = items.toList :=
  rfl

theorem toList_within {count : Nat} (items : Vector α count) (κ : Costs) :
    (toList items).Within κ (Library.toList.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

@[inline] def arrayToList (items : Array α) : Costed (List α) :=
  ⟨items.toList, fun κ n => n = Library.toList.control (κ .visit) items.size,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem arrayToList_val (items : Array α) : (arrayToList items).val = items.toList := rfl

theorem arrayToList_within (items : Array α) (κ : Costs) :
    (arrayToList items).Within κ (Library.toList.control (κ .visit) items.size) :=
  fun _ same => Nat.le_of_eq same

@[inline] def drop (count : Nat) (items : List α) : Costed (List α) :=
  ⟨items.drop count, fun κ n => n = Library.drop.control (κ .visit) (min count items.length),
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem drop_val (count : Nat) (items : List α) : (drop count items).val = items.drop count :=
  rfl

theorem drop_within (count : Nat) (items : List α) (κ : Costs) :
    (drop count items).Within κ (Library.drop.control (κ .visit) count) :=
  fun _ same => by
    rw [same]
    exact Library.control_mono _ (Nat.min_le_left _ _)

@[inline] def finRange (count : Nat) : Costed (List (Fin count)) :=
  ⟨List.finRange count, fun κ n => n = Library.finRange.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem finRange_val (count : Nat) : (finRange count).val = List.finRange count := rfl

theorem finRange_within (count : Nat) (κ : Costs) :
    (finRange count).Within κ (Library.finRange.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

@[inline] def length (items : List α) : Costed Nat :=
  ⟨items.length, fun κ n => n = Library.length.control (κ .visit) items.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem length_val (items : List α) : (length items).val = items.length := rfl

theorem length_within (items : List α) (κ : Costs) :
    (length items).Within κ (Library.length.control (κ .visit) items.length) :=
  fun _ same => Nat.le_of_eq same

@[inline] def mem {bound : Nat} (item : Fin bound) (items : List (Fin bound))
    (_fits : bound < 2 ^ 32) : Costed Bool :=
  ⟨decide (item ∈ items), fun κ n => n = Library.contains.control (κ .visit + κ .compare)
    items.length, fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem mem_val {bound : Nat} (item : Fin bound) (items : List (Fin bound))
    (fits : bound < 2 ^ 32) : (mem item items fits).val = decide (item ∈ items) := rfl

theorem mem_within {bound : Nat} (item : Fin bound) (items : List (Fin bound))
    (fits : bound < 2 ^ 32) (κ : Costs) :
    (mem item items fits).Within κ
      (Library.contains.control (κ .visit + κ .compare) items.length) :=
  fun _ same => Nat.le_of_eq same

@[inline] def vectorEq {count : Nat} (first second : Vector Binary32 count) : Costed Bool :=
  ⟨decide (first = second), fun κ n => n = Library.vectorEq.control (κ .visit + κ .compare) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem vectorEq_val {count : Nat} (first second : Vector Binary32 count) :
    (vectorEq first second).val = decide (first = second) := rfl

theorem vectorEq_within {count : Nat} (first second : Vector Binary32 count) (κ : Costs) :
    (vectorEq first second).Within κ (Library.vectorEq.control (κ .visit + κ .compare) count) :=
  fun _ same => Nat.le_of_eq same

@[inline] def range (count : Nat) : Costed (List Nat) :=
  ⟨List.range count, fun κ n => n = Library.range.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem range_val (count : Nat) : (range count).val = List.range count := rfl

theorem range_within (count : Nat) (κ : Costs) :
    (range count).Within κ (Library.range.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

@[inline] def zipIdx (items : List α) (start : Nat := 0) : Costed (List (α × Nat)) :=
  ⟨items.zipIdx start, fun κ n => n = Library.zipIdx.control (κ .visit) items.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem zipIdx_val (items : List α) (start : Nat) :
    (zipIdx items start).val = items.zipIdx start := rfl

theorem zipIdx_within (items : List α) (start : Nat) (κ : Costs) :
    (zipIdx items start).Within κ (Library.zipIdx.control (κ .visit) items.length) :=
  fun _ same => Nat.le_of_eq same

@[inline] def append (first second : List α) : Costed (List α) :=
  ⟨first ++ second, fun κ n => n = Library.append.control (κ .visit) first.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem append_val (first second : List α) : (append first second).val = first ++ second := rfl

theorem append_within (first second : List α) (κ : Costs) :
    (append first second).Within κ (Library.append.control (κ .visit) first.length) :=
  fun _ same => Nat.le_of_eq same

@[inline] def prepend {count : Nat} (head : α) (tail : Vector α count) :
    Costed (Vector α (count + 1)) :=
  ⟨(#v[head] ++ tail).cast (Nat.add_comm 1 count),
    fun κ n => n = κ .read + Library.vectorAppend.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem prepend_val {count : Nat} (head : α) (tail : Vector α count) :
    (prepend head tail).val = (#v[head] ++ tail).cast (Nat.add_comm 1 count) := rfl

theorem prepend_within {count : Nat} (head : α) (tail : Vector α count) (κ : Costs) :
    (prepend head tail).Within κ (κ .read + Library.vectorAppend.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

@[inline] def reverse (items : List α) : Costed (List α) :=
  ⟨items.reverse, fun κ n => n = Library.reverse.control (κ .visit) items.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem reverse_val (items : List α) : (reverse items).val = items.reverse := rfl

theorem reverse_within (items : List α) (κ : Costs) :
    (reverse items).Within κ (Library.reverse.control (κ .visit) items.length) :=
  fun _ same => Nat.le_of_eq same

@[inline] def sum (items : List Int) : Costed Int :=
  ⟨items.sum, fun κ n => n = Library.sum.control (κ .visit + κ .sumTerm) items.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem sum_val (items : List Int) : (sum items).val = items.sum := rfl

theorem sum_within (items : List Int) (κ : Costs) :
    (sum items).Within κ (Library.sum.control (κ .visit + κ .sumTerm) items.length) :=
  fun _ same => Nat.le_of_eq same

end Costed

end Acorn
