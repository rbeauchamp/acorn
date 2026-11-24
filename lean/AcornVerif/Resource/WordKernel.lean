import Init

namespace AcornVerif.Resource

inductive WordOp where
  | primitive (name : String)
  | cacheRead (name : String) (once : Bool)
  | literal
  | scalarRead
  | allocate (pointers scalarBytes : Nat)
  | box (kind : String)
  | retain
  | call (name : String)
  | branchSelect
  | transfer
  deriving Repr

inductive WordTree where
  | done
  | step (op : WordOp) (next : WordTree)
  | seq (first next : WordTree)
  | branch (left right : WordTree)
  deriving Repr

def WordTree.bound : WordTree → Nat
  | .done => 0
  | .step _ next => 1 + next.bound
  | .seq first next => first.bound + next.bound
  | .branch left right => 1 + max left.bound right.bound

inductive WordTree.Exec : WordTree → Nat → Prop where
  | done : Exec .done 0
  | step {next : WordTree} {cost : Nat} (op : WordOp) :
      Exec next cost → Exec (.step op next) (1 + cost)
  | seq {first next : WordTree} {a b : Nat} :
      Exec first a → Exec next b → Exec (.seq first next) (a + b)
  | left {left right : WordTree} {cost : Nat} :
      Exec left cost → Exec (.branch left right) (1 + cost)
  | right {left right : WordTree} {cost : Nat} :
      Exec right cost → Exec (.branch left right) (1 + cost)

theorem WordTree.exec_le_bound {tree : WordTree} {cost : Nat}
    (execution : tree.Exec cost) : cost ≤ tree.bound := by
  induction execution with
  | done => exact Nat.le_refl _
  | step _ _ ih => exact Nat.add_le_add_left ih 1
  | seq _ _ ih₁ ih₂ => exact Nat.add_le_add ih₁ ih₂
  | left _ ih => exact Nat.add_le_add_left (Nat.le_trans ih (Nat.le_max_left _ _)) 1
  | right _ ih => exact Nat.add_le_add_left (Nat.le_trans ih (Nat.le_max_right _ _)) 1

theorem WordTree.bound_attained (tree : WordTree) : tree.Exec tree.bound := by
  induction tree with
  | done => exact .done
  | step op next ih => exact .step op ih
  | seq first next ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch left right ih₁ ih₂ =>
    by_cases h : left.bound ≤ right.bound
    · simpa only [bound, Nat.max_eq_right h] using WordTree.Exec.right (right := right) (left := left) ih₂
    · simpa only [bound, Nat.max_eq_left (Nat.le_of_not_ge h)] using WordTree.Exec.left (right := right) ih₁

abbrev CostModel := WordOp → Nat

def WordTree.cost (model : CostModel) : WordTree → Nat
  | .done => 0
  | .step op next => model op + next.cost model
  | .seq first next => first.cost model + next.cost model
  | .branch left right => model .branchSelect + max (left.cost model) (right.cost model)

def WordTree.repeatBody (count : Nat) (body : WordTree) : WordTree :=
  match count with
  | 0 => .done
  | n + 1 => .seq body (repeatBody n body)

theorem WordTree.repeatBody_cost (count : Nat) (body : WordTree) (model : CostModel) :
    (repeatBody count body).cost model = count * body.cost model := by
  induction count with
  | zero => simp only [repeatBody, cost, Nat.zero_mul]
  | succ n ih => simp only [repeatBody, cost, ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

inductive WordTree.CostExec (model : CostModel) : WordTree → Nat → Prop where
  | done : CostExec model .done 0
  | step {next : WordTree} {cost : Nat} (op : WordOp) :
      CostExec model next cost → CostExec model (.step op next) (model op + cost)
  | seq {first next : WordTree} {a b : Nat} :
      CostExec model first a → CostExec model next b → CostExec model (.seq first next) (a + b)
  | left {left right : WordTree} {cost : Nat} :
      CostExec model left cost → CostExec model (.branch left right) (model .branchSelect + cost)
  | right {left right : WordTree} {cost : Nat} :
      CostExec model right cost → CostExec model (.branch left right) (model .branchSelect + cost)

theorem WordTree.costExec_le_cost {model : CostModel} {tree : WordTree} {cost : Nat}
    (execution : tree.CostExec model cost) : cost ≤ tree.cost model := by
  induction execution with
  | done => exact Nat.le_refl _
  | step _ _ ih => exact Nat.add_le_add_left ih _
  | seq _ _ ih₁ ih₂ => exact Nat.add_le_add ih₁ ih₂
  | left _ ih => exact Nat.add_le_add_left (Nat.le_trans ih (Nat.le_max_left _ _)) _
  | right _ ih => exact Nat.add_le_add_left (Nat.le_trans ih (Nat.le_max_right _ _)) _

theorem WordTree.cost_unit (tree : WordTree) : tree.cost (fun _ => 1) = tree.bound := by
  induction tree with
  | done => rfl
  | step op next ih => simp only [cost, bound, ih]
  | seq first next ih₁ ih₂ => simp only [cost, bound, ih₁, ih₂]
  | branch left right ih₁ ih₂ => simp only [cost, bound, ih₁, ih₂]

structure InitCell where
  name : String
  body : WordTree

def initCredit (model : CostModel) (pending : List InitCell) : Nat :=
  (pending.map (fun cell => cell.body.cost model)).sum

inductive InitExec (model : CostModel) : List InitCell → Nat → List InitCell → Prop where
  | done (pending : List InitCell) : InitExec model pending 0 pending
  | take {before after remaining : List InitCell} {cell : InitCell} {first rest : Nat} :
      cell.body.CostExec model first → InitExec model (before ++ after) rest remaining →
      InitExec model (before ++ cell :: after) (first + rest) remaining

theorem InitExec.credit_bound {model : CostModel} {pending remaining : List InitCell}
    {work : Nat} (execution : InitExec model pending work remaining) :
    work + initCredit model remaining ≤ initCredit model pending := by
  induction execution with
  | done => simp
  | take first _ ih =>
    have hf := WordTree.costExec_le_cost first
    simp only [initCredit, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at ih ⊢
    omega

inductive HalvingExec (model : CostModel) (body : WordTree) : Nat → Nat → Prop where
  | stop {cost : Nat} : body.CostExec model cost → HalvingExec model body 0 cost
  | step {counter first rest : Nat} : 0 < counter → body.CostExec model first →
      HalvingExec model body (counter / 2) rest →
      HalvingExec model body counter (first + rest)

theorem HalvingExec.cost_bound {model : CostModel} {body : WordTree}
    {width counter cost : Nat} (execution : HalvingExec model body counter cost)
    (fits : counter < 2^width) : cost ≤ (width + 1) * body.cost model := by
  induction width generalizing counter cost with
  | zero =>
    have hz : counter = 0 := by simpa using fits
    subst counter
    cases execution with
    | stop h => simpa using WordTree.costExec_le_cost h
    | step positive _ _ => omega
  | succ width ih =>
    cases execution with
    | stop h =>
      have hb := WordTree.costExec_le_cost h
      have hm := Nat.mul_le_mul_right (body.cost model) (show 1 ≤ width + 1 + 1 by omega)
      simp only [Nat.one_mul] at hm
      exact Nat.le_trans hb hm
    | step positive first rest =>
      have small : counter / 2 < 2^width := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
        simpa only [Nat.pow_succ] using fits
      have hr := ih rest small
      have hf := WordTree.costExec_le_cost first
      have total := Nat.add_le_add hf hr
      simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using total

structure BudgetedTree (limit : Nat) where
  tree : WordTree
  fits : tree.bound ≤ limit

def WordTree.admit (tree : WordTree) (limit : Nat) : Option (BudgetedTree limit) :=
  if h : tree.bound ≤ limit then some ⟨tree, h⟩ else none

theorem BudgetedTree.exec_le_limit {limit : Nat} (admitted : BudgetedTree limit)
    {cost : Nat} (execution : admitted.tree.Exec cost) : cost ≤ limit :=
  Nat.le_trans (WordTree.exec_le_bound execution) admitted.fits

end AcornVerif.Resource
