/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# Finite scalar execution resource model

This is a control/resource abstraction of admitted compiler IR, not a second
implementation of numerical functions. The native resource audit extracts trees from actual compiler declarations.
Weighted costs retain primitive and callee identities; the unit interpretation
is only a structural regression budget. Ordinary roots exclude heap operations
except explicit bounded integer egress; startup admits reviewed constructors.
Unknown calls and cycles are rejected, with a separately checked halving loop. Extraction,
compiler lowering and the reviewed native primitives remain trusted boundaries.
No unit denotes seconds, bytes, energy, or a hardware instruction.
-/

namespace AcornVerif.Resource

/-- Closed instruction domain for numerical execution and its initialization.
There is no general arithmetic, indirect call or unaccounted back edge. -/
inductive WordOp where
  /-- Fixed-width scalar primitive. -/
  | primitive (name : String)
  /-- Read a cached scalar or object; the flag distinguishes once access from a global load. -/
  | cacheRead (name : String) (once : Bool)
  /-- Scalar literal. -/
  | literal
  /-- Read one scalar field from an already allocated, borrowed interval. -/
  | scalarRead
  /-- A startup constructor carries its pointer and scalar storage sizes. -/
  | allocate (pointers scalarBytes : Nat)
  /-- A startup scalar box retains its exact native representation. -/
  | box (kind : String)
  /-- Startup retains one already constructed object reference. -/
  | retain
  /-- Direct call with its body accounted separately. -/
  | call (name : String)
  /-- Conditional branch selection, distinct from an unconditional transfer. -/
  | branchSelect
  /-- Return or jump to an admitted acyclic continuation. -/
  | transfer
  deriving Repr

/-- A finite expansion of scalar instructions, calls and branch alternatives.
Unknown branch conditions are deliberately overapproximated by either arm. -/
inductive WordTree where
  /-- No remaining execution. -/
  | done
  /-- One instruction followed by a continuation. -/
  | step (op : WordOp) (next : WordTree)
  /-- Sequential execution, including an expanded direct call. -/
  | seq (first next : WordTree)
  /-- One branch instruction followed by one of two alternatives. -/
  | branch (left right : WordTree)
  deriving Repr

/-- Worst-path bound derived from the complete admitted tree. -/
def WordTree.bound : WordTree → Nat
  | .done => 0
  | .step _ next => 1 + next.bound
  | .seq first next => first.bound + next.bound
  | .branch left right => 1 + max left.bound right.bound

/-- Resource semantics. A derivation describes any possible finite branch
selection; it assumes nothing about the numerical values choosing the path. -/
inductive WordTree.Exec : WordTree → Nat → Prop where
  /-- Empty execution costs zero. -/
  | done : Exec .done 0
  /-- Every admitted instruction costs one abstract unit. -/
  | step {next : WordTree} {cost : Nat} (op : WordOp) :
      Exec next cost → Exec (.step op next) (1 + cost)
  /-- Sequential costs add. -/
  | seq {first next : WordTree} {a b : Nat} :
      Exec first a → Exec next b → Exec (.seq first next) (a + b)
  /-- The left branch includes branch-selection cost. -/
  | left {left right : WordTree} {cost : Nat} :
      Exec left cost → Exec (.branch left right) (1 + cost)
  /-- The right branch includes branch-selection cost. -/
  | right {left right : WordTree} {cost : Nat} :
      Exec right cost → Exec (.branch left right) (1 + cost)

/-- Every execution path is bounded by the structural bound, universally over
trees and branch choices. No enumeration or certified re-execution is needed. -/
theorem WordTree.exec_le_bound {tree : WordTree} {cost : Nat}
    (execution : tree.Exec cost) : cost ≤ tree.bound := by
  induction execution with
  | done => exact Nat.le_refl _
  | step _ _ ih => exact Nat.add_le_add_left ih 1
  | seq _ _ ih₁ ih₂ => exact Nat.add_le_add ih₁ ih₂
  | left _ ih => exact Nat.add_le_add_left (Nat.le_trans ih (Nat.le_max_left _ _)) 1
  | right _ ih => exact Nat.add_le_add_left (Nat.le_trans ih (Nat.le_max_right _ _)) 1

/-- The abstract bound is attained by some branch selection. This excludes a
vacuous resource contract; a concrete program may take fewer feasible paths. -/
theorem WordTree.bound_attained (tree : WordTree) : tree.Exec tree.bound := by
  induction tree with
  | done => exact .done
  | step op next ih => exact .step op ih
  | seq first next ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch left right ih₁ ih₂ =>
    by_cases h : left.bound ≤ right.bound
    · simpa only [bound, Nat.max_eq_right h] using WordTree.Exec.right (right := right) (left := left) ih₂
    · simpa only [bound, Nat.max_eq_left (Nat.le_of_not_ge h)] using WordTree.Exec.left (right := right) ih₁

/-- A platform interpretation supplies a nonnegative cost for each admitted
instruction, retaining exact primitive identity. No particular assignment is
assumed to represent time or bytes without a justified external platform model. -/
abbrev CostModel := WordOp → Nat

/-- Weighted worst-path cost follows the extracted body and branch structure.
Unlike the unit bound, it distinguishes each admitted native primitive. -/
def WordTree.cost (model : CostModel) : WordTree → Nat
  | .done => 0
  | .step op next => model op + next.cost model
  | .seq first next => first.cost model + next.cost model
  | .branch left right => model .branchSelect + max (left.cost model) (right.cost model)

/-- A fixed number of already admitted bodies, used after proving a loop bound. -/
def WordTree.repeatBody (count : Nat) (body : WordTree) : WordTree :=
  match count with
  | 0 => .done
  | n + 1 => .seq body (repeatBody n body)

/-- Repeated-body cost is derived by composition, for every primitive interpretation. -/
theorem WordTree.repeatBody_cost (count : Nat) (body : WordTree) (model : CostModel) :
    (repeatBody count body).cost model = count * body.cost model := by
  induction count with
  | zero => simp only [repeatBody, cost, Nat.zero_mul]
  | succ n ih => simp only [repeatBody, cost, ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Weighted execution follows the same admitted tree under any platform model. -/
inductive WordTree.CostExec (model : CostModel) : WordTree → Nat → Prop where
  /-- Empty execution contributes no work. -/
  | done : CostExec model .done 0
  /-- The named instruction contributes its interpreted cost. -/
  | step {next : WordTree} {cost : Nat} (op : WordOp) :
      CostExec model next cost → CostExec model (.step op next) (model op + cost)
  /-- Calls and continuations compose additively. -/
  | seq {first next : WordTree} {a b : Nat} :
      CostExec model first a → CostExec model next b → CostExec model (.seq first next) (a + b)
  /-- Left branch with its selection cost. -/
  | left {left right : WordTree} {cost : Nat} :
      CostExec model left cost → CostExec model (.branch left right) (model .branchSelect + cost)
  /-- Right branch with its selection cost. -/
  | right {left right : WordTree} {cost : Nat} :
      CostExec model right cost → CostExec model (.branch left right) (model .branchSelect + cost)

/-- Every path obeys the extracted weighted bound for every cost assignment.
The theorem does not assert that an assignment describes a physical machine. -/
theorem WordTree.costExec_le_cost {model : CostModel} {tree : WordTree} {cost : Nat}
    (execution : tree.CostExec model cost) : cost ≤ tree.cost model := by
  induction execution with
  | done => exact Nat.le_refl _
  | step _ _ ih => exact Nat.add_le_add_left ih _
  | seq _ _ ih₁ ih₂ => exact Nat.add_le_add ih₁ ih₂
  | left _ ih => exact Nat.add_le_add_left (Nat.le_trans ih (Nat.le_max_left _ _)) _
  | right _ ih => exact Nat.add_le_add_left (Nat.le_trans ih (Nat.le_max_right _ _)) _

/-- The unit-count contract is the constant-one interpretation of the same tree. -/
theorem WordTree.cost_unit (tree : WordTree) : tree.cost (fun _ => 1) = tree.bound := by
  induction tree with
  | done => rfl
  | step op next ih => simp only [cost, bound, ih]
  | seq first next ih₁ ih₂ => simp only [cost, bound, ih₁, ih₂]
  | branch left right ih₁ ih₂ => simp only [cost, bound, ih₁, ih₂]

/-- One distinct compiler-owned cached value and its initializer body. -/
structure InitCell where
  /-- Compiler identity, used to deduplicate shared initializers. -/
  name : String
  /-- Extracted initializer body, with dependent reads represented explicitly. -/
  body : WordTree

/-- Remaining first-use credit includes each pending initializer once. -/
def initCredit (model : CostModel) (pending : List InitCell) : Nat :=
  (pending.map (fun cell => cell.body.cost model)).sum

/-- Single-thread startup or first-use execution consumes a cell on its first visit.
The compiler/runtime once primitive owns this transition at native execution. -/
inductive InitExec (model : CostModel) : List InitCell → Nat → List InitCell → Prop where
  /-- No initialization is needed. -/
  | done (pending : List InitCell) : InitExec model pending 0 pending
  /-- An initializer runs once and is absent from all subsequent pending states. -/
  | take {before after remaining : List InitCell} {cell : InitCell} {first rest : Nat} :
      cell.body.CostExec model first → InitExec model (before ++ after) rest remaining →
      InitExec model (before ++ cell :: after) (first + rest) remaining

/-- First-use work is paid by the finite initial credit, independently of call
order or which subset of initializers is ever reached. -/
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

/-- A halving loop executes one extracted body per nonzero counter and one
final body at zero. Each iteration permits every admitted branch choice. -/
inductive HalvingExec (model : CostModel) (body : WordTree) : Nat → Nat → Prop where
  /-- The zero counter takes the final exit body. -/
  | stop {cost : Nat} : body.CostExec model cost → HalvingExec model body 0 cost
  /-- A positive counter executes the body and recurs on its integer half. -/
  | step {counter first rest : Nat} : 0 < counter → body.CostExec model first →
      HalvingExec model body (counter / 2) rest →
      HalvingExec model body counter (first + rest)

/-- A counter below 2^width permits at most width nonzero iterations and one
exit body. The argument follows halving, without enumerating word values. -/
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

/-- An admitted tree carries its resource bound at the admission boundary. -/
structure BudgetedTree (limit : Nat) where
  /-- Extracted execution tree. -/
  tree : WordTree
  /-- Every structural path fits the declared budget. -/
  fits : tree.bound ≤ limit

/-- Resource admission is derived from the exact structural bound. -/
def WordTree.admit (tree : WordTree) (limit : Nat) : Option (BudgetedTree limit) :=
  if h : tree.bound ≤ limit then some ⟨tree, h⟩ else none

/-- Every execution of an admitted tree fits its declared resource budget. -/
theorem BudgetedTree.exec_le_limit {limit : Nat} (admitted : BudgetedTree limit)
    {cost : Nat} (execution : admitted.tree.Exec cost) : cost ≤ limit :=
  Nat.le_trans (WordTree.exec_le_bound execution) admitted.fits

end AcornVerif.Resource
