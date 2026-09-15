/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.WireNumber

/-!
# Observer numeric programs

Programs have a closed arithmetic vocabulary and statically bounded input
references. The same expression owns native evaluation and JavaScript emission;
there is no independently maintained browser formula. ECMAScript binary64,
array reduction, and this small structural emitter remain trusted execution
boundaries. This does not assert a proved Lean-to-JavaScript compiler.

The finite-return sum follows Javed, Sharifnassab & Sutton, *SwiftTD: A Fast
and Robust Algorithm for Temporal Difference Learning*, Reinforcement Learning
Journal 2 (2024), pp. 840–863, §3 eq. (3). The adjacent-frame residual uses
the TD form in Appendix A.1 eq. (17), with reported projected predictions;
it does not claim equality to the learner's internal binary32 error.
Source: https://rlj.cs.umass.edu/2024/papers/RLJ_RLC_2024_111.pdf.
-/
namespace Acorn.Host.Viewer.BrowserMath

variable {n m p k : Nat} {α : Type}

/-- Closed unary numeric vocabulary of the observer. -/
inductive Unary where
  /-- Absolute value. -/
  | abs
  /-- Natural logarithm. -/
  | log
  /-- Ceiling. -/
  | ceil
  deriving Repr

/-- Closed binary numeric vocabulary of the observer. -/
inductive Binary where
  /-- Addition with explicit evaluation order. -/
  | add
  /-- Subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Division. -/
  | div
  /-- Minimum. -/
  | min
  /-- Maximum. -/
  | max
  deriving Repr

/-- Closed predicates for branch selection, including exceptional readings. -/
inductive Test where
  /-- Ordered strict comparison. -/
  | lt
  /-- Binary64 numeric equality. -/
  | eq
  /-- The left operand is finite; the right operand is unused. -/
  | finite
  deriving Repr

/-- Every expression reference belongs to its statically specified environment. -/
inductive Expr (n : Nat) where
  /-- Exact machine literal. -/
  | literal (value : Float)
  /-- Bounded input reference. -/
  | input (index : Fin n)
  /-- Unary operation. -/
  | unary (op : Unary) (value : Expr n)
  /-- Binary operation. -/
  | binary (op : Binary) (left right : Expr n)
  /-- Lazy choice preserves unavailable values without eager arithmetic. -/
  | choose (test : Test) (left right yes no : Expr n)

/-- Native semantics of the unary vocabulary. -/
def Unary.eval : Unary → Float → Float
  | .abs, x => x.abs
  | .log, x => x.log
  | .ceil, x => x.ceil

private def minimum (x y : Float) : Float :=
  if x.isNaN || y.isNaN then 0 / 0
  else if x < y then x else if y < x then y
  else if x.toBits == 0x8000000000000000 || y.toBits == 0x8000000000000000
    then Float.ofBits 0x8000000000000000 else x

private def maximum (x y : Float) : Float :=
  if x.isNaN || y.isNaN then 0 / 0
  else if x > y then x else if y > x then y
  else if x.toBits == 0 || y.toBits == 0 then 0 else x

/-- Native semantics of the binary vocabulary. -/
def Binary.eval : Binary → Float → Float → Float
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .min, x, y => minimum x y
  | .max, x, y => maximum x y

/-- Native predicate semantics. -/
def Test.eval : Test → Float → Float → Bool
  | .lt, x, y => x < y
  | .eq, x, y => x == y
  | .finite, x, _ => !x.isNaN && !x.isInf

/-- Structural evaluation has no parser, dynamic variable lookup, or partial indexing. -/
def Expr.eval (environment : Fin n → Float) : Expr n → Float
  | .literal value => value
  | .input index => environment index
  | .unary op value => op.eval (value.eval environment)
  | .binary op left right => op.eval (left.eval environment) (right.eval environment)
  | .choose test left right yes no =>
    if test.eval (left.eval environment) (right.eval environment)
    then yes.eval environment else no.eval environment

private def jsLiteral (value : Float) : String :=
  if value.isNaN then "NaN"
  else if value.isInf then if value < 0 then "(-Infinity)" else "Infinity"
  else "(" ++ binary64Text ⟨value.toBits⟩ ++ ")"

/-- Structural backend; all emitted identifiers are supplied by bounded positions. -/
def Expr.javascript (environment : Fin n → String) : Expr n → String
  | .literal value => jsLiteral value
  | .input index => environment index
  | .unary op value =>
    let name := match op with | .abs => "abs" | .log => "log" | .ceil => "ceil"
    s!"Math.{name}({value.javascript environment})"
  | .binary op left right =>
    let l := left.javascript environment
    let r := right.javascript environment
    match op with
    | .min => s!"Math.min({l},{r})"
    | .max => s!"Math.max({l},{r})"
    | _ =>
      let token := match op with | .add => "+" | .sub => "-" | .mul => "*" | _ => "/"
      s!"({l}{token}{r})"
  | .choose test left right yes no =>
    let l := left.javascript environment
    let r := right.javascript environment
    let condition := match test with
      | .lt => s!"({l}<{r})"
      | .eq => s!"({l}==={r})"
      | .finite => s!"Number.isFinite({l})"
    s!"({condition}?{yes.javascript environment}:{no.javascript environment})"

/-- A fold retains a fixed number of accumulators over rows of fixed width.
Environment positions are parameters, old accumulators, then the current row. -/
structure Fold (p k m : Nat) where
  /-- Initial accumulators. -/
  initial : Fin k → Expr p
  /-- Simultaneous next-accumulator expressions. -/
  step : Fin k → Expr (p + k + m)
  /-- Scalar result after the last row. -/
  result : Expr (p + k)

private def appendEnv (a : Fin n → α) (b : Fin m → α) (i : Fin (n + m)) : α :=
  if h : i.val < n then a ⟨i.val, h⟩ else b ⟨i.val - n, by omega⟩

/-- Native executable fold semantics over arbitrary finite observation rows. -/
def Fold.eval (program : Fold p k m) (parameters : Fin p → Float)
    (rows : List (Fin m → Float)) : Float :=
  let initial := fun i => (program.initial i).eval parameters
  let final := rows.foldl (fun state row => fun i =>
    (program.step i).eval (appendEnv (appendEnv parameters state) row)) initial
  program.result.eval (appendEnv parameters final)

private def expressions (n : Nat) (f : Fin n → String) : String :=
  "[" ++ String.intercalate "," ((List.finRange n).map f) ++ "]"

/-- Backend for one typed fold; row gathering belongs to the replay adapter. -/
def Fold.javascript (program : Fold p k m) : String :=
  let params := fun (i : Fin p) => s!"p[{i.val}]"
  let state := fun (i : Fin k) => s!"a[{i.val}]"
  let row := fun (i : Fin m) => s!"x[{i.val}]"
  let initial := expressions k fun i => (program.initial i).javascript params
  let step := expressions k fun i =>
    (program.step i).javascript (appendEnv (appendEnv params state) row)
  let result := program.result.javascript (appendEnv params state)
  "(p,rows)=>{const a=rows.reduce((a,x)=>" ++ step ++ "," ++ initial ++
    ");return " ++ result ++ ";}"

/-- Empty folds return the initial-state result for every parameter environment. -/
theorem Fold.eval_nil (program : Fold p k m) (parameters : Fin p → Float) :
    program.eval parameters [] = program.result.eval
      (appendEnv parameters fun i => (program.initial i).eval parameters) := rfl

private def c (value : Float) : Expr n := .literal value
private def ref (index : Fin n) : Expr n := .input index
private def add : Expr n → Expr n → Expr n := .binary .add
private def sub : Expr n → Expr n → Expr n := .binary .sub
private def mul : Expr n → Expr n → Expr n := .binary .mul
private def divide : Expr n → Expr n → Expr n := .binary .div
private def absolute : Expr n → Expr n := .unary .abs
private def finite (x yes no : Expr n) : Expr n := .choose .finite x (c 0) yes no
private def positive (x yes no : Expr n) : Expr n := .choose .lt (c 0) x yes no

/-- Ordered sum includes every member, including unavailable readings. -/
def sum : Fold 0 1 1 where
  initial := fun _ => c 0
  step := fun _ => add (ref 0) (ref 1)
  result := ref 0

/-- Frame-weighted mean with explicit unavailable empty-window result. -/
def mean : Fold 0 2 1 where
  initial := fun _ => c 0
  step := fun i => if i.val == 0 then add (ref 0) (ref 2) else add (ref 1) (c 1)
  result := positive (ref 1) (divide (ref 0) (ref 1)) (c (0/0))

/-- Mean absolute readings preserve nonfinite members as unavailable. -/
def meanAbsolute : Fold 0 2 1 :=
  { mean with step := fun i =>
      if i.val == 0 then add (ref 0) (absolute (ref 2)) else add (ref 1) (c 1) }

/-- Number of observations equal to the requested closed-domain label. -/
def countEqual : Fold 1 1 1 where
  initial := fun _ => c 0
  step := fun _ => .choose .eq (ref 0) (ref 2) (add (ref 1) (c 1)) (ref 1)
  result := ref 1

/-- Positive finite rates contribute; any nonfinite reading makes the mean unavailable.
An all-idle finite family has rate zero. -/
def meanPositive : Fold 0 2 1 where
  initial := fun _ => c 0
  step := fun i =>
    if i.val == 0 then
      finite (ref 2) (positive (ref 2) (add (ref 0) (ref 2)) (ref 0)) (c (0/0))
    else finite (ref 2) (positive (ref 2) (add (ref 1) (c 1)) (ref 1)) (add (ref 1) (c 1))
  result := positive (ref 1) (divide (ref 0) (ref 1)) (c 0)

/-- Finite return preserves the forward accumulator and weight multiplication order.
The sole parameter is gamma; each row carries one future cumulant. -/
def finiteReturn : Fold 1 2 1 where
  initial := fun i => c (if i.val == 0 then 0 else 1)
  step := fun i => if i.val == 0 then add (ref 1) (mul (ref 2) (ref 3)) else mul (ref 2) (ref 0)
  result := ref 1

/-- Mean absolute TD residual over rows containing cumulant, gamma, current and previous prediction. -/
def tdSurprise : Fold 0 2 4 where
  initial := fun _ => c 0
  step := fun i => if i.val == 0 then
    add (ref 0) (absolute (sub (add (ref 2) (mul (ref 3) (ref 4))) (ref 5)))
    else add (ref 1) (c 1)
  result := positive (ref 1) (divide (ref 0) (ref 1)) (c (0/0))

/-- Both latency readings must be finite to contribute to the selected column's mean.
Rows are ordered selected latency first, companion latency second. -/
def pairedLatency : Fold 0 2 2 where
  initial := fun _ => c 0
  step := fun i =>
    let changed := if i.val == 0 then add (ref 0) (ref 2) else add (ref 1) (c 1)
    finite (ref 2) (finite (ref 3) changed (ref ⟨i.val, by omega⟩)) (ref ⟨i.val, by omega⟩)
  result := positive (ref 1) (divide (ref 0) (ref 1)) (c (0/0))

/-- Settled prediction error divided by the unit-cumulant discounted range. -/
def normalizedError : Expr 3 :=
  divide (absolute (sub (ref 0) (ref 1))) (divide (c 1) (sub (c 1) (ref 2)))

/-- Display settlement horizon with the declared eight-to-six-hundred frame bounds. -/
def horizon : Expr 1 :=
  .binary .min (c 600) (.binary .max (c 8)
    (.unary .ceil (divide (.unary .log (c 0.01)) (.unary .log (ref 0)))))

/-- Relative trend change with explicit near-zero denominator semantics. -/
def relativeChange : Expr 2 :=
  .choose .lt (c 1e-12) (absolute (ref 1))
    (divide (sub (ref 0) (ref 1)) (absolute (ref 1)))
    (.choose .eq (ref 0) (ref 1) (c 0) (c (1/0)))

/-- Signed trend classification; NaN marks an unavailable comparison. -/
def trend : Expr 2 :=
  finite (ref 0) (finite (ref 1)
    (.choose .lt (absolute relativeChange) (c 0.05) (c 0)
      (.choose .lt (ref 1) (ref 0) (c 1) (c (-1)))) (c (0/0))) (c (0/0))

/-- Newest lifetime bin remains provisional below one eighth of its predecessor. -/
def filling : Expr 2 :=
  .choose .lt (ref 0) (divide (ref 1) (c 8)) (c 1) (c 0)

/-- The displayed historical-error trend requires thirty samples in each half. -/
def enoughSamples : Expr 1 :=
  .choose .lt (ref 0) (c 30) (c 0) (c 1)

private def scalar (program : Expr n) : String :=
  "(...p)=>" ++ program.javascript (fun i => s!"p[{i.val}]")

/-- Browser kernel is generated exclusively from the maintained numeric programs. -/
def javascript : String :=
  "const ObserverMath=Object.freeze({\n" ++ String.intercalate ",\n"
    ["sum:" ++ sum.javascript, "mean:" ++ mean.javascript,
     "meanAbsolute:" ++ meanAbsolute.javascript, "countEqual:" ++ countEqual.javascript,
     "ratio:" ++ scalar (divide (ref (0 : Fin 2)) (ref 1)),
     "meanPositive:" ++ meanPositive.javascript, "finiteReturn:" ++ finiteReturn.javascript,
     "tdSurprise:" ++ tdSurprise.javascript, "pairedLatency:" ++ pairedLatency.javascript,
     "normalizedError:" ++ scalar normalizedError, "horizon:" ++ scalar horizon,
     "relativeChange:" ++ scalar relativeChange, "trend:" ++ scalar trend,
     "filling:" ++ scalar filling, "enoughSamples:" ++ scalar enoughSamples] ++ "\n});\n"

end Acorn.Host.Viewer.BrowserMath
