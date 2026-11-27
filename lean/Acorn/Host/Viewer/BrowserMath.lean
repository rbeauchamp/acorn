import Acorn.Host.Viewer.WireNumber

namespace Acorn.Host.Viewer.BrowserMath

variable {n m p k : Nat} {α : Type}

inductive Unary where
  | abs
  | log
  | ceil
  deriving Repr

inductive Binary where
  | add
  | sub
  | mul
  | div
  | min
  | max
  deriving Repr

inductive Test where
  | lt
  | eq
  | finite
  deriving Repr

inductive Expr (n : Nat) where
  | literal (value : Float)
  | input (index : Fin n)
  | unary (op : Unary) (value : Expr n)
  | binary (op : Binary) (left right : Expr n)
  | choose (test : Test) (left right yes no : Expr n)

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

def Binary.eval : Binary → Float → Float → Float
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .min, x, y => minimum x y
  | .max, x, y => maximum x y

def Test.eval : Test → Float → Float → Bool
  | .lt, x, y => x < y
  | .eq, x, y => x == y
  | .finite, x, _ => !x.isNaN && !x.isInf

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

structure Fold (p k m : Nat) where
  initial : Fin k → Expr p
  step : Fin k → Expr (p + k + m)
  result : Expr (p + k)

private def appendEnv (a : Fin n → α) (b : Fin m → α) (i : Fin (n + m)) : α :=
  if h : i.val < n then a ⟨i.val, h⟩ else b ⟨i.val - n, by omega⟩

def Fold.eval (program : Fold p k m) (parameters : Fin p → Float)
    (rows : List (Fin m → Float)) : Float :=
  let initial := fun i => (program.initial i).eval parameters
  let final := rows.foldl (fun state row => fun i =>
    (program.step i).eval (appendEnv (appendEnv parameters state) row)) initial
  program.result.eval (appendEnv parameters final)

private def expressions (n : Nat) (f : Fin n → String) : String :=
  "[" ++ String.intercalate "," ((List.finRange n).map f) ++ "]"

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

def sum : Fold 0 1 1 where
  initial := fun _ => c 0
  step := fun _ => add (ref 0) (ref 1)
  result := ref 0

def mean : Fold 0 2 1 where
  initial := fun _ => c 0
  step := fun i => if i.val == 0 then add (ref 0) (ref 2) else add (ref 1) (c 1)
  result := positive (ref 1) (divide (ref 0) (ref 1)) (c (0/0))

def meanAbsolute : Fold 0 2 1 :=
  { mean with step := fun i =>
      if i.val == 0 then add (ref 0) (absolute (ref 2)) else add (ref 1) (c 1) }

def countEqual : Fold 1 1 1 where
  initial := fun _ => c 0
  step := fun _ => .choose .eq (ref 0) (ref 2) (add (ref 1) (c 1)) (ref 1)
  result := ref 1

def meanPositive : Fold 0 2 1 where
  initial := fun _ => c 0
  step := fun i =>
    if i.val == 0 then
      finite (ref 2) (positive (ref 2) (add (ref 0) (ref 2)) (ref 0)) (c (0/0))
    else finite (ref 2) (positive (ref 2) (add (ref 1) (c 1)) (ref 1)) (add (ref 1) (c 1))
  result := positive (ref 1) (divide (ref 0) (ref 1)) (c 0)

def finiteReturn : Fold 1 2 1 where
  initial := fun i => c (if i.val == 0 then 0 else 1)
  step := fun i => if i.val == 0 then add (ref 1) (mul (ref 2) (ref 3)) else mul (ref 2) (ref 0)
  result := ref 1

def tdSurprise : Fold 0 2 4 where
  initial := fun _ => c 0
  step := fun i => if i.val == 0 then
    add (ref 0) (absolute (sub (add (ref 2) (mul (ref 3) (ref 4))) (ref 5)))
    else add (ref 1) (c 1)
  result := positive (ref 1) (divide (ref 0) (ref 1)) (c (0/0))

def pairedLatency : Fold 0 2 2 where
  initial := fun _ => c 0
  step := fun i =>
    let changed := if i.val == 0 then add (ref 0) (ref 2) else add (ref 1) (c 1)
    finite (ref 2) (finite (ref 3) changed (ref ⟨i.val, by omega⟩)) (ref ⟨i.val, by omega⟩)
  result := positive (ref 1) (divide (ref 0) (ref 1)) (c (0/0))

def normalizedError : Expr 3 :=
  divide (absolute (sub (ref 0) (ref 1))) (divide (c 1) (sub (c 1) (ref 2)))

def horizon : Expr 1 :=
  .binary .min (c 600) (.binary .max (c 8)
    (.unary .ceil (divide (.unary .log (c 0.01)) (.unary .log (ref 0)))))

def relativeChange : Expr 2 :=
  .choose .lt (c 1e-12) (absolute (ref 1))
    (divide (sub (ref 0) (ref 1)) (absolute (ref 1)))
    (.choose .eq (ref 0) (ref 1) (c 0) (c (1/0)))

def trend : Expr 2 :=
  finite (ref 0) (finite (ref 1)
    (.choose .lt (absolute relativeChange) (c 0.05) (c 0)
      (.choose .lt (ref 1) (ref 0) (c 1) (c (-1)))) (c (0/0))) (c (0/0))

def filling : Expr 2 :=
  .choose .lt (ref 0) (divide (ref 1) (c 8)) (c 1) (c 0)

def enoughSamples : Expr 1 :=
  .choose .lt (ref 0) (c 30) (c 0) (c 1)

private def scalar (program : Expr n) : String :=
  "(...p)=>" ++ program.javascript (fun i => s!"p[{i.val}]")

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
