/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Lifetime

/-!
# Integer observer classifications

Natural subtraction and logarithms use integer semantics. The browser backend
uses exact safe-integer inputs and repeated powers of two for log2, avoiding
floating logarithm rounding at bucket boundaries. Runtime arithmetic and the
small structural backend remain explicit trust boundaries.
-/
namespace Acorn.Host.Viewer.BrowserNat
variable {n : Nat}

/-- Closed natural expression vocabulary used by observer bin labels. -/
inductive Expr (n : Nat) where
  /-- Bounded argument reference. -/
  | input (index : Fin n)
  /-- Constant natural. -/
  | constant (value : Nat)
  /-- Natural addition. -/
  | add (left right : Expr n)
  /-- Saturating natural subtraction. -/
  | sub (left right : Expr n)
  /-- Minimum. -/
  | minimum (left right : Expr n)
  /-- Integer base-two logarithm, with log2 zero equal to zero. -/
  | logTwo (value : Expr n)
  /-- Exact power of two. -/
  | powerTwo (value : Expr n)
  /-- Ordered branch selection. -/
  | ifLess (left right yes no : Expr n)

/-- Native integer semantics. -/
def Expr.eval (values : Fin n → Nat) : Expr n → Nat
  | .input i => values i
  | .constant value => value
  | .add a b => a.eval values + b.eval values
  | .sub a b => a.eval values - b.eval values
  | .minimum a b => min (a.eval values) (b.eval values)
  | .logTwo x => (x.eval values).log2
  | .powerTwo x => 2 ^ x.eval values
  | .ifLess a b yes no => if a.eval values < b.eval values then yes.eval values else no.eval values

/-- Structural numeric backend for the admitted safe-integer domain. -/
def Expr.javascript (values : Fin n → String) : Expr n → String
  | .input i => values i
  | .constant value => toString value
  | .add a b => "(" ++ a.javascript values ++ "+" ++ b.javascript values ++ ")"
  | .sub a b => "Math.max(0," ++ a.javascript values ++ "-" ++ b.javascript values ++ ")"
  | .minimum a b => "Math.min(" ++ a.javascript values ++ "," ++ b.javascript values ++ ")"
  | .logTwo x => "observerLog2(" ++ x.javascript values ++ ")"
  | .powerTwo x => "(2**" ++ x.javascript values ++ ")"
  | .ifLess a b yes no => "(" ++ a.javascript values ++ "<" ++ b.javascript values ++ "?" ++
      yes.javascript values ++ ":" ++ no.javascript values ++ ")"

/-- Exact-cycle prefix and saturated logarithmic tail from the lifetime owner. -/
def cycleBucket : Expr 1 :=
  .ifLess (.input 0) (.constant FeatureConstants.exactCycles) (.input 0)
    (.minimum (.add (.constant FeatureConstants.exactCycles)
      (.logTwo (.add (.sub (.input 0) (.constant FeatureConstants.exactCycles)) (.constant 1))))
      (.constant (FeatureConstants.cycleBins - 1)))

/-- The native lifetime array owner and emitted expression classify every clock identically. -/
theorem cycleBucket_execution (cycle : UInt64) :
    cycleBucket.eval (fun _ => cycle.toNat) = (Lifetime.cycleBin cycle).val := by
  by_cases h : cycle.toNat < FeatureConstants.exactCycles
  · simp only [cycleBucket, Expr.eval, Lifetime.cycleBin, h, ↓reduceDIte, ↓reduceIte]
  · simp only [cycleBucket, Expr.eval, Lifetime.cycleBin, h, ↓reduceDIte, ↓reduceIte]

/-- First lifetime step of a logarithmic history bin, including the special zero bin. -/
def historyStart : Expr 1 :=
  .ifLess (.input 0) (.constant 1) (.constant 0) (.powerTwo (.input 0))

/-- One-based first cycle in the displayed bucket. -/
def cycleFirst : Expr 1 :=
  .ifLess (.input 0) (.constant FeatureConstants.exactCycles) (.add (.input 0) (.constant 1))
    (.add (.constant FeatureConstants.exactCycles)
      (.powerTwo (.sub (.input 0) (.constant FeatureConstants.exactCycles))))

/-- One-based last cycle before the saturated tail. -/
def cycleLast : Expr 1 :=
  .ifLess (.input 0) (.constant FeatureConstants.exactCycles) (.add (.input 0) (.constant 1))
    (.add (.constant (FeatureConstants.exactCycles - 1))
      (.powerTwo (.add (.sub (.input 0) (.constant FeatureConstants.exactCycles)) (.constant 1))))

/-- Generated integer classification and labels; the generic log primitive doubles exact powers. -/
def javascript : String :=
  "function observerLog2(x){let k=0,p=2;while(p<=x){k++;p*=2;}return k;}\n" ++
  String.join (([("observerCycleBucket", cycleBucket), ("observerHistoryStart", historyStart),
    ("observerCycleFirst", cycleFirst), ("observerCycleLast", cycleLast)]).map fun (name, program) =>
      "const " ++ name ++ "=(x)=>" ++ program.javascript (fun _ => "x") ++ ";\n")

end Acorn.Host.Viewer.BrowserNat
