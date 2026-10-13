/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Lifetime
import Acorn.Host.WorldState

/-!
# Integer observer classifications

Natural subtraction, division, remainders and logarithms use integer
semantics. The browser backend uses exact safe-integer inputs and repeated
powers of two for log2, avoiding floating logarithm rounding at bucket
boundaries. Its division takes the floor of the binary64 quotient, which is the
integer quotient for safe-integer operands: rounded once to nearest, the quotient
moves by at most 2⁻⁵³ of itself, which is less than the reciprocal of the
divisor, while the exact quotient lies at least that reciprocal below the next
integer. Runtime arithmetic and the small structural backend remain explicit
trust boundaries.
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
  /-- Maximum. -/
  | maximum (left right : Expr n)
  /-- Natural division, with a zero divisor giving zero. -/
  | div (left right : Expr n)
  /-- Natural remainder, with a zero divisor giving the dividend. -/
  | mod (left right : Expr n)
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
  | .maximum a b => max (a.eval values) (b.eval values)
  | .div a b => a.eval values / b.eval values
  | .mod a b => a.eval values % b.eval values
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
  | .maximum a b => "Math.max(" ++ a.javascript values ++ "," ++ b.javascript values ++ ")"
  | .div a b => "observerDiv(" ++ a.javascript values ++ "," ++ b.javascript values ++ ")"
  | .mod a b => "observerMod(" ++ a.javascript values ++ "," ++ b.javascript values ++ ")"
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

/-- The arguments of `dayPhase`: the clock of the world, then the length of its day. -/
def dayArguments (clock length : Nat) : Fin 2 → Nat
  | ⟨0, _⟩ => clock
  | ⟨_ + 1, _⟩ => length

/-- The phase of the day from the clock and the day length, by the formula of
`Host.World.dayPhase`: the slot of the clock in the day, its half and its eighth of at least one
step, and in each half four phases. -/
def dayPhase : Expr 2 :=
  let slot : Expr 2 := .mod (.input 0) (.input 1)
  let half : Expr 2 := .div (.input 1) (.constant 2)
  let eighth : Expr 2 :=
    .maximum (.constant 1) (.div (.input 1) (.constant FeatureConstants.dayPhases))
  let last : Expr 2 := .constant (FeatureConstants.dayPhases / 2 - 1)
  .ifLess slot half (.minimum (.div slot eighth) last)
    (.add (.constant (FeatureConstants.dayPhases / 2))
      (.minimum (.div (.sub slot half) eighth) last))

/-- The natural-number semantics of the program is the phase of the day that the world observes
and charges, for every configuration and world. The statement is about `Expr.eval`, not the
emitted JavaScript: the page's `observerDayPhase` agrees with it on admitted safe-integer inputs,
under the emitter and runtime assumptions of this module. -/
theorem dayPhase_execution {config : Host.WorldConfig} (world : Host.World config) :
    dayPhase.eval (dayArguments world.time.toNat config.raw.dayLength.toNat) =
      world.dayPhase.val := by
  simp only [dayPhase, Expr.eval, dayArguments]
  unfold Host.World.dayPhase
  dsimp only
  by_cases first :
      world.time.toNat % config.raw.dayLength.toNat < config.raw.dayLength.toNat / 2 <;>
    simp only [first, ↓reduceIte]

/-- Generated integer classification and labels; the generic log primitive doubles exact powers,
and division and remainder by zero give zero and the dividend, as natural numbers do. -/
def javascript : String :=
  "function observerLog2(x){let k=0,p=2;while(p<=x){k++;p*=2;}return k;}\n" ++
  "function observerDiv(a,b){return b===0?0:Math.floor(a/b);}\n" ++
  "function observerMod(a,b){return b===0?a:a%b;}\n" ++
  String.join (([("observerCycleBucket", cycleBucket), ("observerHistoryStart", historyStart),
    ("observerCycleFirst", cycleFirst), ("observerCycleLast", cycleLast)]).map fun (name, program) =>
      "const " ++ name ++ "=(x)=>" ++ program.javascript (fun _ => "x") ++ ";\n") ++
  "const observerDayPhase=(clock,length)=>" ++
    dayPhase.javascript (fun index => if index.val = 0 then "clock" else "length") ++ ";\n"

end Acorn.Host.Viewer.BrowserNat
