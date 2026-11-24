import Acorn.Lifetime
import Acorn.Host.WorldState

namespace Acorn.Host.Viewer.BrowserNat
variable {n : Nat}

inductive Expr (n : Nat) where
  | input (index : Fin n)
  | constant (value : Nat)
  | add (left right : Expr n)
  | sub (left right : Expr n)
  | minimum (left right : Expr n)
  | maximum (left right : Expr n)
  | div (left right : Expr n)
  | mod (left right : Expr n)
  | logTwo (value : Expr n)
  | powerTwo (value : Expr n)
  | ifLess (left right yes no : Expr n)

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

def cycleBucket : Expr 1 :=
  .ifLess (.input 0) (.constant FeatureConstants.exactCycles) (.input 0)
    (.minimum (.add (.constant FeatureConstants.exactCycles)
      (.logTwo (.add (.sub (.input 0) (.constant FeatureConstants.exactCycles)) (.constant 1))))
      (.constant (FeatureConstants.cycleBins - 1)))

theorem cycleBucket_execution (cycle : UInt64) :
    cycleBucket.eval (fun _ => cycle.toNat) = (Lifetime.cycleBin cycle).val := by
  by_cases h : cycle.toNat < FeatureConstants.exactCycles
  · simp only [cycleBucket, Expr.eval, Lifetime.cycleBin, h, ↓reduceDIte, ↓reduceIte]
  · simp only [cycleBucket, Expr.eval, Lifetime.cycleBin, h, ↓reduceDIte, ↓reduceIte]

def historyStart : Expr 1 :=
  .ifLess (.input 0) (.constant 1) (.constant 0) (.powerTwo (.input 0))

def cycleFirst : Expr 1 :=
  .ifLess (.input 0) (.constant FeatureConstants.exactCycles) (.add (.input 0) (.constant 1))
    (.add (.constant FeatureConstants.exactCycles)
      (.powerTwo (.sub (.input 0) (.constant FeatureConstants.exactCycles))))

def cycleLast : Expr 1 :=
  .ifLess (.input 0) (.constant FeatureConstants.exactCycles) (.add (.input 0) (.constant 1))
    (.add (.constant (FeatureConstants.exactCycles - 1))
      (.powerTwo (.add (.sub (.input 0) (.constant FeatureConstants.exactCycles)) (.constant 1))))

def dayArguments (clock length : Nat) : Fin 2 → Nat
  | ⟨0, _⟩ => clock
  | ⟨_ + 1, _⟩ => length

def dayPhase : Expr 2 :=
  let slot : Expr 2 := .mod (.input 0) (.input 1)
  let half : Expr 2 := .div (.input 1) (.constant 2)
  let eighth : Expr 2 :=
    .maximum (.constant 1) (.div (.input 1) (.constant FeatureConstants.dayPhases))
  let last : Expr 2 := .constant (FeatureConstants.dayPhases / 2 - 1)
  .ifLess slot half (.minimum (.div slot eighth) last)
    (.add (.constant (FeatureConstants.dayPhases / 2))
      (.minimum (.div (.sub slot half) eighth) last))

theorem dayPhase_execution {config : Host.WorldConfig} (world : Host.World config) :
    dayPhase.eval (dayArguments world.time.toNat config.raw.dayLength.toNat) =
      world.dayPhase.val := by
  simp only [dayPhase, Expr.eval, dayArguments]
  unfold Host.World.dayPhase
  dsimp only
  by_cases first :
      world.time.toNat % config.raw.dayLength.toNat < config.raw.dayLength.toNat / 2 <;>
    simp only [first, ↓reduceIte]

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
