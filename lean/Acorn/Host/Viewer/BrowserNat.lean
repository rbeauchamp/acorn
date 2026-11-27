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

end Acorn.Host.Viewer.BrowserNat
