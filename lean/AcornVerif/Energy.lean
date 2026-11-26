import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import AcornVerif.ModelConstants

namespace AcornVerif

open AcornVerif.ModelConstants

structure Ledger where
  steps : ℚ
  exhausted : ℚ
  eats : ℚ
  costs : ℚ

def Ledger.conserved (l : Ledger) (capacity rest eat : ℚ) : Prop :=
  rest * l.exhausted + eat * l.eats - l.costs ≤ capacity

def Ledger.costsBounded (l : Ledger) (cmax : ℚ) : Prop :=
  l.costs ≤ cmax * (l.steps - l.exhausted)

theorem exhausted_bound (l : Ledger) (capacity rest eat cmax : ℚ)
    (hcons : l.conserved capacity rest eat) (hcost : l.costsBounded cmax) :
    l.exhausted * (rest + cmax) ≤ capacity + cmax * l.steps - eat * l.eats := by
  unfold Ledger.conserved Ledger.costsBounded at *
  nlinarith [hcons, hcost]

theorem exhaustion_rate_bound (l : Ledger) (capacity rest cmax : ℚ)
    (hnoeat : l.eats = 0)
    (hcons : l.conserved capacity rest 0) (hcost : l.costsBounded cmax) :
    l.exhausted * (rest + cmax) ≤ capacity + cmax * l.steps := by
  have h := exhausted_bound l capacity rest 0 cmax hcons hcost
  simpa [hnoeat] using h

theorem exhaustion_rate_at_build (l : Ledger)
    (hnoeat : l.eats = 0)
    (hcons : l.conserved (energyMax : ℚ) (energyRestRecover : ℚ) 0)
    (hcost : l.costsBounded (energyMaxStepCost : ℚ)) :
    l.exhausted * 24 ≤ 2000 + 4 * l.steps := by
  have h := exhaustion_rate_bound l (energyMax : ℚ) (energyRestRecover : ℚ)
    (energyMaxStepCost : ℚ) hnoeat hcons hcost
  norm_num [energyMax, energyRestRecover, energyMaxStepCost] at h
  linarith

theorem rest_pays_for_an_action : energyMaxStepCost ≤ energyRestRecover := by
  norm_num [energyMaxStepCost, energyRestRecover]

theorem every_action_costs : 0 < energyMinStepCost := by
  norm_num [energyMinStepCost]

end AcornVerif
