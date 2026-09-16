/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import AcornVerif.ModelConstants

/-!
# Conditional energy-ledger bounds

For a ledger with `N` total steps, `X` exhausted steps, `A` successful eats and
aggregate action cost, conservation and a per-action cost bound imply a bound
on exhaustion. The theorems quantify over those hypotheses and need no
steady-state assumption.

`CurrentConstants` links capacity, rest recovery and eating recovery to current
world constants. This module does not construct a ledger from executed world
transitions or discharge conservation, saturation or cost hypotheses for a run.
The no-eating specialization removes the eating term; it does not establish
that a policy learns to eat or that an observed run meets the hypotheses.
-/

namespace AcornVerif

open AcornVerif.ModelConstants

/-- Rational step, exhaustion, eating and cost totals supplied to the analysis. -/
structure Ledger where
  /-- Total steps taken. -/
  steps : ℚ
  /-- Steps on which the action could not be paid for. -/
  exhausted : ℚ
  /-- Steps on which the agent successfully ate. -/
  eats : ℚ
  /-- Total energy spent by the steps that executed. -/
  costs : ℚ

/-- Assumed net inflow bound: credited recovery minus action costs is at most capacity.
Relating a concrete run to this inequality must account for recovery saturation. -/
def Ledger.conserved (l : Ledger) (capacity rest eat : ℚ) : Prop :=
  rest * l.exhausted + eat * l.eats - l.costs ≤ capacity

/-- Assumed total cost bound: at most `cmax` times the non-exhausted step count. -/
def Ledger.costsBounded (l : Ledger) (cmax : ℚ) : Prop :=
  l.costs ≤ cmax * (l.steps - l.exhausted)

/-- **Exhausted steps are bounded by conservation.**

`X·(rest + cmax) ≤ capacity + cmax·N − eat·A`, for every ledger and constants
satisfying the conservation and cost premises. -/
theorem exhausted_bound (l : Ledger) (capacity rest eat cmax : ℚ)
    (hcons : l.conserved capacity rest eat) (hcost : l.costsBounded cmax) :
    l.exhausted * (rest + cmax) ≤ capacity + cmax * l.steps - eat * l.eats := by
  unfold Ledger.conserved Ledger.costsBounded at *
  nlinarith [hcons, hcost]

/-- With no eating, the multiplied conservation bound loses its eating term.
For `N > 0` and `rest + cmax > 0`, division gives exhaustion fraction at most
`cmax / (rest + cmax) + capacity / ((rest + cmax) * N)`.
The theorem itself requires no division or positivity premises. -/
theorem exhaustion_rate_bound (l : Ledger) (capacity rest cmax : ℚ)
    (hnoeat : l.eats = 0)
    (hcons : l.conserved capacity rest 0) (hcost : l.costsBounded cmax) :
    l.exhausted * (rest + cmax) ≤ capacity + cmax * l.steps := by
  have h := exhausted_bound l capacity rest 0 cmax hcons hcost
  simpa [hnoeat] using h

/-- The bound at the model constants: `X · 24 ≤ 2000 + 4·N`.
Under the no-eating, conservation and cost hypotheses, exhausted steps have
asymptotic upper fraction `4/24 = 1/6`. The finite bound includes the capacity
transient. `CurrentConstants` links capacity and rest recovery to execution;
the cost bound remains a premise of this specialization. -/
theorem exhaustion_rate_at_build (l : Ledger)
    (hnoeat : l.eats = 0)
    (hcons : l.conserved (energyMax : ℚ) (energyRestRecover : ℚ) 0)
    (hcost : l.costsBounded (energyMaxStepCost : ℚ)) :
    l.exhausted * 24 ≤ 2000 + 4 * l.steps := by
  have h := exhaustion_rate_bound l (energyMax : ℚ) (energyRestRecover : ℚ)
    (energyMaxStepCost : ℚ) hnoeat hcons hcost
  norm_num [energyMax, energyRestRecover, energyMaxStepCost] at h
  linarith

/-- At the model constants, recovery covers the maximum cost of one action:
`energyMaxStepCost ≤ energyRestRecover`. -/
theorem rest_pays_for_an_action : energyMaxStepCost ≤ energyRestRecover := by
  norm_num [energyMaxStepCost, energyRestRecover]

/-- The declared minimum action cost is positive. -/
theorem every_action_costs : 0 < energyMinStepCost := by
  norm_num [energyMinStepCost]

end AcornVerif
