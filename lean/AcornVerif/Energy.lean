/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import AcornVerif.Generated

/-!
# The exhaustion rate is bounded, not observed

Energy enters the body from exactly two sources, and that is a fact of the
type rather than of a reading: `Energy::gain` takes an `EnergyGain`, a closed
enum of `Rest` and `Eat`, matched exhaustively. A third source cannot be added
without failing to compile. So the ledger below has one term per variant by
construction, and the fraction of steps lost to exhaustion is a
**conservation** question — decidable, and settled here rather than measured.

The argument needs no steady-state assumption. Over `N` steps,

`E_N = E_0 + R·X + F·A − Σᵢ cᵢ`

where `X` counts exhausted steps, `A` counts successful eats, and `cᵢ` is what
each executed step cost. `E` is confined to `[0, energyMax]` by the `Energy`
type, so `E_N − E_0` is bounded by `energyMax` in absolute value whatever the
policy does, and the bound below follows by arithmetic alone.

Two premises remain outside Lean and are named rather than hidden: that
`World::step` charges each executed step at most `cmax` (exhausted steps charge
nothing, since `spend` leaves the balance untouched on failure), and that
`gain` does not saturate — guaranteed for `Rest`, because an exhausted
balance is below `MAX_STEP_COST ≤ REST_RECOVER`, and **not** guaranteed for
`Eat`. The non-eating corollary is therefore the one stated at full strength.

What is *not* settled here, and cannot be: whether the agent learns to eat.
That is a fact about what this world teaches, and it is the only part of the
energy story that is measured. See `docs/verification.md` for verification scope
and trust boundaries.
-/

namespace AcornVerif

open AcornVerif.Generated

/-- The energy ledger over a run, as rationals so the counts can be divided.

`N` steps, of which `X` were exhausted and `A` were successful eats; `costs` is
`Σᵢ cᵢ` over the steps that actually executed. `capacity`, `rest`, `eat` are
`Energy::MAX`, `Energy::REST_RECOVER` and `Energy::EAT_RESTORE`. -/
structure Ledger where
  /-- Total steps taken. -/
  steps : ℚ
  /-- Steps on which the action could not be paid for. -/
  exhausted : ℚ
  /-- Steps on which the agent successfully ate. -/
  eats : ℚ
  /-- Total energy spent by the steps that executed. -/
  costs : ℚ

/-- **The conservation bound.** Energy in minus energy out cannot exceed
capacity, because the balance it moves is confined to `[0, capacity]`.

Read the scope exactly. The `Energy` type gives `0 ≤ e ≤ capacity` on every
path, and `EnergyGain` gives that `rest` and `eat` are the only inflows. What
this hypothesis adds on top is that the ledger is an *identity* — that each
inflow adds its full amount rather than saturating. It is an assumption about
the run, not a consequence of the type, and it is discharged for `Rest` and not
for `Eat`; see the module note. -/
def Ledger.conserved (l : Ledger) (capacity rest eat : ℚ) : Prop :=
  rest * l.exhausted + eat * l.eats - l.costs ≤ capacity

/-- Every executed step costs at most `cmax`, so the total is bounded by
`cmax` times the number of steps that executed. -/
def Ledger.costsBounded (l : Ledger) (cmax : ℚ) : Prop :=
  l.costs ≤ cmax * (l.steps - l.exhausted)

/-- **Exhausted steps are bounded by conservation.**

`X·(rest + cmax) ≤ capacity + cmax·N − eat·A`. Universal in the ledger and in
the constants: no policy, and no trajectory, escapes it. -/
theorem exhausted_bound (l : Ledger) (capacity rest eat cmax : ℚ)
    (hcons : l.conserved capacity rest eat) (hcost : l.costsBounded cmax) :
    l.exhausted * (rest + cmax) ≤ capacity + cmax * l.steps - eat * l.eats := by
  unfold Ledger.conserved Ledger.costsBounded at *
  nlinarith [hcons, hcost]

/-- **The exhaustion rate of a non-eating agent.** With `A = 0`, the fraction
of steps lost to exhaustion is at most `cmax / (rest + cmax)`, plus a transient
of `capacity / ((rest + cmax)·N)` that vanishes as the run lengthens. Note the
denominator: dividing the statement below by `N` carries `(rest + cmax)` with
it, so the transient is 24× smaller here than `capacity / N` would suggest.

Stated multiplied through by `N` so no division-by-zero side condition is
needed; the ratio reading is immediate for `N > 0`. -/
theorem exhaustion_rate_bound (l : Ledger) (capacity rest cmax : ℚ)
    (hnoeat : l.eats = 0)
    (hcons : l.conserved capacity rest 0) (hcost : l.costsBounded cmax) :
    l.exhausted * (rest + cmax) ≤ capacity + cmax * l.steps := by
  have h := exhausted_bound l capacity rest 0 cmax hcons hcost
  simpa [hnoeat] using h

/-- The bound at **this build's** constants, taken from `acorn emit-lean` rather
than retyped: `X · 24 ≤ 2000 + 4·N`.

So an agent that never eats loses at most one step in six to exhaustion, once
the `2000/N` transient is small — `energyMaxStepCost / (energyRestRecover +
energyMaxStepCost) = 4/24 = 1/6`. Raising an action's cost past
`Energy::REST_RECOVER` would break the companion build gate in `src/world.rs`
before it could weaken this. -/
theorem exhaustion_rate_at_build (l : Ledger)
    (hnoeat : l.eats = 0)
    (hcons : l.conserved (energyMax : ℚ) (energyRestRecover : ℚ) 0)
    (hcost : l.costsBounded (energyMaxStepCost : ℚ)) :
    l.exhausted * 24 ≤ 2000 + 4 * l.steps := by
  have h := exhaustion_rate_bound l (energyMax : ℚ) (energyRestRecover : ℚ)
    (energyMaxStepCost : ℚ) hnoeat hcons hcost
  norm_num [energyMax, energyRestRecover, energyMaxStepCost] at h
  linarith

/-- Resting pays for at least one action at this build's constants:
`energyMaxStepCost ≤ energyRestRecover`. This is the Lean counterpart of the
`const _: () = assert!` in `src/world.rs`, and it is what makes exhaustion a
*tax* rather than a terminal state — a spent agent can always act again on the
step after resting. -/
theorem rest_pays_for_an_action : energyMaxStepCost ≤ energyRestRecover := by
  norm_num [energyMaxStepCost, energyRestRecover]

/-- Every action costs something, so the bound above is not vacuous: an agent
cannot act indefinitely without spending. -/
theorem every_action_costs : 0 < energyMinStepCost := by
  norm_num [energyMinStepCost]

end AcornVerif
