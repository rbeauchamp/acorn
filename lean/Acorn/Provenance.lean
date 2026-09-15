/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Declared origins

The closed register requires a declaration, not proof that the declaration is
true. Learned module admission is independently checked after Lean elaboration.
-/
namespace Acorn

/-- Current declared departures, corresponding to the maintained D1–D5 register. -/
inductive Departure where
  /-- D1: hand-authored feature-channel layout. -/
  | featureChannels
  /-- D2: hand-authored spatial option potentials. -/
  | spatialPotentials
  /-- D3: prescribed exploration-duration law. -/
  | explorationDuration
  /-- D4: hand-set domain-general learner parameters. -/
  | learnerParameters
  /-- D5: prescribed prediction targets and horizons. -/
  | cumulants
  deriving DecidableEq

/-- Every admitted signal/encoding family declares its origin. Declaration
truth remains a reviewed scientific claim rather than a decidable predicate. -/
class Provenance (α : Type) where
  /-- Absent for a learned construct, otherwise its registered departure. -/
  origin : Option Departure

end Acorn
