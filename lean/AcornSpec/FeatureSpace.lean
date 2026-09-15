/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
/-!
# The retained evaluator's feature dimension

The featurizer's mask and its learner arrays share this dimension. Isolating
its declaration lets the integer index proofs compile independently of the
learner's floating-point operations and transition loops.
-/

namespace AcornSpec

/-- The weight-space size `N = 2¹⁴` (`agent::DEFAULT_WEIGHT_SPACE`). -/
def weightSpace : Nat := 16384

end AcornSpec
