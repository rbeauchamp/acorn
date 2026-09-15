/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Collapse

/-!
# Historical study domains and their generated numeric identities

Every compatibility domain is a constructor of the closed type.
The first theorem checks all constructors with the kernel, using the exact
stored UTF-8 bytes and wrapping UInt64 FNV arithmetic. The stream and analysis
identities then follow by substitution for every seed and input population;
neither executes a world, a learner, or a bootstrap. These are compatibility
identities, not evidence of registration timing or of empirical usefulness.
-/

namespace AcornVerif

open AcornSpec

/-- Every generated machine-word identity is the FNV hash of its preserved
historical UTF-8 bytes. A different byte or numeric identity refutes this
closed-domain statement; no execution or outcome assumption is needed. -/
theorem historical_domain_identity (domain : Constants.Compatibility.Domain) :
    domain.value = fnv1a domain.bytes := by
  cases domain <;> decide

/-- Domain substitution preserves every stream key at every UInt64 base seed.
This proves the initialization identity over the declared constants; full-agent
execution correspondence is a separate property. -/
theorem historical_stream_identity (seed : UInt64) (domain : Constants.Compatibility.Domain) :
    Xoshiro256.streamKey seed domain.value =
      Xoshiro256.streamKey seed (fnv1a domain.bytes) := by
  rw [historical_domain_identity]

/-- The registered paired analysis is identical for every population when its
domain is replaced by the generated numeric identity. This is substitution
through the existing functional, not reflection or resampling in the kernel. -/
theorem historical_analysis_identity (domain : Constants.Compatibility.Domain)
    (diffs : SeedDiffs) :
    pairedSummaryAt domain.value diffs = pairedSummaryAt (fnv1a domain.bytes) diffs := by
  rw [historical_domain_identity]

end AcornVerif
