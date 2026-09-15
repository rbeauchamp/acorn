/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Runner
import Acorn.Handcrafted.FeatureProfile

/-!
# Public research-profile admission

The host maps CLI/runner selections to immutable policy discriminants. Keeping
this bridge in the host prevents runner IO dependencies from entering policy code.
-/
namespace Acorn.Host
open Handcrafted

/-- Closed public research profiles choose every implementation discriminant. -/
def researchProfile : ResearchProfile → FeatureProfile
  | .ranked => ⟨.final, .perStep, .perLearner, .learned⟩
  | .primitive => ⟨.primitiveOnly, .perStep, .perLearner, .learned⟩
  | .boundaryCredit => ⟨.final, .smdpCatchUp, .perLearner, .learned⟩
  | .annealed => ⟨.final, .perStep, .annealed, .learned⟩
  | .spatial => ⟨.final, .perStep, .perLearner, .spatial⟩

/-- Public profile admission agrees with the implemented feature-image refusal. -/
theorem research_resumable (profile : ResearchProfile) :
    (researchProfile profile).checkpointSupported = profile.resumable := by cases profile <;> rfl

end Acorn.Host
