import Acorn.Host.Runner
import Acorn.Handcrafted.FeatureProfile

namespace Acorn.Host
open Handcrafted

def researchProfile : ResearchProfile → FeatureProfile
  | .ranked => ⟨.final, .perStep, .declared, .learned⟩
  | .primitive => ⟨.primitiveOnly, .perStep, .declared, .learned⟩
  | .boundaryCredit => ⟨.final, .smdpCatchUp, .declared, .learned⟩
  | .annealed => ⟨.final, .perStep, .annealed, .learned⟩
  | .spatial => ⟨.final, .perStep, .declared, .spatial⟩

theorem research_resumable (profile : ResearchProfile) :
    (researchProfile profile).checkpointSupported = profile.resumable := by cases profile <;> rfl

end Acorn.Host
