import AcornVerif.MissionVisits
import AcornVerif.Intent.PostconditionConsequences
import AcornVerif.StoredExperience

namespace AcornVerif.StoredExperienceRecord
open Acorn.Features AcornVerif.Kernel AcornVerif.MissionVisits AcornVerif.Intent
open AcornVerif.Intent.MissionTheorem

variable {interface : Interface}

theorem replay_not_memoryBounded (family : WorldClass interface) (length horizon lapses : ℕ)
    (pay : Percept interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface)
    (updates : (replay interface length signal explore).Memory → Percept interface × ℚ →
      List OneStream.Update)
    (work : (replay interface length signal explore).Memory → Percept interface × ℚ → ℕ)
    (resume : (replay interface length signal explore).Memory →
      (replay interface length signal explore).Memory)
    (index : family.Index) :
    ¬ MemoryBounded (visitsRung family length horizon lapses pay met counted
      (replay interface length signal explore) updates work resume) := by
  rintro ⟨held, all⟩
  refine replay_unbounded (family.world index) (family.start index) length signal explore
    ⟨held, fun time => ?_⟩
  have reached := Postcondition.run_reaches
    (visitMember (family.world index) (family.start index) length pay (met index))
    (recordAgent (replay interface length signal explore)) time
  have member := all index _ time _ _ reached
  rw [run_eq_loop] at member
  exact member

end AcornVerif.StoredExperienceRecord
