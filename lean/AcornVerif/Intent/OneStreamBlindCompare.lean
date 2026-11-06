/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.OneStreamBlindReading
import AcornVerif.Intent.OneStreamBlindCases

/-!
# The blind record reading of contract 3, compared with the record

The blind record `AcornVerif.Intent.OneStream.OwnerRecord.oneStreamIntent` and the record
`AcornVerif.Intent.OneStream.oneStream` are both over `AcornVerif.Intent.OneStream.Learner`. Neither
implies the other: this module proves each direction under the conditions that close the gap, and
names a learner that meets one record and not the other for each difference.

* `mine_theirs`: a learner that meets the record, and whose agent resumes with the memory it held at
  every memory a run holds, not only at the stops a run makes, meets the blind record.
  `mine_not_theirs`: the learner `resumesOtherUnstopped`, whose run never stops and whose agent
  would resume with `false` from every memory, a memory other than `true`, which its run holds after
  one step, meets the record and not the blind record.
* `theirs_mine`: a learner that meets the blind record, holds finitely many memories, learns on
  every step if on any, plans on every step if on any, and makes a bounded number of internal
  updates per step, meets the record. Four learners meet the blind record and not the record, each
  lacking one of these: `counting`, whose agent counts its steps (`counting_theirs`, and
  `counting_not_mine` here); `learnsOnce`, which learns on its first step only (`learnsOnce_theirs`;
  it fails the record by `AcornVerif.Intent.OneStream.learnsOnce_fails`); `plansOnce`, which plans on
  its first step only (`plansOnce_theirs`; `AcornVerif.Intent.OneStream.plansOnce_fails`); and
  `plansMore`, which makes one more planning update at each step than at the step before while
  reporting no work (`plansMore_theirs`; `AcornVerif.Intent.OneStream.plansMore_fails`).

How each difference was settled is in the record's confirmation file,
`lean/AcornVerif/Intent/OneStream.md`.
-/

namespace AcornVerif.Intent.OneStream.Compare

open LeanIntent WorldInterface AcornVerif.Intent.OneStream OwnerRecord

/-- A learner meets the blind record exactly when each of its six properties holds of it. -/
theorem theirs_meets {w : Learner} :
    oneStreamIntent.Meets w ↔
      LearnsOnlyFromTheExperienceOfThisStep w ∧ WorkHasAFixedLifetimeBound w ∧
        NoInternalUpdateResetsMemory w ∧ TheRunCarriesTheAgentsNextMemory w ∧
          ResumptionPreservesTheStoppedMemory w ∧ AfterwardsActsAndLearnsAsWithoutTheStop w := by
  constructor
  · intro hm
    have h : ∀ c ∈ requirements, c.holds w := hm.2
    exact ⟨h _ (.head _), h _ (.tail _ (.head _)), h _ (.tail _ (.tail _ (.head _))),
      h _ (.tail _ (.tail _ (.tail _ (.head _)))), h _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))),
      h _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))⟩
  · intro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [oneStreamIntent, requirements, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6

/-- **A learner that meets the record, and whose agent resumes with the memory it held at every
memory a run holds, meets the blind record.** -/
theorem mine_theirs {w : Learner} (hw : oneStream.Meets w)
    (hres : ∀ ins t s m, w.Reaches ins t s m → w.resume m = m) : oneStreamIntent.Meets w := by
  obtain ⟨h1, ⟨B, hB⟩, -, -, -, h6, h7, -⟩ := oneStream_meets.mp hw
  have h5 : ResumptionPreservesTheStoppedMemory w := fun p hp => hres _ _ _ _ hp
  exact theirs_meets.mpr ⟨fun p hp => h1 _ _ _ _ hp, ⟨B, fun p hp => (hB _ _ _ _ hp).1⟩,
    fun p hp => h6 _ _ _ _ hp, fun p hp => h7 _ _ _ _ hp, h5,
    exact_memory_preserves_continuations h5⟩

/-- **A learner that meets the blind record and the record's further conditions meets the record.**
A learner that meets the blind record, holds finitely many memories, learns on every step if on any, plans on every
step if on any, and makes a bounded number of internal updates per step, meets the record. -/
theorem theirs_mine {w : Learner} (h : oneStreamIntent.Meets w) (hmem : boundedMemory.holds w)
    (hlearn : learnsEveryStep.holds w) (hplan : plansEveryStep.holds w)
    (hcount : ∃ C, ∀ ins t s m, w.Takes ins t s m → (w.stepUpdates s m (ins t)).length ≤ C) :
    oneStream.Meets w := by
  obtain ⟨h1, ⟨B, hB⟩, h3, h4, h5, -⟩ := theirs_meets.mp h
  obtain ⟨C, hC⟩ := hcount
  exact oneStream_meets.mpr ⟨fun ins t s m hs => h1 ⟨ins, t, s, m⟩ hs,
    ⟨max B C, fun ins t s m hs => ⟨Nat.le_trans (hB ⟨ins, t, s, m⟩ hs) (Nat.le_max_left _ _),
      Nat.le_trans (hC _ _ _ _ hs) (Nat.le_max_right _ _)⟩⟩,
    hmem, hlearn, hplan, fun ins t s m hs => h3 ⟨ins, t, s, m⟩ hs,
    fun ins t s m hs => h4 ⟨ins, t, s, m⟩ hs, fun ins t s m hs => h5 ⟨ins, t, s, m⟩ hs.1⟩

/-! ## Learners that meet one record and not the other -/

/-- Case 13 of the blind cases reading, whose run takes a step whatever it is sent, with an agent
that would resume with the memory `false` from any memory. -/
def resumesOtherUnstopped : Learner := { Cases.case13 with resume := fun _ => false }

/-- `resumesOtherUnstopped` meets the record: its run never stops, so the record asks nothing of how
it resumes. -/
theorem resumesOtherUnstopped_mine : oneStream.Meets resumesOtherUnstopped := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := oneStream_meets.mp Cases.c13
  exact oneStream_meets.mpr ⟨h1, h2, h3, h4, h5, h6, h7,
    fun _ _ _ _ h => Bool.noConfusion (h.2.symm.trans rfl)⟩

/-- `resumesOtherUnstopped` does not meet the blind record: after one step its run holds the memory
`true`, and its agent would resume from it with `false`. -/
theorem resumesOtherUnstopped_not_theirs : ¬ oneStreamIntent.Meets resumesOtherUnstopped :=
  fun h => Bool.noConfusion ((theirs_meets.mp h).2.2.2.2.1
    ⟨fun _ => false, 1, (), true⟩ (.next .start rfl))

/-- **Some learner meets the record and not the blind record.** -/
theorem mine_not_theirs : ∃ w, oneStream.Meets w ∧ ¬ oneStreamIntent.Meets w :=
  ⟨_, resumesOtherUnstopped_mine, resumesOtherUnstopped_not_theirs⟩

/-- A learner run faithfully meets the blind record when every learning update it reports learns
from the experience its step was given, its work is bounded, it reports no reset, and it resumes
with the memory it held. -/
theorem learner_theirs (W : World) (A : Agent W.Obs W.Act)
    (ups : A.Memory → W.Obs × Rat → List Update) (cost : A.Memory → W.Obs × Rat → Nat)
    (hlearn : ∀ m o d, Update.learn d ∈ ups m o → d = .stream 0)
    (hcost : ∃ B, ∀ m o, cost m o ≤ B) (hreset : ∀ m o, Update.reset ∉ ups m o) :
    oneStreamIntent.Meets (learner W A ups cost id) := by
  obtain ⟨B, hB⟩ := hcost
  have h5 : ResumptionPreservesTheStoppedMemory (learner W A ups cost id) := fun _ _ => rfl
  exact theirs_meets.mpr ⟨fun _ _ d hd => hlearn _ _ d hd, ⟨B, fun _ _ => hB _ _⟩,
    fun _ _ => hreset _ _, fun _ _ => rfl, h5, exact_memory_preserves_continuations h5⟩

/-- `counting`, whose agent counts its steps, meets the blind record. -/
theorem counting_theirs : oneStreamIntent.Meets counting :=
  learner_theirs _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => Nat.le_refl _⟩ fun _ _ h => nomatch List.mem_singleton.mp h

/-- `counting` does not meet the record: its runs hold every natural as a memory. -/
theorem counting_not_mine : ¬ oneStream.Meets counting := fun h => by
  obtain ⟨L, hL⟩ := (oneStream_meets.mp h).2.2.1
  obtain ⟨n, hn⟩ := exists_not_mem L
  obtain ⟨_, hr⟩ := echo_counts n
  exact hn (hL neverStop n _ _ hr)

/-- `learnsOnce`, which learns on its first step only, meets the blind record (it fails the record,
`learnsOnce_fails`). -/
theorem learnsOnce_theirs : oneStreamIntent.Meets learnsOnce :=
  learner_theirs _ _ _ _
    (fun m _ d h => by
      cases m with
      | false => exact Update.learn.inj (List.mem_singleton.mp h)
      | true => exact nomatch h)
    ⟨1, fun _ _ => Nat.le_refl _⟩
    fun m _ h => by
      cases m with
      | false => exact nomatch List.mem_singleton.mp h
      | true => exact nomatch h

/-- `plansOnce`, which plans on its first step only, meets the blind record (it fails the record,
`plansOnce_fails`). -/
theorem plansOnce_theirs : oneStreamIntent.Meets plansOnce :=
  learner_theirs _ _ _ _
    (fun m _ d h => by
      cases m with
      | false => exact nomatch List.mem_singleton.mp h
      | true => exact nomatch h)
    ⟨1, fun _ _ => Nat.le_refl _⟩
    fun m _ h => by
      cases m with
      | false => exact nomatch List.mem_singleton.mp h
      | true => exact nomatch h

/-- `plansMore`, which makes one more planning update at each step than at the step before while
reporting no work, meets the blind record (it fails the record, `plansMore_fails`). -/
theorem plansMore_theirs : oneStreamIntent.Meets plansMore :=
  learner_theirs _ _ _ _ (fun _ _ _ h => by simp at h) ⟨0, fun _ _ => Nat.le_refl _⟩
    fun _ _ h => by simp at h

/-- **Some learner meets the blind record and not the record.** -/
theorem theirs_not_mine : ∃ w, oneStreamIntent.Meets w ∧ ¬ oneStream.Meets w :=
  ⟨_, counting_theirs, counting_not_mine⟩

end AcornVerif.Intent.OneStream.Compare
