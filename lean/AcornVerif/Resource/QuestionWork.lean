/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.TemporalControl
import AcornVerif.CurrentOffPolicy
import AcornVerif.Resource.Work

/-!
# Work of every option's off-policy questions

The bounds of the costed definitions of the options' off-policy questions, which the second part
runs in a learning hierarchy (`Acorn.Handcrafted.askQuestions`); `Acorn.Cost` names each costed
definition. Each `_within` theorem bounds a costed definition directly. No twin reads these
definitions, so no adapter is defined here.

An option's questions advance their stored set `x` to the frame's active set `x'`. The advance
filters both sets by one membership flag per slot and writes the flags over both, so its work is
linear in `|x| + |x'|` (`advanceCosted_within`). When the advance classifies a transition, each of
the option's questions takes one GTD2-MP step from it: four sums, over the three classes of
`x ∪ x'` for the main weights and over `x` for the second weights, and four write passes over the
same lists. The four lists of a step have at most `2·|x| + |x'|` slots in all
(`questionStepCosted_within`). A bank of `k` questions is one pass over its questions
(`bankStepCosted_within`), so an option's questions do work linear in `|x| + |x'|` and in
`k·(2·|x| + |x'|)` (`followCosted_within`). Every set fits the dimension
(`AcornVerif.CurrentLearner.active_cardinality`), so with the capacity of the dimension in place of
each set's length the bound of every option's questions is a function of the configuration
(`askQuestionsCosted_within_capacity`).
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features Acorn.Handcrafted

variable {dimension : Dimension}

/-! ## Loops over slots -/

/-- Four loops of one row with one callback bound do the work of one loop over their elements
together, and three more end visits. -/
theorem foldl_work_four (visit bound a b c d : Nat) :
    Library.foldl.work visit a bound + Library.foldl.work visit b bound +
        Library.foldl.work visit c bound + Library.foldl.work visit d bound =
      Library.foldl.work visit (a + b + c + d) bound + 3 * visit := by
  simp only [Library.work, Library.control, Library.passes, Nat.add_mul, Nat.one_mul]
  omega

theorem setFlagsCosted_within (κ : Costs) {size : Nat} (indices : List (Fin size)) (value : Bool)
    (flags : Vector Bool size) :
    (setFlagsCosted indices value flags).Within κ
      (Library.foldl.work (κ .visit) indices.length (κ .write)) :=
  Acorn.Costed.foldl_within fun _ _ _ => Acorn.Costed.op_within _ _ κ

theorem wideSumCosted_within (κ : Costs) {rule : ValueRule} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (total : Binary64) :
    (wideSumCosted weights indices total).Within κ
      (Library.foldl.work (κ .visit) indices.length (κ .sumTerm)) :=
  Acorn.Costed.foldl_within fun _ _ _ => Acorn.Costed.op_within _ _ κ

theorem addAllCosted_within (κ : Costs) {rule : ValueRule} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (delta : Binary32) :
    (addAllCosted weights indices delta).Within κ
      (Library.foldl.work (κ .visit) indices.length (κ .gradientWrite)) :=
  Acorn.Costed.foldl_within fun _ _ _ => Acorn.Costed.op_within _ _ κ

theorem subAllCosted_within (κ : Costs) {rule : ValueRule} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (delta : Binary32) :
    (subAllCosted weights indices delta).Within κ
      (Library.foldl.work (κ .visit) indices.length (κ .gradientWrite)) :=
  Acorn.Costed.foldl_within fun _ _ _ => Acorn.Costed.op_within _ _ κ

/-! ## The advance of the stored set -/

/-- Bound of a preceding set's advance from a stored set of `stored` slots to a current set of
`width` slots: the current set's two filters and the stored set's one, the flags cleared over the
stored set, set over the current one and cleared over it again, the two sets' lengths, the three
classes' lengths, and the record. -/
abbrev advanceBound (κ : Costs) (stored width : Nat) : Nat :=
  2 * Library.filter.work (κ .visit) width (κ .flagTest) +
    Library.filter.work (κ .visit) stored (κ .flagTest) +
    Library.foldl.work (κ .visit) stored (κ .write) +
    2 * Library.foldl.work (κ .visit) width (κ .write) +
    2 * Library.length.control (κ .visit) stored +
    3 * Library.length.control (κ .visit) width + κ .preceding

/-- A preceding set's advance is within its bound at the lengths of the stored set and the current
one. -/
theorem advanceCosted_within (κ : Costs) (preceding : Preceding dimension)
    (current : SwiftTd.ActiveSet dimension) (armed : Bool) :
    (preceding.advanceCosted current armed).Within κ
      (advanceBound κ preceding.features.indices.length current.indices.length) := by
  rcases preceding with ⟨⟨indices, nodup⟩, flags, agrees⟩
  cases indices with
  | nil =>
    dsimp only [Preceding.advanceCosted]
    refine Acorn.Costed.ite_within (fun _ => ?_) (fun _ => ?_)
    · exact (Acorn.Costed.bind_within
        (Acorn.Costed.attach_within (setFlagsCosted_within κ _ _ _))
        (Acorn.Costed.op_within _ _ κ)).mono (by simp only [advanceBound]; omega)
    · exact (Acorn.Costed.op_within _ _ κ).mono (by simp only [advanceBound]; omega)
  | cons head tail =>
    dsimp only [Preceding.advanceCosted]
    refine Acorn.Costed.Within.mono
      (a := Library.filter.work (κ .visit) current.indices.length (κ .flagTest) +
        (Library.filter.work (κ .visit) current.indices.length (κ .flagTest) +
          (Library.foldl.work (κ .visit) (head :: tail).length (κ .write) +
            (Library.foldl.work (κ .visit) current.indices.length (κ .write) +
              (Library.length.control (κ .visit) (head :: tail).length +
                (Library.length.control (κ .visit) current.indices.length +
                  ((Library.filter.work (κ .visit) (head :: tail).length (κ .flagTest) +
                      (Library.length.control (κ .visit) (head :: tail).length +
                        (Library.length.control (κ .visit) current.indices.length +
                          (Library.length.control (κ .visit) current.indices.length + 0)))) +
                    (Library.foldl.work (κ .visit) current.indices.length (κ .write) +
                      κ .preceding)))))))) ?_ (by simp only [advanceBound]; omega)
    refine Acorn.Costed.bind_within (Acorn.Costed.attach_within
      (Acorn.Costed.filter_within fun _ _ => Acorn.Costed.op_within _ _ κ)) ?_
    refine Acorn.Costed.bind_within (Acorn.Costed.attach_within
      (Acorn.Costed.filter_within fun _ _ => Acorn.Costed.op_within _ _ κ)) ?_
    refine Acorn.Costed.bind_within (Acorn.Costed.attach_within (setFlagsCosted_within κ _ _ _)) ?_
    refine Acorn.Costed.bind_within (Acorn.Costed.attach_within (setFlagsCosted_within κ _ _ _)) ?_
    refine Acorn.Costed.bind_within (Acorn.Costed.attach_within (Acorn.Costed.length_within _ κ)) ?_
    refine Acorn.Costed.bind_within (Acorn.Costed.attach_within (Acorn.Costed.length_within _ κ)) ?_
    refine Acorn.Costed.bind_within (Acorn.Costed.dite_within (fun _ => ?_)
      (fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))) ?_
    · refine Acorn.Costed.bind_within (Acorn.Costed.attach_within
        (Acorn.Costed.filter_within fun _ _ => Acorn.Costed.op_within _ _ κ)) ?_
      refine Acorn.Costed.bind_within (Acorn.Costed.attach_within
        ((Acorn.Costed.length_within _ κ).mono
          (Library.control_mono _ (List.length_filter_le _ _)))) ?_
      refine Acorn.Costed.bind_within (Acorn.Costed.attach_within
        ((Acorn.Costed.length_within _ κ).mono
          (Library.control_mono _ (List.length_filter_le _ _)))) ?_
      refine Acorn.Costed.bind_within (Acorn.Costed.attach_within
        ((Acorn.Costed.length_within _ κ).mono
          (Library.control_mono _ (List.length_filter_le _ _)))) ?_
      exact Acorn.Costed.pure_within _ κ
    · exact Acorn.Costed.ite_within
        (fun _ => (Acorn.Costed.op_within _ _ κ).mono (Nat.le_add_left _ _))
        (fun _ => Acorn.Costed.bind_within
          (Acorn.Costed.attach_within (setFlagsCosted_within κ _ _ _))
          (Acorn.Costed.op_within _ _ κ))

/-- An advance's bound grows with each set's length. -/
theorem advanceBound_mono (κ : Costs) {stored most width limit : Nat} (storedFits : stored ≤ most)
    (widthFits : width ≤ limit) : advanceBound κ stored width ≤ advanceBound κ most limit := by
  have currentFilters :=
    Library.filter.work_mono (visit := κ .visit) widthFits (Nat.le_refl (κ .flagTest))
  have storedFilter :=
    Library.filter.work_mono (visit := κ .visit) storedFits (Nat.le_refl (κ .flagTest))
  have storedFlags :=
    Library.foldl.work_mono (visit := κ .visit) storedFits (Nat.le_refl (κ .write))
  have currentFlags :=
    Library.foldl.work_mono (visit := κ .visit) widthFits (Nat.le_refl (κ .write))
  have storedLength := Library.length.control_mono (visit := κ .visit) storedFits
  have currentLength := Library.length.control_mono (visit := κ .visit) widthFits
  simp only [advanceBound]
  omega

/-! ## A question's step -/

theorem scalarsCosted_within (κ : Costs) {discount : Discount}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    (learner.scalarsCosted passage cumulant).Within κ
      (Library.foldl.work (κ .visit) passage.both.length (κ .sumTerm) +
        (Library.foldl.work (κ .visit) passage.onlySource.length (κ .sumTerm) +
          (Library.foldl.work (κ .visit) passage.onlyTarget.length (κ .sumTerm) +
            (Library.foldl.work (κ .visit) passage.source.indices.length (κ .sumTerm) +
              κ .innerProducts)))) :=
  Acorn.Costed.bind_within (wideSumCosted_within κ _ _ _)
    (Acorn.Costed.bind_within (wideSumCosted_within κ _ _ _)
      (Acorn.Costed.bind_within (wideSumCosted_within κ _ _ _)
        (Acorn.Costed.bind_within (wideSumCosted_within κ _ _ _)
          (Acorn.Costed.op_within _ _ κ))))

theorem incrementsCosted_within (κ : Costs) {discount : Discount}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    (learner.incrementsCosted passage cumulant).Within κ
      (Library.foldl.work (κ .visit) passage.both.length (κ .sumTerm) +
        (Library.foldl.work (κ .visit) passage.onlySource.length (κ .sumTerm) +
          (Library.foldl.work (κ .visit) passage.onlyTarget.length (κ .sumTerm) +
            (Library.foldl.work (κ .visit) passage.source.indices.length (κ .sumTerm) +
              κ .innerProducts))) + κ .increments) :=
  Acorn.Costed.bind_within (scalarsCosted_within κ learner passage cumulant)
    (Acorn.Costed.op_within _ _ κ)

/-- A learner's step: its four sums, its inner products and increments, and its four write
passes, over the three classes of `x ∪ x'` and over `x`. -/
theorem learnerStepCosted_within (κ : Costs) {discount : Discount}
    (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    (learner.stepCosted passage cumulant).Within κ
      (Library.foldl.work (κ .visit) passage.both.length (κ .sumTerm) +
        Library.foldl.work (κ .visit) passage.onlySource.length (κ .sumTerm) +
        Library.foldl.work (κ .visit) passage.onlyTarget.length (κ .sumTerm) +
        Library.foldl.work (κ .visit) passage.source.indices.length (κ .sumTerm) +
        κ .innerProducts + κ .increments +
        (Library.foldl.work (κ .visit) passage.onlySource.length (κ .gradientWrite) +
          Library.foldl.work (κ .visit) passage.both.length (κ .gradientWrite) +
          Library.foldl.work (κ .visit) passage.onlyTarget.length (κ .gradientWrite) +
          Library.foldl.work (κ .visit) passage.source.indices.length (κ .gradientWrite))) := by
  rcases learner with ⟨main, second⟩
  exact (Acorn.Costed.bind_within (incrementsCosted_within κ _ passage cumulant)
    (Acorn.Costed.bind_within (addAllCosted_within κ _ _ _)
      (Acorn.Costed.bind_within (addAllCosted_within κ _ _ _)
        (Acorn.Costed.bind_within (subAllCosted_within κ _ _ _)
          (Acorn.Costed.bind_within (addAllCosted_within κ _ _ _)
            (Acorn.Costed.pure_within _ κ)))))).mono (by omega)

/-- Bound of one question's step from a stored set of `stored` slots to a current set of `width`
slots: four sums and four write passes, each four over lists of at most `2·stored + width` slots in
all, the further end visits of those loops, the inner products, the increments and the question's
record. -/
abbrev questionBound (κ : Costs) (stored width : Nat) : Nat :=
  Library.foldl.work (κ .visit) (2 * stored + width) (κ .sumTerm) +
    Library.foldl.work (κ .visit) (2 * stored + width) (κ .gradientWrite) +
    6 * κ .visit + κ .innerProducts + κ .increments + κ .question

/-- A question's step is within its bound at the lengths of the transition's two sets: its four
lists, the three classes of `x ∪ x'` and `x` itself, have `2·|x| + |x'| − |x ∩ x'|` slots in
all. -/
theorem questionStepCosted_within (κ : Costs) {discount : Discount}
    (question : Question discount dimension) (passage : Passage dimension) (cumulant : Binary32) :
    (question.stepCosted passage cumulant).Within κ
      (questionBound κ passage.source.indices.length passage.target.indices.length) := by
  rcases question with ⟨learner, silent, blank⟩
  dsimp only [Question.stepCosted]
  have counts := CurrentOffPolicy.class_counts passage
  have sums := foldl_work_four (κ .visit) (κ .sumTerm) passage.both.length
    passage.onlySource.length passage.onlyTarget.length passage.source.indices.length
  have writes := foldl_work_four (κ .visit) (κ .gradientWrite) passage.onlySource.length
    passage.both.length passage.onlyTarget.length passage.source.indices.length
  have sumsFit := Library.foldl.work_mono (visit := κ .visit)
    (show passage.both.length + passage.onlySource.length + passage.onlyTarget.length +
        passage.source.indices.length ≤
      2 * passage.source.indices.length + passage.target.indices.length by omega)
    (Nat.le_refl (κ .sumTerm))
  have writesFit := Library.foldl.work_mono (visit := κ .visit)
    (show passage.onlySource.length + passage.both.length + passage.onlyTarget.length +
        passage.source.indices.length ≤
      2 * passage.source.indices.length + passage.target.indices.length by omega)
    (Nat.le_refl (κ .gradientWrite))
  refine Acorn.Costed.ite_within (fun _ => (Acorn.Costed.op_within _ _ κ).mono ?_)
    (fun _ => (Acorn.Costed.bind_within (learnerStepCosted_within κ learner passage cumulant)
      (Acorn.Costed.op_within _ _ κ)).mono ?_)
  · simp only [questionBound]
    omega
  · simp only [questionBound]
    omega

/-- A question's bound grows with each set's length. -/
theorem questionBound_mono (κ : Costs) {stored most width limit : Nat} (storedFits : stored ≤ most)
    (widthFits : width ≤ limit) : questionBound κ stored width ≤ questionBound κ most limit := by
  have lists : 2 * stored + width ≤ 2 * most + limit := by omega
  have sums := Library.foldl.work_mono (visit := κ .visit) lists (Nat.le_refl (κ .sumTerm))
  have writes := Library.foldl.work_mono (visit := κ .visit) lists (Nat.le_refl (κ .gradientWrite))
  simp only [questionBound]
  omega

/-! ## A bank of questions -/

/-- A bank of questions steps within one pass over its questions, each within its bound at the
lengths of the transition's two sets and its record before the rest. -/
theorem bankStepCosted_within (κ : Costs) {discounts : List Discount}
    (bank : GradientBank dimension discounts) (passage : Passage dimension)
    (cumulants : Cumulants discounts) :
    (bank.stepCosted passage cumulants).Within κ
      (pass (κ .visit) discounts.length
        (questionBound κ passage.source.indices.length passage.target.indices.length +
          κ .questionBank)) := by
  induction bank with
  | nil =>
    cases cumulants
    exact (Acorn.Costed.op_within _ _ κ).mono (by simp [pass])
  | cons question rest ih =>
    cases cumulants with
    | cons origin value values =>
      refine (Acorn.Costed.charge_within
        (Acorn.Costed.bind_within_all (questionStepCosted_within κ question passage value)
          fun _ => Acorn.Costed.bind_within_all (ih values) fun _ =>
            Acorn.Costed.op_within _ _ κ)).mono ?_
      simp only [pass, List.length_cons, Nat.succ_mul]
      omega

/-! ## An option's questions -/

/-- Bound of an option's questions following a frame, from a stored set of `stored` slots to a
current set of `width` slots, with `count` questions: the advance, the bank's step and the
record. -/
abbrev followBound (κ : Costs) (stored width count : Nat) : Nat :=
  advanceBound κ stored width +
    pass (κ .visit) count (questionBound κ stored width + κ .questionBank) + κ .follow

/-- An option's questions follow a frame within their bound at the lengths of the stored set and
the frame's active set: a classified transition joins the stored set to the frame's
(`AcornVerif.CurrentOffPolicy.advance_passage`). -/
theorem followCosted_within (κ : Costs) {discounts : List Discount}
    (questions : OptionQuestions dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (cumulants : Cumulants discounts) (armed : Bool) :
    (questions.followCosted features cumulants armed).Within κ
      (followBound κ questions.preceding.features.indices.length features.indices.length
        discounts.length) := by
  rcases questions with ⟨learners, preceding⟩
  refine (Acorn.Costed.bind_within (advanceCosted_within κ preceding features armed)
    (b := pass (κ .visit) discounts.length
        (questionBound κ preceding.features.indices.length features.indices.length +
          κ .questionBank) + κ .follow) ?_).mono (Nat.le_of_eq (by simp only [followBound]; omega))
  rcases learned : (preceding.advanceCosted features armed).val with ⟨_ | passage, next⟩
  · exact (Acorn.Costed.op_within _ _ κ).mono (Nat.le_add_left _ _)
  · obtain ⟨source, target⟩ :=
      CurrentOffPolicy.advance_passage preceding features armed passage (congrArg Prod.fst learned)
    have bank := bankStepCosted_within κ learners passage cumulants
    rw [source, target] at bank
    exact Acorn.Costed.bind_within bank (Acorn.Costed.op_within _ _ κ)

/-- An option's bound grows with each set's length. -/
theorem followBound_mono (κ : Costs) {stored most width limit : Nat} (storedFits : stored ≤ most)
    (widthFits : width ≤ limit) (count : Nat) :
    followBound κ stored width count ≤ followBound κ most limit count := by
  have advance := advanceBound_mono κ storedFits widthFits
  have bank := pass_mono (visit := κ .visit) (Nat.le_refl count)
    (Nat.add_le_add_right (questionBound_mono κ storedFits widthFits) (κ .questionBank))
  simp only [followBound]
  omega

/-! ## Every option's questions -/

variable {interface : Interface} {config : Features.Config} {criterion : Criterion}

/-- Every option's questions follow the frame within one indexed map over the options, each
within its bound at the capacity of the dimension, which every stored set fits
(`AcornVerif.CurrentLearner.active_cardinality`), and at the frame's feature count. -/
theorem askQuestionsCosted_within (κ : Costs)
    (skills : Vector (Skill interface.actions config criterion dimension interface.layout)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (cumulants : Features.Cumulants interface.layout)
    (decision : TemporalDecision interface.actions) :
    (askQuestionsCosted skills features cumulants decision).Within κ
      (Library.mapFinIdx.work (κ .visit) Acorn.FeatureConstants.skillCount
        (followBound κ dimension.capacity features.indices.length interface.layout.length +
          κ .ask)) :=
  Acorn.Costed.mapFinIdx_within fun _ =>
    (Acorn.Costed.bind_within (followCosted_within κ _ features cumulants _)
      (Acorn.Costed.op_within _ _ κ)).mono
      (Nat.add_le_add_right (followBound_mono κ (CurrentLearner.active_cardinality _)
        (Nat.le_refl _) _) _)

/-- Every option's questions follow the frame within a function of the configuration alone: the
capacity of the dimension, the number of prediction signals and the cost model. Every active set
fits the dimension (`AcornVerif.CurrentLearner.active_cardinality`). -/
theorem askQuestionsCosted_within_capacity (κ : Costs)
    (skills : Vector (Skill interface.actions config criterion dimension interface.layout)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (cumulants : Features.Cumulants interface.layout)
    (decision : TemporalDecision interface.actions) :
    (askQuestionsCosted skills features cumulants decision).Within κ
      (Library.mapFinIdx.work (κ .visit) Acorn.FeatureConstants.skillCount
        (followBound κ dimension.capacity dimension.capacity interface.layout.length +
          κ .ask)) :=
  (askQuestionsCosted_within κ skills features cumulants decision).mono
    (Library.mapFinIdx.work_mono (visit := κ .visit) (Nat.le_refl _)
      (Nat.add_le_add_right (followBound_mono κ (Nat.le_refl _)
        (CurrentLearner.active_cardinality features) _) _))

end AcornVerif.Resource.Twin
