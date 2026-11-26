import Acorn.Host.Checkpoint.Image
import AcornVerif.CurrentFeatureConsumers
import AcornVerif.CurrentLifetime

namespace AcornVerif.CurrentImage
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime
open AcornVerif.CurrentLearner AcornVerif.CurrentLearnerCheck AcornVerif.CurrentFeatureConsumers

variable {config : Acorn.Config} {dimension : Dimension}

theorem binary32Format_exact : binary32Format.Exact := Codec.format_exact binary32Codec_canonical

theorem u64Format_exact : u64Format.Exact := Codec.format_exact u64Codec_canonical

theorem smallFormat_exact (count : Nat) (fits : count ≤ 2 ^ 32) : (smallFormat count).Exact :=
  Format.fin_exact 4 count (by simpa using fits)

theorem indexFormat_exact (dimension : Dimension) : (indexFormat dimension).Exact :=
  smallFormat_exact dimension.capacity (Nat.le_of_lt dimension.wordBound)

theorem wideFormat_exact (count : Nat) (fits : count ≤ 2 ^ 64) : (Format.fin 8 count).Exact :=
  Format.fin_exact 8 count (by simpa using fits)

theorem boundedFormat_exact (range : Interval32) : (boundedFormat range).Exact :=
  Format.filterMap_exact binary32Format_exact (fun stored => Bounded32.admit_self stored)
    (fun raw stored admitted => (Bounded32.admit_exact range raw stored admitted).1)

theorem weightFormat_exact (rule : ValueRule) : (weightFormat rule).Exact :=
  Format.map_exact (boundedFormat_exact _) (fun _ => rfl) (fun _ => rfl)

theorem departureFormat_exact : departureFormat.Exact :=
  Format.enum_exact _ _ (fun departure => by cases departure <;> rfl) (by decide) (by decide)

theorem optionEndFormat_exact : optionEndFormat.Exact :=
  Format.enum_exact _ _ (fun reason => by cases reason <;> rfl) (by decide) (by decide)

theorem faultFormat_exact : faultFormat.Exact :=
  Format.enum_exact _ _ (fun fault => by cases fault <;> rfl) (by decide) (by decide)

theorem fold_reversed : ∀ (indices : List (FeatIdx dimension)) (builder : UniqueBuilder dimension),
    indices.Nodup → (∀ index ∈ indices, index ∉ builder.reversed) →
      (indices.foldl UniqueBuilder.add builder).reversed = indices.reverse ++ builder.reversed
  | [], _, _, _ => by simp
  | index :: rest, builder, fresh, unseen => by
    rw [List.foldl_cons]
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp fresh
    have here := unseen index List.mem_cons_self
    have later : ∀ other ∈ rest, other ∉ (builder.add index).reversed := by
      intro other member
      rw [add_unseen builder index here]
      intro inside
      rcases List.mem_cons.mp inside with same | earlier
      · exact absent (same ▸ member)
      · exact unseen other (List.mem_cons_of_mem _ member) earlier
    rw [fold_reversed rest (builder.add index) tail later, add_unseen builder index here]
    simp

theorem unique_self (indices : List (FeatIdx dimension)) (fresh : indices.Nodup) :
    (unique indices).indices = indices := by
  have folded := fold_reversed indices (UniqueBuilder.empty dimension) fresh
    (by simp [UniqueBuilder.empty_def])
  simp only [UniqueBuilder.empty_def, List.append_nil] at folded
  simp [unique_def, UniqueBuilder.finish_def, UniqueBuilder.empty_def, folded]

theorem activeSet_ext {first second : SwiftTd.ActiveSet dimension}
    (same : first.indices = second.indices) : first = second := by
  cases first
  cases second
  cases same
  rfl

theorem activeSetFormat_exact (dimension : Dimension) : (activeSetFormat dimension).Exact :=
  Format.filterMap_exact_of
    (fun set suffix => Format.list_lawful (indexFormat_exact dimension).lawful _
      (Nat.lt_trans dimension.wordBound (by decide)) set.indices (active_cardinality set) suffix)
    (Format.list_canonical (indexFormat_exact dimension).canonical _)
    (fun set => by
      have kept := unique_self set.indices set.nodup
      simp only [kept, ↓reduceIte]
      exact congrArg some (activeSet_ext kept))
    (fun stored set built => by
      split at built
      · rename_i kept
        obtain rfl := Option.some.inj built
        exact kept
      · contradiction)

theorem nine_entries (words : Vector Binary32 9) :
    #v[words[0], words[1], words[2], words[3], words[4], words[5], words[6], words[7],
      words[8]] = words := by
  apply Vector.ext
  intro position inside
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | position := position
  all_goals first | (exfalso; omega) | rfl

theorem registerWords_write (transient : TransientState dimension) (index other : FeatIdx dimension)
    (words : Vector Binary32 9) :
    registerWords (transient.writeRegisters index words) other =
      if other = index then words else registerWords transient other := by
  by_cases same : other = index
  · subst same
    simp only [registerWords, TransientState.writeRegisters, vector_get, Vector.getElem_set_self,
      ↓reduceIte]
    exact nine_entries words
  · have apart : index.val ≠ other.val := fun equal => same (Fin.ext equal.symm)
    simp only [registerWords, TransientState.writeRegisters, vector_get, same, ↓reduceIte,
      Vector.getElem_set, apart]

abbrev writeAll (entries : List (FeatIdx dimension × Vector Binary32 9))
    (transient : TransientState dimension) : TransientState dimension :=
  entries.foldl (fun transient entry => transient.writeRegisters entry.1 entry.2) transient

theorem fold_scalars (entries : List (FeatIdx dimension × Vector Binary32 9))
    (transient : TransientState dimension) :
    (writeAll entries transient).eligible = transient.eligible ∧
      (writeAll entries transient).vDelta = transient.vDelta ∧
      (writeAll entries transient).vOld = transient.vOld := by
  induction entries generalizing transient with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons entry rest ih => exact ih (transient.writeRegisters entry.1 entry.2)

theorem fold_absent : ∀ (entries : List (FeatIdx dimension × Vector Binary32 9))
    (transient : TransientState dimension) (other : FeatIdx dimension),
    (∀ entry ∈ entries, entry.1 ≠ other) →
      registerWords (writeAll entries transient) other = registerWords transient other
  | [], _, _, _ => rfl
  | entry :: rest, transient, other, absent => by
    change registerWords (writeAll rest (transient.writeRegisters entry.1 entry.2)) other = _
    rw [fold_absent rest _ other (fun later member => absent later (List.mem_cons_of_mem _ member)),
      registerWords_write, ite_eq_right (fun same => absent entry List.mem_cons_self same.symm)]

theorem fold_present : ∀ (entries : List (FeatIdx dimension × Vector Binary32 9))
    (transient : TransientState dimension) (entry : FeatIdx dimension × Vector Binary32 9),
    (entries.map Prod.fst).Nodup → entry ∈ entries →
      registerWords (writeAll entries transient) entry.1 = entry.2
  | [], _, _, _, member => absurd member List.not_mem_nil
  | first :: rest, transient, entry, fresh, member => by
    rw [List.map_cons, List.nodup_cons] at fresh
    change registerWords (writeAll rest (transient.writeRegisters first.1 first.2)) entry.1 = _
    rcases List.mem_cons.mp member with same | later
    · subst same
      rw [fold_absent rest _ entry.1 (fun other inside equal =>
          fresh.1 (List.mem_map.mpr ⟨other, inside, equal⟩)),
        registerWords_write, ite_eq_left rfl]
    · exact fold_present rest _ entry fresh.2 later

theorem transient_ext {first second : TransientState dimension}
    (eligible : first.eligible = second.eligible) (vDelta : first.vDelta = second.vDelta)
    (vOld : first.vOld = second.vOld)
    (words : ∀ index, registerWords first index = registerWords second index) :
    first = second := by
  obtain ⟨z, zDelta, zBar, lastAlpha, deltaWeight, h, hOld, hTemp, p, e, d, o⟩ := first
  obtain ⟨z', zDelta', zBar', lastAlpha', deltaWeight', h', hOld', hTemp', p', e', d', o'⟩ := second
  simp only at eligible vDelta vOld
  subst eligible vDelta vOld
  have entry := fun (position : Nat) (inside : position < 9) (index : FeatIdx dimension) =>
    congrArg (fun word : Vector Binary32 9 => word[position]'inside) (words index)
  simp only [registerWords, vector_get] at entry
  have trace : ∀ {left right : Vector TraceRegister dimension.capacity},
      (∀ index : FeatIdx dimension, (left[index.val]).value = (right[index.val]).value) →
        left = right := fun {left right} same => by
    apply Vector.ext
    intro index inside
    exact congrArg TraceRegister.mk (same ⟨index, inside⟩)
  have metaWords : ∀ {left right : Vector MetaRegister dimension.capacity},
      (∀ index : FeatIdx dimension, (left[index.val]).value = (right[index.val]).value) →
        left = right := fun {left right} same => by
    apply Vector.ext
    intro index inside
    exact congrArg MetaRegister.mk (same ⟨index, inside⟩)
  obtain rfl := trace fun index => by simpa using entry 0 (by decide) index
  obtain rfl := trace fun index => by simpa using entry 1 (by decide) index
  obtain rfl := trace fun index => by simpa using entry 2 (by decide) index
  obtain rfl := trace fun index => by simpa using entry 3 (by decide) index
  obtain rfl := metaWords fun index => by simpa using entry 4 (by decide) index
  obtain rfl := metaWords fun index => by simpa using entry 5 (by decide) index
  obtain rfl := metaWords fun index => by simpa using entry 6 (by decide) index
  obtain rfl := metaWords fun index => by simpa using entry 7 (by decide) index
  obtain rfl := metaWords fun index => by simpa using entry 8 (by decide) index
  rfl

theorem zero_words (index : FeatIdx dimension) :
    registerWords (TransientState.zero dimension) index = Vector.replicate 9 Binary32.zero := by
  apply Vector.ext
  intro position inside
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | position := position
  all_goals first
    | (exfalso; omega)
    | simp [registerWords, TransientState.zero_def, vector_get]

theorem registers_words (state : NumericState config dimension) (index : FeatIdx dimension) :
    registers state index = registerWords state.transient index := rfl

theorem entries_slots (transient : TransientState dimension) :
    (transientEntries transient).map Prod.fst = transient.eligible.toList := by
  unfold transientEntries
  rw [List.map_map]
  exact List.map_id _

theorem transient_roundtrip (state : NumericState config dimension)
    (fresh : state.transient.eligible.toList.Nodup)
    (support : Supported state state.transient.eligible) :
    transientOf (transientEntries state.transient) state.transient.vDelta state.transient.vOld =
      state.transient := by
  have scalars := fold_scalars (transientEntries state.transient)
    { TransientState.zero dimension with
      eligible := ((transientEntries state.transient).map Prod.fst).toArray
      vDelta := state.transient.vDelta
      vOld := state.transient.vOld }
  apply transient_ext
  · rw [transientOf, scalars.1, entries_slots]
  · rw [transientOf, scalars.2.1]
  · rw [transientOf, scalars.2.2]
  · intro index
    by_cases member : index ∈ state.transient.eligible.toList
    · have present := fold_present (transientEntries state.transient)
        { TransientState.zero dimension with
          eligible := ((transientEntries state.transient).map Prod.fst).toArray
          vDelta := state.transient.vDelta
          vOld := state.transient.vOld }
        (index, registerWords state.transient index) (by rw [entries_slots]; exact fresh)
        (List.mem_map.mpr ⟨index, member, rfl⟩)
      exact present
    · have absent := fold_absent (transientEntries state.transient)
        { TransientState.zero dimension with
          eligible := ((transientEntries state.transient).map Prod.fst).toArray
          vDelta := state.transient.vDelta
          vOld := state.transient.vOld } index (fun entry inside same => by
          obtain ⟨slot, eligible, built⟩ := List.mem_map.mp inside
          subst built
          exact member (same ▸ eligible))
      rw [transientOf, absent]
      have zero := support index (fun inside => member (Array.mem_toList_iff.mpr inside))
      rw [registers_words] at zero
      rw [zero]
      exact zero_words index

theorem entries_roundtrip (entries : List (FeatIdx dimension × Vector Binary32 9))
    (vDelta vOld : Binary32) (fresh : (entries.map Prod.fst).Nodup) :
    transientEntries (transientOf entries vDelta vOld) = entries := by
  have scalars := fold_scalars entries
    { TransientState.zero dimension with
      eligible := (entries.map Prod.fst).toArray, vDelta := vDelta, vOld := vOld }
  unfold transientEntries
  rw [transientOf, scalars.1]
  simp only [List.map_map]
  conv => rhs; rw [← List.map_id entries]
  apply List.map_congr_left
  intro entry member
  change (entry.1, registerWords (writeAll entries _) entry.1) = entry
  rw [fold_present entries _ entry fresh member]

theorem numeric_mk {rails : StepSizeRails config} {weights : WeightArray config.rule dimension}
    {beta beta' : Vector (LogStepSize rails) dimension.capacity}
    {alpha alpha' : Vector Binary32 dimension.capacity}
    {evaluated : LogStepSize.Evaluated beta alpha} {evaluated' : LogStepSize.Evaluated beta' alpha'}
    {transient transient' : TransientState dimension}
    (sameBeta : beta = beta') (sameAlpha : alpha = alpha')
    (sameTransient : transient = transient') :
    (⟨rails, weights, beta, alpha, evaluated, transient⟩ : NumericState config dimension) =
      ⟨rails, weights, beta', alpha', evaluated', transient'⟩ := by
  subst sameBeta sameAlpha sameTransient
  rfl

theorem managed_ext {first second : Managed config dimension}
    (state : first.state = second.state) (phase : first.phase = second.phase) : first = second := by
  obtain ⟨firstState, firstPhase, _⟩ := first
  obtain ⟨secondState, secondPhase, _⟩ := second
  simp only at state phase
  subst state phase
  rfl

theorem retypeBeta_self {count : Nat}
    (beta : Vector (LogStepSize (StepSizeRails.ofConfig config)) count) :
    retypeBeta beta = beta := by
  apply Vector.ext
  intro index inside
  simp only [retypeBeta, Vector.getElem_map]

theorem managedState_words (learner : Managed config dimension) :
    managedState (managedWords learner) = learner.state := by
  have schedule := managed_schedule learner
  obtain ⟨⟨rails, weights, beta, alpha, evaluated, transient⟩, phase, admitted⟩ := learner
  obtain rfl := StepSizeRails.unique rails
  have steps : beta.map (fun stored => stored.alpha) = alpha := by
    apply Vector.ext
    intro index inside
    rw [Vector.getElem_map, evaluated index inside]
  have rebuilt := transient_roundtrip ⟨StepSizeRails.ofConfig config, weights, beta, alpha,
    evaluated, transient⟩ schedule.2.1 schedule.1.1
  exact numeric_mk (retypeBeta_self beta)
    (by simp only [managedWords, retypeBeta_self]; exact steps) rebuilt

theorem managedFormat_exact (config : Acorn.Config) (dimension : Dimension) :
    (managedFormat config dimension).Exact := by
  have short : ∀ learner : Managed config dimension,
      (transientEntries learner.state.transient).length ≤ dimension.capacity := fun learner => by
    have counted := eligible_cardinality learner.state (managed_schedule learner).2.1
    simpa [transientEntries, NumericState.eligibleCount] using counted
  apply Format.filterMap_exact_of
  · intro learner suffix
    exact Format.pair_lawfulAt
      ((Format.vector_exact (weightFormat_exact _) _).lawful _)
      (Format.pair_lawfulAt ((Format.vector_exact (boundedFormat_exact _) _).lawful _)
        (Format.pair_lawfulAt
          (Format.list_lawful (Format.pair_exact (indexFormat_exact dimension)
            (Format.vector_exact binary32Format_exact 9)).lawful _
            (Nat.lt_trans dimension.wordBound (by decide)) _ (short learner))
          (Format.pair_lawfulAt (binary32Format_exact.lawful _)
            (Format.pair_lawfulAt (binary32Format_exact.lawful _) (Format.bool_exact.lawful _)))))
      suffix
  · exact Format.pair_canonical (Format.vector_exact (weightFormat_exact _) _).canonical
      (Format.pair_canonical (Format.vector_exact (boundedFormat_exact _) _).canonical
        (Format.pair_canonical (Format.list_canonical (Format.pair_exact
            (indexFormat_exact dimension) (Format.vector_exact binary32Format_exact 9)).canonical _)
          (Format.pair_canonical binary32Format_exact.canonical
            (Format.pair_canonical binary32Format_exact.canonical Format.bool_exact.canonical))))
  · intro learner
    have checked : (managedState (managedWords learner)).resumable
        (managedWords learner).2.2.2.2.2 = true := by
      rw [managedState_words learner]
      exact managed_resumable learner
    unfold managedPack
    rw [dite_eq_left checked]
    exact congrArg some (managed_ext (managedState_words learner) rfl)
  · intro raw learner built
    unfold managedPack at built
    split at built
    · rename_i checked
      obtain rfl := Option.some.inj built
      obtain ⟨weights, beta, entries, vDelta, vOld, phase⟩ := raw
      have scalars := fold_scalars entries
        { TransientState.zero dimension with
          eligible := (entries.map Prod.fst).toArray, vDelta := vDelta, vOld := vOld }
      have fresh : (entries.map Prod.fst).Nodup := by
        have eligible := ((resumable_iff _ _).mp checked).2.1
        simpa [managedState, transientOf, scalars.1] using eligible
      refine Prod.ext rfl (Prod.ext (retypeBeta_self beta) (Prod.ext
        (entries_roundtrip entries vDelta vOld fresh) (Prod.ext scalars.2.1
          (Prod.ext scalars.2.2 rfl))))
    · contradiction

theorem controllerFormat_exact (config : Acorn.Config) (dimension : Dimension) (actions : Nat) :
    (controllerFormat config dimension actions).Exact :=
  Format.map_exact (Format.pair_exact (Format.vector_exact (managedFormat_exact _ _) _)
    (Format.pair_exact binary32Format_exact (Format.pair_exact binary32Format_exact
      Format.bool_exact))) (fun _ => rfl) (fun _ => rfl)

theorem present_nodup {α : Type} : ∀ slots : List (Option α),
    slots.Pairwise SlotsDistinct → (slots.filterMap id).Nodup
  | [], _ => List.nodup_nil
  | none :: rest, distinct => by
    simpa using present_nodup rest (List.pairwise_cons.mp distinct).2
  | some head :: rest, distinct => by
    obtain ⟨apart, tail⟩ := List.pairwise_cons.mp distinct
    simp only [List.filterMap_cons, id_eq, List.nodup_cons]
    refine ⟨fun member => ?_, present_nodup rest tail⟩
    obtain ⟨other, inside, same⟩ := List.mem_filterMap.mp member
    exact apart other inside head rfl (by simpa using same)

theorem rankedFormat_exact (dimension : Dimension) : (rankedFormat dimension).Exact :=
  Format.filterMap_exact
    (Format.vector_exact (Format.option_exact (indexFormat_exact dimension)) _)
    (fun ranked => by
      obtain ⟨slots, table, tabulated, reserved, distinct⟩ := ranked
      subst tabulated
      have fresh := unique_self _ (present_nodup _ distinct)
      unfold rankedPack
      rw [dite_eq_left reserved, dite_eq_left fresh]
      rfl)
    (fun slots ranked built => by
      unfold rankedPack at built
      split at built
      · split at built
        · obtain rfl := Option.some.inj built
          rfl
        · contradiction
      · contradiction)

theorem transitionFormat_exact (dimension : Dimension) (criterion : Criterion) :
    (transitionFormat dimension criterion).Exact :=
  Format.map_exact (Format.pair_exact (rankedFormat_exact dimension)
    (Format.pair_exact (Format.vector_exact (managedFormat_exact _ _) _)
      (Format.vector_exact (managedFormat_exact _ _) _))) (fun _ => rfl) (fun _ => rfl)

theorem modelFormat_exact (dimension : Dimension) :
    ∀ criterion : Criterion, (modelFormat dimension criterion).Exact
  | .discounted =>
    Format.map_exact (Format.pair_exact (managedFormat_exact _ _)
      (Format.pair_exact (managedFormat_exact _ _) (transitionFormat_exact _ _)))
      (fun model => by cases model; rfl) (fun _ => rfl)
  | .differential =>
    Format.map_exact (Format.pair_exact (managedFormat_exact _ _)
      (Format.pair_exact (managedFormat_exact _ _) (Format.pair_exact (managedFormat_exact _ _)
        (transitionFormat_exact _ _))))
      (fun model => by cases model; rfl) (fun _ => rfl)

theorem demonBankFormat_exact (dimension : Dimension) :
    ∀ discounts : List Discount, (demonBankFormat dimension discounts).Exact
  | [] => Format.map_exact Format.unit_exact (fun bank => by cases bank; rfl) (fun _ => rfl)
  | _ :: rest =>
    Format.map_exact (Format.pair_exact (managedFormat_exact _ _)
      (demonBankFormat_exact dimension rest)) (fun bank => by cases bank; rfl) (fun _ => rfl)

theorem assignmentFormat_exact (config : Features.Config) (dimension : Dimension) :
    (assignmentFormat config dimension).Exact :=
  Format.filterMap_exact (Codec.format_exact assignmentCodec_canonical)
    (Assignment.words_roundtrip dimension)
    (fun raw assignment admitted => (Assignment.admit_words dimension raw assignment admitted).symm)

theorem interestFormat_exact (config : Features.Config) (dimension : Dimension) :
    (interestFormat config dimension).Exact :=
  Format.map_exact (Format.sum_exact (assignmentFormat_exact config dimension)
    (Format.pair_exact departureFormat_exact (smallFormat_exact _ (by decide))))
    (fun interest => by cases interest <;> rfl)
    (fun raw => by rcases raw with assignment | ⟨origin, tag⟩ <;> rfl)

theorem followingFormat_exact : followingFormat.Exact :=
  Format.map_exact (Format.pair_exact (smallFormat_exact _ (by decide))
    (Format.pair_exact Format.bool_exact Format.bool_exact)) (fun _ => rfl) (fun _ => rfl)

theorem skillFormat_exact (actions : Word.Count) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) :
    (skillFormat actions config criterion dimension discounts).Exact :=
  Format.map_exact (Format.pair_exact (interestFormat_exact config dimension)
    (Format.pair_exact (controllerFormat_exact _ _ _) (Format.pair_exact (modelFormat_exact _ _)
      (Format.option_exact followingFormat_exact)))) (fun _ => rfl) (fun _ => rfl)

theorem ensembleFormat_exact (actions : Word.Count) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (discounts : List Discount) :
    (ensembleFormat actions config criterion dimension discounts).Exact :=
  Format.map_exact (Format.pair_exact (controllerFormat_exact _ _ _)
    (Format.pair_exact (controllerFormat_exact _ _ _)
      (Format.pair_exact (Format.vector_exact (skillFormat_exact _ _ _ _ _) _)
        (demonBankFormat_exact _ _)))) (fun _ => rfl) (fun _ => rfl)

theorem testerWords_progress {config : Features.Config} (progress : Progress config) :
    (testerWords progress).progress = progress.words := rfl

theorem tester_ext {first second : TesterWords} (same : first.progress = second.progress) :
    first = second := by
  obtain ⟨stream, credit, replaced, last, ⟨units, bound⟩⟩ := first
  obtain ⟨stream', credit', replaced', last', ⟨units', bound'⟩⟩ := second
  simp only [TesterWords.progress, ProgressWords.mk.injEq] at same
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
  rfl

theorem progressFormat_exact (config : Features.Config) : (progressFormat config).Exact :=
  Format.filterMap_exact (Format.pair_exact u64Format_exact
      (Codec.format_exact testerCodec_canonical))
    (fun progress => Progress.words_roundtrip progress)
    (fun raw progress admitted => by
      obtain ⟨clock, words⟩ := raw
      obtain ⟨rfl, same⟩ := Progress.admit_words clock words.progress progress admitted
      exact Prod.ext rfl (tester_ext same.symm))

theorem representationFormat_exact (shape : PatchShape) (config : Features.Config) :
    (representationFormat shape config).Exact :=
  Format.map_exact (progressFormat_exact config)
    (fun representation => by
      obtain ⟨progress, bank, identity⟩ := representation
      subst identity
      rfl)
    (fun _ => rfl)

theorem lifecycleFormat_exact (shape : PatchShape) (actions : Word.Count) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (discounts : List Discount) :
    (lifecycleFormat shape actions config criterion dimension discounts).Exact :=
  Format.map_exact (Format.pair_exact (representationFormat_exact _ _)
    (ensembleFormat_exact _ _ _ _ _)) (fun _ => rfl) (fun _ => rfl)

theorem predictionCacheFormat_exact :
    ∀ discounts : List Discount, (predictionCacheFormat discounts).Exact
  | [] => Format.map_exact Format.unit_exact (fun cache => by cases cache; rfl) (fun _ => rfl)
  | _ :: rest =>
    Format.map_exact (Format.pair_exact (boundedFormat_exact _) (predictionCacheFormat_exact rest))
      (fun cache => by cases cache; rfl) (fun _ => rfl)

theorem modelCacheFormat_exact : modelCacheFormat.Exact :=
  Format.map_exact (Format.pair_exact binary32Format_exact
    (Format.pair_exact binary32Format_exact binary32Format_exact)) (fun _ => rfl) (fun _ => rfl)

theorem activationFormat_exact (mode : Bool) : (activationFormat mode).Exact :=
  Format.map_exact (Format.pair_exact (smallFormat_exact _ (by decide)) Format.bool_exact)
    (fun _ => rfl) (fun _ => rfl)

theorem runFormat_exact (count : Word.Count) : (runFormat count).Exact :=
  Format.map_exact (Format.pair_exact (wideFormat_exact _ (Nat.le_of_lt count.word.toNat_lt))
    (smallFormat_exact _ (by decide))) (fun _ => rfl) (fun _ => rfl)

theorem committedFormat_exact (actions : Word.Count) (mode : Bool) :
    (committedFormat actions mode).Exact :=
  Format.filterMap_exact (Format.pair_exact (runFormat_exact actions)
      (Format.option_exact (Format.pair_exact (smallFormat_exact _ (by decide))
        (activationFormat_exact mode))))
    (fun committed => by
      unfold committedPack
      rw [dite_eq_left committed.pending])
    (fun raw committed built => by
      unfold committedPack at built
      split at built
      · obtain rfl := Option.some.inj built
        rfl
      · contradiction)

theorem occupancyFormat_exact {activation exploration : Type} {activations : Format activation}
    {explorations : Format exploration} (activationsExact : activations.Exact)
    (explorationsExact : explorations.Exact) :
    (occupancyFormat activations explorations).Exact :=
  Format.map_exact (Format.sum_exact Format.unit_exact (Format.sum_exact explorationsExact
    (Format.pair_exact (smallFormat_exact _ (by decide)) activationsExact)))
    (fun occupancy => by cases occupancy <;> rfl)
    (fun raw => by rcases raw with ⟨⟩ | run | ⟨slot, state⟩ <;> rfl)

theorem snapshotFormat_exact (count : Word.Count) : (snapshotFormat count).Exact :=
  Format.map_exact (Format.pair_exact (Format.vector_exact binary32Format_exact _)
    (boundedFormat_exact _)) (fun _ => rfl) (fun _ => rfl)

theorem policyDecisionFormat_exact (count : Word.Count) : (policyDecisionFormat count).Exact :=
  Format.map_exact (Format.pair_exact (snapshotFormat_exact count)
    (Format.pair_exact (wideFormat_exact _ (Nat.le_of_lt count.word.toNat_lt)) Format.bool_exact))
    (fun _ => rfl) (fun _ => rfl)

theorem sourceFormat_exact : sourceFormat.Exact :=
  Format.map_exact (Format.sum_exact Format.unit_exact (Format.sum_exact Format.unit_exact
    (Format.sum_exact Format.unit_exact (smallFormat_exact _ (by decide)))))
    (fun source => by cases source <;> rfl)
    (fun raw => by rcases raw with ⟨⟩ | ⟨⟩ | ⟨⟩ | slot <;> rfl)

theorem endEventFormat_exact : endEventFormat.Exact :=
  Format.map_exact (Format.pair_exact (smallFormat_exact _ (by decide))
    (Format.pair_exact (smallFormat_exact _ (by decide)) optionEndFormat_exact))
    (fun _ => rfl) (fun _ => rfl)

theorem decisionFormat_exact (actions : Word.Count) : (decisionFormat actions).Exact :=
  Format.map_exact (Format.pair_exact sourceFormat_exact
    (Format.pair_exact (wideFormat_exact _ (Nat.le_of_lt actions.word.toNat_lt))
    (Format.pair_exact (Format.vector_exact binary32Format_exact _)
    (Format.pair_exact (Format.vector_exact binary32Format_exact _)
    (Format.pair_exact Format.bool_exact (Format.pair_exact
      (Format.vector_exact binary32Format_exact _)
    (Format.pair_exact (Format.option_exact (policyDecisionFormat_exact _))
    (Format.pair_exact (Format.option_exact (smallFormat_exact _ (by decide)))
      (Format.option_exact endEventFormat_exact)))))))))
    (fun _ => rfl) (fun _ => rfl)

theorem recentFormat_exact (dimension : Dimension) : (recentFormat dimension).Exact :=
  Format.map_exact (Format.pair_exact (Format.vector_exact (activeSetFormat_exact dimension) _)
    (Format.pair_exact (smallFormat_exact _ (by decide)) (smallFormat_exact _ (by decide))))
    (fun _ => rfl) (fun _ => rfl)

theorem rngFormat_exact : rngFormat.Exact :=
  Format.map_exact (Format.pair_exact u64Format_exact (Format.pair_exact u64Format_exact
    (Format.pair_exact u64Format_exact u64Format_exact))) (fun _ => rfl) (fun _ => rfl)

theorem referencesFormat_exact (dimension : Dimension) (discounts : List Discount)
    {activation exploration decision : Type} {occupancy : Format (Occupancy activation exploration)}
    {decisions : Format decision} (occupancyExact : occupancy.Exact)
    (decisionsExact : decisions.Exact) :
    (referencesFormat dimension discounts occupancy decisions).Exact :=
  Format.map_exact (Format.pair_exact (predictionCacheFormat_exact discounts)
    (Format.pair_exact (Format.vector_exact binary32Format_exact _)
    (Format.pair_exact (Format.vector_exact modelCacheFormat_exact _)
    (Format.pair_exact occupancyExact (Format.pair_exact u64Format_exact
    (Format.pair_exact (Format.vector_exact binary32Format_exact _)
    (Format.pair_exact Format.byte_exact (Format.pair_exact binary32Format_exact
    (Format.pair_exact rngFormat_exact (Format.pair_exact Format.bool_exact
    (Format.pair_exact decisionsExact (recentFormat_exact dimension))))))))))))
    (fun _ => rfl) (fun _ => rfl)

theorem runtimeFormat_exact (shape : PatchShape) (actions : Word.Count) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (discounts : List Discount)
    {activation exploration decision : Type} {occupancy : Format (Occupancy activation exploration)}
    {decisions : Format decision} (occupancyExact : occupancy.Exact)
    (decisionsExact : decisions.Exact) :
    (runtimeFormat shape actions config criterion dimension discounts occupancy decisions).Exact :=
  Format.map_exact (Format.pair_exact (lifecycleFormat_exact _ _ _ _ _ _)
    (referencesFormat_exact _ _ occupancyExact decisionsExact)) (fun _ => rfl) (fun _ => rfl)

theorem gapFormat_exact : gapFormat.Exact :=
  Format.map_exact (Format.pair_exact Format.byte_exact binary32Format_exact)
    (fun _ => rfl) (fun _ => rfl)

theorem creditFormat_exact : creditFormat.Exact :=
  Format.map_exact (Format.sum_exact Format.unit_exact (Format.sum_exact gapFormat_exact
    Format.unit_exact)) (fun credit => by cases credit <;> rfl)
    (fun raw => by rcases raw with ⟨⟩ | gap | ⟨⟩ <;> rfl)

theorem averageFormat_exact : averageFormat.Exact :=
  Format.map_exact (boundedFormat_exact _) (fun _ => rfl) (fun _ => rfl)

theorem rateFormat_exact : ∀ policy : RatePolicy, (rateFormat policy).Exact
  | .declared => Format.map_exact Format.unit_exact (fun rate => by cases rate; rfl) (fun _ => rfl)
  | .perLearner =>
    Format.map_exact Format.unit_exact (fun rate => by cases rate; rfl) (fun _ => rfl)
  | .shared => Format.map_exact Format.unit_exact (fun rate => by cases rate; rfl) (fun _ => rfl)
  | .annealed =>
    Format.map_exact (boundedFormat_exact _) (fun rate => by cases rate; rfl) (fun _ => rfl)

theorem sum_roundtrip {quantity : Quantity} (record : SumCount quantity) :
    admitSum quantity (sumWords record) = some record := by
  simp [admitSum, sumWords, SumCount.admit, CurrentLifetime.stored_sum_legal record]

theorem sumFormat_exact (quantity : Quantity) : (sumFormat quantity).Exact :=
  Format.filterMap_exact (Codec.format_exact sumCodec_canonical) sum_roundtrip
    (fun raw record admitted => by
      obtain ⟨count, sum⟩ := raw
      unfold admitSum SumCount.admit at admitted
      split at admitted
      · obtain rfl := Option.some.inj admitted
        rfl
      · contradiction)

theorem goalFormat_exact : goalFormat.Exact :=
  Format.filterMap_exact (Codec.format_exact goalCodec_canonical)
    (fun record => by
      unfold admitGoal goalWords
      rw [dite_eq_left ⟨record.successesBound, record.emptySteps⟩])
    (fun raw record admitted => by
      unfold admitGoal at admitted
      split at admitted
      · obtain rfl := Option.some.inj admitted
        rfl
      · contradiction)

theorem episodesFormat_exact : episodesFormat.Exact := Codec.format_exact episodesCodec_canonical

theorem demonDurableFormat_exact (discount : Discount) : (demonDurableFormat discount).Exact :=
  Format.map_exact (Format.pair_exact (sumFormat_exact _) (Format.pair_exact (boundedFormat_exact _)
    (boundedFormat_exact _))) (fun _ => rfl) (fun _ => rfl)

theorem pendingFormat_exact (discount : Discount) : (pendingFormat discount).Exact :=
  Format.map_exact (Format.pair_exact (smallFormat_exact _ (by decide))
    (Format.pair_exact (boundedFormat_exact _) (Format.pair_exact binary32Format_exact
      (Format.pair_exact binary32Format_exact u64Format_exact)))) (fun _ => rfl) (fun _ => rfl)

theorem totalFormat_exact (envelope : Nat) : (totalFormat envelope).Exact :=
  Format.filterMap_exact (Format.pair_exact (wideFormat_exact _ (by decide)) Format.natural_exact)
    (fun total => by simp only [dite_eq_left total.bounded])
    (fun raw total built => by
      simp only at built
      split at built
      · obtain rfl := Option.some.inj built
        rfl
      · contradiction)

theorem ratioFormat_exact : ratioFormat.Exact :=
  Format.filterMap_exact (Format.pair_exact Format.natural_exact Format.natural_exact)
    (fun ratio => by
      simp only [Agreement.Ratio.admit, dite_eq_left ratio.positive, dite_eq_left ratio.bounded])
    (fun raw ratio admitted => by
      simp only [Agreement.Ratio.admit] at admitted
      split at admitted
      · split at admitted
        · obtain rfl := Option.some.inj admitted
          rfl
        · contradiction
      · contradiction)

theorem precisionFormat_exact : precisionFormat.Exact :=
  Format.map_exact (Format.pair_exact ratioFormat_exact ratioFormat_exact)
    (fun _ => rfl) (fun _ => rfl)

theorem clockRangeFormat_exact : clockRangeFormat.Exact :=
  Format.filterMap_exact (Format.pair_exact u64Format_exact u64Format_exact)
    (fun range => by simp only [dite_eq_left range.ordered])
    (fun raw range built => by
      simp only at built
      split at built
      · obtain rfl := Option.some.inj built
        rfl
      · contradiction)

theorem channelFormat_exact (discount : Discount) : (channelFormat discount).Exact :=
  Format.map_exact (Format.pair_exact (totalFormat_exact _) (Format.pair_exact
    (Format.option_exact faultFormat_exact) (Format.pair_exact
    (Format.option_exact clockRangeFormat_exact) (Format.pair_exact
    (Format.option_exact clockRangeFormat_exact) (Format.pair_exact
    (wideFormat_exact _ (by decide)) (Format.option_exact precisionFormat_exact))))))
    (fun _ => rfl) (fun _ => rfl)

theorem demonStatsFormat_exact (discount : Discount) : (demonStatsFormat discount).Exact :=
  Format.map_exact (Format.pair_exact (demonDurableFormat_exact _)
    (Format.pair_exact (Format.vector_exact (Format.option_exact (pendingFormat_exact _)) _)
      (channelFormat_exact _)))
    (fun stats => by
      obtain ⟨durable, pending, agreement, ⟨settleAfter, same⟩⟩ := stats
      subst same
      rfl)
    (fun _ => rfl)

theorem demonRecordsFormat_exact : ∀ discounts : List Discount, (demonRecordsFormat discounts).Exact
  | [] => Format.map_exact Format.unit_exact (fun records => by cases records; rfl) (fun _ => rfl)
  | _ :: rest =>
    Format.map_exact (Format.pair_exact (demonStatsFormat_exact _) (demonRecordsFormat_exact rest))
      (fun records => by cases records; rfl) (fun _ => rfl)

theorem agreementPointFormat_exact : agreementPointFormat.Exact :=
  Format.map_exact (Format.pair_exact u64Format_exact ratioFormat_exact)
    (fun _ => rfl) (fun _ => rfl)

theorem statsFormat_exact (discounts : List Discount) : (statsFormat discounts).Exact :=
  Format.map_exact (Format.pair_exact (sumFormat_exact _) (Format.pair_exact
    (Format.vector_exact (sumFormat_exact _) _) (Format.pair_exact
    (Format.vector_exact (sumFormat_exact _) _) (Format.pair_exact
    (demonRecordsFormat_exact discounts) (Format.pair_exact
    (Format.vector_exact (sumFormat_exact _) _) (Format.pair_exact
    (Format.vector_exact episodesFormat_exact _) (Format.pair_exact
    (Format.vector_exact goalFormat_exact _) (Format.pair_exact
    (Format.vector_exact (Format.vector_exact goalFormat_exact _) _) (Format.pair_exact
    (Format.option_exact u64Format_exact) (Format.pair_exact
    (Format.vector_exact (Format.option_exact agreementPointFormat_exact) _)
    (Format.pair_exact (Format.option_exact u64Format_exact) Format.bool_exact)))))))))))
    (fun _ => rfl) (fun _ => rfl)

theorem controlFormat_exact (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension) :
    (controlFormat interface profile config criterion dimension).Exact :=
  Format.filterMap_exact (Format.pair_exact (runtimeFormat_exact _ _ _ _ _ _
      (occupancyFormat_exact (activationFormat_exact _) (committedFormat_exact _ _))
      (Format.option_exact (decisionFormat_exact _)))
    (Format.pair_exact creditFormat_exact (Format.pair_exact averageFormat_exact
      (Format.pair_exact (rateFormat_exact _) (statsFormat_exact _)))))
    (fun control => by
      unfold controlPack
      rw [dite_eq_left control.creditMatches])
    (fun raw control built => by
      unfold controlPack at built
      split at built
      · obtain rfl := Option.some.inj built
        rfl
      · contradiction)

theorem agentImageFormat_exact (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension) :
    (agentImageFormat interface profile config criterion dimension).Exact :=
  Format.filterMap_exact (controlFormat_exact _ _ _ _ _)
    (fun image => by
      unfold imagePack
      rw [dite_eq_left image.aligned, dite_eq_left image.episodes])
    (fun raw image built => by
      unfold imagePack at built
      split at built
      · split at built
        · obtain rfl := Option.some.inj built
          rfl
        · contradiction
      · contradiction)

theorem imageFormat_exact (construction : AgentConstruction) :
    (imageFormat construction).Exact :=
  Format.map_exact (agentImageFormat_exact _ _ _ _ _) (fun _ => rfl) (fun _ => rfl)

end AcornVerif.CurrentImage
