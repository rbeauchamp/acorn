import Acorn.Host.Checkpoint.Format
import Acorn.Host.AgentConstruction

namespace Acorn.Checkpoint
open Features Handcrafted Lifetime

def binary32Format : Format Binary32 := binary32Codec.format

def u64Format : Format UInt64 := u64Codec.format

def indexFormat (dimension : Dimension) : Format (FeatIdx dimension) :=
  Format.fin 4 dimension.capacity

def smallFormat (count : Nat) : Format (Fin count) := Format.fin 4 count

def boundedFormat (range : Interval32) : Format (Bounded32 range) :=
  binary32Format.filterMap (Bounded32.admit range) (·.value)

def weightFormat (rule : ValueRule) : Format (Weight rule) :=
  (boundedFormat rule.domain.range).map Weight.mk Weight.bounded

def departures : List Departure :=
  [.featureChannels, .spatialPotentials, .explorationDuration, .learnerParameters, .cumulants,
    .explorationRate, .featureTester, .achievementEvent]

def Departure.position : Departure → Nat
  | .featureChannels => 0
  | .spatialPotentials => 1
  | .explorationDuration => 2
  | .learnerParameters => 3
  | .cumulants => 4
  | .explorationRate => 5
  | .featureTester => 6
  | .achievementEvent => 7

def departureFormat : Format Departure := Format.enum departures Departure.position

def optionEnds : List OptionEnd := [.goal, .duration, .interrupted]

def OptionEnd.position : OptionEnd → Nat
  | .goal => 0
  | .duration => 1
  | .interrupted => 2

def optionEndFormat : Format OptionEnd := Format.enum optionEnds OptionEnd.position

def faults : List Agreement.Fault := [.invalid, .saturated]

def Agreement.Fault.position : Agreement.Fault → Nat
  | .invalid => 0
  | .saturated => 1

def faultFormat : Format Agreement.Fault := Format.enum faults Agreement.Fault.position

def presence {dimension : Dimension} (indices : List (FeatIdx dimension)) : UniqueBuilder dimension :=
  indices.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)

theorem presence_mem {dimension : Dimension} (indices : List (FeatIdx dimension))
    (index : FeatIdx dimension) : index ∈ (presence indices).reversed ↔ index ∈ indices := by
  have kept := mem_unique indices index
  simp only [unique_def, UniqueBuilder.finish_def, List.mem_reverse] at kept
  exact kept

def activeSetFormat (dimension : Dimension) : Format (SwiftTd.ActiveSet dimension) :=
  ((indexFormat dimension).list dimension.capacity).filterMap
    (fun stored => if (unique stored).indices = stored then some (unique stored) else none)
    (·.indices)

def registerWords {dimension : Dimension} (transient : TransientState dimension)
    (index : FeatIdx dimension) : Vector Binary32 9 :=
  #v[(transient.z.get index).value, (transient.zDelta.get index).value,
    (transient.zBar.get index).value, (transient.lastAlpha.get index).value,
    (transient.deltaWeight.get index).value, (transient.h.get index).value,
    (transient.hOld.get index).value, (transient.hTemp.get index).value,
    (transient.p.get index).value]

def _root_.Acorn.TransientState.writeRegisters {dimension : Dimension} (transient : TransientState dimension)
    (index : FeatIdx dimension) (words : Vector Binary32 9) : TransientState dimension :=
  { transient with
    z := transient.z.set index.val ⟨words[0]⟩ index.isLt
    zDelta := transient.zDelta.set index.val ⟨words[1]⟩ index.isLt
    zBar := transient.zBar.set index.val ⟨words[2]⟩ index.isLt
    lastAlpha := transient.lastAlpha.set index.val ⟨words[3]⟩ index.isLt
    deltaWeight := transient.deltaWeight.set index.val ⟨words[4]⟩ index.isLt
    h := transient.h.set index.val ⟨words[5]⟩ index.isLt
    hOld := transient.hOld.set index.val ⟨words[6]⟩ index.isLt
    hTemp := transient.hTemp.set index.val ⟨words[7]⟩ index.isLt
    p := transient.p.set index.val ⟨words[8]⟩ index.isLt }

def transientEntries {dimension : Dimension} (transient : TransientState dimension) :
    List (FeatIdx dimension × Vector Binary32 9) :=
  transient.eligible.toList.map fun index => (index, registerWords transient index)

def transientOf {dimension : Dimension} (entries : List (FeatIdx dimension × Vector Binary32 9))
    (vDelta vOld : Binary32) : TransientState dimension :=
  entries.foldl (fun transient entry => transient.writeRegisters entry.1 entry.2)
    { TransientState.zero dimension with
      eligible := (entries.map Prod.fst).toArray
      vDelta := vDelta
      vOld := vOld }

theorem _root_.Acorn.StepSizeRails.unique {config : Acorn.Config} (rails : StepSizeRails config) :
    rails = StepSizeRails.ofConfig config := by
  obtain ⟨⟨lower, upper, lowerFinite, upperFinite, ordered⟩, lowerIdentity, upperIdentity⟩ := rails
  simp only at lowerIdentity upperIdentity
  subst lowerIdentity upperIdentity
  rfl

abbrev ManagedWords (config : Acorn.Config) (dimension : Dimension) :=
  Vector (Weight config.rule) dimension.capacity ×
    Vector (LogStepSize (StepSizeRails.ofConfig config)) dimension.capacity ×
    List (FeatIdx dimension × Vector Binary32 9) × Binary32 × Binary32 × Bool

def retypeBeta {config : Acorn.Config} {rails : StepSizeRails config} {count : Nat}
    (beta : Vector (LogStepSize rails) count) :
    Vector (LogStepSize (StepSizeRails.ofConfig config)) count :=
  beta.map fun stored => ⟨stored.value, (StepSizeRails.unique rails) ▸ stored.legal⟩

def managedWords {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) : ManagedWords config dimension :=
  (learner.state.weights, retypeBeta learner.state.beta,
    transientEntries learner.state.transient, learner.state.transient.vDelta,
    learner.state.transient.vOld, learner.phase)

def managedState {config : Acorn.Config} {dimension : Dimension}
    (raw : ManagedWords config dimension) : NumericState config dimension :=
  ⟨StepSizeRails.ofConfig config, raw.1, raw.2.1, raw.2.1.map fun stored => stored.alpha,
    LogStepSize.Evaluated.map raw.2.1, transientOf raw.2.2.1 raw.2.2.2.1 raw.2.2.2.2.1⟩

def managedPack {config : Acorn.Config} {dimension : Dimension}
    (raw : ManagedWords config dimension) : Option (Managed config dimension) :=
  if checked : (managedState raw).resumable raw.2.2.2.2.2 = true then
    some ⟨managedState raw, raw.2.2.2.2.2, .durable checked⟩
  else none

def managedFormat (config : Acorn.Config) (dimension : Dimension) :
    Format (Managed config dimension) :=
  ((Format.vector (weightFormat config.rule) dimension.capacity).pair
    ((Format.vector (boundedFormat (StepSizeRails.ofConfig config).range) dimension.capacity).pair
    ((((indexFormat dimension).pair (Format.vector binary32Format 9)).list
        dimension.capacity).pair
    (binary32Format.pair (binary32Format.pair Format.bool))))).filterMap managedPack managedWords

def controllerFormat (config : Acorn.Config) (dimension : Dimension) (actions : Nat) :
    Format (Controller config dimension actions) :=
  ((Format.vector (managedFormat config dimension) actions).pair
    (binary32Format.pair (binary32Format.pair Format.bool))).map
    (fun (learners, vOld, vDelta, restartPending) => ⟨learners, vOld, vDelta, restartPending⟩)
    (fun controller => (controller.learners, controller.vOld, controller.vDelta,
      controller.restartPending))

theorem slots_distinct {α : Type} : ∀ slots : List (Option α),
    (slots.filterMap id).Nodup → slots.Pairwise SlotsDistinct
  | [], _ => .nil
  | none :: rest, fresh => by
    refine List.Pairwise.cons ?_ (slots_distinct rest (by simpa using fresh))
    intro other _ slot held
    cases held
  | some head :: rest, fresh => by
    simp only [List.filterMap_cons, id_eq, List.nodup_cons] at fresh
    obtain ⟨absent, tail⟩ := fresh
    refine List.Pairwise.cons ?_ (slots_distinct rest tail)
    intro other member slot held same
    cases held
    subst same
    exact absent (List.mem_filterMap.mpr ⟨some head, member, rfl⟩)

def rankedPack {dimension : Dimension}
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity) :
    Option (RankedFeatures dimension) :=
  if reserved : slots[(rankDimension dimension).capacity - 1]'(Nat.sub_lt
      (rankDimension dimension).positive (by decide)) = none then
    if fresh : (unique (slots.toList.filterMap id)).indices = slots.toList.filterMap id then
      some (.ofSlots slots reserved (slots_distinct _ (fresh ▸ (unique _).nodup)))
    else none
  else none

def rankedFormat (dimension : Dimension) : Format (RankedFeatures dimension) :=
  (Format.vector (Format.option (indexFormat dimension)) (rankDimension dimension).capacity).filterMap
    rankedPack (·.slots)

def transitionFormat (dimension : Dimension) (criterion : Criterion) :
    Format (Transition dimension criterion) :=
  ((rankedFormat dimension).pair
    ((Format.vector (managedFormat (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity).pair
    (Format.vector (managedFormat (criterion.config .demon) (rankDimension dimension))
      Acorn.FeatureConstants.metaActionCount))).map
    (fun (ranked, rows, deviations) => ⟨ranked, rows, deviations⟩)
    (fun transition => (transition.ranked, transition.rows, transition.deviations))

def modelFormat (dimension : Dimension) : (criterion : Criterion) → Format (Model dimension criterion)
  | .discounted =>
    ((managedFormat (Criterion.config .discounted .demon) dimension).pair
      ((managedFormat (Criterion.config .discounted .demon) dimension).pair
        (transitionFormat dimension .discounted))).map
      (fun (reward, continuation, transition) => .discounted reward continuation transition)
      (fun | .discounted reward continuation transition => (reward, continuation, transition))
  | .differential =>
    ((managedFormat (Criterion.config .differential .demon) dimension).pair
      ((managedFormat (Criterion.config .differential .demon) dimension).pair
      ((managedFormat (Criterion.config .differential .demon) dimension).pair
        (transitionFormat dimension .differential)))).map
      (fun (reward, continuation, duration, transition) =>
        .differential reward continuation duration transition)
      (fun model => match model with
        | .differential reward continuation duration transition =>
          (reward, continuation, duration, transition))

def demonBankFormat (dimension : Dimension) :
    (discounts : List Discount) → Format (DemonBank dimension discounts)
  | [] => Format.unit.map (fun _ => .nil) (fun _ => ())
  | discount :: rest =>
    ((managedFormat ⟨.demon, .discounted discount⟩ dimension).pair
      (demonBankFormat dimension rest)).map
      (fun (head, tail) => .cons head tail) (fun | .cons head tail => (head, tail))

def assignmentCodec : Codec AssignmentWords :=
  (u32Codec.pair (u32Codec.pair (u32Codec.pair u32Codec))).iso
    (fun (tag, unit, feature, bonus) => ⟨tag, unit, feature, bonus⟩)
    (fun a => (a.tag, a.unit, a.feature, a.bonus)) (by intro a; rfl)

theorem assignmentCodec_canonical : assignmentCodec.Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical u32Codec_canonical (Codec.pair_canonical u32Codec_canonical
      (Codec.pair_canonical u32Codec_canonical u32Codec_canonical)))
    fun _ => rfl

def assignmentFormat (config : Features.Config) (dimension : Dimension) :
    Format (Assignment config) :=
  assignmentCodec.format.filterMap (Assignment.admit dimension config) (Assignment.words dimension)

def interestFormat (config : Features.Config) (dimension : Dimension) : Format (Interest config) :=
  ((assignmentFormat config dimension).sum
    (departureFormat.pair (smallFormat Acorn.FeatureConstants.skillCount))).map
    (fun raw => match raw with
      | .inl assignment => .learned assignment
      | .inr (origin, tag) => .declared origin tag)
    (fun interest => match interest with
      | .learned assignment => .inl assignment
      | .declared origin tag => .inr (origin, tag))

def followingFormat : Format Following :=
  ((smallFormat (Acorn.FeatureConstants.optionMaxDuration + 1)).pair
    (Format.bool.pair Format.bool)).map
    (fun (age, live, previous) => ⟨age, live, previous⟩)
    (fun following => (following.age, following.live, following.previous))

def skillFormat (actions : Word.Count) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) :
    Format (Skill actions config criterion dimension discounts) :=
  ((interestFormat config dimension).pair
    ((controllerFormat (criterion.config .optionSkill) dimension actions.word.toNat).pair
    ((modelFormat dimension criterion).pair followingFormat.option))).map
    (fun (interest, policy, model, following) => ⟨interest, policy, model, following⟩)
    (fun skill => (skill.interest, skill.policy, skill.model, skill.following))

def ensembleFormat (actions : Word.Count) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) :
    Format (Ensemble actions config criterion dimension discounts) :=
  ((controllerFormat (criterion.config .control) dimension actions.word.toNat).pair
    ((controllerFormat (criterion.config .control) dimension
      Acorn.FeatureConstants.metaActionCount).pair
    ((Format.vector (skillFormat actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount).pair
    (demonBankFormat dimension discounts)))).map
    (fun (control, metaController, skills, demons) => ⟨control, metaController, skills, demons⟩)
    (fun ensemble => (ensemble.control, ensemble.metaController, ensemble.skills,
      ensemble.demons))

def lastCodec : Codec LastWords := u32Codec.pair (u64Codec.pair u16Codec)

def unitStateCodec : Codec UnitWords := u64Codec.pair (u64Codec.pair binary32Codec)

abbrev UnitList := { units : List UnitWords // units.length ≤ 65535 }

def unitListCodec : Codec UnitList where
  encode units := u32Codec.encode units.val.length.toUInt32 ++ units.val.flatMap unitStateCodec.encode
  decode bytes := do
    let (count, rest) ← u32Codec.decode bytes
    if bound : count.toNat ≤ 65535 then
      match h : decodeList unitStateCodec count.toNat rest with
      | none => none
      | some (units, rest') =>
        some (⟨units, by rw [decodeList_length unitStateCodec count.toNat rest units rest' h]; exact bound⟩,
          rest')
    else none
  roundtrip := by
    intro units suffix
    have exactCount : units.val.length.toUInt32.toNat = units.val.length :=
      Nat.mod_eq_of_lt (by have := units.property; omega)
    simp only [List.append_assoc, u32Codec.roundtrip, bind, Option.bind]
    simp only [exactCount, units.property, ↓reduceDIte]
    split <;> rename_i parsed
    · rw [exactCount, list_roundtrip] at parsed; contradiction
    · rw [exactCount, list_roundtrip] at parsed
      cases parsed
      rfl

structure TesterWords where
  stream : UInt64
  credit : UInt32
  replaced : UInt64
  last : LastWords
  units : UnitList

def testerCodec : Codec TesterWords :=
  (u64Codec.pair (u32Codec.pair (u64Codec.pair (lastCodec.pair unitListCodec)))).iso
    (fun (stream, credit, replaced, last, units) => ⟨stream, credit, replaced, last, units⟩)
    (fun t => (t.stream, t.credit, t.replaced, t.last, t.units)) (by intro t; rfl)

def TesterWords.progress (words : TesterWords) : ProgressWords :=
  ⟨words.stream, words.credit, words.replaced, words.last, words.units.val⟩

def testerWords {config : Features.Config} (progress : Progress config) : TesterWords :=
  ⟨progress.words.stream, progress.words.credit, progress.words.replaced, progress.words.last,
    ⟨progress.words.units, by
      simpa [Progress.words] using config.units.bounded⟩⟩

theorem lastCodec_canonical : lastCodec.Canonical :=
  Codec.pair_canonical u32Codec_canonical
    (Codec.pair_canonical u64Codec_canonical u16Codec_canonical)

theorem unitStateCodec_canonical : unitStateCodec.Canonical :=
  Codec.pair_canonical u64Codec_canonical
    (Codec.pair_canonical u64Codec_canonical binary32Codec_canonical)

theorem unitListCodec_canonical : unitListCodec.Canonical := by
  intro bytes value rest decoded
  cases counted : u32Codec.decode bytes with
  | none => simp [unitListCodec, counted] at decoded
  | some found =>
    obtain ⟨count, tail⟩ := found
    simp only [unitListCodec, counted, bind, Option.bind] at decoded
    split at decoded
    · split at decoded
      · contradiction
      · rename_i units suffix listed
        simp only [Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        have length := decodeList_length unitStateCodec count.toNat tail units suffix listed
        obtain ⟨read, unitsRead, tailRead⟩ :=
          decodeListInto_written unitStateCodec_canonical count.toNat tail [] units suffix listed
        simp only [List.reverse_nil, List.nil_append] at unitsRead
        have countWord : units.length.toUInt32 = count := by
          rw [length]
          exact UInt32.toNat_inj.mp (Nat.mod_eq_of_lt count.toNat_lt)
        rw [u32Codec_canonical _ _ _ counted]
        simp only [unitListCodec, countWord, List.append_assoc]
        rw [tailRead, ← unitsRead]
    · contradiction

theorem testerCodec_canonical : testerCodec.Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical u64Codec_canonical (Codec.pair_canonical u32Codec_canonical
      (Codec.pair_canonical u64Codec_canonical
        (Codec.pair_canonical lastCodec_canonical unitListCodec_canonical))))
    fun _ => rfl

def progressFormat (config : Features.Config) : Format (Progress config) :=
  (u64Format.pair testerCodec.format).filterMap
    (fun (clock, words) => Progress.admit config clock words.progress)
    (fun progress => (progress.clock, testerWords progress))

def representationFormat (shape : PatchShape) (config : Features.Config) :
    Format (Representation shape config) :=
  (progressFormat config).map (Representation.restore shape) (·.progress)

def lifecycleFormat (shape : PatchShape) (actions : Word.Count) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (discounts : List Discount) :
    Format (Lifecycle shape actions config criterion dimension discounts) :=
  ((representationFormat shape config).pair
    (ensembleFormat actions config criterion dimension discounts)).map
    (fun (representation, consumers) => ⟨representation, consumers⟩)
    (fun lifecycle => (lifecycle.representation, lifecycle.consumers))

def predictionCacheFormat : (discounts : List Discount) → Format (PredictionCache discounts)
  | [] => Format.unit.map (fun _ => .nil) (fun _ => ())
  | discount :: rest =>
    ((boundedFormat discount.predictionRange).pair (predictionCacheFormat rest)).map
      (fun (value, tail) => .cons value tail) (fun | .cons value tail => (value, tail))

def modelCacheFormat : Format ModelCache :=
  (binary32Format.pair (binary32Format.pair binary32Format)).map
    (fun (reward, continuation, duration) => ⟨reward, continuation, duration⟩)
    (fun cache => (cache.reward, cache.continuation, cache.duration))

def activationFormat (mode : Bool) : Format (OptionActivation mode) :=
  ((smallFormat (Acorn.FeatureConstants.optionMaxDuration + 1)).pair Format.bool).map
    (fun (age, previous) => OptionActivation.stored age previous)
    (fun activation => (activation.age, activation.previous))

def runFormat (count : Word.Count) : Format (ExploratoryRun count) :=
  ((Format.fin 8 count.word.toNat).pair (smallFormat explorationCap)).map
    (fun (action, remaining) => ⟨action, remaining⟩) (fun run => (run.action, run.remaining))

def committedPack {actions : Word.Count} {mode : Bool}
    (raw : ExploratoryRun actions × Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation mode)) : Option (CommittedRun actions mode) :=
  if pending : raw.2.isSome → 0 < raw.1.remaining.val then some ⟨raw.1, raw.2, pending⟩
  else none

def committedFormat (actions : Word.Count) (mode : Bool) : Format (CommittedRun actions mode) :=
  ((runFormat actions).pair
    ((smallFormat Acorn.FeatureConstants.skillCount).pair (activationFormat mode)).option).filterMap
    committedPack (fun committed => (committed.run, committed.origin))

def occupancyFormat {activation exploration : Type} (activationFormat : Format activation)
    (explorationFormat : Format exploration) : Format (Occupancy activation exploration) :=
  (Format.unit.sum (explorationFormat.sum
    ((smallFormat Acorn.FeatureConstants.skillCount).pair activationFormat))).map
    (fun raw => match raw with
      | .inl () => .idle
      | .inr (.inl run) => .exploring run
      | .inr (.inr (slot, state)) => .option slot state)
    (fun occupancy => match occupancy with
      | .idle => .inl ()
      | .exploring run => .inr (.inl run)
      | .option slot state => .inr (.inr (slot, state)))

def snapshotFormat (count : Word.Count) : Format (PolicySnapshot count) :=
  ((Format.vector binary32Format count.word.toNat).pair (boundedFormat SwiftTd.exploreRange)).map
    (fun (values, epsilon) => ⟨values, epsilon⟩) (fun snapshot => (snapshot.values, snapshot.epsilon))

def policyDecisionFormat (count : Word.Count) : Format (PolicyDecision count) :=
  ((snapshotFormat count).pair ((Format.fin 8 count.word.toNat).pair Format.bool)).map
    (fun (snapshot, action, explored) => PolicyDecision.stored snapshot action explored)
    (fun decision => (decision.snapshot, decision.action, decision.explored))

def sourceFormat : Format TemporalSource :=
  (Format.unit.sum (Format.unit.sum (Format.unit.sum
    (smallFormat Acorn.FeatureConstants.skillCount)))).map
    (fun raw => match raw with
      | .inl () => .primitive
      | .inr (.inl ()) => .explorationStart
      | .inr (.inr (.inl ())) => .explorationContinuation
      | .inr (.inr (.inr slot)) => .option slot)
    (fun source => match source with
      | .primitive => .inl ()
      | .explorationStart => .inr (.inl ())
      | .explorationContinuation => .inr (.inr (.inl ()))
      | .option slot => .inr (.inr (.inr slot)))

def endEventFormat : Format EndEvent :=
  ((smallFormat Acorn.FeatureConstants.skillCount).pair
    ((smallFormat (Acorn.FeatureConstants.optionMaxDuration + 1)).pair optionEndFormat)).map
    (fun (slot, age, reason) => ⟨slot, age, reason⟩) (fun event => (event.slot, event.age, event.reason))

def decisionFormat (actions : Word.Count) : Format (TemporalDecision actions) :=
  (sourceFormat.pair ((Format.fin 8 actions.word.toNat).pair
    ((Format.vector binary32Format actions.word.toNat).pair
    ((Format.vector binary32Format actions.word.toNat).pair
    (Format.bool.pair ((Format.vector binary32Format metaCount.word.toNat).pair
    ((policyDecisionFormat metaCount).option.pair
    ((smallFormat Acorn.FeatureConstants.skillCount).option.pair endEventFormat.option)))))))).map
    (fun (source, action, values, probabilities, explored, metaValues, metaDecision, started,
        ended) =>
      ⟨source, action, values, probabilities, explored, metaValues, metaDecision, started, ended⟩)
    (fun decision => (decision.source, decision.action, decision.values, decision.probabilities,
      decision.explored, decision.metaValues, decision.metaDecision, decision.started,
      decision.ended))

def recentFormat (dimension : Dimension) : Format (RecentFeatures dimension) :=
  ((Format.vector (activeSetFormat dimension) Acorn.FeatureConstants.optionMaxDuration).pair
    ((smallFormat Acorn.FeatureConstants.optionMaxDuration).pair
      (smallFormat Acorn.FeatureConstants.optionMaxDuration))).map
    (fun (frames, next, cursor) => ⟨frames, next, cursor⟩)
    (fun recent => (recent.frames, recent.next, recent.cursor))

def rngFormat : Format Rng.Xoshiro256 :=
  (u64Format.pair (u64Format.pair (u64Format.pair u64Format))).map
    (fun (s0, s1, s2, s3) => ⟨s0, s1, s2, s3⟩) (fun rng => (rng.s0, rng.s1, rng.s2, rng.s3))

def referencesFormat (dimension : Dimension) (discounts : List Discount)
    {activation exploration decision : Type} (occupancy : Format (Occupancy activation exploration))
    (decisions : Format decision) :
    Format (TemporalReferences dimension discounts activation exploration decision) :=
  ((predictionCacheFormat discounts).pair
    ((Format.vector binary32Format discounts.length).pair
    ((Format.vector modelCacheFormat Acorn.FeatureConstants.skillCount).pair
    (occupancy.pair (u64Format.pair
    ((Format.vector binary32Format Acorn.FeatureConstants.skillCount).pair
    (Format.byte.pair (binary32Format.pair (rngFormat.pair (Format.bool.pair
    (decisions.pair (recentFormat dimension)))))))))))).map
    (fun (demonPredictions, demonErrors, modelPredictions, phase, planningSteps, planningErrors,
        gapSteps, gapReward, rng, pendingAction, lastDecision, recent) =>
      ⟨demonPredictions, demonErrors, modelPredictions, phase, planningSteps, planningErrors,
        gapSteps, gapReward, rng, pendingAction, lastDecision, recent⟩)
    (fun references => (references.demonPredictions, references.demonErrors,
      references.modelPredictions, references.phase, references.planningSteps,
      references.planningErrors, references.gapSteps, references.gapReward, references.rng,
      references.pendingAction, references.lastDecision, references.recent))

def runtimeFormat (shape : PatchShape) (actions : Word.Count) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (discounts : List Discount)
    {activation exploration decision : Type} (occupancy : Format (Occupancy activation exploration))
    (decisions : Format decision) :
    Format (FeatureRuntime shape actions config criterion dimension discounts activation
      exploration decision) :=
  ((lifecycleFormat shape actions config criterion dimension discounts).pair
    (referencesFormat dimension discounts occupancy decisions)).map
    (fun (lifecycle, references) => ⟨lifecycle, references⟩)
    (fun runtime => (runtime.lifecycle, runtime.references))

def gapFormat : Format CreditGap :=
  (Format.byte.pair binary32Format).map (fun (steps, reward) => ⟨steps, reward⟩)
    (fun gap => (gap.steps, gap.reward))

def creditFormat : Format PrimitiveCredit :=
  (Format.unit.sum (gapFormat.sum Format.unit)).map
    (fun raw => match raw with
      | .inl () => .perStep
      | .inr (.inl gap) => .catchUp gap
      | .inr (.inr ()) => .noSpan)
    (fun credit => match credit with
      | .perStep => .inl ()
      | .catchUp gap => .inr (.inl gap)
      | .noSpan => .inr (.inr ()))

def averageFormat : Format AverageRewardTracker :=
  (boundedFormat rewardRange).map AverageRewardTracker.mk AverageRewardTracker.rate

def rateFormat : (policy : RatePolicy) → Format (RateState policy)
  | .declared => Format.unit.map (fun _ => .declared) (fun _ => ())
  | .perLearner => Format.unit.map (fun _ => .perLearner) (fun _ => ())
  | .shared => Format.unit.map (fun _ => .shared) (fun _ => ())
  | .annealed => (boundedFormat annealedRange).map RateState.annealed (fun | .annealed rate => rate)

abbrev SumWords := UInt64 × Binary64

def sumCodec : Codec SumWords := u64Codec.pair binary64Codec

def episodesCodec : Codec Lifetime.OptionEpisodes :=
  (u64Codec.pair (u64Codec.pair (vectorCodec u64Codec 3))).iso
    (fun (started, duration, reasons) => ⟨started, duration, reasons⟩)
    (fun record => (record.started, record.duration, record.reasons)) (by intro record; rfl)

abbrev GoalWords := UInt64 × UInt64 × UInt64

def goalCodec : Codec GoalWords := u64Codec.pair (u64Codec.pair u64Codec)

theorem sumCodec_canonical : sumCodec.Canonical :=
  Codec.pair_canonical u64Codec_canonical binary64Codec_canonical

theorem episodesCodec_canonical : episodesCodec.Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical u64Codec_canonical
      (Codec.pair_canonical u64Codec_canonical (vectorCodec_canonical u64Codec_canonical _)))
    fun _ => rfl

theorem goalCodec_canonical : goalCodec.Canonical :=
  Codec.pair_canonical u64Codec_canonical
    (Codec.pair_canonical u64Codec_canonical u64Codec_canonical)

def sumWords {quantity : Quantity} (record : SumCount quantity) : SumWords := (record.count, record.sum)

def goalWords (record : GoalTotals) : GoalWords := (record.attempts, record.successes, record.steps)

def admitGoal (words : GoalWords) : Option GoalTotals :=
  if valid : words.2.1.toNat ≤ words.1.toNat ∧ (words.1 = 0 → words.2.2 = 0) then
    some ⟨words.1, words.2.1, words.2.2, valid.1, valid.2⟩
  else none

def admitSum (quantity : Quantity) (words : SumWords) : Option (SumCount quantity) :=
  SumCount.admit quantity words.1 words.2

instance (record : OptionEpisodes) (active : Bool) : Decidable (record.Valid active) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount)
    (active : Option (Fin Acorn.FeatureConstants.skillCount)) : Decidable (OptionsValid options active) :=
  inferInstanceAs (Decidable (∀ _slot : Fin Acorn.FeatureConstants.skillCount, _))

def sumFormat (quantity : Quantity) : Format (SumCount quantity) :=
  sumCodec.format.filterMap (admitSum quantity) sumWords

def goalFormat : Format GoalTotals := goalCodec.format.filterMap admitGoal goalWords

def episodesFormat : Format OptionEpisodes := episodesCodec.format

def demonDurableFormat (discount : Discount) : Format (DemonDurable discount) :=
  ((sumFormat (.squaredError discount)).pair ((boundedFormat discount.predictionRange).pair
    (boundedFormat (errorRange discount).range))).map
    (fun (squaredError, lastReturn, lastError) => ⟨squaredError, lastReturn, lastError⟩)
    (fun record => (record.squaredError, record.lastReturn, record.lastError))

def pendingFormat (discount : Discount) : Format (PendingPrediction discount) :=
  ((smallFormat (Acorn.FeatureConstants.maxSettlement + 1)).pair
    ((boundedFormat discount.predictionRange).pair (binary32Format.pair
      (binary32Format.pair u64Format)))).map
    (fun (age, prediction, returnSum, discountPower, startedAt) =>
      ⟨age, prediction, returnSum, discountPower, startedAt⟩)
    (fun pending => (pending.age, pending.prediction, pending.returnSum, pending.discountPower,
      pending.startedAt))

def totalFormat (envelope : Nat) : Format (Agreement.Total envelope) :=
  ((Format.fin 8 (Agreement.countLimit + 1)).pair Format.natural).filterMap
    (fun (count, sum) => if bounded : sum ≤ count.val * envelope ^ 2 then
      some ⟨count, sum, bounded⟩ else none)
    (fun total => (total.count, total.sum))

def ratioFormat : Format Agreement.Ratio :=
  (Format.natural.pair Format.natural).filterMap
    (fun (numerator, denominator) => Agreement.Ratio.admit numerator denominator)
    (fun ratio => (ratio.numerator, ratio.denominator))

def precisionFormat : Format Agreement.Precision :=
  (ratioFormat.pair ratioFormat).map (fun (tail, rounding) => ⟨tail, rounding⟩)
    (fun precision => (precision.tail, precision.rounding))

def clockRangeFormat : Format Agreement.ClockRange :=
  (u64Format.pair u64Format).filterMap
    (fun (first, last) => if ordered : first.toNat ≤ last.toNat then some ⟨first, last, ordered⟩
      else none)
    (fun range => (range.first, range.last))

def channelFormat (discount : Discount) : Format (Agreement.Channel discount) :=
  ((totalFormat (Agreement.envelopeUnits discount)).pair (faultFormat.option.pair
    (clockRangeFormat.option.pair (clockRangeFormat.option.pair
    ((Format.fin 8 (Agreement.countLimit + 1)).pair precisionFormat.option))))).map
    (fun (total, fault, starts, settlements, censored, precision) =>
      ⟨total, fault, starts, settlements, censored, precision⟩)
    (fun channel => (channel.total, channel.fault, channel.starts, channel.settlements,
      channel.censored, channel.precision))

def demonStatsFormat (discount : Discount) : Format (DemonStats discount) :=
  ((demonDurableFormat discount).pair
    ((Format.vector (pendingFormat discount).option Acorn.FeatureConstants.pendingSamples).pair
      (channelFormat discount))).map
    (fun (durable, pending, agreement) =>
      ⟨durable, pending, agreement, ⟨settlementHorizon discount, rfl⟩⟩)
    (fun stats => (stats.durable, stats.pending, stats.agreement))

def demonRecordsFormat : (discounts : List Discount) → Format (DemonRecords discounts)
  | [] => Format.unit.map (fun _ => .nil) (fun _ => ())
  | discount :: rest =>
    ((demonStatsFormat discount).pair (demonRecordsFormat rest)).map
      (fun (head, tail) => .cons head tail) (fun | .cons head tail => (head, tail))

def agreementPointFormat : Format AgreementPoint :=
  (u64Format.pair ratioFormat).map (fun (clock, ratio) => ⟨clock, ratio⟩)
    (fun point => (point.clock, point.ratio))

def statsFormat (discounts : List Discount) : Format (Stats discounts) :=
  ((sumFormat .reward).pair ((Format.vector (sumFormat .reward) 4).pair
    ((Format.vector (sumFormat .reward) Acorn.FeatureConstants.historyBins).pair
    ((demonRecordsFormat discounts).pair
    ((Format.vector (sumFormat (.squaredError .g99)) Acorn.FeatureConstants.historyBins).pair
    ((Format.vector episodesFormat Acorn.FeatureConstants.skillCount).pair
    ((Format.vector goalFormat 4).pair
    ((Format.vector (Format.vector goalFormat Acorn.FeatureConstants.cycleBins) 4).pair
    (u64Format.option.pair
    ((Format.vector agreementPointFormat.option Acorn.FeatureConstants.historyBins).pair
    (u64Format.option.pair Format.bool))))))))))).map
    (fun (reward, rewardByFamily, rewardHistory, demons, errorHistory, options, goals,
        goalCycles, agreementStarted, agreementHistory, agreementLastClock, agreementStopped) =>
      ⟨reward, rewardByFamily, rewardHistory, demons, errorHistory, options, goals, goalCycles,
        agreementStarted, agreementHistory, agreementLastClock, agreementStopped⟩)
    (fun stats => (stats.reward, stats.rewardByFamily, stats.rewardHistory, stats.demons,
      stats.errorHistory, stats.options, stats.goals, stats.goalCycles, stats.agreementStarted,
      stats.agreementHistory, stats.agreementLastClock, stats.agreementStopped))

instance instDecidableInterestAligned {config : Features.Config} (interest : Interest config) :
    Decidable interest.Aligned :=
  match interest with
  | .learned _ => isTrue trivial
  | .declared origin _ => inferInstanceAs (Decidable (origin = .spatialPotentials))

instance instDecidableEnsembleAligned {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts) :
    Decidable ensemble.Aligned :=
  inferInstanceAs (Decidable (∀ _slot : Fin Acorn.FeatureConstants.skillCount, _))

instance instDecidableEnsembleDistinct {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts) :
    Decidable ensemble.Distinct :=
  decidable_of_iff _ (Assignment.distinct_iff (ensemble.skills.map (·.interest.held)))

instance instDecidableEpisodes {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}
    (control : TemporalControl interface profile config criterion dimension) :
    Decidable control.Episodes :=
  inferInstanceAs (Decidable (_ ∧ _))

def controlPack {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}
    (raw : FeatureRuntime interface.symbols interface.actions config criterion dimension
        interface.layout (OptionActivation (profile.mode != .frozen))
        (CommittedRun interface.actions (profile.mode != .frozen))
        (Option (TemporalDecision interface.actions)) ×
      PrimitiveCredit × AverageRewardTracker × RateState profile.rate ×
      Lifetime.Stats interface.layout) :
    Option (TemporalControl interface profile config criterion dimension) :=
  if creditMatches : creditKind raw.2.1 = profile.credit then
    some ⟨raw.1, raw.2.1, creditMatches, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2⟩
  else none

def controlFormat (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) :
    Format (TemporalControl interface profile config criterion dimension) :=
  ((runtimeFormat interface.symbols interface.actions config criterion dimension interface.layout
      (occupancyFormat (activationFormat (profile.mode != .frozen))
        (committedFormat interface.actions (profile.mode != .frozen)))
      (decisionFormat interface.actions).option).pair
    (creditFormat.pair (averageFormat.pair ((rateFormat profile.rate).pair
      (statsFormat interface.layout))))).filterMap controlPack
    (fun control => (control.runtime, control.credit, control.average, control.rate,
      control.lifetime))

def imagePack {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}
    (control : TemporalControl interface profile config criterion dimension) :
    Option (AgentImage interface profile config criterion dimension) :=
  if aligned : control.Aligned then
    if episodes : control.Episodes then some ⟨control, aligned, episodes⟩ else none
  else none

def agentImageFormat (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) :
    Format (AgentImage interface profile config criterion dimension) :=
  (controlFormat interface profile config criterion dimension).filterMap imagePack (·.control)

def imageFormat (construction : AgentConstruction) : Format construction.Image :=
  (agentImageFormat Grid.interface construction.profile construction.config
    construction.criterion construction.dimension).map AgentConstruction.Image.mk (·.image)

end Acorn.Checkpoint
