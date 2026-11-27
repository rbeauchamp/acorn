import Acorn.Host.Checkpoint.Size
import AcornVerif.CurrentImage

namespace AcornVerif.CurrentCheckpointSize
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime
open AcornVerif.CurrentLearner AcornVerif.CurrentFeatureConsumers

variable {α β : Type}

def Fits (format : Format α) (value : α) (bytes : Nat) : Prop :=
  (format.encode value).length ≤ bytes

def Within (format : Format α) (bytes : Nat) : Prop := ∀ value, Fits format value bytes

theorem fits_mono {format : Format α} {value : α} {small large : Nat}
    (fits : Fits format value small) (larger : small ≤ large) : Fits format value large :=
  Nat.le_trans fits larger

theorem within_mono {format : Format α} {small large : Nat} (within : Within format small)
    (larger : small ≤ large) : Within format large :=
  fun value => fits_mono (within value) larger

theorem codec_within {codec : Codec α} {bytes : Nat}
    (fixed : ∀ value, (codec.encode value).length = bytes) : Within codec.format bytes :=
  fun value => Nat.le_of_eq (fixed value)

theorem pair_fits {left : Format α} {right : Format β} {value : α × β} {first second : Nat}
    (head : Fits left value.1 first) (tail : Fits right value.2 second) :
    Fits (left.pair right) value (first + second) := by
  change (left.encode value.1 ++ right.encode value.2).length ≤ first + second
  rw [List.length_append]
  exact Nat.add_le_add head tail

theorem pair_within {left : Format α} {right : Format β} {first second : Nat}
    (head : Within left first) (tail : Within right second) :
    Within (left.pair right) (first + second) :=
  fun value => pair_fits (head value.1) (tail value.2)

theorem filterMap_fits {format : Format α} {pack : α → Option β} {unpack : β → α} {value : β}
    {bytes : Nat} (fits : Fits format (unpack value) bytes) :
    Fits (format.filterMap pack unpack) value bytes :=
  fits

theorem filterMap_within {format : Format α} {pack : α → Option β} {unpack : β → α}
    {bytes : Nat} (within : Within format bytes) : Within (format.filterMap pack unpack) bytes :=
  fun value => within (unpack value)

theorem map_fits {format : Format α} {pack : α → β} {unpack : β → α} {value : β} {bytes : Nat}
    (fits : Fits format (unpack value) bytes) : Fits (format.map pack unpack) value bytes :=
  fits

theorem map_within {format : Format α} {pack : α → β} {unpack : β → α} {bytes : Nat}
    (within : Within format bytes) : Within (format.map pack unpack) bytes :=
  fun value => within (unpack value)

theorem flatMap_length {format : Format α} {bytes : Nat} :
    ∀ values : List α, (∀ value ∈ values, Fits format value bytes) →
      (values.flatMap format.encode).length ≤ values.length * bytes
  | [], _ => by simp
  | value :: rest, fits => by
    have head : (format.encode value).length ≤ bytes := fits value List.mem_cons_self
    have tail := flatMap_length rest fun other member => fits other (List.mem_cons_of_mem _ member)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem vector_fits {format : Format α} {count bytes : Nat} {values : Vector α count}
    (fits : ∀ value ∈ values.toList, Fits format value bytes) :
    Fits (format.vector count) values (count * bytes) := by
  have total := flatMap_length values.toList fits
  rw [Vector.length_toList] at total
  exact total

theorem vector_within {format : Format α} {bytes : Nat} (within : Within format bytes)
    (count : Nat) : Within (format.vector count) (count * bytes) :=
  fun _ => vector_fits fun value _ => within value

theorem option_none_fits {format : Format α} : Fits format.option none 1 :=
  Nat.le_refl 1

theorem option_some_fits {format : Format α} {inner : α} {bytes : Nat}
    (fits : Fits format inner bytes) : Fits format.option (some inner) (bytes + 1) := by
  change (1 :: format.encode inner).length ≤ bytes + 1
  rw [List.length_cons]
  exact Nat.succ_le_succ fits

theorem option_within {format : Format α} {bytes : Nat} (within : Within format bytes) :
    Within format.option (bytes + 1) := by
  intro value
  cases value with
  | none => exact fits_mono option_none_fits (Nat.le_add_left 1 bytes)
  | some inner => exact option_some_fits (within inner)

theorem sum_within {left : Format α} {right : Format β} {bytes : Nat} (first : Within left bytes)
    (second : Within right bytes) : Within (left.sum right) (bytes + 1) := by
  intro value
  cases value with
  | inl value =>
    change (0 :: left.encode value).length ≤ bytes + 1
    rw [List.length_cons]
    exact Nat.succ_le_succ (first value)
  | inr value =>
    change (1 :: right.encode value).length ≤ bytes + 1
    rw [List.length_cons]
    exact Nat.succ_le_succ (second value)

theorem list_fits {format : Format α} {bound bytes : Nat} {values : List α}
    (fits : ∀ value ∈ values, Fits format value bytes) :
    Fits (format.list bound) values (8 + values.length * bytes) := by
  change (u64Codec.encode values.length.toUInt64 ++ values.flatMap format.encode).length ≤ _
  rw [List.length_append, u64_size]
  exact Nat.add_le_add_left (flatMap_length values fits) 8

theorem unit_within : Within Format.unit 0 := fun _ => Nat.le_refl 0

theorem byte_within : Within Format.byte 1 := fun _ => Nat.le_refl 1

theorem bool_within : Within Format.bool 1 := filterMap_within byte_within

theorem enum_within (values : List α) (position : α → Nat) :
    Within (Format.enum values position) 1 :=
  filterMap_within byte_within

theorem fin_within (width count : Nat) : Within (Format.fin width count) width :=
  filterMap_within (codec_within fun word => encodeNat_length width word.val)

theorem binary32_within : Within binary32Format 4 := codec_within binary32_size

theorem u64_within : Within u64Format 8 := codec_within u64_size

theorem bounded_within (range : Interval32) : Within (boundedFormat range) 4 :=
  filterMap_within binary32_within

theorem weight_within (rule : ValueRule) : Within (weightFormat rule) 4 :=
  map_within (bounded_within _)

theorem activeSetFormat_within (dimension : Dimension) :
    Within (activeSetFormat dimension) (8 + 4 * dimension.capacity) := by
  intro features
  have short := active_cardinality features
  refine fits_mono (filterMap_fits (list_fits fun index _ => fin_within 4 _ index)) ?_
  omega

theorem managedFormat_within (config : Acorn.Config) (dimension : Dimension) :
    Within (managedFormat config dimension) (managedBytes dimension.capacity) := by
  intro learner
  have short : (managedWords learner).2.2.1.length ≤ dimension.capacity := by
    have counted := eligible_cardinality learner.state (managed_schedule learner).2.1
    simpa [managedWords, transientEntries, NumericState.eligibleCount] using counted
  refine fits_mono (filterMap_fits (pair_fits (vector_within (weight_within _) _ _)
    (pair_fits (vector_within (bounded_within _) _ _) (pair_fits
      (list_fits fun entry _ =>
        pair_within (fin_within 4 _) (vector_within binary32_within 9) entry)
      (pair_within binary32_within (pair_within binary32_within bool_within) _))))) ?_
  unfold managedBytes
  omega

theorem controllerFormat_within (config : Acorn.Config) (dimension : Dimension) (actions : Nat) :
    Within (controllerFormat config dimension actions)
      (controllerBytes dimension.capacity actions) :=
  within_mono (map_within (pair_within (vector_within (managedFormat_within config dimension) _)
    (pair_within binary32_within (pair_within binary32_within bool_within))))
    (by unfold controllerBytes; omega)

theorem transitionFormat_within (dimension : Dimension) (criterion : Criterion) :
    Within (transitionFormat dimension criterion) (transitionBytes (rankWidth dimension)) :=
  within_mono (map_within (pair_within
    (filterMap_within (vector_within (option_within (fin_within 4 _)) _))
    (pair_within (vector_within (managedFormat_within _ _) _)
      (vector_within (managedFormat_within _ _) _))))
    (by
      change _ ≤ transitionBytes (rankDimension dimension).capacity
      unfold transitionBytes
      omega)

theorem modelFormat_within (dimension : Dimension) :
    ∀ criterion : Criterion, Within (modelFormat dimension criterion) (modelBytes dimension)
  | .discounted =>
    within_mono (map_within (pair_within (managedFormat_within _ _)
      (pair_within (managedFormat_within _ _) (transitionFormat_within _ _))))
      (by unfold modelBytes; omega)
  | .differential =>
    within_mono (map_within (pair_within (managedFormat_within _ _)
      (pair_within (managedFormat_within _ _) (pair_within (managedFormat_within _ _)
        (transitionFormat_within _ _))))) (by unfold modelBytes; omega)

theorem demonBankFormat_within (dimension : Dimension) :
    ∀ discounts : List Discount, Within (demonBankFormat dimension discounts)
      (discounts.length * managedBytes dimension.capacity)
  | [] => within_mono (map_within unit_within) (Nat.zero_le _)
  | _ :: rest =>
    within_mono (map_within (pair_within (managedFormat_within _ _)
      (demonBankFormat_within dimension rest)))
      (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)

theorem assignmentFormat_within (config : Features.Config) (dimension : Dimension) :
    Within (assignmentFormat config dimension) 16 :=
  filterMap_within (codec_within fun assignment => by
    simp [assignmentCodec, Codec.iso, Codec.pair, u32_size])

theorem interestFormat_within (config : Features.Config) (dimension : Dimension) :
    Within (interestFormat config dimension) 17 :=
  map_within (sum_within (assignmentFormat_within config dimension)
    (within_mono (pair_within (enum_within _ _) (fin_within 4 _)) (by omega)))

theorem followingFormat_within : Within followingFormat 6 :=
  within_mono (map_within (pair_within (fin_within 4 _) (pair_within bool_within bool_within)))
    (by omega)

theorem grid_actions :
    Grid.interface.actions.word.toNat = Acorn.FeatureConstants.primitiveCount := by
  decide

theorem skillFormat_within (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) :
    Within (skillFormat Grid.interface.actions config criterion dimension discounts)
      (skillBytes dimension) :=
  within_mono (map_within (pair_within (interestFormat_within config dimension)
    (pair_within (controllerFormat_within _ _ _)
      (pair_within (modelFormat_within dimension criterion)
      (option_within followingFormat_within)))))
    (by unfold skillBytes; rw [grid_actions]; omega)

theorem ensembleFormat_within (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) :
    Within (ensembleFormat Grid.interface.actions config criterion dimension discounts)
      (ensembleBytes dimension discounts.length) :=
  within_mono (map_within (pair_within (controllerFormat_within _ _ _)
    (pair_within (controllerFormat_within _ _ _)
      (pair_within (vector_within (skillFormat_within config criterion dimension discounts) _)
        (demonBankFormat_within dimension discounts)))))
    (by unfold ensembleBytes; rw [grid_actions]; omega)

theorem last_size (last : LastWords) : (lastCodec.encode last).length = 14 := by
  simp [lastCodec, Codec.pair, u32_size, u64_size, u16_size]

theorem unitState_size (unit : UnitWords) : (unitStateCodec.encode unit).length = 20 := by
  simp [unitStateCodec, Codec.pair, u64_size, binary32_size]

theorem unitList_size (units : UnitList) :
    (unitListCodec.encode units).length = 4 + units.val.length * 20 := by
  simp [unitListCodec, u32_size, list_size unitStateCodec 20 unitState_size]

theorem tester_size (tester : TesterWords) :
    (testerCodec.encode tester).length = 34 + (4 + tester.units.val.length * 20) := by
  simp [testerCodec, Codec.iso, Codec.pair, u64_size, u32_size, last_size, unitList_size]
  omega

theorem representationFormat_within (shape : PatchShape) (config : Features.Config) :
    Within (representationFormat shape config) (46 + 20 * config.units.count) := by
  intro representation
  have units : (testerWords representation.progress).units.val.length = config.units.count := by
    simp [testerWords, Progress.words]
  change (u64Codec.encode representation.progress.clock ++
    testerCodec.encode (testerWords representation.progress)).length ≤ _
  rw [List.length_append, u64_size, tester_size, units]
  omega

theorem predictionCacheFormat_within :
    ∀ discounts : List Discount, Within (predictionCacheFormat discounts) (discounts.length * 4)
  | [] => within_mono (map_within unit_within) (Nat.zero_le _)
  | _ :: rest =>
    within_mono (map_within (pair_within (bounded_within _) (predictionCacheFormat_within rest)))
      (by simp only [List.length_cons]; omega)

theorem modelCacheFormat_within : Within modelCacheFormat 12 :=
  within_mono (map_within (pair_within binary32_within
    (pair_within binary32_within binary32_within))) (by omega)

theorem activationFormat_within (mode : Bool) : Within (activationFormat mode) 5 :=
  within_mono (map_within (pair_within (fin_within 4 _) bool_within)) (by omega)

theorem committedFormat_within (actions : Word.Count) (mode : Bool) :
    Within (committedFormat actions mode) 22 :=
  within_mono (filterMap_within (pair_within (map_within (pair_within (fin_within 8 _)
    (fin_within 4 _))) (option_within (pair_within (fin_within 4 _)
      (activationFormat_within mode))))) (by omega)

theorem occupancyFormat_within (actions : Word.Count) (mode : Bool) :
    Within (occupancyFormat (activationFormat mode) (committedFormat actions mode)) 24 :=
  within_mono (map_within (sum_within (within_mono unit_within (Nat.zero_le 23))
    (within_mono (sum_within (committedFormat_within actions mode)
      (within_mono (pair_within (fin_within 4 _) (activationFormat_within mode)) (by omega)))
      (by omega)))) (by omega)

theorem sourceFormat_within : Within sourceFormat 7 :=
  within_mono (map_within (sum_within (within_mono unit_within (Nat.zero_le 6))
    (within_mono (sum_within (within_mono unit_within (Nat.zero_le 5))
      (within_mono (sum_within (within_mono unit_within (Nat.zero_le 4)) (fin_within 4 _))
        (by omega))) (by omega)))) (by omega)

theorem endEventFormat_within : Within endEventFormat 9 :=
  within_mono (map_within (pair_within (fin_within 4 _)
    (pair_within (fin_within 4 _) (enum_within _ _)))) (by omega)

theorem policyDecisionFormat_within (count : Word.Count) :
    Within (policyDecisionFormat count) (count.word.toNat * 4 + 4 + 9) :=
  within_mono (map_within (pair_within (map_within (pair_within (vector_within binary32_within _)
    (bounded_within _))) (pair_within (fin_within 8 _) bool_within))) (by omega)

theorem decisionFormat_within (actions : Word.Count) :
    Within (decisionFormat actions) (45 + 8 * actions.word.toNat + 8 * metaCount.word.toNat) :=
  within_mono (map_within (pair_within sourceFormat_within (pair_within (fin_within 8 _)
    (pair_within (vector_within binary32_within _) (pair_within (vector_within binary32_within _)
    (pair_within bool_within (pair_within (vector_within binary32_within _)
    (pair_within (option_within (policyDecisionFormat_within _))
    (pair_within (option_within (fin_within 4 _))
      (option_within endEventFormat_within))))))))))
    (by omega)

theorem recentFormat_within (dimension : Dimension) :
    Within (recentFormat dimension)
      (Acorn.FeatureConstants.optionMaxDuration * (8 + 4 * dimension.capacity) + 8) :=
  within_mono (map_within (pair_within (vector_within (activeSetFormat_within dimension) _)
    (pair_within (fin_within 4 _) (fin_within 4 _)))) (by omega)

theorem rngFormat_within : Within rngFormat 32 :=
  within_mono (map_within (pair_within u64_within (pair_within u64_within
    (pair_within u64_within u64_within)))) (by omega)

theorem referencesFormat_within (dimension : Dimension) (discounts : List Discount)
    {activation exploration decision : Type} {occupancy : Format (Occupancy activation exploration)}
    {decisions : Format decision} (occupancyWithin : Within occupancy 24)
    (decisionsWithin : Within decisions 150) :
    Within (referencesFormat dimension discounts occupancy decisions)
      (referencesBytes dimension.capacity discounts.length) :=
  within_mono (map_within (pair_within (predictionCacheFormat_within discounts)
    (pair_within (vector_within binary32_within _)
    (pair_within (vector_within modelCacheFormat_within _)
    (pair_within occupancyWithin (pair_within u64_within
    (pair_within (vector_within binary32_within _)
    (pair_within byte_within (pair_within binary32_within (pair_within rngFormat_within
    (pair_within bool_within (pair_within decisionsWithin
      (recentFormat_within dimension)))))))))))))
    (by unfold referencesBytes Acorn.FeatureConstants.skillCount; omega)

theorem creditFormat_within : Within creditFormat 7 :=
  within_mono (map_within (sum_within (within_mono unit_within (Nat.zero_le 6))
    (within_mono (sum_within (map_within (pair_within byte_within binary32_within))
      (within_mono unit_within (Nat.zero_le _))) (by omega)))) (by omega)

theorem averageFormat_within : Within averageFormat 4 := map_within (bounded_within _)

theorem rateFormat_within : ∀ policy : RatePolicy, Within (rateFormat policy) 4
  | .declared => within_mono (map_within unit_within) (Nat.zero_le _)
  | .perLearner => within_mono (map_within unit_within) (Nat.zero_le _)
  | .shared => within_mono (map_within unit_within) (Nat.zero_le _)
  | .annealed => map_within (bounded_within _)

def Allowed (values : List Nat) : Prop :=
  ∀ value ∈ values, Fits Format.natural value naturalAllowance

theorem allowed_append {first second : List Nat} (allowed : Allowed (first ++ second)) :
    Allowed first ∧ Allowed second :=
  ⟨fun value member => allowed value (List.mem_append_left _ member),
    fun value member => allowed value (List.mem_append_right _ member)⟩

def ratioNaturals (ratio : Agreement.Ratio) : List Nat := [ratio.numerator, ratio.denominator]

def channelNaturals {discount : Discount} (channel : Agreement.Channel discount) : List Nat :=
  channel.total.sum :: channel.precision.elim [] fun precision =>
    ratioNaturals precision.tail ++ ratioNaturals precision.rounding

def recordsNaturals : {discounts : List Discount} → DemonRecords discounts → List Nat
  | _, .nil => []
  | _, .cons head tail => channelNaturals head.agreement ++ recordsNaturals tail

def statsNaturals {discounts : List Discount} (stats : Stats discounts) : List Nat :=
  recordsNaturals stats.demons ++ stats.agreementHistory.toList.flatMap fun point =>
    point.elim [] fun point => ratioNaturals point.ratio

theorem sumFormat_within (quantity : Quantity) : Within (sumFormat quantity) 16 :=
  filterMap_within (codec_within fun words => by
    simp [sumCodec, Codec.pair, u64_size, binary64_size])

theorem goalFormat_within : Within goalFormat 24 :=
  filterMap_within (codec_within fun words => by simp [goalCodec, Codec.pair, u64_size])

theorem episodesFormat_within : Within episodesFormat 40 :=
  codec_within fun record => by
    simp [episodesCodec, Codec.iso, Codec.pair, u64_size, vector_size u64Codec 8 u64_size]

theorem demonDurableFormat_within (discount : Discount) :
    Within (demonDurableFormat discount) 24 :=
  within_mono (map_within (pair_within (sumFormat_within _)
    (pair_within (bounded_within _) (bounded_within _)))) (by omega)

theorem pendingFormat_within (discount : Discount) : Within (pendingFormat discount) 24 :=
  within_mono (map_within (pair_within (fin_within 4 _) (pair_within (bounded_within _)
    (pair_within binary32_within (pair_within binary32_within u64_within))))) (by omega)

theorem clockRangeFormat_within : Within clockRangeFormat 16 :=
  within_mono (filterMap_within (pair_within u64_within u64_within)) (by omega)

theorem ratioFormat_fits (ratio : Agreement.Ratio) (allowed : Allowed (ratioNaturals ratio)) :
    Fits ratioFormat ratio (2 * naturalAllowance) :=
  fits_mono (filterMap_fits (pair_fits (allowed _ List.mem_cons_self)
    (allowed _ (List.mem_cons_of_mem _ List.mem_cons_self)))) (by omega)

theorem precisionFormat_fits {precision : Option Agreement.Precision}
    (allowed : Allowed (precision.elim [] fun precision =>
      ratioNaturals precision.tail ++ ratioNaturals precision.rounding)) :
    Fits precisionFormat.option precision (4 * naturalAllowance + 1) := by
  cases precision with
  | none => exact fits_mono option_none_fits (by omega)
  | some precision =>
    obtain ⟨tail, rounding⟩ := allowed_append allowed
    exact fits_mono (option_some_fits (map_fits (pair_fits (ratioFormat_fits _ tail)
      (ratioFormat_fits _ rounding)))) (by omega)

theorem channelFormat_fits {discount : Discount} (channel : Agreement.Channel discount)
    (allowed : Allowed (channelNaturals channel)) :
    Fits (channelFormat discount) channel (53 + 5 * naturalAllowance) := by
  have sum : Fits Format.natural channel.total.sum naturalAllowance :=
    allowed _ List.mem_cons_self
  have precision := precisionFormat_fits (precision := channel.precision)
    fun value member => allowed value (List.mem_cons_of_mem _ member)
  exact fits_mono (map_fits (pair_fits (filterMap_fits (pair_fits (fin_within 8 _ _) sum))
    (pair_fits (option_within (enum_within _ _) _)
      (pair_fits (option_within clockRangeFormat_within _)
    (pair_fits (option_within clockRangeFormat_within _) (pair_fits (fin_within 8 _ _)
      precision)))))) (by omega)

theorem demonStatsFormat_fits {discount : Discount} (stats : DemonStats discount)
    (allowed : Allowed (channelNaturals stats.agreement)) :
    Fits (demonStatsFormat discount) stats demonStatsBytes :=
  fits_mono (map_fits (pair_fits (demonDurableFormat_within _ _) (pair_fits
    (vector_within (option_within (pendingFormat_within _)) _ _) (channelFormat_fits _ allowed))))
    (by unfold demonStatsBytes Acorn.FeatureConstants.pendingSamples; omega)

theorem demonRecordsFormat_fits : ∀ {discounts : List Discount} (records : DemonRecords discounts),
    Allowed (recordsNaturals records) →
      Fits (demonRecordsFormat discounts) records (discounts.length * demonStatsBytes)
  | _, .nil, _ => fits_mono (map_fits (unit_within _)) (Nat.zero_le _)
  | _, .cons head tail, allowed => by
    obtain ⟨first, rest⟩ := allowed_append allowed
    exact fits_mono (map_fits (pair_fits (demonStatsFormat_fits head first)
      (demonRecordsFormat_fits tail rest)))
      (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)

theorem pointFormat_fits {point : Option AgreementPoint}
    (allowed : Allowed (point.elim [] fun point => ratioNaturals point.ratio)) :
    Fits agreementPointFormat.option point (8 + 2 * naturalAllowance + 1) := by
  cases point with
  | none => exact fits_mono option_none_fits (by omega)
  | some point =>
    exact option_some_fits (map_fits (pair_fits (u64_within _) (ratioFormat_fits _ allowed)))

theorem statsFormat_fits {discounts : List Discount} (stats : Stats discounts)
    (allowed : Allowed (statsNaturals stats)) :
    Fits (statsFormat discounts) stats (statsBytes discounts.length) := by
  obtain ⟨records, points⟩ := allowed_append allowed
  have history : Fits (Format.vector agreementPointFormat.option
      Acorn.FeatureConstants.historyBins) stats.agreementHistory
      (Acorn.FeatureConstants.historyBins * (8 + 2 * naturalAllowance + 1)) :=
    vector_fits fun point member => pointFormat_fits fun value inside =>
      points value (List.mem_flatMap.mpr ⟨point, member, inside⟩)
  exact fits_mono (map_fits (pair_fits (sumFormat_within _ _) (pair_fits
    (vector_within (sumFormat_within _) _ _) (pair_fits (vector_within (sumFormat_within _) _ _)
    (pair_fits (demonRecordsFormat_fits _ records)
    (pair_fits (vector_within (sumFormat_within _) _ _)
    (pair_fits (vector_within episodesFormat_within _ _)
    (pair_fits (vector_within goalFormat_within _ _)
    (pair_fits (vector_within (vector_within goalFormat_within _) _ _)
    (pair_fits (option_within u64_within _) (pair_fits history
    (pair_fits (option_within u64_within _) (bool_within _)))))))))))))
    (by unfold statsBytes Acorn.FeatureConstants.historyBins; omega)

theorem controlFormat_fits {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}
    (control : TemporalControl Grid.interface profile config criterion dimension)
    (allowed : Allowed (statsNaturals control.lifetime)) :
    Fits (controlFormat Grid.interface profile config criterion dimension) control
      (46 + 20 * config.units.count + ensembleBytes dimension Grid.interface.layout.length +
        referencesBytes dimension.capacity Grid.interface.layout.length + 7 + 4 + 4 +
        statsBytes Grid.interface.layout.length) := by
  have decisions : Within (decisionFormat Grid.interface.actions).option 150 :=
    within_mono (option_within (decisionFormat_within _)) (by decide)
  exact fits_mono (filterMap_fits (pair_fits
    (map_within (pair_within (map_within (pair_within (representationFormat_within _ _)
      (ensembleFormat_within _ _ _ _))) (referencesFormat_within _ _
        (occupancyFormat_within _ _) decisions)) _)
    (pair_fits (creditFormat_within _) (pair_fits (averageFormat_within _)
      (pair_fits (rateFormat_within _ _) (statsFormat_fits _ allowed)))))) (by omega)

theorem imageFormat_fits (construction : AgentConstruction) (image : construction.Image)
    (allowed : Allowed (statsNaturals image.image.control.lifetime)) :
    Fits (imageFormat construction) image (imageBytes construction) :=
  map_fits (filterMap_fits (controlFormat_fits image.image.control allowed))

theorem snapshot_size_bound (construction : AgentConstruction) (state : construction.State)
    (allowed : ∀ value ∈ statsNaturals state.agent.control.lifetime,
      (Format.natural.encode value).length ≤ naturalAllowance) :
    (encode (snapshot construction state)).length ≤ maximumBytes construction := by
  rw [encoded_size]
  exact Nat.add_le_add_left (imageFormat_fits construction (stateImage construction state)
    allowed) 72

end AcornVerif.CurrentCheckpointSize
