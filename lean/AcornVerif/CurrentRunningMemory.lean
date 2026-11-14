/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentCheckpoint
import AcornVerif.CurrentCheckpointSize

/-!
# Every state a host runs has a bounded image

`AcornVerif.CurrentCheckpointSize.snapshot_size_bound` bounds a saved image for every state whose
evaluator naturals each encode within `naturalAllowance` bytes. This module discharges that
hypothesis for every state a host runs, and turns the bound on the image into a bound on how many
such states there are. It is the mission rbeauchamp/acorn#195, which serves obligation 6 of
`docs/mission-contract.md`.

`Running` defines the states a host runs: the cold state, a state resumed from bytes, and every
state one host operation after such a state (a whole step of the construction's order, the two
observation writes, the censoring at process exit, the start of an evaluator session). It has one
constructor for each constructor of `AgentConstruction.Reached`, with `loaded` replaced by
`resumed`. Under a profile that restores, every agent is reached
(`AcornVerif.CurrentCheckpoint.loader_reaches`), and the type of a ratio bounds neither of its
naturals, so a reached agent can hold a natural longer than its allowance (argued, not proved
here). A state that `Acorn.Checkpoint.resume` returns has a new evaluator session, and so holds no
evaluator natural but the zero sums of its empty channels.

The naturals stay below bounds that do not depend on the number of steps:

- the sum of a channel's total is at most its count times the square of the channel's scale, by
  its type, and a scale is below `2 ^ 278` (`magnitudeUnits_lt`), so a sum is below `2 ^ 620`
  (`sum_lt`);
- a channel's precision is written by a settlement only, as a derived precision or its merge with
  the one held, and a merge returns one of its two arguments for each ratio; a derived precision
  has denominators below `2 ^ 427` (`precision_bounded`, `settle_bounded`);
- an agreement point's ratio is the ratio of the equal-question mean over the channels, whose
  denominator is at most the number of channels times `2 ^ 620` to the power of that number,
  whatever the records hold (`agreementRatio_bounded`).

`StatsBounded` is the invariant these give: every precision and every agreement point bounded. The
cold observations and the observations of a new session satisfy it (`initial_stats`,
`restore_stats`). Recording a reward, an attempt or a step's predictions, and censoring, keep it
(`recordEnvironment_stats`, `recordAttempt_stats`, `recordDemons_stats`, `censor_stats`). A whole
step writes the observations at its completion boundary only, under every step order: the first
part, the owed writes, the deferred planning and the tester write none (`choose_lifetime`,
`actOrdered_bounded`). That rests on the executing library's theorems that selection, the
draw-first selection, the deferred writes and option learning hold the lifetime record. So every
running state satisfies the invariant (`running_bounded`), and over the grid's eleven channels
every natural is below `128 ^ naturalAllowance`, which is `2 ^ 28672`
(`running_naturals_allowed`): a natural below `128 ^ (digits + 1)` encodes in at most `digits + 1`
bytes (`natural_length`).

`running_snapshot_size` is then `snapshot_size_bound`. For a construction whose profile restores, a
load of the bytes a save writes returns the saved state, so a state is a function of the bytes of
its image, and a list of at most `n` bytes has a code below `256 ^ (n + 1)` (`code_injective`,
`code_lt`). That gives `running_memory_bits`.

What the bound is not. It counts memory in the bytes of the exact image: it says nothing about
native allocation or work, or about how the executed agent uses its memory.

- `Running` is a definition over the states of a grid construction. No theorem says that a native
  loop holds only such states. The host's loops are generic in the agent's type and reach an agent
  only through the constructor, the callbacks and the checkpoint hooks, and the hooks load through
  `Acorn.Checkpoint.resume` (argued). A host operation added to `AgentConstruction.Reached` is not
  thereby added to `Running`.
- The count, `running_memory_bits`, is of a construction whose profile restores, because it reads
  a state back from the bytes of its image. The two bounds on size hold of every construction.
- Neither relates a running state to the memory of a kernel loop, which
  `AcornVerif.Kernel.campaign_count` and the record of contract 3 read: that link is a further
  step.
-/

set_option exponentiation.threshold 32768

namespace AcornVerif.CurrentRunningMemory
open Acorn Acorn.Features Acorn.Handcrafted Acorn.Checkpoint

/-! ## Naturals within the allowance -/

/-- A natural below `128 ^ (digits + 1)` encodes in at most `digits + 1` bytes. -/
theorem natural_length (digits : Nat) : ∀ value, value < 128 ^ (digits + 1) →
    (Format.natural.encode value).length ≤ digits + 1 := by
  induction digits with
  | zero =>
    intro value small
    change (Format.encodeNatural value).length ≤ 1
    rw [Format.encodeNatural_eq]
    split
    · exact Nat.le_refl 1
    · rename_i large
      exact absurd small large
  | succ digits ih =>
    intro value small
    change (Format.encodeNatural value).length ≤ digits + 1 + 1
    rw [Format.encodeNatural_eq]
    split
    · exact Nat.succ_le_succ (Nat.zero_le _)
    · rw [List.length_cons]
      refine Nat.succ_le_succ (ih (value / 128) ?_)
      rw [Nat.pow_succ, Nat.mul_comm] at small
      exact Nat.div_lt_of_lt_mul small

/-- A natural below `128 ^ naturalAllowance`, which is `2 ^ 28672`, encodes within the
allowance. -/
theorem natural_allowed {value : Nat} (small : value < 128 ^ naturalAllowance) :
    (Format.natural.encode value).length ≤ naturalAllowance :=
  natural_length 4095 value small

/-! ## Bounds of the evaluator's arithmetic -/

/-- The units of a binary32 word are fewer than `2 ^ 278`. -/
theorem magnitudeUnits_lt (value : Binary32) : Agreement.magnitudeUnits value < 2 ^ 278 := by
  have bound := value.magnitude_lt
  have fraction : value.magnitude % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have exponent : value.magnitude / 2 ^ 23 < 2 ^ 8 :=
    Nat.div_lt_of_lt_mul (by simpa using bound)
  unfold Agreement.magnitudeUnits
  dsimp only
  split
  · exact Nat.lt_of_lt_of_le fraction (Nat.pow_le_pow_right (by decide) (by decide))
  · have scale : 2 ^ (value.magnitude / 2 ^ 23 - 1) ≤ 2 ^ 254 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have significand : 2 ^ 23 + value.magnitude % 2 ^ 23 < 2 ^ 24 := by omega
    calc (2 ^ 23 + value.magnitude % 2 ^ 23) * 2 ^ (value.magnitude / 2 ^ 23 - 1)
        < 2 ^ 24 * 2 ^ 254 := Nat.mul_lt_mul_of_lt_of_le significand scale (Nat.two_pow_pos 254)
      _ = 2 ^ 278 := by rw [← Nat.pow_add]

/-- The scale of a channel's discrepancies is below `2 ^ 278`. -/
theorem envelopeUnits_lt (discount : Discount) : Agreement.envelopeUnits discount < 2 ^ 278 :=
  magnitudeUnits_lt _

/-- The bound of the two denominators of a channel's precision: `2 ^ 427`. -/
def precisionBound : Nat := 2 ^ 427

/-- The bound of a channel's sum and of the denominator of its ratio: `2 ^ 620`. -/
def sumBound : Nat := 2 ^ 620

/-- The bound of the denominator of an agreement point over a number of channels. -/
def pointBound (channels : Nat) : Nat := channels * sumBound ^ channels

/-- An admitted ratio has the denominator it was admitted with. -/
theorem admit_denominator {numerator denominator : Nat} {ratio : Agreement.Ratio}
    (admitted : Agreement.Ratio.admit numerator denominator = some ratio) :
    ratio.denominator = denominator := by
  unfold Agreement.Ratio.admit at admitted
  split at admitted
  · split at admitted
    · cases admitted
      rfl
    · cases admitted
  · cases admitted

/-- The larger of two ratios is one of the two. -/
theorem maximum_cases (left right : Agreement.Ratio) :
    left.maximum right = left ∨ left.maximum right = right := by
  unfold Agreement.Ratio.maximum
  split
  · exact .inr rfl
  · exact .inl rfl

/-- A precision the evaluator derives has both denominators below `2 ^ 427`: the first is a
difference of units below `2 ^ 149` times the channel's scale, and the second is the scale. -/
theorem precision_bounded {discount : Discount} {steps : Nat} {power : Binary32}
    {precision : Agreement.Precision}
    (derived : Agreement.precision discount steps power = some precision) :
    precision.tail.denominator < precisionBound ∧
      precision.rounding.denominator < precisionBound := by
  have envelope := envelopeUnits_lt discount
  unfold Agreement.precision at derived
  split at derived
  · cases derived
  · simp only [bind, Option.bind] at derived
    split at derived
    · cases derived
    · rename_i tail admittedTail
      dsimp only at derived
      split at derived
      · cases derived
      · rename_i rounding admittedRounding
        have same : some (Agreement.Precision.mk tail rounding) = some precision := derived
        cases same
        rw [admit_denominator admittedTail, admit_denominator admittedRounding]
        constructor
        · calc (2 ^ Agreement.unitExponent - Agreement.magnitudeUnits discount.gamma) *
                Agreement.envelopeUnits discount
              ≤ 2 ^ 149 * Agreement.envelopeUnits discount :=
                Nat.mul_le_mul_right _ (Nat.sub_le _ _)
            _ < 2 ^ 149 * 2 ^ 278 := Nat.mul_lt_mul_of_pos_left envelope (Nat.two_pow_pos 149)
            _ = precisionBound := by rw [← Nat.pow_add]; rfl
        · exact Nat.lt_of_lt_of_le envelope (Nat.pow_le_pow_right (by decide) (by decide))

/-- A count of at most the count limit, times the square of a channel's scale, is below `2 ^ 620`:
the limit is below `2 ^ 64` and the scale below `2 ^ 278`. -/
theorem scaled_lt (discount : Discount) (count : Nat) (small : count ≤ Agreement.countLimit) :
    count * Agreement.envelopeUnits discount ^ 2 < sumBound := by
  have envelope := envelopeUnits_lt discount
  calc count * Agreement.envelopeUnits discount ^ 2
      ≤ Agreement.countLimit * Agreement.envelopeUnits discount ^ 2 :=
        Nat.mul_le_mul_right _ small
    _ < 2 ^ 64 * (2 ^ 278) ^ 2 :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos 64) Nat.one_pos)
          (Nat.pow_le_pow_left (Nat.le_of_lt envelope) 2) (Nat.pow_pos (Nat.two_pow_pos 278))
    _ = sumBound := by rw [← Nat.pow_mul, ← Nat.pow_add]; rfl

/-- The sum of a channel's total is below `2 ^ 620`. -/
theorem sum_lt {discount : Discount}
    (total : Agreement.Total (Agreement.envelopeUnits discount)) : total.sum < sumBound :=
  Nat.lt_of_le_of_lt total.bounded
    (scaled_lt discount total.count.val (Nat.le_of_lt_succ total.count.isLt))

/-- The ratio of a channel has a denominator of at most `2 ^ 620`. -/
theorem channel_ratio_bounded {discount : Discount} (channel : Agreement.Channel discount)
    {ratio : Agreement.Ratio} (scored : channel.ratio = some ratio) :
    ratio.denominator ≤ sumBound := by
  unfold Agreement.Channel.ratio at scored
  split at scored
  · cases scored
  · unfold Agreement.Total.ratio at scored
    split at scored
    · cases scored
      exact Nat.le_of_lt
        (scaled_lt discount channel.total.count.val (Nat.le_of_lt_succ channel.total.count.isLt))
    · cases scored

/-- An aggregate of ratios whose denominators are each at most `2 ^ 620` counts every ratio and has
a denominator of at most that bound to the power of their number. -/
theorem aggregate_bounded : ∀ (ratios : List (Option Agreement.Ratio))
    (aggregate : Agreement.Aggregate),
    (∀ ratio ∈ ratios, ∀ held, ratio = some held → held.denominator ≤ sumBound) →
    Agreement.aggregateAll ratios = some aggregate →
    aggregate.questions = ratios.length ∧ aggregate.denominator ≤ sumBound ^ ratios.length
  | [], aggregate, _, all => by
    cases all
    exact ⟨rfl, Nat.le_refl 1⟩
  | none :: _, _, _, all => by cases all
  | some head :: tail, aggregate, bounded, all => by
    change (Agreement.aggregateAll tail).map (·.add head) = some aggregate at all
    obtain ⟨before, found, added⟩ := Option.map_eq_some_iff.mp all
    obtain ⟨counted, small⟩ := aggregate_bounded tail before
      (fun ratio member => bounded ratio (List.mem_cons_of_mem _ member)) found
    subst added
    refine ⟨congrArg (· + 1) counted, ?_⟩
    change before.denominator * head.denominator ≤ sumBound ^ (tail.length + 1)
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul small (bounded (some head) List.mem_cons_self head rfl)

/-- The ratio of an aggregate of ratios whose denominators are each at most `2 ^ 620` has a
denominator of at most their number times that bound to the power of their number. -/
theorem aggregate_ratio_bounded (ratios : List (Option Agreement.Ratio))
    (bounded : ∀ ratio ∈ ratios, ∀ held, ratio = some held → held.denominator ≤ sumBound)
    {ratio : Agreement.Ratio}
    (scored : (Agreement.aggregateAll ratios).bind Agreement.Aggregate.ratio = some ratio) :
    ratio.denominator ≤ pointBound ratios.length := by
  obtain ⟨aggregate, found, taken⟩ := Option.bind_eq_some_iff.mp scored
  obtain ⟨counted, small⟩ := aggregate_bounded ratios aggregate bounded found
  unfold Agreement.Aggregate.ratio at taken
  split at taken
  · cases taken
    change aggregate.questions * aggregate.denominator ≤ ratios.length * sumBound ^ ratios.length
    rw [counted]
    exact Nat.mul_le_mul_left _ small
  · cases taken

/-! ## The invariant of the evaluator -/

section evaluator
open Acorn.Lifetime

variable {discount : Discount} {discounts : List Discount}

/-- A channel's precision, when it holds one, has both denominators below `2 ^ 427`. -/
def ChannelBounded (channel : Agreement.Channel discount) : Prop :=
  ∀ precision, channel.precision = some precision →
    precision.tail.denominator < precisionBound ∧
      precision.rounding.denominator < precisionBound

/-- An empty channel is bounded: it holds no precision. -/
theorem empty_bounded (discount : Discount) :
    ChannelBounded (Agreement.Channel.empty discount) :=
  fun _ held => nomatch held

/-- Counting censored futures writes no precision. -/
theorem censor_bounded (channel : Agreement.Channel discount) (count : Nat)
    (held : ChannelBounded channel) : ChannelBounded (channel.censor count) := by
  unfold Agreement.Channel.censor
  split <;> exact held

/-- A settlement keeps the bound. It writes no precision, or the derived precision where the
channel held none, or the merge of the one held with the derived one, and a merge returns, for
each ratio, one of its two arguments. -/
theorem settle_bounded (channel : Agreement.Channel discount) (forecast outcome power : Binary32)
    (steps : Nat) (started settled : UInt64) (held : ChannelBounded channel) :
    ChannelBounded (channel.settle forecast outcome power steps started settled) := by
  unfold Agreement.Channel.settle
  split
  · exact held
  · split
    · exact held
    · split
      · exact held
      · exact held
      · rename_i sample derived admitted computed
        split
        · exact held
        · intro kept same
          have fresh := precision_bounded computed
          cases before : channel.precision with
          | none =>
            rw [before] at same
            cases same
            exact fresh
          | some earlier =>
            rw [before] at same
            cases same
            have old := held earlier before
            change (earlier.tail.maximum derived.tail).denominator < precisionBound ∧
              (earlier.rounding.maximum derived.rounding).denominator < precisionBound
            constructor
            · rcases maximum_cases earlier.tail derived.tail with same | same
              · rw [same]
                exact old.1
              · rw [same]
                exact fresh.1
            · rcases maximum_cases earlier.rounding derived.rounding with same | same
              · rw [same]
                exact old.2
              · rw [same]
                exact fresh.2

/-- One pending return advanced, settled or not, keeps the channel's bound. -/
theorem advanceSlot_bounded (state : DemonStats discount)
    (slot : Fin Acorn.FeatureConstants.pendingSamples) (cumulant : Binary32) (clock : UInt64)
    (held : ChannelBounded state.agreement) :
    ChannelBounded (state.advanceSlot slot cumulant clock).1.agreement := by
  unfold DemonStats.advanceSlot
  simp only [Id.run]
  split
  · exact held
  · split
    · exact settle_bounded _ _ _ _ _ _ _ held
    · exact held

/-- Every pending return advanced in turn keeps the channel's bound. -/
theorem advanceSlots_bounded (cumulant : Binary32) (clock : UInt64) :
    ∀ (slots : List (Fin Acorn.FeatureConstants.pendingSamples))
      (current : DemonStats discount ×
        Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins),
      ChannelBounded current.1.agreement →
      ChannelBounded (slots.foldl (fun current slot =>
        DemonStats.visit current slot cumulant clock) current).1.agreement
  | [], _, held => held
  | slot :: rest, current, held =>
    advanceSlots_bounded cumulant clock rest (DemonStats.visit current slot cumulant clock)
      (advanceSlot_bounded current.1 slot cumulant clock held)

/-- Starting a pending return writes no precision. -/
theorem start_bounded (state : DemonStats discount) (clock : UInt64)
    (prediction : Prediction discount) (held : ChannelBounded state.agreement) :
    ChannelBounded (state.start clock prediction).agreement := by
  unfold DemonStats.start
  split
  · split <;> exact held
  · exact held

/-- One channel's observation of a step keeps its bound. -/
theorem observe_bounded (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins)
    (clock : UInt64) (cumulant : Binary32) (prediction : Prediction discount)
    (held : ChannelBounded state.agreement) :
    ChannelBounded (state.observe history clock cumulant prediction).1.agreement := by
  have advanced : ChannelBounded (state.advanceSlots history clock cumulant
      (List.finRange Acorn.FeatureConstants.pendingSamples)).1.agreement := by
    unfold DemonStats.advanceSlots
    exact advanceSlots_bounded cumulant clock _ (state, history) held
  exact start_bounded _ clock prediction advanced

/-- Every channel of the records is bounded. -/
def RecordsBounded : {discounts : List Discount} → DemonRecords discounts → Prop
  | _, .nil => True
  | _, .cons head tail => ChannelBounded head.agreement ∧ RecordsBounded tail

/-- Records rebuilt from their durable projection are bounded: every channel is empty. -/
theorem restore_bounded : ∀ {discounts : List Discount} (durable : DurableDemons discounts),
    RecordsBounded durable.restore
  | _, .nil => trivial
  | _, .cons _ tail => ⟨empty_bounded _, restore_bounded tail⟩

/-- Cold records are bounded: every channel is empty. -/
theorem initial_bounded : ∀ discounts : List Discount,
    RecordsBounded (DemonRecords.initial discounts)
  | [] => trivial
  | discount :: rest => ⟨empty_bounded discount, initial_bounded rest⟩

/-- Censoring every channel keeps the bound. -/
theorem censorRecords_bounded : ∀ {discounts : List Discount} (state : DemonRecords discounts),
    RecordsBounded state → RecordsBounded state.censor
  | _, .nil, _ => trivial
  | _, .cons head tail, held =>
    ⟨censor_bounded head.agreement head.pendingCount held.1, censorRecords_bounded tail held.2⟩

/-- Marking every channel failed writes no precision. -/
theorem failRecords_bounded (fault : Agreement.Fault) :
    ∀ {discounts : List Discount} (state : DemonRecords discounts),
      RecordsBounded state → RecordsBounded (state.fail fault)
  | _, .nil, _ => trivial
  | _, .cons _ tail, held => ⟨held.1, failRecords_bounded fault tail held.2⟩

/-- The records' observation of a step keeps every channel's bound. -/
theorem observeRecords_bounded : ∀ {discounts : List Discount} (state : DemonRecords discounts)
    (history : Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins)
    (clock : UInt64) (cumulants : Cumulants discounts) (predictions : PredictionCache discounts),
    RecordsBounded state → RecordsBounded (state.observe history clock cumulants predictions).1
  | _, .nil, _, _, .nil, .nil, _ => trivial
  | _, .cons head tail, history, clock, .cons _ cumulant cumulants,
      .cons prediction predictions, held =>
    ⟨observe_bounded head history clock cumulant prediction held.1,
      observeRecords_bounded tail (head.observe history clock cumulant prediction).2 clock
        cumulants predictions held.2⟩

/-- The ratio of the records' equal-question mean has a denominator of at most the number of
channels times `2 ^ 620` to the power of that number, whatever the records hold. -/
theorem agreementRatio_bounded (state : DemonRecords discounts) {ratio : Agreement.Ratio}
    (scored : state.agreementRatio = some ratio) :
    ratio.denominator ≤ pointBound discounts.length := by
  have each : ∀ {discounts : List Discount} (state : DemonRecords discounts),
      ∀ entry ∈ state.agreementRatios, ∀ held, entry = some held →
        held.denominator ≤ sumBound := by
    intro discounts state
    induction state with
    | nil => intro entry member; cases member
    | cons head tail ih =>
      intro entry member held same
      rcases List.mem_cons.mp member with first | later
      · exact channel_ratio_bounded head.agreement (first ▸ same)
      · exact ih entry later held same
  have bound := aggregate_ratio_bounded state.agreementRatios (each state) scored
  rwa [state.agreementRatios_length] at bound

end evaluator

/-! ## The invariant of the lifetime observations -/

section observations
open Acorn.Lifetime

variable {discounts : List Discount}

/-- Every agreement point of a history has a ratio whose denominator is at most the bound of a
point over a number of channels. -/
def HistoryBounded (channels : Nat) {bins : Nat}
    (history : Vector (Option AgreementPoint) bins) : Prop :=
  ∀ point ∈ history.toList, ∀ held, point = some held →
    held.ratio.denominator ≤ pointBound channels

/-- A history with no point is bounded. -/
theorem empty_history (channels bins : Nat) :
    HistoryBounded channels (Vector.replicate bins (none : Option AgreementPoint)) := by
  intro point member held same
  rw [Vector.toList_replicate] at member
  rw [List.eq_of_mem_replicate member] at same
  cases same

/-- Writing a bounded point into a bounded history keeps it bounded. -/
theorem set_history {channels bins : Nat} (history : Vector (Option AgreementPoint) bins)
    (index : Nat) (within : index < bins) (point : Option AgreementPoint)
    (held : HistoryBounded channels history)
    (fresh : ∀ kept, point = some kept → kept.ratio.denominator ≤ pointBound channels) :
    HistoryBounded channels (history.set index point within) := by
  intro entry member kept same
  rw [Vector.toList_set] at member
  rcases List.mem_or_eq_of_mem_set member with earlier | written
  · exact held entry earlier kept same
  · exact fresh kept (written ▸ same)

/-- **The invariant.** Every channel's precision has denominators below `2 ^ 427`, and every
agreement point's ratio has a denominator of at most the bound of a point over the channels. -/
def StatsBounded (stats : Stats discounts) : Prop :=
  RecordsBounded stats.demons ∧ HistoryBounded discounts.length stats.agreementHistory

/-- Cold observations are bounded. -/
theorem initial_stats (discounts : List Discount) : StatsBounded (Stats.initial discounts) :=
  ⟨initial_bounded discounts, empty_history _ _⟩

/-- Observations rebuilt from their durable projection are bounded, whatever the session's
clocks: every channel is empty and the history holds no point. -/
theorem restore_stats (durable : Durable discounts) (started last : Option UInt64) :
    StatsBounded { durable.restore with agreementStarted := started, agreementLastClock := last } :=
  ⟨restore_bounded durable.demons, empty_history _ _⟩

/-- Recording a reward writes neither a channel nor the agreement history. -/
theorem recordEnvironment_stats (stats : Stats discounts) (clock : UInt64) (family : Fin 4)
    (value : Binary32) (held : StatsBounded stats) :
    StatsBounded (stats.recordEnvironment clock family value) :=
  held

/-- Recording an attempt writes neither a channel nor the agreement history. -/
theorem recordAttempt_stats (stats : Stats discounts) (family : Fin 4) (cycle steps : UInt64)
    (achieved : Bool) (held : StatsBounded stats) :
    StatsBounded (stats.recordAttempt family cycle steps achieved) :=
  held

/-- Censoring the observations keeps them bounded. -/
theorem censor_stats (stats : Stats discounts) (held : StatsBounded stats) :
    StatsBounded stats.censor :=
  ⟨censorRecords_bounded stats.demons held.1, held.2⟩

/-- Observing a step with bounded records, and writing the agreement point of the observed
records into a bounded history, gives bounded records and a bounded history. -/
theorem observed_stats (stats : Stats discounts) (records : DemonRecords discounts)
    (clock : UInt64) (cumulants : Cumulants discounts) (predictions : PredictionCache discounts)
    (held : StatsBounded stats) (chosen : RecordsBounded records) :
    RecordsBounded (records.observe stats.errorHistory clock cumulants predictions).1 ∧
      HistoryBounded discounts.length
        (if clock.toNat % Acorn.FeatureConstants.settleStride = 0 then
          stats.agreementHistory.set (historyBin clock).val
            (Option.map (fun ratio => AgreementPoint.mk clock ratio)
              (records.observe stats.errorHistory clock cumulants predictions).1.agreementRatio)
            (historyBin clock).isLt
        else stats.agreementHistory) := by
  refine ⟨observeRecords_bounded records _ clock cumulants predictions chosen, ?_⟩
  split
  · refine set_history _ _ _ _ held.2 (fun kept same => ?_)
    obtain ⟨ratio, scored, made⟩ := Option.map_eq_some_iff.mp same
    subst made
    exact agreementRatio_bounded _ scored
  · exact held.2

/-- Recording the predictions of a step keeps the observations bounded. -/
theorem recordDemons_stats (stats : Stats discounts) (clock : UInt64)
    (cumulants : Cumulants discounts) (predictions : PredictionCache discounts)
    (held : StatsBounded stats) :
    StatsBounded (stats.recordDemons clock cumulants predictions) := by
  cases stopped : stats.agreementStopped with
  | true =>
    rw [Stats.recordDemons_stopped stats clock cumulants predictions stopped]
    exact held
  | false =>
    have chosen : RecordsBounded
        (if clock.toNat = Agreement.countLimit then stats.demons.censor.fail .saturated else
          match stats.agreementLastClock with
          | none => stats.demons
          | some last =>
            if clock.toNat = last.toNat + 1 then stats.demons
            else stats.demons.censor.fail .invalid) := by
      split
      · exact failRecords_bounded _ _ (censorRecords_bounded _ held.1)
      · split
        · exact held.1
        · split
          · exact held.1
          · exact failRecords_bounded _ _ (censorRecords_bounded _ held.1)
    unfold Stats.recordDemons
    simp only [Id.run, stopped, Bool.false_eq_true, ↓reduceIte]
    exact observed_stats stats _ clock cumulants predictions held chosen

/-- The naturals of bounded channels are below `128 ^ naturalAllowance`. -/
theorem records_small : ∀ {discounts : List Discount} (records : DemonRecords discounts),
    RecordsBounded records →
      ∀ value ∈ CurrentCheckpointSize.recordsNaturals records, value < 128 ^ naturalAllowance
  | _, .nil, _, _, member => nomatch member
  | _, .cons head tail, held, value, member => by
    have sums : sumBound < 128 ^ naturalAllowance := by decide
    have precisions : precisionBound < 128 ^ naturalAllowance := by decide
    rcases List.mem_append.mp member with channel | later
    · rcases List.mem_cons.mp channel with sum | precise
      · rw [sum]
        exact Nat.lt_trans (sum_lt head.agreement.total) sums
      · cases kept : head.agreement.precision with
        | none =>
          rw [kept] at precise
          cases precise
        | some precision =>
          rw [kept] at precise
          obtain ⟨tail, rounding⟩ := held.1 precision kept
          have within : value ≤ precision.tail.denominator ∨
              value ≤ precision.rounding.denominator := by
            rcases List.mem_append.mp precise with first | second
            · rcases List.mem_cons.mp first with numerator | rest
              · exact .inl (numerator ▸ precision.tail.bounded)
              · exact .inl (Nat.le_of_eq (List.mem_singleton.mp rest))
            · rcases List.mem_cons.mp second with numerator | rest
              · exact .inr (numerator ▸ precision.rounding.bounded)
              · exact .inr (Nat.le_of_eq (List.mem_singleton.mp rest))
          rcases within with small | small
          · exact Nat.lt_trans (Nat.lt_of_le_of_lt small tail) precisions
          · exact Nat.lt_trans (Nat.lt_of_le_of_lt small rounding) precisions
    · exact records_small tail held.2 value later

/-- **Bounded observations have allowed naturals.** Where the bound of an agreement point over
the channels is below `128 ^ naturalAllowance`, every evaluator natural of bounded observations
encodes within the allowance. -/
theorem bounded_allowed (stats : Stats discounts) (held : StatsBounded stats)
    (fits : pointBound discounts.length < 128 ^ naturalAllowance) :
    ∀ value ∈ CurrentCheckpointSize.statsNaturals stats,
      (Format.natural.encode value).length ≤ naturalAllowance := by
  intro value member
  apply natural_allowed
  rcases List.mem_append.mp member with channel | point
  · exact records_small stats.demons held.1 value channel
  · obtain ⟨entry, listed, inside⟩ := List.mem_flatMap.mp point
    cases entry with
    | none => cases inside
    | some kept =>
      have bound := held.2 (some kept) listed kept rfl
      have within : value ≤ kept.ratio.denominator := by
        rcases List.mem_cons.mp inside with numerator | rest
        · exact numerator ▸ kept.ratio.bounded
        · exact Nat.le_of_eq (List.mem_singleton.mp rest)
      exact Nat.lt_of_le_of_lt (Nat.le_trans within bound) fits

end observations

/-! ## A whole step -/

section step

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- The completion boundary of a step keeps the observations bounded: it records the option
episodes, which the invariant does not read, and, where the profile learns, the predictions. -/
theorem finish_bounded (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) (held : StatsBounded state.lifetime) :
    StatsBounded (state.finish features obs reward decision).lifetime := by
  rw [TemporalControl.finish_eq]
  change StatsBounded ((state.recordEpisodes decision).predictionView.advanceWith features
    (signalValues obs reward) reward decision.action decision.own
    state.runtime.lifecycle.representation.progress.clock).lifetime
  unfold PredictionControl.advanceWith
  split
  · exact held
  · exact recordDemons_stats _ _ _ _ held

/-- The learning part of a step keeps the observations bounded: only its completion boundary
writes them. -/
theorem learn_bounded (middle : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions)
    (held : StatsBounded middle.lifetime) :
    StatsBounded (middle.learn features obs reward goal decision).lifetime := by
  unfold TemporalControl.learn
  dsimp only
  apply finish_bounded
  rw [(TemporalControl.closeSpan_episodes _ _).1, (TemporalControl.follow_episodes _ _ _ _ _ _ _).1]
  exact held

/-- The first part of a step, under every order, writes no observation. -/
theorem choose_lifetime (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    (state.choose order percept).control.lifetime = state.control.lifetime := by
  cases order with
  | actThenLearn =>
    exact (TemporalControl.drawFirst_episodes state.advanceClock.control _
      (modelOperations criterion dimension) (planningBoundary .none)
      (state.advanceClock.frame percept.frame).active percept.frame.declared
      percept.frame.achieved _ _ state.advanceClock.episodes.2 (state.choose_drawn percept).1).1
  | learnThenAct =>
    exact (TemporalControl.select_episodes state.advanceClock.control _
      (modelOperations criterion dimension)
      (planningBoundary (firstPlanning .learnThenAct planning))
      (state.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
      percept.frame.achieved _ state.advanceClock.episodes.2
      (state.choose_selected .learnThenAct (by decide) percept).1).1
  | planAfterAct =>
    exact (TemporalControl.select_episodes state.advanceClock.control _
      (modelOperations criterion dimension)
      (planningBoundary (firstPlanning .planAfterAct planning))
      (state.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
      percept.frame.achieved _ state.advanceClock.episodes.2
      (state.choose_selected .planAfterAct (by decide) percept).1).1

/-- The tester writes no observation. -/
theorem retire_lifetime (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (state.retire active).control.lifetime = state.control.lifetime := by
  unfold Agent.retire
  split <;> rfl

/-- **A whole step keeps the observations bounded, under every step order.** The first part
writes no observation, the writes an order owes and its deferred planning write none, the
learning part writes them at its completion boundary only, and the tester writes none. -/
theorem actOrdered_bounded (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface)
    (held : StatsBounded state.control.lifetime) :
    StatsBounded (state.actOrdered order percept).1.control.lifetime := by
  change StatsBounded ((state.choose order percept).learned.retire
    (state.choose order percept).units).control.lifetime
  rw [retire_lifetime]
  change StatsBounded (((state.choose order percept).control.deferred
    (state.choose order percept).order planning (state.choose order percept).features
    (state.choose order percept).owed (state.choose order percept).percept.reward
    (state.choose order percept).percept.frame.achieved (state.choose order percept).decision).learn
    (state.choose order percept).features (state.choose order percept).percept.frame
    (state.choose order percept).percept.reward
    (state.choose order percept).percept.frame.achieved
    (state.choose order percept).decision).lifetime
  apply learn_bounded
  rw [(TemporalControl.deferred_frame _ _ _ _ _ _ _ _).1, choose_lifetime]
  exact held

end step

/-! ## The states a host runs -/

/-- The states a host runs: cold, resumed from bytes, or one host operation after such a state. -/
inductive Running (construction : AgentConstruction) : construction.State → Prop where
  /-- The cold state. -/
  | initial : Running construction construction.initial
  /-- A state the host resumes from bytes: the loaded state with a new evaluator session. -/
  | resumed (receiver state : construction.State) (bytes : List UInt8)
      (loaded : resume construction receiver bytes = .ok state) : Running construction state
  /-- One whole step of the construction's order. -/
  | step {state : construction.State} (before : Running construction state)
      (observation : Host.Observation) (result : Host.RawStepResult) :
      Running construction (construction.callbacks.act state observation result).2
  /-- The host records a completed world transition. -/
  | environment {state : construction.State} (before : Running construction state)
      (family : Host.GoalFamily) (reward : Binary32) :
      Running construction (construction.callbacks.recordEnvironment state family reward)
  /-- The host records a completed attempt. -/
  | attempt {state : construction.State} (before : Running construction state)
      (family : Host.GoalFamily) (cycle steps : UInt64) (achieved : Bool) :
      Running construction (construction.callbacks.recordAttempt state family cycle steps achieved)
  /-- The host censors the evaluator's unavailable futures at process exit. -/
  | censored {state : construction.State} (before : Running construction state) :
      Running construction state.censorObservations
  /-- The host begins an evaluator session. -/
  | session {state : construction.State} (before : Running construction state) :
      Running construction state.beginSession

/-- **Every state a host runs has bounded observations.** The cold state and a resumed state hold
empty channels and no agreement point, and every host operation keeps the invariant. -/
theorem running_bounded (construction : AgentConstruction) (state : construction.State)
    (running : Running construction state) : StatsBounded state.agent.control.lifetime := by
  induction running with
  | initial => exact initial_stats _
  | resumed receiver state bytes loaded =>
    unfold resume at loaded
    cases restored : load construction receiver bytes with
    | error refused =>
      rw [restored] at loaded
      cases loaded
    | ok saved =>
      rw [restored] at loaded
      have same : Except.ok saved.beginSession = Except.ok state := loaded
      cases same
      exact restore_stats _ _ _
  | step before observation result ih =>
    exact actOrdered_bounded _ construction.order _ ih
  | environment before family reward ih => exact recordEnvironment_stats _ _ _ _ ih
  | attempt before family cycle steps achieved ih => exact recordAttempt_stats _ _ _ _ _ ih
  | censored before ih => exact censor_stats _ ih
  | session before ih => exact restore_stats _ _ _

/-- Every evaluator natural of a running state fits its allowance. -/
theorem running_naturals_allowed (construction : AgentConstruction) (state : construction.State)
    (running : Running construction state) :
    ∀ value ∈ CurrentCheckpointSize.statsNaturals state.agent.control.lifetime,
      (Format.natural.encode value).length ≤ naturalAllowance := by
  exact bounded_allowed _ (running_bounded construction state running) (by decide)

/-- The image of every running state fits the read limit. -/
theorem running_snapshot_size (construction : AgentConstruction) (state : construction.State)
    (running : Running construction state) :
    (encode (snapshot construction state)).length ≤ maximumBytes construction := by
  exact CurrentCheckpointSize.snapshot_size_bound construction state
    (running_naturals_allowed construction state running)

/-! ## Counting the states a host runs -/

/-- A natural for each byte list: its bytes as the digits of base 256, the first lowest, closed
by a digit one. -/
def code : List UInt8 → Nat
  | [] => 1
  | byte :: rest => byte.toNat + 256 * code rest

/-- The code of a byte list is positive. -/
theorem code_pos : ∀ bytes : List UInt8, 0 < code bytes
  | [] => Nat.one_pos
  | _ :: rest => by
    have positive := code_pos rest
    simp only [code]
    omega

/-- Two byte lists with one code are one list. -/
theorem code_injective : ∀ first second : List UInt8, code first = code second → first = second
  | [], [], _ => rfl
  | [], byte :: rest, same => by
    have positive := code_pos rest
    simp only [code] at same
    omega
  | byte :: rest, [], same => by
    have positive := code_pos rest
    simp only [code] at same
    omega
  | byte :: rest, other :: tail, same => by
    have small := byte.toNat_lt
    have less := other.toNat_lt
    simp only [code] at same
    have bytes : byte.toNat = other.toNat := by omega
    have codes : code rest = code tail := by omega
    rw [UInt8.toNat_inj.mp bytes, code_injective rest tail codes]

/-- The code of a byte list is below 256 to the power of one more than its length. -/
theorem code_lt : ∀ bytes : List UInt8, code bytes < 256 ^ (bytes.length + 1)
  | [] => by decide
  | byte :: rest => by
    have earlier := code_lt rest
    have small := byte.toNat_lt
    simp only [code, List.length_cons]
    rw [Nat.pow_succ]
    omega

/-- The code of the exact image of a state. -/
def imageCode (construction : AgentConstruction) (state : construction.State) : Nat :=
  code (encode (snapshot construction state))

/-- The code of a running state's image is below 256 to the power of one more than the read
limit. -/
theorem imageCode_lt (construction : AgentConstruction) (state : construction.State)
    (running : Running construction state) :
    imageCode construction state < 2 ^ (8 * (maximumBytes construction + 1)) := by
  have size := running_snapshot_size construction state running
  calc imageCode construction state
      < 256 ^ ((encode (snapshot construction state)).length + 1) := code_lt _
    _ ≤ 256 ^ (maximumBytes construction + 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ size)
    _ = 2 ^ (8 * (maximumBytes construction + 1)) := (Nat.pow_mul 2 8 _).symm

/-- Under a profile that restores, two states with one image code are one state: a load of the
bytes a save writes returns the saved state. -/
theorem imageCode_injective (construction : AgentConstruction)
    (supported : construction.profile.checkpointSupported = true)
    (first second : construction.State)
    (same : imageCode construction first = imageCode construction second) : first = second := by
  have bytes := code_injective _ _ same
  have one := CurrentCheckpoint.save_load construction construction.initial first supported
  have two := CurrentCheckpoint.save_load construction construction.initial second supported
  rw [bytes] at one
  exact Except.ok.inj (one.symm.trans two)

/-- A resumable construction's running states embed in the bit strings of a fixed width. -/
theorem running_memory_bits (construction : AgentConstruction)
    (supported : construction.profile.checkpointSupported = true) :
    Nonempty ({ state : construction.State // Running construction state } ↪
      Fin (2 ^ (8 * (maximumBytes construction + 1)))) := by
  exact ⟨⟨fun state => ⟨imageCode construction state.1,
      imageCode_lt construction state.1 state.2⟩,
    fun first second same =>
      Subtype.ext (imageCode_injective construction supported first.1 second.1
        (Fin.mk.inj same))⟩⟩

end AcornVerif.CurrentRunningMemory
