import Acorn.FeatureConsumers
import Acorn.FeatureHistory

namespace Acorn.Features

variable {actions : Word.Count}

structure Lifecycle (shape : PatchShape) (actions : Word.Count) (config : Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) where
  representation : Representation shape config
  consumers : Ensemble actions config criterion dimension discounts

def Ensemble.holds {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (unit : Fin config.units.count) : Bool :=
  ensemble.skills.toList.any (·.interest.held.holds unit)

theorem Ensemble.retire_holds {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (feature : FeatIdx dimension) (unit : Fin config.units.count) :
    (ensemble.retire feature).holds unit = ensemble.holds unit := by
  simp [Ensemble.holds, Ensemble.retire, Skill.retire]

variable {shape : PatchShape} {config : Config} {criterion : Criterion} {dimension : Dimension}
  {discounts : List Discount}

abbrev Lifecycle.progress (state : Lifecycle shape actions config criterion dimension discounts) :
    Progress config :=
  state.representation.progress

def Lifecycle.mature (state : Lifecycle shape actions config criterion dimension discounts)
    (unit : Fin config.units.count) : Bool :=
  decide (state.progress.units[unit.val].birth.toNat + config.tester.maturity <
    state.progress.clock.toNat)

def Lifecycle.eligible (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) : Bool :=
  state.mature unit && (free || !state.consumers.holds unit)

def Lifecycle.eligibleCount (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) : Nat :=
  (List.finRange config.units.count).countP (state.eligible free)

def Lifecycle.lessUseful (state : Lifecycle shape actions config criterion dimension discounts)
    (unit other : Fin config.units.count) : Bool :=
  state.progress.units[unit.val].utility.value.less state.progress.units[other.val].utility.value

def Lifecycle.prefer (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (best : Option (Fin config.units.count)) (unit : Fin config.units.count) :
    Option (Fin config.units.count) :=
  if state.eligible free unit then
    match best with
    | none => some unit
    | some prior => if state.lessUseful unit prior then some unit else some prior
  else best

def Lifecycle.candidate (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) : Option (Fin config.units.count) :=
  (List.finRange config.units.count).foldl (state.prefer free) none

def Lifecycle.Scanned (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (best : Option (Fin config.units.count)) (seen : List (Fin config.units.count)) :
    Prop :=
  (best = none ↔ ∀ unit ∈ seen, state.eligible free unit = false) ∧
    ∀ chosen, best = some chosen → state.eligible free chosen = true ∧
      ∀ unit ∈ seen, state.eligible free unit = true →
        state.progress.units[chosen.val].utility.value.key ≤
          state.progress.units[unit.val].utility.value.key

theorem Lifecycle.lessUseful_iff (state : Lifecycle shape actions config criterion dimension discounts)
    (unit other : Fin config.units.count) :
    state.lessUseful unit other = true ↔
      state.progress.units[unit.val].utility.value.key <
        state.progress.units[other.val].utility.value.key := by
  unfold Lifecycle.lessUseful
  rw [Binary32.less_finite _ _ (state.progress.units[unit.val].utility.legal.1)
    (state.progress.units[other.val].utility.legal.1)]
  simp

theorem Lifecycle.prefer_scanned (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (best : Option (Fin config.units.count)) (seen : List (Fin config.units.count))
    (unit : Fin config.units.count) (scanned : state.Scanned free best seen) :
    state.Scanned free (state.prefer free best unit) (seen ++ [unit]) := by
  obtain ⟨empty, chosen⟩ := scanned
  unfold Lifecycle.prefer
  by_cases eligible : state.eligible free unit = true
  · simp only [eligible, ↓reduceIte]
    cases best with
    | none =>
      have none := empty.mp rfl
      refine ⟨?_, ?_⟩
      · simp only [reduceCtorEq, false_iff]
        intro all
        have ineligible := all unit (by simp)
        rw [eligible] at ineligible
        contradiction
      · intro picked same
        rw [← Option.some.inj same]
        refine ⟨eligible, ?_⟩
        intro other member otherEligible
        rcases List.mem_append.mp member with old | new
        · rw [none other old] at otherEligible
          contradiction
        · have : other = unit := by simpa using new
          rw [this]
          exact Int.le_refl _
    | some prior =>
      obtain ⟨priorEligible, priorLeast⟩ := chosen prior rfl
      by_cases less : state.lessUseful unit prior = true
      · simp only [less, ↓reduceIte]
        have strict := (state.lessUseful_iff unit prior).mp less
        refine ⟨?_, ?_⟩
        · simp only [reduceCtorEq, false_iff]
          intro all
          have ineligible := all unit (by simp)
          rw [eligible] at ineligible
          contradiction
        · intro picked same
          rw [← Option.some.inj same]
          refine ⟨eligible, ?_⟩
          intro other member otherEligible
          rcases List.mem_append.mp member with old | new
          · have := priorLeast other old otherEligible
            omega
          · have : other = unit := by simpa using new
            rw [this]
            exact Int.le_refl _
      · have noLess : state.lessUseful unit prior = false := Bool.eq_false_iff.mpr less
        have weak : ¬ state.progress.units[unit.val].utility.value.key <
            state.progress.units[prior.val].utility.value.key := fun strict =>
          less ((state.lessUseful_iff unit prior).mpr strict)
        simp only [noLess, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · simp only [reduceCtorEq, false_iff]
          intro all
          have ineligible := all unit (by simp)
          rw [eligible] at ineligible
          contradiction
        · intro picked same
          rw [← Option.some.inj same]
          refine ⟨priorEligible, ?_⟩
          intro other member otherEligible
          rcases List.mem_append.mp member with old | new
          · exact priorLeast other old otherEligible
          · have : other = unit := by simpa using new
            subst this
            omega
  · have ineligible : state.eligible free unit = false := Bool.eq_false_iff.mpr eligible
    simp only [ineligible, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [empty]
      constructor
      · intro all other member
        rcases List.mem_append.mp member with old | new
        · exact all other old
        · have : other = unit := by simpa using new
          subst this
          exact ineligible
      · intro all other member
        exact all other (List.mem_append_left _ member)
    · intro picked same
      obtain ⟨pickedEligible, least⟩ := chosen picked same
      refine ⟨pickedEligible, ?_⟩
      intro other member otherEligible
      rcases List.mem_append.mp member with old | new
      · exact least other old otherEligible
      · have : other = unit := by simpa using new
        subst this
        rw [ineligible] at otherEligible
        contradiction

theorem Lifecycle.fold_scanned (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (units : List (Fin config.units.count)) (best : Option (Fin config.units.count))
    (seen : List (Fin config.units.count)) (scanned : state.Scanned free best seen) :
    state.Scanned free (units.foldl (state.prefer free) best) (seen ++ units) := by
  induction units generalizing best seen with
  | nil => simpa using scanned
  | cons unit rest ih =>
    have next := ih (state.prefer free best unit) (seen ++ [unit])
      (state.prefer_scanned free best seen unit scanned)
    simpa [List.foldl_cons, List.append_assoc] using next

theorem Lifecycle.candidate_scanned (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) :
    state.Scanned free (state.candidate free) (List.finRange config.units.count) := by
  have start : state.Scanned free none [] := ⟨by simp, by simp⟩
  simpa [Lifecycle.candidate] using state.fold_scanned free _ none [] start

theorem Lifecycle.candidate_eligible (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) (selected : state.candidate free = some unit) :
    state.eligible free unit = true :=
  ((state.candidate_scanned free).2 unit selected).1

theorem Lifecycle.candidate_least (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) (selected : state.candidate free = some unit)
    (other : Fin config.units.count) (eligible : state.eligible free other = true) :
    state.progress.units[unit.val].utility.value.key ≤
      state.progress.units[other.val].utility.value.key :=
  ((state.candidate_scanned free).2 unit selected).2 other (List.mem_finRange other) eligible

theorem Lifecycle.candidate_none_iff (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) : state.candidate free = none ↔ state.eligibleCount free = 0 := by
  rw [(state.candidate_scanned free).1, Lifecycle.eligibleCount, List.countP_eq_zero]
  simp

theorem Lifecycle.candidate_unheld (state : Lifecycle shape actions config criterion dimension discounts)
    (unit : Fin config.units.count) (selected : state.candidate false = some unit) :
    state.consumers.holds unit = false := by
  have eligible := state.candidate_eligible false unit selected
  simp only [Lifecycle.eligible, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at eligible
  exact eligible.2

def Lifecycle.replace (state : Lifecycle shape actions config criterion dimension discounts)
    (unit : Fin config.units.count) : Lifecycle shape actions config criterion dimension discounts :=
  ⟨state.representation.replace unit, state.consumers.retire (unitFeature dimension config unit)⟩

theorem Lifecycle.replace_readers (state : Lifecycle shape actions config criterion dimension discounts)
    (unit : Fin config.units.count) :
    (state.replace unit).consumers.readers =
      state.consumers.readers.map (PackedLearner.retire (unitFeature dimension config unit)) :=
  Ensemble.retire_readers _ _

theorem Lifecycle.replace_holds (state : Lifecycle shape actions config criterion dimension discounts)
    (unit : Fin config.units.count) :
    (state.replace unit).consumers.holds = state.consumers.holds := by
  funext other
  exact Ensemble.retire_holds _ _ _

theorem Lifecycle.replace_self (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) :
    (state.replace unit).eligible free unit = false := by
  have birth := Progress.replace_birth state.representation.progress unit
  have clock := (Progress.replace_counters state.representation.progress unit).1
  simp only [Lifecycle.eligible, Lifecycle.mature, Lifecycle.progress, Lifecycle.replace,
    Representation.replace, birth, clock]
  have late : ¬ (state.representation.progress.clock.toNat + config.tester.maturity <
      state.representation.progress.clock.toNat) := by omega
  simp [late]

theorem Lifecycle.replace_other (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit other : Fin config.units.count) (different : other ≠ unit) :
    (state.replace unit).eligible free other = state.eligible free other := by
  have distinct : unit.val ≠ other.val := fun same => different (Fin.ext same.symm)
  have kept := Progress.replace_other state.representation.progress unit other distinct
  have clock := (Progress.replace_counters state.representation.progress unit).1
  simp only [Lifecycle.eligible, Lifecycle.mature, Lifecycle.progress, Lifecycle.replace,
    Representation.replace, kept, clock, Ensemble.retire_holds]

theorem countP_drop_one {α : Type} (p q : α → Bool) (target : α) :
    ∀ (items : List α), items.Nodup → target ∈ items → p target = true → q target = false →
      (∀ item ∈ items, item ≠ target → q item = p item) → items.countP q + 1 = items.countP p
  | [], _, member, _, _, _ => by simp at member
  | head :: rest, nodup, member, satisfied, removed, agree => by
    have ⟨absent, restNodup⟩ := List.nodup_cons.mp nodup
    by_cases same : head = target
    · subst same
      have restAgree : rest.countP q = rest.countP p := by
        apply List.countP_congr
        intro item itemMember
        have different : item ≠ head := fun equal => absent (equal ▸ itemMember)
        rw [agree item (List.mem_cons_of_mem _ itemMember) different]
      simp [satisfied, removed, restAgree]
    · have restMember : target ∈ rest := by
        rcases List.mem_cons.mp member with equal | inner
        · exact absurd equal.symm same
        · exact inner
      have headAgree := agree head (List.mem_cons_self) same
      have inner := countP_drop_one p q target rest restNodup restMember satisfied removed
        (fun item itemMember => agree item (List.mem_cons_of_mem _ itemMember))
      simp only [List.countP_cons, headAgree]
      omega

theorem Lifecycle.eligibleCount_replace (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) (eligible : state.eligible free unit = true) :
    (state.replace unit).eligibleCount free + 1 = state.eligibleCount free :=
  countP_drop_one _ _ unit _ (List.nodup_finRange _) (List.mem_finRange _) eligible
    (state.replace_self free unit)
    (fun other _ different => state.replace_other free unit other different)

def Lifecycle.replaceDue (free : Bool) :
    Nat → Lifecycle shape actions config criterion dimension discounts →
      Lifecycle shape actions config criterion dimension discounts × List (Fin config.units.count)
  | 0, state => (state, [])
  | due + 1, state =>
    match state.candidate free with
    | none => (state, [])
    | some unit =>
      let rest := Lifecycle.replaceDue free due (state.replace unit)
      (rest.1, unit :: rest.2)

theorem Lifecycle.replaceDue_length (free : Bool) :
    ∀ (due : Nat) (state : Lifecycle shape actions config criterion dimension discounts),
      due ≤ state.eligibleCount free → (Lifecycle.replaceDue free due state).2.length = due
  | 0, _, _ => rfl
  | due + 1, state, enough => by
    cases selected : state.candidate free with
    | none =>
      have := (state.candidate_none_iff free).mp selected
      omega
    | some unit =>
      have eligible := state.candidate_eligible free unit selected
      have fewer := state.eligibleCount_replace free unit eligible
      have rest := Lifecycle.replaceDue_length free due (state.replace unit) (by omega)
      simp [Lifecycle.replaceDue, selected, rest]

theorem Lifecycle.replaceDue_unheld :
    ∀ (due : Nat) (state : Lifecycle shape actions config criterion dimension discounts),
      ∀ unit ∈ (Lifecycle.replaceDue false due state).2, state.consumers.holds unit = false
  | 0, _, unit, member => by simp [Lifecycle.replaceDue] at member
  | due + 1, state, unit, member => by
    cases selected : state.candidate false with
    | none => simp [Lifecycle.replaceDue, selected] at member
    | some chosen =>
      simp only [Lifecycle.replaceDue, selected, List.mem_cons] at member
      rcases member with same | later
      · subst same
        exact state.candidate_unheld _ selected
      · have held := Lifecycle.replaceDue_unheld due (state.replace chosen) unit later
        rwa [state.replace_holds chosen] at held

theorem Lifecycle.replaceDue_preserves (free : Bool)
    (property : Ensemble actions config criterion dimension discounts → Prop)
    (closed : ∀ ensemble feature, property ensemble → property (ensemble.retire feature)) :
    ∀ (due : Nat) (state : Lifecycle shape actions config criterion dimension discounts),
      property state.consumers → property (Lifecycle.replaceDue free due state).1.consumers
  | 0, _, holds => holds
  | due + 1, state, holds => by
    cases selected : state.candidate free with
    | none => simpa [Lifecycle.replaceDue, selected] using holds
    | some unit =>
      have rest := Lifecycle.replaceDue_preserves free property closed due (state.replace unit)
        (closed _ _ holds)
      simpa [Lifecycle.replaceDue, selected] using rest

theorem Lifecycle.replaceDue_counters (free : Bool) :
    ∀ (due : Nat) (state : Lifecycle shape actions config criterion dimension discounts),
      (Lifecycle.replaceDue free due state).1.progress.credit = state.progress.credit ∧
        (Lifecycle.replaceDue free due state).1.progress.clock = state.progress.clock
  | 0, _ => ⟨rfl, rfl⟩
  | due + 1, state => by
    cases selected : state.candidate free with
    | none => simp [Lifecycle.replaceDue, selected]
    | some unit =>
      have rest := Lifecycle.replaceDue_counters free due (state.replace unit)
      have kept := Progress.replace_counters state.representation.progress unit
      rw [Lifecycle.replaceDue.eq_2, selected]
      simp only [Lifecycle.progress, Lifecycle.replace, Representation.replace, kept.1, kept.2]
        at rest ⊢
      exact rest

def Lifecycle.score (state : Lifecycle shape actions config criterion dimension discounts)
    (active : Vector Bool config.units.count) : Lifecycle shape actions config criterion dimension discounts :=
  let readers := state.consumers.stored
  let utility := fun (unit : Fin config.units.count) (current : UnitState) =>
    current.utility.update config.tester
      (if active[unit.val] then outgoing readers (unitFeature dimension config unit) else .zero)
  { state with representation := state.representation.rescore utility }

theorem Lifecycle.score_eligible (state : Lifecycle shape actions config criterion dimension discounts)
    (active : Vector Bool config.units.count) (free : Bool) :
    (state.score active).eligible free = state.eligible free ∧
      (state.score active).progress.credit = state.progress.credit := by
  constructor
  · funext unit
    simp only [Lifecycle.eligible, Lifecycle.mature, Lifecycle.progress, Lifecycle.score,
      Representation.rescore, Progress.rescore_birth, (Progress.rescore_counters _ _).1]
  · simp only [Lifecycle.progress, Lifecycle.score, Representation.rescore,
      (Progress.rescore_counters _ _).2]

def Lifecycle.withCredit (state : Lifecycle shape actions config criterion dimension discounts)
    (credit : Fin config.tester.period) : Lifecycle shape actions config criterion dimension discounts :=
  { state with representation := state.representation.withCredit credit }

theorem Lifecycle.withCredit_eligible (state : Lifecycle shape actions config criterion dimension discounts)
    (credit : Fin config.tester.period) (free : Bool) :
    (state.withCredit credit).eligible free = state.eligible free ∧
      (state.withCredit credit).progress.credit = credit := by
  have fields := Progress.withCredit_fields state.representation.progress credit
  constructor
  · funext unit
    simp only [Lifecycle.eligible, Lifecycle.mature, Lifecycle.progress, Lifecycle.withCredit,
      Representation.withCredit, fields.1, fields.2.1]
  · simp only [Lifecycle.progress, Lifecycle.withCredit, Representation.withCredit, fields.2.2]

theorem Lifecycle.score_birth (state : Lifecycle shape actions config criterion dimension discounts)
    (active : Vector Bool config.units.count) (unit : Fin config.units.count) :
    (state.score active).progress.units[unit.val].birth = state.progress.units[unit.val].birth := by
  simp only [Lifecycle.progress, Lifecycle.score, Representation.rescore, Progress.rescore_birth]

theorem Lifecycle.withCredit_units (state : Lifecycle shape actions config criterion dimension discounts)
    (credit : Fin config.tester.period) :
    (state.withCredit credit).progress.units = state.progress.units := by
  simp only [Lifecycle.progress, Lifecycle.withCredit, Representation.withCredit,
    (Progress.withCredit_fields _ _).1]

def Lifecycle.accrued (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) : Nat :=
  state.progress.credit.val + state.eligibleCount free

def Tester.due (tester : Tester) (accrued : Nat) : Nat := accrued / tester.period

def Tester.remainder (tester : Tester) (accrued : Nat) : Fin tester.period :=
  ⟨accrued % tester.period, Nat.mod_lt _ tester.positive⟩

def Lifecycle.test (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) :
    Lifecycle shape actions config criterion dimension discounts × List (Fin config.units.count) :=
  let scored := state.score active
  let accrued := scored.accrued free
  Lifecycle.replaceDue free (config.tester.due accrued)
    (scored.withCredit (config.tester.remainder accrued))

theorem due_le (period credit eligible : Nat) (below : credit < period) :
    (credit + eligible) / period ≤ eligible := by
  cases eligible with
  | zero => simp [Nat.div_eq_of_lt below]
  | succ rest =>
    apply Nat.div_le_of_le_mul
    have grow : rest ≤ period * rest := Nat.le_mul_of_pos_left rest (by omega)
    rw [Nat.mul_succ]
    omega

theorem Lifecycle.test_accrual (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) :
    (state.test free active).2.length =
        (state.progress.credit.val + state.eligibleCount free) / config.tester.period ∧
      (state.test free active).1.progress.credit.val =
        (state.progress.credit.val + state.eligibleCount free) % config.tester.period := by
  have scored := state.score_eligible active free
  have count : (state.score active).eligibleCount free = state.eligibleCount free := by
    simp only [Lifecycle.eligibleCount, scored.1]
  have accrued : (state.score active).accrued free =
      state.progress.credit.val + state.eligibleCount free := by
    simp only [Lifecycle.accrued, count, scored.2]
  have credited := (state.score active).withCredit_eligible
    (config.tester.remainder ((state.score active).accrued free)) free
  have creditedCount : ((state.score active).withCredit
      (config.tester.remainder ((state.score active).accrued free))).eligibleCount free =
        state.eligibleCount free := by
    simp only [Lifecycle.eligibleCount, credited.1, scored.1]
  have enough : config.tester.due ((state.score active).accrued free) ≤
      ((state.score active).withCredit
        (config.tester.remainder ((state.score active).accrued free))).eligibleCount free := by
    rw [creditedCount, accrued]
    exact due_le _ _ _ state.progress.credit.isLt
  have length := Lifecycle.replaceDue_length free _ _ enough
  have kept := (Lifecycle.replaceDue_counters free (config.tester.due ((state.score active).accrued free))
    ((state.score active).withCredit (config.tester.remainder ((state.score active).accrued free)))).1
  constructor
  · show (Lifecycle.replaceDue free (config.tester.due ((state.score active).accrued free))
      ((state.score active).withCredit
        (config.tester.remainder ((state.score active).accrued free)))).2.length = _
    rw [length, accrued]
    rfl
  · show (Lifecycle.replaceDue free (config.tester.due ((state.score active).accrued free))
      ((state.score active).withCredit
        (config.tester.remainder ((state.score active).accrued free)))).1.progress.credit.val = _
    rw [kept, credited.2, accrued]
    rfl

theorem Lifecycle.test_balance (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) :
    config.tester.period * (state.test free active).2.length +
        (state.test free active).1.progress.credit.val =
      state.progress.credit.val + state.eligibleCount free := by
  rw [(state.test_accrual free active).1, (state.test_accrual free active).2]
  exact Nat.div_add_mod _ _

theorem Lifecycle.test_unheld (state : Lifecycle shape actions config criterion dimension discounts)
    (active : Vector Bool config.units.count) :
    ∀ unit ∈ (state.test false active).2, state.consumers.holds unit = false :=
  Lifecycle.replaceDue_unheld _ _

theorem Lifecycle.test_preserves (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count)
    (property : Ensemble actions config criterion dimension discounts → Prop)
    (closed : ∀ ensemble feature, property ensemble → property (ensemble.retire feature))
    (holds : property state.consumers) : property (state.test free active).1.consumers :=
  Lifecycle.replaceDue_preserves free property closed _ _ holds

theorem Lifecycle.test_holds (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) :
    (state.test free active).1.consumers.holds = state.consumers.holds :=
  state.test_preserves free active (fun ensemble => ensemble.holds = state.consumers.holds)
    (fun ensemble feature same => by
      funext unit
      rw [Ensemble.retire_holds, same]) rfl

theorem Lifecycle.test_clock (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) :
    (state.test free active).1.progress.clock = state.progress.clock :=
  (Lifecycle.replaceDue_counters free _ _).2

def Lifecycle.advance (state : Lifecycle shape actions config criterion dimension discounts) :
    Lifecycle shape actions config criterion dimension discounts :=
  { state with representation := state.representation.advance }

end Acorn.Features
