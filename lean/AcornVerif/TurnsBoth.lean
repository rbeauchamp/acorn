import AcornVerif.TurnsKeeping

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {family : TurnClass interface} {goals : family.Goals}
  {length : ℕ}

def MastersGridBy (family : TurnClass interface) (goals : family.Goals) (length bound : ℕ)
    {κ μ : Type} (first : family.Index → κ) (second : family.Index → μ)
    (limit horizon returns : ℕ) (admits : family.Index → (ℕ → Bool) → ℕ → Prop)
    (agent : Agent interface) : Prop :=
  ∃ (order : ℕ → Bool) (visit : ℕ) (firsts : Finset κ) (seconds : Finset μ),
    visit < limit ∧ bound < firsts.card ∧ bound < seconds.card ∧
    ∀ one ∈ firsts, ∀ two ∈ seconds, ∃ index, first index = one ∧ second index = two ∧
      ∀ situation : Bool,
        SolvesTurn family goals length (Function.update order visit situation) agent visit
          index ∧
        admits index (Function.update order visit situation) visit ∧
        ∃ later : Finset ℕ, returns ≤ later.card ∧
          ∀ other ∈ later, visit < other ∧ other < horizon ∧
            Function.update order visit situation other = situation ∧
            admits index (Function.update order visit situation) other

variable {κ μ : Type} {first : family.Index → κ} {second : family.Index → μ}
  {bound limit horizon returns : ℕ} {admits : family.Index → (ℕ → Bool) → ℕ → Prop}
  {agent : Agent interface}

theorem MastersGridBy.mono {later : ℕ} (within : limit ≤ later)
    (masters : MastersGridBy family goals length bound first second limit horizon returns admits
      agent) :
    MastersGridBy family goals length bound first second later horizon returns admits agent := by
  obtain ⟨order, visit, firsts, seconds, before, rest⟩ := masters
  exact ⟨order, visit, firsts, seconds, Nat.lt_of_lt_of_le before within, rest⟩

theorem MastersGridBy.solves
    (masters : MastersGridBy family goals length bound first second limit horizon returns admits
      agent) :
    ∃ (order : ℕ → Bool) (visit : ℕ) (index : family.Index), visit < limit ∧
      ∀ situation : Bool, SolvesTurn family goals length (Function.update order visit situation)
        agent visit index := by
  obtain ⟨order, visit, firsts, seconds, before, manyFirst, manySecond, each⟩ := masters
  obtain ⟨one, inFirsts⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manyFirst)
  obtain ⟨two, inSeconds⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manySecond)
  obtain ⟨index, -, -, solved⟩ := each one inFirsts two inSeconds
  exact ⟨order, visit, index, before, fun situation => (solved situation).1⟩

theorem FeedbackDriven.mastersGrid {Φ : Type} {feedback : Percept interface → Φ}
    (blind : FeedbackDriven feedback agent) (mute : Mute feedback family goals)
    (apart : Apart family goals length) :
    ¬ MastersGridBy family goals length bound first second limit horizon returns admits
      agent := by
  intro masters
  obtain ⟨order, visit, index, -, solved⟩ := masters.solves
  exact blind.turn mute apart order visit index solved

theorem MastersGridBy.of_states {other : Agent interface}
    (same : ∀ (index : family.Index) (order : ℕ → Bool) (time : ℕ),
      stateAt (turns (family.world index) (family.start index) order length) agent
          (turnStart (family.world index) (family.start index) order length 0) time =
        stateAt (turns (family.world index) (family.start index) order length) other
          (turnStart (family.world index) (family.start index) order length 0) time)
    (masters : MastersGridBy family goals length bound first second limit horizon returns admits
      agent) :
    MastersGridBy family goals length bound first second limit horizon returns admits other := by
  obtain ⟨order, visit, firsts, seconds, before, manyFirst, manySecond, each⟩ := masters
  refine ⟨order, visit, firsts, seconds, before, manyFirst, manySecond,
    fun one inFirsts two inSeconds => ?_⟩
  obtain ⟨index, isOne, isTwo, solved⟩ := each one inFirsts two inSeconds
  exact ⟨index, isOne, isTwo, fun situation =>
    ⟨(solvesTurn_of_states same _ visit index).mp (solved situation).1, (solved situation).2⟩⟩

theorem aloof_mastersGrid {Φ E Core V : Type} {feedback : Percept interface → Φ}
    (select : E → V → Act interface × E) (core : Core) (seed : E) (prefer : Core → Φ → V)
    (advance : Core → Φ → Act interface → Core)
    (alien : Percept interface → Prop) [DecidablePred alien] (rest : V)
    (never : ∀ (index : family.Index) (state : (family.world index).State),
      ¬ alien ((family.world index).percept state))
    (mute : Mute feedback family goals) (apart : Apart family goals length) :
    ¬ MastersGridBy family goals length bound first second limit horizon returns admits
      (chooser select core seed
        (aloof alien rest (fun inner percept => prefer inner (feedback percept)))
        (fun inner percept action => advance inner (feedback percept) action)) := by
  intro masters
  refine (chooser_stepped feedback select core seed prefer advance).feedbackDriven.mastersGrid
    mute apart (masters.of_states (fun index order time => ?_))
  exact congrArg Prod.fst (aloof_loop select core seed _ _ alien rest
    (turns (family.world index) (family.start index) order length) _
    (fun state => never index state.1) time)

theorem turns_need_grid {reference : World interface} {origin : reference.State}
    (hidden : Conceals (family.side false) goals reference origin)
    (covered : ∀ (actions : ℕ → Act interface) (solved : Finset family.Index),
      (∀ one ∈ solved, ∀ two ∈ solved, first one = first two → one = two) →
      (∀ index ∈ solved,
        (turnGoal goals length index).MetBy (family.start index false) actions) →
      solved.card ≤ bound)
    (free : ExperienceFree agent) :
    ¬ MastersGridBy family goals length bound first second limit horizon returns admits
      agent := by
  classical
  rintro ⟨order, visit, firsts, seconds, -, manyFirst, manySecond, each⟩
  obtain ⟨two, inSeconds⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manySecond)
  obtain ⟨advance, law⟩ := free
  choose pick isOne _ solved using fun (one : κ) (inFirsts : one ∈ firsts) =>
    each one inFirsts two inSeconds
  have image : (firsts.attach.image fun one => pick one.1 one.2).card = firsts.card := by
    rw [Finset.card_image_of_injective _ (fun one other same => Subtype.ext (by
      rw [← isOne one.1 one.2, ← isOne other.1 other.2, same])), Finset.card_attach]
  refine absurd (covered (actionAt reference
    (agent.resume (advanced advance agent.initial (visit * (length + 1)))) origin)
    (firsts.attach.image fun one => pick one.1 one.2) (fun left inLeft right inRight same => ?_)
    (fun index member => ?_)) (by rw [image]; exact Nat.not_le_of_lt manyFirst)
  · obtain ⟨one, -, rfl⟩ := Finset.mem_image.mp inLeft
    obtain ⟨other, -, rfl⟩ := Finset.mem_image.mp inRight
    rw [isOne one.1 one.2, isOne other.1 other.2] at same
    rw [Subtype.ext same]
  · obtain ⟨one, -, rfl⟩ := Finset.mem_image.mp member
    have solves := (solvesTurn_side family goals length order agent visit _ false).mp
      (solved one.1 one.2 false).1
    unfold turnMemory at solves
    rw [experienceFree_memoryAt law] at solves
    exact ((hidden.withLength length).solves_iff _ _).mp solves

theorem MastersGridBy.kept
    (masters : MastersGridBy family goals length bound first second limit horizon returns admits
      agent)
    (keeps : KeepsOn family goals length horizon admits agent) :
    ∃ (order : ℕ → Bool) (visit : ℕ) (firsts : Finset κ) (seconds : Finset μ),
      visit < limit ∧ bound < firsts.card ∧ bound < seconds.card ∧
      ∀ one ∈ firsts, ∀ two ∈ seconds, ∃ index, first index = one ∧ second index = two ∧
        ∀ situation : Bool, ∃ later : Finset ℕ, returns ≤ later.card ∧
          ∀ other ∈ later, visit < other ∧ other < horizon ∧
            Function.update order visit situation other = situation ∧
            SolvesTurn family goals length (Function.update order visit situation) agent
              other index := by
  obtain ⟨order, visit, firsts, seconds, before, manyFirst, manySecond, each⟩ := masters
  refine ⟨order, visit, firsts, seconds, before, manyFirst, manySecond,
    fun one inFirsts two inSeconds => ?_⟩
  obtain ⟨index, isOne, isTwo, solved⟩ := each one inFirsts two inSeconds
  refine ⟨index, isOne, isTwo, fun situation => ?_⟩
  obtain ⟨once, -, later, count, occasions⟩ := solved situation
  refine ⟨later, count, fun other member => ?_⟩
  obtain ⟨after, within, same, admitted⟩ := occasions other member
  exact ⟨after, within, same,
    keeps index (Function.update order visit situation) visit other after within
      (same.trans (Function.update_self visit situation order).symm) once admitted⟩

theorem mastersGrid_of_never (family : TurnClass interface) (goals : family.Goals)
    (length bound : ℕ) {κ μ : Type} (first : family.Index → κ) (second : family.Index → μ)
    (limit horizon returns : ℕ) (agent : Agent interface) :
    ¬ MastersGridBy family goals length bound first second limit horizon returns
      (fun _ _ _ => False) agent := by
  rintro ⟨order, visit, firsts, seconds, -, manyFirst, manySecond, each⟩
  obtain ⟨one, inFirsts⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manyFirst)
  obtain ⟨two, inSeconds⟩ :=
    Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) manySecond)
  obtain ⟨index, -, -, solved⟩ := each one inFirsts two inSeconds
  exact (solved false).2.1

end AcornVerif.Kernel
