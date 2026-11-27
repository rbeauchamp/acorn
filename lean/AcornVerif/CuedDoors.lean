import AcornVerif.Perceiving
import AcornVerif.SituatedClass

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

def key (four : 4 ≤ interface.actions.word.toNat) (situation door : Bool) : Act interface :=
  match situation, door with
  | false, false => ⟨0, by omega⟩
  | false, true => ⟨1, by omega⟩
  | true, false => ⟨2, by omega⟩
  | true, true => ⟨3, by omega⟩

theorem key_inj (four : 4 ≤ interface.actions.word.toNat) {situation door other gate : Bool}
    (same : (key four situation door).val = (key four other gate).val) :
    situation = other ∧ door = gate := by
  cases situation <;> cases door <;> cases other <;> cases gate <;> simp [key] at same ⊢

def cued (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (situation door : Bool) : World interface where
  State := Option Bool
  step := fun state action =>
    match state with
    | none => some (decide (action.val = (key four situation door).val))
    | some outcome => some outcome
  percept := fun state =>
    match state with
    | some true => win
    | _ => quiet situation

theorem cued_quiet (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (situation door : Bool) (state : Option Bool)
    (unmet : state ≠ some true) :
    (cued four quiet win situation door).percept state = quiet situation := by
  match state, unmet with
  | none, _ => rfl
  | some false, _ => rfl
  | some true, wrong => exact absurd rfl wrong

abbrev cuedDoors (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) : WorldClass interface where
  Index := Bool × Bool
  world := fun index => cued four quiet win index.1 index.2
  start := fun _ => (none : Option Bool)

def cuedGoals (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) : (cuedDoors four quiet win).Goals :=
  fun _ => ⟨fun (state : Option Bool) => state = some true, 1⟩

theorem cued_met (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (index : Bool × Bool) (actions : ℕ → Act interface)
    (met : (visitGoals (cuedGoals four quiet win) 1 index).MetBy
      ((cuedDoors four quiet win).start index) actions) :
    (actions 0).val = (key four index.1 index.2).val := by
  obtain ⟨time, low, high, reached⟩ := met
  have one : time = 1 := Nat.le_antisymm high low
  subst one
  have outcome : some (decide ((actions 0).val = (key four index.1 index.2).val)) = some true :=
    reached
  exact of_decide_eq_true (Option.some.inj outcome)

theorem cued_covered (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) :
    Covered (cuedDoors four quiet win) (visitGoals (cuedGoals four quiet win) 1) 1 := by
  intro actions solved each
  refine Finset.card_le_one.mpr (fun first inFirst second inSecond => ?_)
  have keyFirst := cued_met four quiet win first actions (each first inFirst)
  have keySecond := cued_met four quiet win second actions (each second inSecond)
  obtain ⟨situation, door⟩ := key_inj four (keyFirst.symm.trans keySecond)
  exact Prod.ext situation door

theorem cued_conceals (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (canon : Percept interface → Percept interface)
    (flat : ∀ situation, canon (quiet situation) = canon (quiet false)) :
    Conceals ((cuedDoors four quiet win).masked canon)
      (maskedGoals (cuedGoals four quiet win) canon)
      (firstActionWorld interface (canon (quiet false))) none := by
  intro (index : Bool × Bool) actions time unmet
  have same := path_masked (cued four quiet win index.1 index.2) canon none actions time
  have still : path (cued four quiet win index.1 index.2) none actions time ≠ some true := by
    cases time with
    | zero =>
      intro wrong
      have bad : (none : Option Bool) = some true := wrong
      cases bad
    | succ time =>
      intro wrong
      exact unmet (time + 1) (Nat.succ_le_succ (Nat.zero_le time)) (Nat.le_refl _)
        (same.trans wrong)
  have shown := cued_quiet four quiet win index.1 index.2 _ still
  exact (congrArg (fun state => canon
    ((cued four quiet win index.1 index.2).percept state)) same).trans
      ((congrArg canon shown).trans (flat index.1))

def cuedNeeded {Φ : Type} (feedback : Percept interface → Φ)
    (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (canon : Percept interface → Percept interface)
    (keeps : ∀ percept, feedback (canon percept) = feedback percept)
    (flat : ∀ situation, canon (quiet situation) = canon (quiet false)) :
    PerceptNeeded feedback (cuedDoors four quiet win) (cuedGoals four quiet win) 1 3 2 where
  canon := canon
  keeps := keeps
  reference := firstActionWorld interface (canon (quiet false))
  origin := none
  conceals := cued_conceals four quiet win canon flat
  cover := 1
  covered := cued_covered four quiet win
  short := by decide

def cuedAll : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

theorem cuedAll_mem (index : Bool × Bool) : index ∈ cuedAll := by
  obtain ⟨situation, door⟩ := index
  cases situation <;> cases door <;> decide

theorem cuedAll_large : ∑ _situation : Bool, 1 < cuedAll.toFinset.card := by decide

def cuedSituated (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) :
    SituatedClass (cuedDoors four quiet win) (cuedGoals four quiet win) 1 Bool where
  situation := fun (index : Bool × Bool) => index.1
  reference := fun here => firstActionWorld interface (quiet here)
  origin := fun _ => none
  conceals := by
    rintro here ⟨⟨situation, door⟩, inside⟩ actions time unmet
    have same : situation = here := inside
    subst same
    have still : path (cued four quiet win situation door) none actions time ≠ some true := by
      cases time with
      | zero =>
        intro wrong
        have bad : (none : Option Bool) = some true := wrong
        cases bad
      | succ time =>
        exact unmet (time + 1) (Nat.succ_le_succ (Nat.zero_le time)) (Nat.le_refl _)
    exact cued_quiet four quiet win situation door _ still
  cover := fun _ => 1
  covered := by
    intro here actions solved each
    refine Finset.card_le_one.mpr (fun first inFirst second inSecond => ?_)
    have keyFirst := cued_met four quiet win first.1 actions (each first inFirst)
    have keySecond := cued_met four quiet win second.1 actions (each second inSecond)
    obtain ⟨situation, door⟩ := key_inj four (keyFirst.symm.trans keySecond)
    exact Subtype.ext (Prod.ext situation door)
  members := cuedAll.toFinset
  large := cuedAll_large

theorem cued_need (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) {agent : Agent interface} (free : ExperienceFree agent)
    (visit : ℕ) (solved : Finset (Bool × Bool))
    (each : ∀ index ∈ solved, SolvesOnVisit (cuedDoors four quiet win)
      (cuedGoals four quiet win) 1 agent visit index) :
    solved.card ≤ 2 :=
  (cuedSituated four quiet win).need free visit solved each

end AcornVerif.Kernel
