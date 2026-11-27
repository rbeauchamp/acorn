import AcornVerif.Replay
import AcornVerif.Turns

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {Φ : Type}

theorem replay_steppedBy (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) :
    Stepped signal (replay interface length signal explore) :=
  ⟨fun memory shown =>
    (memory.choose (memory.record shown) explore,
      if memory.step < length then
        ⟨memory.step + 1, memory.choose (memory.record shown) explore :: memory.taken,
          memory.count, memory.record shown⟩
      else ⟨0, [], memory.count + 1, memory.record shown⟩),
    fun _ _ => rfl⟩

def rival (reference : World interface) (origin : reference.State) (length : ℕ)
    (signal : Percept interface → Bool) (agent : Agent interface) : Agent interface :=
  replay interface length signal
    (fun visit step => visitActions reference origin length agent visit step)

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

theorem replay_dominates (hidden : Conceals family goals reference origin) (length : ℕ)
    (signal : Percept interface → Bool)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (agent : Agent interface) :
    Stepped signal (rival reference origin length signal agent) ∧
      (∀ index visit, SolvesOnVisit family goals length agent visit index →
        SolvesOnVisit family goals length (rival reference origin length signal agent) visit
          index) ∧
      Retains family goals length (rival reference origin length signal agent) := by
  refine ⟨replay_steppedBy _ _ _, fun index visit solved => ?_,
    fun index visit later after solved => ?_⟩
  · obtain ⟨found, before, time, low, high, met⟩ :=
      (hidden.found_within length agent index (visit + 1)).mp
        ⟨visit, Nat.lt_succ_self visit, solved⟩
    exact replay_solves_explored family goals length signal _ index (decodes index) found visit
      (Nat.le_of_lt_succ before) ⟨time, low, high, met⟩
  · exact replay_solves family goals length signal _ index (decodes index) visit later after
      solved

theorem rival_separates (hidden : Conceals family goals reference origin) (length : ℕ)
    (signal : Percept interface → Bool)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    {agent : Agent interface} {bound limit : ℕ} {counted : List family.Index}
    (separates : SeparatesBy family goals length bound counted limit agent) :
    SeparatesBy family goals length bound counted limit
        (rival reference origin length signal agent) ∧
      ∀ horizon, RetainsBut family goals length horizon 0
        (rival reference origin length signal agent) := by
  obtain ⟨-, dominates, retains⟩ := replay_dominates hidden length signal decodes agent
  obtain ⟨visit, solved, before, many, each⟩ := separates
  exact ⟨⟨visit, solved, before, many, fun index member =>
    ⟨(each index member).1, dominates index visit (each index member).2⟩⟩,
    fun horizon => retains.but horizon⟩

abbrev World.masked (world : World interface) (canon : Percept interface → Percept interface) :
    World interface where
  State := world.State
  step := world.step
  percept := fun state => canon (world.percept state)

abbrev WorldClass.masked (family : WorldClass interface)
    (canon : Percept interface → Percept interface) : WorldClass interface where
  Index := family.Index
  world := fun index => (family.world index).masked canon
  start := fun index => family.start index

def maskedGoals {family : WorldClass interface} (goals : family.Goals)
    (canon : Percept interface → Percept interface) : (family.masked canon).Goals :=
  fun index => ⟨(goals index).satisfied, (goals index).cap⟩

theorem path_masked (world : World interface) (canon : Percept interface → Percept interface)
    (start : world.State) (actions : ℕ → Act interface) (time : ℕ) :
    path (world.masked canon) start actions time = path world start actions time := by
  induction time with
  | zero => rfl
  | succ time ih => exact congrArg (fun state => world.step state (actions time)) ih

theorem FeedbackDriven.masked_stateAt {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (canon : Percept interface → Percept interface)
    (keeps : ∀ percept, feedback (canon percept) = feedback percept)
    (world : World interface) (start : world.State) (time : ℕ) :
    stateAt (world.masked canon) agent start time = stateAt world agent start time := by
  induction time using Nat.strong_induction_on with
  | _ time ih =>
    cases time with
    | zero => rfl
    | succ time =>
      have same : actionAt (world.masked canon) agent start time =
          actionAt world agent start time :=
        (actionAt_response (world.masked canon) agent start time).trans
          ((blind _ _ time (fun earlier within =>
            (keeps _).trans (congrArg (fun state => feedback (world.percept state))
              (ih earlier (Nat.lt_succ_of_le within))))).trans
            (actionAt_response world agent start time).symm)
      change world.step (stateAt (world.masked canon) agent start time)
          (actionAt (world.masked canon) agent start time) =
        world.step (stateAt world agent start time) (actionAt world agent start time)
      rw [same, ih time (Nat.lt_succ_self time)]

theorem masked_visits (world : World interface) (canon : Percept interface → Percept interface)
    (start : world.State) (length : ℕ) :
    visits (world.masked canon) start length = (visits world start length).masked canon := rfl

theorem FeedbackDriven.masked_solves {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (canon : Percept interface → Percept interface)
    (keeps : ∀ percept, feedback (canon percept) = feedback percept)
    (family : WorldClass interface) (goals : family.Goals) (length visit : ℕ)
    (index : family.Index) :
    SolvesOnVisit (family.masked canon) (maskedGoals goals canon) length agent visit index ↔
      SolvesOnVisit family goals length agent visit index := by
  have same := fun time => blind.masked_stateAt canon keeps
    (visits (family.world index) (family.start index) length)
    (visitStart (family.world index) (family.start index) length) time
  constructor
  · rintro ⟨step, low, high, met⟩
    exact ⟨step, low, high, Eq.mp (congrArg
      (fun state : (family.world index).State × Fin (length + 1) =>
        (goals index).satisfied state.1) (same _)) met⟩
  · rintro ⟨step, low, high, met⟩
    exact ⟨step, low, high, Eq.mpr (congrArg
      (fun state : (family.world index).State × Fin (length + 1) =>
        (goals index).satisfied state.1) (same _)) met⟩

theorem covered_masked (canon : Percept interface → Percept interface) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound) :
    Covered (family.masked canon) (visitGoals (maskedGoals goals canon) length) bound := by
  intro actions solved each
  refine covered actions solved (fun index member => ?_)
  obtain ⟨time, low, high, met⟩ := each index member
  exact ⟨time, low, high, Eq.mp (congrArg (fun state => (goals index).satisfied state)
    (path_masked (family.world index) canon (family.start index) actions time)) met⟩

structure PerceptNeeded (feedback : Percept interface → Φ) (family : WorldClass interface)
    (goals : family.Goals) (length bound limit : ℕ) where
  canon : Percept interface → Percept interface
  keeps : ∀ percept, feedback (canon percept) = feedback percept
  reference : World interface
  origin : reference.State
  conceals : Conceals (family.masked canon) (maskedGoals goals canon) reference origin
  cover : ℕ
  covered : Covered family (visitGoals goals length) cover
  short : limit * cover ≤ bound

theorem PerceptNeeded.need {feedback : Percept interface → Φ} {length bound limit : ℕ}
    (needed : PerceptNeeded feedback family goals length bound limit) {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (counted : List family.Index) :
    ¬ SeparatesBy family goals length bound counted limit agent := by
  rintro ⟨visit, solved, before, many, each⟩
  have found := visits_ever needed.conceals (covered_masked needed.canon needed.covered) agent
    (visit + 1) solved (fun index member => ⟨visit, Nat.lt_succ_self visit,
      (blind.masked_solves needed.canon needed.keeps family goals length visit index).mpr
        (each index member).2⟩)
  exact absurd many (Nat.not_lt.mpr (found.trans
    ((Nat.mul_le_mul_right needed.cover (Nat.succ_le_of_lt before)).trans needed.short)))

theorem not_perceptNeeded_of_conceals (hidden : Conceals family goals reference origin)
    (length : ℕ) (signal : Percept interface → Bool)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    {agent : Agent interface} {bound limit : ℕ} {counted : List family.Index}
    (separates : SeparatesBy family goals length bound counted limit agent) :
    ¬ Nonempty (PerceptNeeded signal family goals length bound limit) := by
  rintro ⟨needed⟩
  exact needed.need (replay_steppedBy length signal _).feedbackDriven counted
    (rival_separates hidden length signal decodes separates).1

structure Run (interface : Interface) where
  world : World interface
  start : world.State

def RunsAsDriven {ι : Type} (feedback : Percept interface → Φ) (run : ι → Run interface)
    (agent : Agent interface) : Prop :=
  ∃ shadow : Agent interface, FeedbackDriven feedback shadow ∧ ∀ index time,
    stateAt (run index).world agent (run index).start time =
      stateAt (run index).world shadow (run index).start time

def PerceivingNeeded {ι : Type} (feedback : Percept interface → Φ) (run : ι → Run interface)
    (promise : Agent interface → Prop) : Prop :=
  ∀ agent, RunsAsDriven feedback run agent → ¬ promise agent

def PerceivingDecides {ι : Type} (feedback : Percept interface → Φ) (run : ι → Run interface)
    (promise : Agent interface → Prop) : Prop :=
  PerceivingNeeded feedback run promise ∧ ∃ agent, promise agent

theorem not_decides_of_unmet {ι : Type} (feedback : Percept interface → Φ)
    (run : ι → Run interface) {promise : Agent interface → Prop}
    (unmet : ∀ agent, ¬ promise agent) :
    PerceivingNeeded feedback run promise ∧ ¬ PerceivingDecides feedback run promise :=
  ⟨fun agent _ => unmet agent, fun decides => decides.2.elim unmet⟩

theorem FeedbackDriven.runsAsDriven {ι : Type} {feedback : Percept interface → Φ}
    {agent : Agent interface} (blind : FeedbackDriven feedback agent) (run : ι → Run interface) :
    RunsAsDriven feedback run agent :=
  ⟨agent, blind, fun _ _ => rfl⟩

def visitRuns (family : WorldClass interface) (length : ℕ) : family.Index → Run interface :=
  fun index => ⟨visits (family.world index) (family.start index) length,
    visitStart (family.world index) (family.start index) length⟩

theorem PerceptNeeded.perceivingNeeded {feedback : Percept interface → Φ}
    {length bound limit : ℕ} (needed : PerceptNeeded feedback family goals length bound limit)
    (counted : List family.Index) :
    PerceivingNeeded feedback (visitRuns family length)
      (SeparatesBy family goals length bound counted limit) := by
  rintro agent ⟨shadow, blind, same⟩ ⟨visit, solved, before, many, each⟩
  refine needed.need blind counted ⟨visit, solved, before, many, fun index member =>
    ⟨(each index member).1, ?_⟩⟩
  obtain ⟨step, low, high, met⟩ := (each index member).2
  exact ⟨step, low, high, Eq.mp (congrArg
    (fun state : (family.world index).State × Fin (length + 1) =>
      (goals index).satisfied state.1) (same index _)) met⟩

theorem not_decides_of_conceals (hidden : Conceals family goals reference origin) (length : ℕ)
    (signal : Percept interface → Bool)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (bound limit : ℕ) (counted : List family.Index) :
    ¬ PerceivingDecides signal (visitRuns family length)
      (SeparatesBy family goals length bound counted limit) := by
  rintro ⟨needed, agent, separates⟩
  have blind : FeedbackDriven signal (rival reference origin length signal agent) :=
    (replay_steppedBy length signal _).feedbackDriven
  exact needed _ (blind.runsAsDriven _)
    (rival_separates hidden length signal decodes separates).1

theorem aloof_runsAsDriven {ι E V Core : Type} (feedback : Percept interface → Φ)
    (select : E → V → Act interface × E) (core : Core) (seed : E) (prefer : Core → Φ → V)
    (advance : Core → Φ → Act interface → Core) (alien : Percept interface → Prop)
    [DecidablePred alien] (rest : V) (run : ι → Run interface)
    (never : ∀ index state, ¬ alien ((run index).world.percept state)) :
    RunsAsDriven feedback run
      (chooser select core seed
        (aloof alien rest (fun inner percept => prefer inner (feedback percept)))
        (fun inner percept action => advance inner (feedback percept) action)) :=
  ⟨chooser select core seed (fun inner percept => prefer inner (feedback percept))
      (fun inner percept action => advance inner (feedback percept) action),
    (chooser_stepped feedback select core seed prefer advance).feedbackDriven,
    fun index time => congrArg Prod.fst
      (aloof_loop select core seed (fun inner percept => prefer inner (feedback percept))
        (fun inner percept action => advance inner (feedback percept) action) alien rest
        (run index).world (run index).start (never index) time)⟩

def turnRuns (family : TurnClass interface) (length : ℕ) :
    family.Index × (ℕ → Bool) → Run interface :=
  fun pair => ⟨turns (family.world pair.1) (family.start pair.1) pair.2 length,
    turnStart (family.world pair.1) (family.start pair.1) pair.2 length 0⟩

theorem forks_perceivingNeeded {feedback : Percept interface → Φ} {family : TurnClass interface}
    {goals : family.Goals} {length : ℕ} (mute : Mute feedback family goals)
    (apart : Apart family goals length) (bound limit : ℕ) {κ : Type} (key : family.Index → κ) :
    PerceivingNeeded feedback (turnRuns family length)
      (MastersBy family goals length bound key limit) := by
  rintro agent ⟨shadow, blind, same⟩ masters
  exact blind.masters mute apart bound limit key
    (MastersBy.of_states (fun index order time => same (index, order) time) masters)

theorem not_decides_before_zero {ι : Type} (feedback : Percept interface → Φ)
    (run : ι → Run interface) (family : TurnClass interface) (goals : family.Goals)
    (length bound : ℕ) {κ : Type} (key : family.Index → κ) :
    PerceivingNeeded feedback run (MastersBy family goals length bound key 0) ∧
      ¬ PerceivingDecides feedback run (MastersBy family goals length bound key 0) :=
  not_decides_of_unmet feedback run (fun _ masters => by
    obtain ⟨_, _, _, before, _⟩ := masters
    exact Nat.not_lt_zero _ before)

end AcornVerif.Kernel
