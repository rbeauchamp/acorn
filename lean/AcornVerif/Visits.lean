import AcornVerif.Concealment
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

def Agent.resume (agent : Agent interface) (memory : agent.Memory) : Agent interface :=
  { agent with initial := memory }

theorem loop_add (world : World interface) (agent : Agent interface) (start : world.State)
    (time later : ℕ) :
    loop world agent start (time + later) =
      loop world (agent.resume (memoryAt world agent start time))
        (stateAt world agent start time) later := by
  induction later with
  | zero => rfl
  | succ later ih => exact congrArg (interact world agent) ih

theorem stateAt_add (world : World interface) (agent : Agent interface) (start : world.State)
    (time later : ℕ) :
    stateAt world agent start (time + later) =
      stateAt world (agent.resume (memoryAt world agent start time))
        (stateAt world agent start time) later :=
  congrArg Prod.fst (loop_add world agent start time later)

theorem memoryAt_add (world : World interface) (agent : Agent interface) (start : world.State)
    (time later : ℕ) :
    memoryAt world agent start (time + later) =
      memoryAt world (agent.resume (memoryAt world agent start time))
        (stateAt world agent start time) later :=
  congrArg Prod.snd (loop_add world agent start time later)

theorem experienceFree_memoryAt {agent : Agent interface} {advance : agent.Memory → agent.Memory}
    (law : ∀ memory percept, (agent.act memory percept).2 = advance memory)
    (world : World interface) (start : world.State) (time : ℕ) :
    memoryAt world agent start time = advanced advance agent.initial time := by
  induction time with
  | zero => rfl
  | succ time ih => exact (law _ _).trans (congrArg advance ih)

def visits (world : World interface) (start : world.State) (length : ℕ) : World interface where
  State := world.State × Fin (length + 1)
  step := fun state action =>
    if within : state.2.val < length then
      (world.step state.1 action, ⟨state.2.val + 1, by omega⟩)
    else (start, ⟨0, Nat.succ_pos length⟩)
  percept := fun state => world.percept state.1

def visitStart (world : World interface) (start : world.State) (length : ℕ) :
    (visits world start length).State :=
  (start, ⟨0, Nat.succ_pos length⟩)

theorem visits_loop (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (time : ℕ) (within : time ≤ length) :
    loop (visits world start length) agent (visitStart world start length) time =
      (((loop world agent start time).1, ⟨time, Nat.lt_succ_of_le within⟩),
        (loop world agent start time).2) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have earlier := ih (Nat.le_of_succ_le within)
    have short : time < length := Nat.lt_of_succ_le within
    change interact (visits world start length) agent
        (loop (visits world start length) agent (visitStart world start length) time) = _
    rw [earlier]
    simp only [interact, visits, dite_eq_left short]
    rfl

theorem visits_return (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) :
    stateAt (visits world start length) agent (visitStart world start length) (length + 1) =
      visitStart world start length := by
  have last : stateAt (visits world start length) agent (visitStart world start length) length =
      ((loop world agent start length).1, ⟨length, Nat.lt_succ_self length⟩) :=
    congrArg Prod.fst (visits_loop world start length agent length (Nat.le_refl length))
  change (visits world start length).step
      (stateAt (visits world start length) agent (visitStart world start length) length)
      (actionAt (visits world start length) agent (visitStart world start length) length) = _
  rw [last]
  simp only [visits, dite_eq_right (Nat.lt_irrefl length)]
  rfl

theorem visits_period (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (count : ℕ) :
    stateAt (visits world start length) agent (visitStart world start length)
        (count * (length + 1)) =
      visitStart world start length := by
  induction count with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ count ih =>
    rw [Nat.add_mul, Nat.one_mul, stateAt_add, ih]
    exact visits_return world start length _

theorem visits_counter (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (count step : ℕ) (within : step ≤ length) :
    (stateAt (visits world start length) agent (visitStart world start length)
      (count * (length + 1) + step)).2.val = step := by
  rw [stateAt_add, visits_period]
  exact congrArg (fun state : (visits world start length).State => state.2.val)
    (congrArg Prod.fst (visits_loop world start length _ step within))

theorem visits_state (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (count step : ℕ) (within : step ≤ length) :
    (stateAt (visits world start length) agent (visitStart world start length)
        (count * (length + 1) + step)).1 =
      stateAt world (agent.resume (memoryAt (visits world start length) agent
        (visitStart world start length) (count * (length + 1)))) start step := by
  rw [stateAt_add, visits_period]
  exact congrArg Prod.fst (congrArg Prod.fst (visits_loop world start length _ step within))

theorem visits_step (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (time : ℕ) (within : time < length) :
    (stateAt (visits world start length) agent (visitStart world start length) (time + 1)).1 =
      world.step
        (stateAt (visits world start length) agent (visitStart world start length) time).1
        (actionAt (visits world start length) agent (visitStart world start length) time) := by
  have counter : (stateAt (visits world start length) agent (visitStart world start length)
      time).2.val = time :=
    congrArg (fun pair => pair.1.2.val)
      (visits_loop world start length agent time (Nat.le_of_lt within))
  exact congrArg Prod.fst (dite_eq_left (lt_of_eq_of_lt counter within))

theorem visits_percept (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (origin : (visits world start length).State) (time : ℕ) :
    perceptAt (visits world start length) agent origin time =
      world.percept (stateAt (visits world start length) agent origin time).1 := rfl

def visitGoals {family : WorldClass interface} (goals : family.Goals) (length : ℕ) :
    family.Goals :=
  fun index => ⟨(goals index).satisfied, length⟩

def SolvesOnVisit (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (agent : Agent interface) (count : ℕ) (index : family.Index) : Prop :=
  ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
    (stateAt (visits (family.world index) (family.start index) length) agent
      (visitStart (family.world index) (family.start index) length)
      (count * (length + 1) + step)).1

theorem solvesOnVisit_iff (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (agent : Agent interface) (count : ℕ) (index : family.Index) :
    SolvesOnVisit family goals length agent count index ↔
      Solves family (visitGoals goals length)
        (agent.resume (memoryAt (visits (family.world index) (family.start index) length) agent
          (visitStart (family.world index) (family.start index) length)
          (count * (length + 1))))
        index := by
  have inner := visits_state (family.world index) (family.start index) length agent count
  constructor
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    change (goals index).satisfied _
    rw [← inner step high]
    exact met
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    rw [inner step high]
    exact met

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

theorem Conceals.withLength (hidden : Conceals family goals reference origin) (length : ℕ) :
    Conceals family (visitGoals goals length) reference origin :=
  hidden

theorem visits_need (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound)
    {agent : Agent interface} (free : ExperienceFree agent) (count : ℕ)
    (solved : Finset family.Index)
    (each : ∀ index ∈ solved, SolvesOnVisit family goals length agent count index) :
    solved.card ≤ bound := by
  obtain ⟨advance, law⟩ := free
  refine (hidden.withLength length).need covered
    (agent.resume (advanced advance agent.initial (count * (length + 1)))) trivial solved
    (fun index member => ?_)
  have solves := (solvesOnVisit_iff family goals length agent count index).mp (each index member)
  rwa [experienceFree_memoryAt law] at solves

theorem Conceals.visit_memory (hidden : Conceals family goals reference origin) (length : ℕ)
    (agent : Agent interface) (index : family.Index)
    (unmet : ∀ step, 1 ≤ step → step ≤ length → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) step)) :
    memoryAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length) (length + 1) =
      memoryAt (visits reference origin length) agent (visitStart reference origin length)
        (length + 1) := by
  obtain ⟨memory, actions⟩ := hidden.agree agent index length unmet
  have percept := hidden.perceptAt_eq agent index length unmet
    (fun step before => actions step (Nat.le_of_lt before))
  have member := visits_loop (family.world index) (family.start index) length agent length
    (Nat.le_refl length)
  have base := visits_loop reference origin length agent length (Nat.le_refl length)
  have memberMemory : memoryAt (visits (family.world index) (family.start index) length) agent
      (visitStart (family.world index) (family.start index) length) length =
        memoryAt (family.world index) agent (family.start index) length :=
    congrArg Prod.snd member
  have memberPercept : perceptAt (visits (family.world index) (family.start index) length) agent
      (visitStart (family.world index) (family.start index) length) length =
        perceptAt (family.world index) agent (family.start index) length :=
    congrArg (fun pair : (visits (family.world index) (family.start index) length).State ×
      agent.Memory => (family.world index).percept pair.1.1) member
  have baseMemory : memoryAt (visits reference origin length) agent
      (visitStart reference origin length) length = memoryAt reference agent origin length :=
    congrArg Prod.snd base
  have basePercept : perceptAt (visits reference origin length) agent
      (visitStart reference origin length) length = perceptAt reference agent origin length :=
    congrArg (fun pair : (visits reference origin length).State × agent.Memory =>
      reference.percept pair.1.1) base
  change (agent.act
      (memoryAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length) length)
      (perceptAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length) length)).2 =
    (agent.act
      (memoryAt (visits reference origin length) agent (visitStart reference origin length) length)
      (perceptAt (visits reference origin length) agent (visitStart reference origin length)
        length)).2
  rw [memberMemory, memberPercept, baseMemory, basePercept, memory, percept]

theorem Conceals.visits_memory (hidden : Conceals family goals reference origin) (length : ℕ)
    (agent : Agent interface) (index : family.Index) (count : ℕ)
    (unsolved : ∀ earlier, earlier < count →
      ¬ SolvesOnVisit family goals length agent earlier index) :
    memoryAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length) (count * (length + 1)) =
      memoryAt (visits reference origin length) agent (visitStart reference origin length)
        (count * (length + 1)) := by
  induction count with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ count ih =>
    have same := ih (fun earlier before => unsolved earlier (Nat.lt_succ_of_lt before))
    have missed := unsolved count (Nat.lt_succ_self count)
    rw [solvesOnVisit_iff] at missed
    have memberSplit := memoryAt_add (visits (family.world index) (family.start index) length)
      agent (visitStart (family.world index) (family.start index) length)
      (count * (length + 1)) (length + 1)
    have baseSplit := memoryAt_add (visits reference origin length) agent
      (visitStart reference origin length) (count * (length + 1)) (length + 1)
    rw [visits_period] at memberSplit baseSplit
    rw [Nat.add_mul, Nat.one_mul, memberSplit, baseSplit]
    rw [same] at missed ⊢
    exact hidden.visit_memory length _ index (fun step low high met =>
      missed ⟨step, low, high, met⟩)

def visitActions (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (count : ℕ) : ℕ → Act interface :=
  fun step => actionAt (visits world start length) agent (visitStart world start length)
    (count * (length + 1) + step)

theorem visitActions_eq (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (count step : ℕ) (within : step ≤ length) :
    visitActions world start length agent count step =
      actionAt world (agent.resume (memoryAt (visits world start length) agent
        (visitStart world start length) (count * (length + 1)))) start step := by
  have split := loop_add (visits world start length) agent (visitStart world start length)
    (count * (length + 1)) step
  rw [visits_period] at split
  have inner := visits_loop world start length (agent.resume (memoryAt (visits world start length)
    agent (visitStart world start length) (count * (length + 1)))) step within
  change (agent.act (loop (visits world start length) agent (visitStart world start length)
      (count * (length + 1) + step)).2
    ((visits world start length).percept (loop (visits world start length) agent
      (visitStart world start length) (count * (length + 1) + step)).1)).1 = _
  rw [split, inner]
  rfl

theorem Conceals.solvesOnVisit_iff_met (hidden : Conceals family goals reference origin)
    (length : ℕ) (agent : Agent interface) (index : family.Index) (count : ℕ)
    (unsolved : ∀ earlier, earlier < count →
      ¬ SolvesOnVisit family goals length agent earlier index) :
    SolvesOnVisit family goals length agent count index ↔
      (visitGoals goals length index).MetBy (family.start index)
        (visitActions reference origin length agent count) := by
  rw [solvesOnVisit_iff, hidden.visits_memory length agent index count unsolved,
    (hidden.withLength length).solves_iff]
  have same : ∀ time, time ≤ length →
      path (family.world index) (family.start index)
          (actionAt reference (agent.resume (memoryAt (visits reference origin length) agent
            (visitStart reference origin length) (count * (length + 1)))) origin) time =
        path (family.world index) (family.start index)
          (visitActions reference origin length agent count) time :=
    fun time within => path_congr _ _ _ _ time (fun step before =>
      (visitActions_eq reference origin length agent count step (by omega)).symm)
  constructor
  · rintro ⟨time, low, high, met⟩
    refine ⟨time, low, high, ?_⟩
    rw [← same time high]
    exact met
  · rintro ⟨time, low, high, met⟩
    refine ⟨time, low, high, ?_⟩
    rw [same time high]
    exact met

theorem Conceals.found_within (hidden : Conceals family goals reference origin) (length : ℕ)
    (agent : Agent interface) (index : family.Index) (count : ℕ) :
    (∃ visit, visit < count ∧ SolvesOnVisit family goals length agent visit index) ↔
      ∃ visit, visit < count ∧ (visitGoals goals length index).MetBy (family.start index)
        (visitActions reference origin length agent visit) := by
  classical
  constructor
  · rintro ⟨visit, before, solved⟩
    have once : ∃ visit, SolvesOnVisit family goals length agent visit index := ⟨visit, solved⟩
    exact ⟨Nat.find once, Nat.lt_of_le_of_lt (Nat.find_min' once solved) before,
      (hidden.solvesOnVisit_iff_met length agent index (Nat.find once)
        (fun earlier sooner => Nat.find_min once sooner)).mp (Nat.find_spec once)⟩
  · rintro ⟨visit, before, met⟩
    by_cases sooner : ∃ earlier, earlier < visit ∧
        SolvesOnVisit family goals length agent earlier index
    · obtain ⟨earlier, early, solved⟩ := sooner
      exact ⟨earlier, Nat.lt_trans early before, solved⟩
    · exact ⟨visit, before, (hidden.solvesOnVisit_iff_met length agent index visit
        (fun earlier early solved => sooner ⟨earlier, early, solved⟩)).mpr met⟩

theorem Conceals.found_iff (hidden : Conceals family goals reference origin) (length : ℕ)
    (agent : Agent interface) (index : family.Index) :
    (∃ visit, SolvesOnVisit family goals length agent visit index) ↔
      ∃ visit, (visitGoals goals length index).MetBy (family.start index)
        (visitActions reference origin length agent visit) := by
  constructor
  · rintro ⟨visit, solved⟩
    obtain ⟨found, -, met⟩ := (hidden.found_within length agent index (visit + 1)).mp
      ⟨visit, Nat.lt_succ_self visit, solved⟩
    exact ⟨found, met⟩
  · rintro ⟨visit, met⟩
    obtain ⟨found, -, solved⟩ := (hidden.found_within length agent index (visit + 1)).mpr
      ⟨visit, Nat.lt_succ_self visit, met⟩
    exact ⟨found, solved⟩

theorem visits_first_success (hidden : Conceals family goals reference origin)
    {length bound : ℕ} (covered : Covered family (visitGoals goals length) bound)
    (agent : Agent interface) (count : ℕ) (solved : Finset family.Index)
    (each : ∀ index ∈ solved, SolvesOnVisit family goals length agent count index ∧
      ∀ earlier, earlier < count → ¬ SolvesOnVisit family goals length agent earlier index) :
    solved.card ≤ bound := by
  refine (hidden.withLength length).need covered
    (agent.resume (memoryAt (visits reference origin length) agent
      (visitStart reference origin length) (count * (length + 1)))) trivial solved
    (fun index member => ?_)
  have solves := (solvesOnVisit_iff family goals length agent count index).mp
    (each index member).1
  rwa [hidden.visits_memory length agent index count (each index member).2] at solves

theorem visits_first (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound) (agent : Agent interface)
    (solved : Finset family.Index)
    (each : ∀ index ∈ solved, SolvesOnVisit family goals length agent 0 index) :
    solved.card ≤ bound :=
  visits_first_success hidden covered agent 0 solved
    (fun index member => ⟨each index member, fun _ before => absurd before (Nat.not_lt_zero _)⟩)

theorem visits_ever (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound) (agent : Agent interface)
    (count : ℕ) (solved : Finset family.Index)
    (each : ∀ index ∈ solved, ∃ earlier, earlier < count ∧
      SolvesOnVisit family goals length agent earlier index) :
    solved.card ≤ count * bound := by
  classical
  let first : family.Index → ℕ := fun index =>
    if once : ∃ earlier, SolvesOnVisit family goals length agent earlier index then
      Nat.find once else count
  have firstOf : ∀ index
      (once : ∃ earlier, SolvesOnVisit family goals length agent earlier index),
      first index = Nat.find once := fun index once => dite_eq_left once
  have cover : solved ⊆ (Finset.range count).biUnion
      (fun visit => solved.filter (fun index => first index = visit)) := by
    intro index member
    obtain ⟨earlier, before, solves⟩ := each index member
    have once : ∃ earlier, SolvesOnVisit family goals length agent earlier index :=
      ⟨earlier, solves⟩
    have least : Nat.find once ≤ earlier := Nat.find_min' once solves
    rw [Finset.mem_biUnion]
    refine ⟨first index, ?_, Finset.mem_filter.mpr ⟨member, rfl⟩⟩
    rw [Finset.mem_range, firstOf index once]
    omega
  calc solved.card
      ≤ ((Finset.range count).biUnion
          (fun visit => solved.filter (fun index => first index = visit))).card :=
        Finset.card_le_card cover
    _ ≤ (Finset.range count).card * bound := by
        apply Finset.card_biUnion_le_card_mul
        intro visit _
        apply visits_first_success hidden covered agent visit
        intro index member
        obtain ⟨inSolved, isFirst⟩ := Finset.mem_filter.mp member
        obtain ⟨earlier, _, solves⟩ := each index inSolved
        have once : ∃ earlier, SolvesOnVisit family goals length agent earlier index :=
          ⟨earlier, solves⟩
        have found : Nat.find once = visit := (firstOf index once).symm.trans isFirst
        refine ⟨?_, fun sooner before => Nat.find_min once (by rw [found]; exact before)⟩
        rw [← found]
        exact Nat.find_spec once
    _ = count * bound := by rw [Finset.card_range]

structure ConcealedClass (family : WorldClass interface) (goals : family.Goals) (len k : ℕ) where
  reference : World interface
  origin : reference.State
  conceals : Conceals family goals reference origin
  covered : Covered family (visitGoals goals len) k
  feasible : ∀ i, Feasible (visitGoals goals len i) (family.start i)
  members : Finset family.Index
  large : k < members.card

def visitScript (interface : Interface) (length : ℕ) (actions : ℕ → Act interface) :
    Agent interface where
  Memory := Fin (length + 1)
  initial := ⟨0, Nat.succ_pos length⟩
  act := fun count _ =>
    (actions count.val,
      if within : count.val < length then ⟨count.val + 1, by omega⟩ else ⟨0, Nat.succ_pos length⟩)

theorem visitScript_openLoop (length : ℕ) (actions : ℕ → Act interface) :
    OpenLoop (visitScript interface length actions) :=
  ⟨fun count =>
      if within : count.val < length then ⟨count.val + 1, by omega⟩ else ⟨0, Nat.succ_pos length⟩,
    fun count => actions count.val, fun _ _ => rfl⟩

theorem visitScript_memory (length : ℕ) (actions : ℕ → Act interface) :
    MemoryWithin (visitScript interface length actions) (Nat.clog 2 (length + 1)) :=
  ⟨⟨fun (count : Fin (length + 1)) => Fin.castLE (Nat.le_pow_clog Nat.one_lt_two _) count,
    fun (first second : Fin (length + 1)) same =>
      Fin.ext (by
        have values := congrArg (fun x : Fin (2 ^ Nat.clog 2 (length + 1)) => x.val) same
        simpa using values)⟩⟩

theorem succ_mod_visit (time length : ℕ) :
    (time + 1) % (length + 1) =
      if time % (length + 1) < length then time % (length + 1) + 1 else 0 := by
  have split := Nat.div_add_mod time (length + 1)
  have below : time % (length + 1) < length + 1 := Nat.mod_lt time (Nat.succ_pos length)
  have whole : time + 1 = (length + 1) * (time / (length + 1)) + (time % (length + 1) + 1) := by
    omega
  rw [whole, Nat.mul_add_mod]
  split
  · exact Nat.mod_eq_of_lt (by omega)
  · have last : time % (length + 1) = length := by omega
    rw [last]
    exact Nat.mod_self _

theorem visitScript_counter (world : World interface) (start : world.State) (length : ℕ)
    (actions : ℕ → Act interface) (time : ℕ) :
    Fin.val (n := length + 1) (memoryAt world (visitScript interface length actions) start time) =
      time % (length + 1) := by
  induction time with
  | zero => exact (Nat.zero_mod _).symm
  | succ time ih =>
    have next : memoryAt world (visitScript interface length actions) start (time + 1) =
        (if within : Fin.val (n := length + 1)
            (memoryAt world (visitScript interface length actions) start time) < length then
          (⟨Fin.val (n := length + 1)
            (memoryAt world (visitScript interface length actions) start time) + 1, by omega⟩ :
            Fin (length + 1))
          else ⟨0, Nat.succ_pos length⟩) := rfl
    rw [next, succ_mod_visit]
    by_cases short : Fin.val (n := length + 1)
        (memoryAt world (visitScript interface length actions) start time) < length
    · rw [dite_eq_left short, ite_eq_left (by omega)]
      simp [ih]
    · rw [dite_eq_right short, ite_eq_right (by omega)]

theorem visitScript_actionAt (world : World interface) (start : world.State) (length : ℕ)
    (actions : ℕ → Act interface) (time : ℕ) (within : time ≤ length) :
    actionAt world (visitScript interface length actions) start time = actions time := by
  have counter := visitScript_counter world start length actions time
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le within)] at counter
  exact congrArg actions counter

theorem blindSolvable_frozen {family : WorldClass interface} {goals : family.Goals} {length : ℕ}
    (actions : ℕ → Act interface)
    (solves : ∀ index, (visitGoals goals length index).MetBy (family.start index) actions)
    (index : family.Index) (count : ℕ) :
    SolvesOnVisit family goals length (visitScript interface length actions) count index := by
  rw [solvesOnVisit_iff]
  have resumed : (visitScript interface length actions).resume
      (memoryAt (visits (family.world index) (family.start index) length)
        (visitScript interface length actions)
        (visitStart (family.world index) (family.start index) length) (count * (length + 1))) =
      visitScript interface length actions := by
    have zero : memoryAt (visits (family.world index) (family.start index) length)
        (visitScript interface length actions)
        (visitStart (family.world index) (family.start index) length) (count * (length + 1)) =
        (⟨0, Nat.succ_pos length⟩ : Fin (length + 1)) :=
      Fin.ext ((visitScript_counter _ _ length actions _).trans (Nat.mul_mod_left _ _))
    rw [zero]
    rfl
  rw [resumed]
  obtain ⟨time, low, high, met⟩ := solves index
  refine ⟨time, low, high, ?_⟩
  have within : time ≤ length := high
  rw [stateAt_eq_path, path_congr _ _ _ actions time (fun step before =>
    visitScript_actionAt _ _ length actions step (by omega))]
  exact met

theorem blindSolvable_covered {family : WorldClass interface} {goals : family.Goals}
    {length bound : ℕ} (actions : ℕ → Act interface)
    (solves : ∀ index, (visitGoals goals length index).MetBy (family.start index) actions)
    (covered : Covered family (visitGoals goals length) bound) (members : Finset family.Index) :
    members.card ≤ bound :=
  covered actions members (fun index _ => solves index)

end AcornVerif.Kernel
