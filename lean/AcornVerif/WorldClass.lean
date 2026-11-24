import AcornVerif.Kernel
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Log

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

structure AttemptGoal (world : World interface) where
  satisfied : world.State → Prop
  cap : ℕ

variable {world : World interface}

def AttemptGoal.MetBy (goal : AttemptGoal world) (start : world.State)
    (actions : ℕ → Act interface) : Prop :=
  ∃ time, 1 ≤ time ∧ time ≤ goal.cap ∧ goal.satisfied (path world start actions time)

def Feasible (goal : AttemptGoal world) (start : world.State) : Prop :=
  ∃ actions : ℕ → Act interface, goal.MetBy start actions

def Achieves (agent : Agent interface) (goal : AttemptGoal world) (start : world.State) : Prop :=
  ∃ time, 1 ≤ time ∧ time ≤ goal.cap ∧ goal.satisfied (stateAt world agent start time)

theorem achieves_iff_metBy (agent : Agent interface) (goal : AttemptGoal world)
    (start : world.State) :
    Achieves agent goal start ↔ goal.MetBy start (actionAt world agent start) := by
  constructor
  · rintro ⟨time, low, high, met⟩
    rw [stateAt_eq_path] at met
    exact ⟨time, low, high, met⟩
  · rintro ⟨time, low, high, met⟩
    rw [← stateAt_eq_path] at met
    exact ⟨time, low, high, met⟩

theorem Achieves.feasible {agent : Agent interface} {goal : AttemptGoal world}
    {start : world.State} (achieved : Achieves agent goal start) : Feasible goal start :=
  ⟨actionAt world agent start, (achieves_iff_metBy agent goal start).mp achieved⟩

theorem feasible_iff_list (goal : AttemptGoal world) (start : world.State) :
    Feasible goal start ↔ ∃ actions : List (Act interface),
      1 ≤ actions.length ∧ actions.length ≤ goal.cap ∧
        goal.satisfied (actions.foldl world.step start) := by
  constructor
  · rintro ⟨actions, time, low, high, met⟩
    refine ⟨(List.range time).map actions, ?_, ?_, ?_⟩
    · rw [List.length_map, List.length_range]
      exact low
    · rw [List.length_map, List.length_range]
      exact high
    · rw [← path_eq_foldl]
      exact met
  · rintro ⟨actions, low, high, met⟩
    refine ⟨fun index => actions.getD index ⟨0, interface.actions.positive⟩, actions.length,
      low, high, ?_⟩
    rw [path_list]
    exact met

def tick (cap : ℕ) (count : Fin (cap + 1)) : Fin (cap + 1) :=
  ⟨min (count.val + 1) cap, by omega⟩

def script (interface : Interface) (cap : ℕ) (actions : ℕ → Act interface) : Agent interface where
  Memory := Fin (cap + 1)
  initial := ⟨0, Nat.succ_pos cap⟩
  act := fun count _ => (actions count.val, tick cap count)

theorem script_openLoop (cap : ℕ) (actions : ℕ → Act interface) :
    OpenLoop (script interface cap actions) :=
  ⟨tick cap, fun (count : Fin (cap + 1)) => actions count.val, fun _ _ => rfl⟩

theorem script_experienceFree (cap : ℕ) (actions : ℕ → Act interface) :
    ExperienceFree (script interface cap actions) :=
  (script_openLoop cap actions).experienceFree

theorem script_memoryWithin (cap bits : ℕ) (actions : ℕ → Act interface)
    (room : cap + 1 ≤ 2 ^ bits) : MemoryWithin (script interface cap actions) bits := by
  refine ⟨⟨fun (count : Fin (cap + 1)) => Fin.castLE room count, fun first second same => ?_⟩⟩
  have values := congrArg Fin.val same
  exact Fin.ext values

theorem script_memory_clog (cap : ℕ) (actions : ℕ → Act interface) :
    MemoryWithin (script interface cap actions) (Nat.clog 2 (cap + 1)) :=
  script_memoryWithin cap _ actions (Nat.le_pow_clog Nat.one_lt_two _)

theorem script_memoryAt (world : World interface) (start : world.State) (cap : ℕ)
    (actions : ℕ → Act interface) (time : ℕ) (within : time ≤ cap) :
    (memoryAt world (script interface cap actions) start time).val = time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have earlier := ih (Nat.le_of_succ_le within)
    have counted : (memoryAt world (script interface cap actions) start (time + 1)).val =
        min ((memoryAt world (script interface cap actions) start time).val + 1) cap := rfl
    rw [counted, earlier]
    exact Nat.min_eq_left within

theorem script_actionAt (world : World interface) (start : world.State) (cap : ℕ)
    (actions : ℕ → Act interface) (time : ℕ) (within : time < cap) :
    actionAt world (script interface cap actions) start time = actions time :=
  congrArg actions (script_memoryAt world start cap actions time (Nat.le_of_lt within))

theorem script_stateAt (world : World interface) (start : world.State) (cap : ℕ)
    (actions : ℕ → Act interface) (time : ℕ) (within : time ≤ cap) :
    stateAt world (script interface cap actions) start time = path world start actions time := by
  rw [stateAt_eq_path]
  exact path_congr world start _ actions time (fun index before =>
    script_actionAt world start cap actions index (Nat.lt_of_lt_of_le before within))

theorem script_achieves {goal : AttemptGoal world} {start : world.State}
    {actions : ℕ → Act interface} {cap : ℕ} (long : goal.cap ≤ cap)
    (met : goal.MetBy start actions) : Achieves (script interface cap actions) goal start := by
  obtain ⟨time, low, high, satisfied⟩ := met
  refine ⟨time, low, high, ?_⟩
  rw [script_stateAt world start cap actions time (Nat.le_trans high long)]
  exact satisfied

theorem feasible_iff_script (goal : AttemptGoal world) (start : world.State) :
    Feasible goal start ↔
      ∃ actions : ℕ → Act interface, Achieves (script interface goal.cap actions) goal start :=
  ⟨fun ⟨actions, met⟩ => ⟨actions, script_achieves (Nat.le_refl _) met⟩,
    fun ⟨_, achieved⟩ => achieved.feasible⟩

theorem need_iff_infeasible (goal : AttemptGoal world) (start : world.State)
    (admits : Agent interface → Prop)
    (scripts : ∀ actions : ℕ → Act interface, admits (script interface goal.cap actions)) :
    (∀ agent, admits agent → ¬ Achieves agent goal start) ↔ ¬ Feasible goal start := by
  constructor
  · intro fails feasible
    obtain ⟨actions, achieved⟩ := (feasible_iff_script goal start).mp feasible
    exact fails _ (scripts actions) achieved
  · intro infeasible agent _ achieved
    exact infeasible achieved.feasible

theorem experienceFree_iff_infeasible (goal : AttemptGoal world) (start : world.State)
    (bits : ℕ) (room : goal.cap + 1 ≤ 2 ^ bits) :
    (∀ agent : Agent interface, ExperienceFree agent → MemoryWithin agent bits →
      ¬ Achieves agent goal start) ↔ ¬ Feasible goal start := by
  refine Iff.trans ?_ (need_iff_infeasible goal start
    (fun agent => ExperienceFree agent ∧ MemoryWithin agent bits)
    (fun actions => ⟨script_experienceFree goal.cap actions,
      script_memoryWithin goal.cap bits actions room⟩))
  exact ⟨fun fails agent admitted => fails agent admitted.1 admitted.2,
    fun fails agent free fits => fails agent ⟨free, fits⟩⟩

theorem script_reactive_constant (cap : ℕ) (actions : ℕ → Act interface)
    (reactive : Reactive (script interface cap actions)) (percept : Percept interface)
    (first second : ℕ) (low : first ≤ cap) (high : second ≤ cap) :
    actions first = actions second := by
  obtain ⟨rule, law⟩ := reactive
  have early : actions first = rule percept :=
    law (⟨first, Nat.lt_succ_of_le low⟩ : Fin (cap + 1)) percept
  have late : actions second = rule percept :=
    law (⟨second, Nat.lt_succ_of_le high⟩ : Fin (cap + 1)) percept
  exact early.trans late.symm

structure WorldClass (interface : Interface) where
  Index : Type
  world : Index → World interface
  start : (index : Index) → (world index).State

def WorldClass.single (world : World interface) (start : world.State) : WorldClass interface :=
  ⟨Unit, fun _ => world, fun _ => start⟩

abbrev WorldClass.Goals (family : WorldClass interface) : Type :=
  (index : family.Index) → AttemptGoal (family.world index)

variable {family : WorldClass interface}

def Solves (family : WorldClass interface) (goals : family.Goals) (agent : Agent interface)
    (index : family.Index) : Prop :=
  Achieves agent (goals index) (family.start index)

def Need (family : WorldClass interface) (goals : family.Goals)
    (admits : Agent interface → Prop) (bound : ℕ) : Prop :=
  ∀ agent, admits agent → ∀ solved : Finset family.Index,
    (∀ index ∈ solved, Solves family goals agent index) → solved.card ≤ bound

def Covered (family : WorldClass interface) (goals : family.Goals) (bound : ℕ) : Prop :=
  ∀ (actions : ℕ → Act interface) (solved : Finset family.Index),
    (∀ index ∈ solved, (goals index).MetBy (family.start index) actions) → solved.card ≤ bound

def Blind (family : WorldClass interface) (goals : family.Goals) (agent : Agent interface) :
    Prop :=
  ∃ actions : ℕ → Act interface, ∀ index time,
    (∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) earlier)) →
    actionAt (family.world index) agent (family.start index) time = actions time

theorem openLoop_blind (family : WorldClass interface) (goals : family.Goals)
    {agent : Agent interface} (blind : OpenLoop agent) : Blind family goals agent := by
  obtain ⟨actions, law⟩ := openLoop_actions blind
  exact ⟨actions, fun index time _ => law (family.world index) (family.start index) time⟩

theorem blind_metBy {goals : family.Goals} {agent : Agent interface}
    {actions : ℕ → Act interface}
    (law : ∀ index time,
      (∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
        (stateAt (family.world index) agent (family.start index) earlier)) →
      actionAt (family.world index) agent (family.start index) time = actions time)
    (index : family.Index) (solved : Solves family goals agent index) :
    (goals index).MetBy (family.start index) actions := by
  have first : ∀ time, 1 ≤ time → time ≤ (goals index).cap →
      (goals index).satisfied (stateAt (family.world index) agent (family.start index) time) →
      (goals index).MetBy (family.start index) actions := by
    intro time
    induction time using Nat.strongRecOn with
    | _ time ih =>
      intro low high met
      by_cases sooner : ∃ earlier, 1 ≤ earlier ∧ earlier < time ∧ (goals index).satisfied
          (stateAt (family.world index) agent (family.start index) earlier)
      · obtain ⟨earlier, lowEarlier, before, metEarlier⟩ := sooner
        exact ih earlier before lowEarlier (Nat.le_trans (Nat.le_of_lt before) high) metEarlier
      · have agree : ∀ step, step < time →
            actionAt (family.world index) agent (family.start index) step = actions step := by
          intro step before
          apply law index step
          intro earlier lowEarlier within reached
          exact sooner ⟨earlier, lowEarlier, Nat.lt_of_le_of_lt within before, reached⟩
        have same : stateAt (family.world index) agent (family.start index) time =
            path (family.world index) (family.start index) actions time :=
          (stateAt_eq_path _ _ _ time).trans (path_congr _ _ _ actions time agree)
        rw [same] at met
        exact ⟨time, low, high, met⟩
  obtain ⟨time, low, high, met⟩ := solved
  exact first time low high met

theorem need_of_covered {goals : family.Goals} {bound : ℕ} (covered : Covered family goals bound) :
    Need family goals (Blind family goals) bound := by
  intro agent blind solved each
  obtain ⟨actions, law⟩ := blind
  exact covered actions solved (fun index member => blind_metBy law index (each index member))

theorem covered_iff_need (goals : family.Goals) (bound : ℕ) :
    Covered family goals bound ↔ Need family goals OpenLoop bound := by
  constructor
  · intro covered agent blind
    exact need_of_covered covered agent (openLoop_blind family goals blind)
  · intro need actions solved each
    exact need (script interface (solved.sup fun index => (goals index).cap) actions)
      (script_openLoop _ actions) solved (fun index member =>
        script_achieves (Finset.le_sup (f := fun index => (goals index).cap) member)
          (each index member))

theorem need_single (goal : AttemptGoal world) (start : world.State)
    (admits : Agent interface → Prop) :
    Need (WorldClass.single world start) (fun _ => goal) admits 0 ↔
      ∀ agent, admits agent → ¬ Achieves agent goal start := by
  constructor
  · intro need agent admitted achieved
    have one : ({()} : Finset Unit).card ≤ 0 := need agent admitted {()} (fun _ _ => achieved)
    rw [Finset.card_singleton] at one
    exact absurd one (by decide)
  · intro fails agent admitted solved each
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro index member
    exact fails agent admitted (each index member)

theorem need_single_iff_infeasible (goal : AttemptGoal world) (start : world.State)
    (admits : Agent interface → Prop)
    (scripts : ∀ actions : ℕ → Act interface, admits (script interface goal.cap actions)) :
    Need (WorldClass.single world start) (fun _ => goal) admits 0 ↔ ¬ Feasible goal start :=
  (need_single goal start admits).trans (need_iff_infeasible goal start admits scripts)

def firstActionWorld (interface : Interface) (shown : Percept interface) : World interface where
  State := Option (Act interface)
  step := fun state action => state.orElse fun _ => some action
  percept := fun _ => shown

def otherThan (interface : Interface) (bound : 2 ≤ interface.actions.word.toNat)
    (action : Act interface) : Act interface :=
  if action.val = 0 then ⟨1, bound⟩ else ⟨0, by omega⟩

theorem otherThan_ne (interface : Interface) (bound : 2 ≤ interface.actions.word.toNat)
    (action : Act interface) : otherThan interface bound action ≠ action := by
  intro same
  have values := congrArg Fin.val same
  unfold otherThan at values
  split at values <;> simp_all

theorem no_agent_achieves_every_world {interface : Interface}
    (bound : 2 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (agent : Agent interface) :
    ∃ (world : World interface) (start : world.State) (goal : AttemptGoal world),
      (∀ state, world.percept state = shown) ∧ goal.cap = 1 ∧
        Feasible goal start ∧ ¬ Achieves agent goal start := by
  let wrong : Act interface := otherThan interface bound (agent.act agent.initial shown).1
  refine ⟨firstActionWorld interface shown, (none : Option (Act interface)),
    ⟨fun state => state = some wrong, 1⟩, fun _ => rfl, rfl, ?_, ?_⟩
  · exact ⟨fun _ => wrong, 1, le_refl 1, le_refl 1, rfl⟩
  · rintro ⟨time, low, high, met⟩
    have one : time = 1 := by
      change time ≤ 1 at high
      omega
    subst one
    have same : some (agent.act agent.initial shown).1 = some wrong := met
    exact otherThan_ne interface bound _ (Option.some.inj same).symm

end AcornVerif.Kernel
