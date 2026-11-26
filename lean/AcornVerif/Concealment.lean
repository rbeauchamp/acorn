import AcornVerif.WorldClass

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

def Conceals (family : WorldClass interface) (goals : family.Goals)
    (reference : World interface) (origin : reference.State) : Prop :=
  ∀ (index : family.Index) (actions : ℕ → Act interface) (time : ℕ),
    (∀ earlier, 1 ≤ earlier → earlier ≤ time →
      ¬ (goals index).satisfied
        (path (family.world index) (family.start index) actions earlier)) →
    (family.world index).percept (path (family.world index) (family.start index) actions time) =
      reference.percept (path reference origin actions time)

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

theorem Conceals.perceptAt_eq (hidden : Conceals family goals reference origin)
    (agent : Agent interface) (index : family.Index) (time : ℕ)
    (unmet : ∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) earlier))
    (same : ∀ step, step < time →
      actionAt (family.world index) agent (family.start index) step =
        actionAt reference agent origin step) :
    perceptAt (family.world index) agent (family.start index) time =
      perceptAt reference agent origin time := by
  have track : ∀ earlier, earlier ≤ time →
      stateAt (family.world index) agent (family.start index) earlier =
        path (family.world index) (family.start index) (actionAt reference agent origin)
          earlier :=
    fun earlier within => (stateAt_eq_path _ _ _ earlier).trans
      (path_congr _ _ _ _ earlier (fun step before =>
        same step (Nat.lt_of_lt_of_le before within)))
  have shown := hidden index (actionAt reference agent origin) time (fun earlier low high => by
    rw [← track earlier high]
    exact unmet earlier low high)
  change (family.world index).percept
      (stateAt (family.world index) agent (family.start index) time) =
    reference.percept (stateAt reference agent origin time)
  rw [track time (Nat.le_refl time), stateAt_eq_path reference agent origin time]
  exact shown

theorem Conceals.agree_before (hidden : Conceals family goals reference origin)
    (agent : Agent interface) (index : family.Index) (time : ℕ) :
    (∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) earlier)) →
    memoryAt (family.world index) agent (family.start index) time =
        memoryAt reference agent origin time ∧
      ∀ step, step < time → actionAt (family.world index) agent (family.start index) step =
        actionAt reference agent origin step := by
  induction time with
  | zero => exact fun _ => ⟨rfl, fun step early => absurd early (Nat.not_lt_zero step)⟩
  | succ time ih =>
    intro unmet
    have unmetEarlier : ∀ earlier, 1 ≤ earlier → earlier ≤ time →
        ¬ (goals index).satisfied
        (stateAt (family.world index) agent (family.start index) earlier) :=
      fun earlier low high => unmet earlier low (Nat.le_succ_of_le high)
    obtain ⟨memory, actions⟩ := ih unmetEarlier
    have percept := hidden.perceptAt_eq agent index time unmetEarlier actions
    have decided : agent.act (memoryAt (family.world index) agent (family.start index) time)
          (perceptAt (family.world index) agent (family.start index) time) =
        agent.act (memoryAt reference agent origin time)
          (perceptAt reference agent origin time) := by
      rw [memory, percept]
    refine ⟨congrArg Prod.snd decided, fun step early => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ early) with earlier | equal
    · exact actions step earlier
    · rw [equal]
      exact congrArg Prod.fst decided

theorem Conceals.agree (hidden : Conceals family goals reference origin)
    (agent : Agent interface) (index : family.Index) (time : ℕ)
    (unmet : ∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) earlier)) :
    memoryAt (family.world index) agent (family.start index) time =
        memoryAt reference agent origin time ∧
      ∀ step, step ≤ time → actionAt (family.world index) agent (family.start index) step =
        actionAt reference agent origin step := by
  obtain ⟨memory, actions⟩ := hidden.agree_before agent index time unmet
  have percept := hidden.perceptAt_eq agent index time unmet actions
  refine ⟨memory, fun step within => ?_⟩
  rcases Nat.lt_or_eq_of_le within with earlier | equal
  · exact actions step earlier
  · rw [equal]
    change (agent.act (memoryAt (family.world index) agent (family.start index) time)
        (perceptAt (family.world index) agent (family.start index) time)).1 =
      (agent.act (memoryAt reference agent origin time) (perceptAt reference agent origin time)).1
    rw [memory, percept]

theorem Conceals.blind (hidden : Conceals family goals reference origin)
    (agent : Agent interface) : Blind family goals agent :=
  ⟨actionAt reference agent origin, fun index time unmet =>
    (hidden.agree agent index time unmet).2 time (Nat.le_refl time)⟩

theorem Conceals.need (hidden : Conceals family goals reference origin) {bound : ℕ}
    (covered : Covered family goals bound) : Need family goals (fun _ => True) bound :=
  fun agent _ => need_of_covered covered agent (hidden.blind agent)

theorem Conceals.solves_iff (hidden : Conceals family goals reference origin)
    (agent : Agent interface) (index : family.Index) :
    Solves family goals agent index ↔
      (goals index).MetBy (family.start index) (actionAt reference agent origin) := by
  constructor
  · exact blind_metBy (fun member time unmet =>
      (hidden.agree agent member time unmet).2 time (Nat.le_refl time)) index
  · rintro ⟨time, low, high, met⟩
    by_cases sooner : ∃ earlier, 1 ≤ earlier ∧ earlier < time ∧ (goals index).satisfied
        (stateAt (family.world index) agent (family.start index) earlier)
    · obtain ⟨earlier, lowEarlier, before, reached⟩ := sooner
      exact ⟨earlier, lowEarlier, Nat.le_trans (Nat.le_of_lt before) high, reached⟩
    · have same := (hidden.agree agent index (time - 1)
        (fun earlier lowEarlier within reached =>
          sooner ⟨earlier, lowEarlier, by omega, reached⟩)).2
      refine ⟨time, low, high, ?_⟩
      rw [stateAt_eq_path, path_congr _ _ _ (actionAt reference agent origin) time
        (fun step before => same step (by omega))]
      exact met

def park (interface : Interface) (signal : Percept interface → Bool) (stay : Act interface)
    (actions : ℕ → Act interface) : Agent interface where
  Memory := ℕ
  initial := 0
  act := fun count percept => (if signal percept = true then stay else actions count, count + 1)

theorem park_experienceFree (signal : Percept interface → Bool) (stay : Act interface)
    (actions : ℕ → Act interface) : ExperienceFree (park interface signal stay actions) :=
  ⟨fun (count : ℕ) => count + 1, fun _ _ => rfl⟩

theorem park_keeps (world : World interface) (start : world.State)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (shows : ∀ state action, satisfied (world.step state action) →
      signal (world.percept (world.step state action)) = true)
    (stay : Act interface)
    (keeps : ∀ state, satisfied state → satisfied (world.step state stay))
    (actions : ℕ → Act interface) (time later : ℕ)
    (met : satisfied (stateAt world (park interface signal stay actions) start (time + 1))) :
    satisfied (stateAt world (park interface signal stay actions) start (time + 1 + later)) := by
  induction later with
  | zero => exact met
  | succ later ih =>
    have shown : signal (world.percept
        (stateAt world (park interface signal stay actions) start (time + 1 + later))) = true := by
      have stepped : stateAt world (park interface signal stay actions) start (time + 1 + later) =
          world.step (stateAt world (park interface signal stay actions) start (time + later))
            (actionAt world (park interface signal stay actions) start (time + later)) := by
        rw [Nat.add_right_comm]
        rfl
      rw [stepped] at ih ⊢
      exact shows _ _ ih
    change satisfied (world.step
      (stateAt world (park interface signal stay actions) start (time + 1 + later))
      (if signal (world.percept
          (stateAt world (park interface signal stay actions) start (time + 1 + later))) = true
        then stay
        else actions
          (memoryAt world (park interface signal stay actions) start (time + 1 + later))))
    rw [ite_eq_left shown]
    exact keeps _ ih

end AcornVerif.Kernel
