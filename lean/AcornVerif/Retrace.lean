import AcornVerif.Separation

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

structure RetraceMemory (length last : ℕ) where
  step : Fin (length + 1)
  count : Fin (last + 1)
  found : Option (Fin (last + 1))

namespace RetraceMemory

variable {length last : ℕ}

def learn (memory : RetraceMemory length last) (shown : Bool) : Option (Fin (last + 1)) :=
  match memory.found with
  | some walk => some walk
  | none => if 1 ≤ memory.step.val ∧ shown = true then some memory.count else none

def next (memory : RetraceMemory length last) (found : Option (Fin (last + 1))) :
    RetraceMemory length last :=
  if within : memory.step.val < length then
    ⟨⟨memory.step.val + 1, by omega⟩, memory.count, found⟩
  else ⟨⟨0, Nat.succ_pos length⟩, ⟨min (memory.count.val + 1) last, by omega⟩, found⟩

theorem next_within (memory : RetraceMemory length last) (found : Option (Fin (last + 1)))
    (within : memory.step.val < length) :
    (memory.next found).step.val = memory.step.val + 1 ∧
      (memory.next found).count = memory.count ∧ (memory.next found).found = found := by
  unfold next
  rw [dite_eq_left within]
  exact ⟨rfl, rfl, rfl⟩

theorem next_last (memory : RetraceMemory length last) (found : Option (Fin (last + 1)))
    (done : ¬ memory.step.val < length) :
    (memory.next found).step.val = 0 ∧
      (memory.next found).count.val = min (memory.count.val + 1) last ∧
        (memory.next found).found = found := by
  unfold next
  rw [dite_eq_right done]
  exact ⟨rfl, rfl, rfl⟩

end RetraceMemory

def retrace (interface : Interface) (length last : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) : Agent interface where
  Memory := RetraceMemory length last
  initial := ⟨⟨0, Nat.succ_pos length⟩, ⟨0, Nat.succ_pos last⟩, none⟩
  act := fun memory percept =>
    (explore ((memory.learn (signal percept)).getD memory.count).val memory.step.val,
      memory.next (memory.learn (signal percept)))

theorem retraceMemory_finite (length last : ℕ) :
    ∃ memories : List (RetraceMemory length last), ∀ memory, memory ∈ memories := by
  refine ⟨(List.finRange (length + 1)).flatMap fun step =>
    (List.finRange (last + 1)).flatMap fun count =>
      (none :: (List.finRange (last + 1)).map some).map fun found => ⟨step, count, found⟩, ?_⟩
  rintro ⟨step, count, found⟩
  refine List.mem_flatMap.mpr ⟨step, List.mem_finRange step,
    List.mem_flatMap.mpr ⟨count, List.mem_finRange count, List.mem_map.mpr ⟨found, ?_, rfl⟩⟩⟩
  cases found with
  | none => exact List.mem_cons_self
  | some walk =>
    exact List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨walk, List.mem_finRange walk, rfl⟩)

def RetraceFound (world : World interface) (start : world.State) (satisfied : world.State → Prop)
    (walk : ℕ → Act interface) {last : ℕ} (count : Fin (last + 1))
    (found current : Option (Fin (last + 1))) (time : ℕ) : Prop :=
  (∀ visit, found = some visit → current = some visit) ∧
    (found = none →
      (current = none ∧ ∀ earlier, 1 ≤ earlier → earlier < time →
        ¬ satisfied (path world start walk earlier)) ∨
      (current = some count ∧ ∃ earlier, 1 ≤ earlier ∧ earlier < time ∧
        satisfied (path world start walk earlier)))

theorem RetraceFound.getD {world : World interface} {start : world.State}
    {satisfied : world.State → Prop} {walk : ℕ → Act interface} {last : ℕ}
    {count : Fin (last + 1)} {found current : Option (Fin (last + 1))} {time : ℕ}
    (held : RetraceFound world start satisfied walk count found current time) :
    current.getD count = found.getD count := by
  cases found with
  | some visit => rw [held.1 visit rfl]
  | none =>
    rcases held.2 rfl with ⟨empty, -⟩ | ⟨filled, -⟩
    · rw [empty]
    · rw [filled]
      rfl

theorem RetraceFound.learn {world : World interface} {start : world.State}
    {satisfied : world.State → Prop} {walk : ℕ → Act interface} {length last : ℕ}
    {count : Fin (last + 1)} {found : Option (Fin (last + 1))} {time : ℕ}
    (signal : Percept interface → Bool)
    (decodes : ∀ state action, signal (world.percept (world.step state action)) = true ↔
      satisfied (world.step state action))
    (memory : RetraceMemory length last) (stepEq : memory.step.val = time)
    (countEq : memory.count = count)
    (held : RetraceFound world start satisfied walk count found memory.found time) :
    RetraceFound world start satisfied walk count found
      (memory.learn (signal (world.percept (path world start walk time)))) (time + 1) := by
  have shown : 1 ≤ time → (signal (world.percept (path world start walk time)) = true ↔
      satisfied (path world start walk time)) := by
    intro positive
    obtain ⟨before, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    exact decodes (path world start walk before) (walk before)
  refine ⟨fun visit same => ?_, fun fresh => ?_⟩
  · unfold RetraceMemory.learn
    rw [held.1 visit same]
  · rcases held.2 fresh with ⟨empty, unmet⟩ | ⟨filled, earlier, low, high, met⟩
    · unfold RetraceMemory.learn
      rw [empty, stepEq, countEq]
      by_cases now : 1 ≤ time ∧ signal (world.percept (path world start walk time)) = true
      · rw [ite_eq_left now]
        exact .inr ⟨rfl, time, now.1, Nat.lt_succ_self time, (shown now.1).mp now.2⟩
      · rw [ite_eq_right now]
        refine .inl ⟨rfl, fun earlier low high reached => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ high) with sooner | same
        · exact unmet earlier low sooner reached
        · subst same
          exact now ⟨low, (shown low).mpr reached⟩
    · unfold RetraceMemory.learn
      rw [filled]
      exact .inr ⟨rfl, earlier, low, Nat.lt_succ_of_lt high, met⟩

theorem retrace_within (world : World interface) (start : world.State) (length last : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (decodes : ∀ state action, signal (world.percept (world.step state action)) = true ↔
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (memory : RetraceMemory length last)
    (zero : memory.step.val = 0) (time : ℕ) (within : time ≤ length) :
    stateAt world ((retrace interface length last signal explore).resume memory) start time =
        path world start (explore (memory.found.getD memory.count).val) time ∧
      (RetraceMemory.step (length := length) (last := last)
        (memoryAt world ((retrace interface length last signal explore).resume memory) start
          time)).val = time ∧
      RetraceMemory.count (length := length) (last := last)
        (memoryAt world ((retrace interface length last signal explore).resume memory) start
          time) = memory.count ∧
      RetraceFound world start satisfied (explore (memory.found.getD memory.count).val)
        memory.count memory.found
        (RetraceMemory.found (length := length) (last := last)
          (memoryAt world ((retrace interface length last signal explore).resume memory) start
            time)) time := by
  induction time with
  | zero =>
    exact ⟨rfl, zero, rfl, fun _ same => same,
      fun fresh => .inl ⟨fresh, fun _ _ high => absurd high (Nat.not_lt_zero _)⟩⟩
  | succ time ih =>
    obtain ⟨state, stepVal, countEq, held⟩ := ih (Nat.le_of_succ_le within)
    have short : time < length := Nat.lt_of_succ_le within
    have learned := held.learn signal decodes _ stepVal countEq
    have chosen := learned.getD
    have moved := RetraceMemory.next_within
      (memoryAt world ((retrace interface length last signal explore).resume memory) start time)
      (RetraceMemory.learn
        (memoryAt world ((retrace interface length last signal explore).resume memory) start time)
        (signal (world.percept
          (path world start (explore (memory.found.getD memory.count).val) time))))
      (by rw [stepVal]; exact short)
    have stateNext :
        stateAt world ((retrace interface length last signal explore).resume memory) start
          (time + 1) =
        world.step
          (stateAt world ((retrace interface length last signal explore).resume memory) start
            time)
          (explore ((RetraceMemory.learn
            (memoryAt world ((retrace interface length last signal explore).resume memory) start
              time)
            (signal (world.percept (stateAt world
              ((retrace interface length last signal explore).resume memory) start
                time)))).getD
            (RetraceMemory.count (length := length) (last := last) (memoryAt world
              ((retrace interface length last signal explore).resume memory) start time))).val
            (RetraceMemory.step (length := length) (last := last) (memoryAt world
              ((retrace interface length last signal explore).resume memory) start time)).val) :=
      rfl
    have memoryNext :
        memoryAt world ((retrace interface length last signal explore).resume memory) start
          (time + 1) =
        RetraceMemory.next
          (memoryAt world ((retrace interface length last signal explore).resume memory) start
            time)
          (RetraceMemory.learn
            (memoryAt world ((retrace interface length last signal explore).resume memory) start
              time)
            (signal (world.percept (stateAt world
              ((retrace interface length last signal explore).resume memory) start time)))) :=
      rfl
    rw [state] at stateNext memoryNext
    rw [stateNext, memoryNext, countEq, chosen, stepVal]
    refine ⟨rfl, moved.1.trans (congrArg (· + 1) stepVal), moved.2.1.trans countEq, ?_⟩
    rw [moved.2.2]
    exact learned

theorem retrace_visit_end (world : World interface) (start : world.State) (length last : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (decodes : ∀ state action, signal (world.percept (world.step state action)) = true ↔
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (memory : RetraceMemory length last)
    (zero : memory.step.val = 0) :
    (RetraceMemory.step (length := length) (last := last)
        (memoryAt world ((retrace interface length last signal explore).resume memory) start
          (length + 1))).val = 0 ∧
      (RetraceMemory.count (length := length) (last := last)
        (memoryAt world ((retrace interface length last signal explore).resume memory) start
          (length + 1))).val = min (memory.count.val + 1) last ∧
      RetraceFound world start satisfied (explore (memory.found.getD memory.count).val)
        memory.count memory.found
        (RetraceMemory.found (length := length) (last := last)
          (memoryAt world ((retrace interface length last signal explore).resume memory) start
            (length + 1))) (length + 1) := by
  obtain ⟨state, stepVal, countEq, held⟩ :=
    retrace_within world start length last satisfied signal decodes explore memory zero length
      (Nat.le_refl length)
  have learned := held.learn signal decodes _ stepVal countEq
  have moved := RetraceMemory.next_last
    (memoryAt world ((retrace interface length last signal explore).resume memory) start length)
    (RetraceMemory.learn
      (memoryAt world ((retrace interface length last signal explore).resume memory) start length)
      (signal (world.percept
        (path world start (explore (memory.found.getD memory.count).val) length))))
    (by rw [stepVal]; exact Nat.lt_irrefl length)
  have memoryNext :
      memoryAt world ((retrace interface length last signal explore).resume memory) start
        (length + 1) =
      RetraceMemory.next
        (memoryAt world ((retrace interface length last signal explore).resume memory) start
          length)
        (RetraceMemory.learn
          (memoryAt world ((retrace interface length last signal explore).resume memory) start
            length)
          (signal (world.percept (stateAt world
            ((retrace interface length last signal explore).resume memory) start length)))) :=
    rfl
  rw [state] at memoryNext
  rw [memoryNext]
  refine ⟨moved.1, ?_, ?_⟩
  · rw [moved.2.1, countEq]
  · rw [moved.2.2]
    exact learned

theorem visits_memory_end (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) :
    memoryAt (visits world start length) agent (visitStart world start length) (length + 1) =
      memoryAt world agent start (length + 1) := by
  have inner := visits_loop world start length agent length (Nat.le_refl length)
  change (interact (visits world start length) agent
      (loop (visits world start length) agent (visitStart world start length) length)).2 =
    (interact world agent (loop world agent start length)).2
  rw [inner]
  rfl

theorem visits_memory_next (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (count : ℕ) :
    memoryAt (visits world start length) agent (visitStart world start length)
        ((count + 1) * (length + 1)) =
      memoryAt world
        (agent.resume (memoryAt (visits world start length) agent (visitStart world start length)
          (count * (length + 1))))
        start (length + 1) := by
  rw [Nat.add_mul, Nat.one_mul, memoryAt_add, visits_period]
  exact visits_memory_end world start length _

def retraceStart (world : World interface) (start : world.State) (length last : ℕ)
    (signal : Percept interface → Bool) (explore : ℕ → ℕ → Act interface) (visit : ℕ) :
    RetraceMemory length last :=
  memoryAt (visits world start length) (retrace interface length last signal explore)
    (visitStart world start length) (visit * (length + 1))

theorem retraceStart_step (world : World interface) (start : world.State) (length last : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (decodes : ∀ state action, signal (world.percept (world.step state action)) = true ↔
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (visit : ℕ)
    (zero : (retraceStart world start length last signal explore visit).step.val = 0) :
    (retraceStart world start length last signal explore (visit + 1)).step.val = 0 ∧
      (retraceStart world start length last signal explore (visit + 1)).count.val =
        min ((retraceStart world start length last signal explore visit).count.val + 1) last ∧
      RetraceFound world start satisfied
        (explore (((retraceStart world start length last signal explore visit).found.getD
          (retraceStart world start length last signal explore visit).count).val))
        (retraceStart world start length last signal explore visit).count
        (retraceStart world start length last signal explore visit).found
        (retraceStart world start length last signal explore (visit + 1)).found (length + 1) := by
  have next : retraceStart world start length last signal explore (visit + 1) =
      memoryAt world
        ((retrace interface length last signal explore).resume
          (retraceStart world start length last signal explore visit))
        start (length + 1) :=
    visits_memory_next world start length _ visit
  rw [next]
  exact retrace_visit_end world start length last satisfied signal decodes explore _ zero

theorem retraceStart_invariant (world : World interface) (start : world.State) (length last : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (decodes : ∀ state action, signal (world.percept (world.step state action)) = true ↔
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (visit : ℕ) :
    (retraceStart world start length last signal explore visit).step.val = 0 ∧
      (retraceStart world start length last signal explore visit).count.val = min visit last ∧
      ∀ walk, (retraceStart world start length last signal explore visit).found = some walk →
        ∃ step, 1 ≤ step ∧ step ≤ length ∧
          satisfied (path world start (explore walk.val) step) := by
  induction visit with
  | zero =>
    have first : retraceStart world start length last signal explore 0 =
        ⟨⟨0, Nat.succ_pos length⟩, ⟨0, Nat.succ_pos last⟩, none⟩ := by
      unfold retraceStart
      rw [Nat.zero_mul]
      rfl
    rw [first]
    exact ⟨rfl, (Nat.zero_min last).symm, fun _ same => nomatch same⟩
  | succ visit ih =>
    obtain ⟨zero, counted, kept⟩ := ih
    obtain ⟨zeroNext, countedNext, held⟩ :=
      retraceStart_step world start length last satisfied signal decodes explore visit zero
    refine ⟨zeroNext, ?_, fun walk same => ?_⟩
    · rw [countedNext, counted]
      omega
    · cases known : (retraceStart world start length last signal explore visit).found with
      | some before =>
        have stays := held.1 before known
        rw [same] at stays
        rw [Option.some.inj stays]
        exact kept before known
      | none =>
        rw [known] at held
        rcases held.2 rfl with ⟨empty, -⟩ | ⟨filled, earlier, low, high, met⟩
        · rw [same] at empty
          exact nomatch empty
        · rw [same] at filled
          rw [Option.some.inj filled]
          exact ⟨earlier, low, Nat.le_of_lt_succ high, met⟩

theorem retraceStart_keeps (world : World interface) (start : world.State) (length last : ℕ)
    (satisfied : world.State → Prop) (signal : Percept interface → Bool)
    (decodes : ∀ state action, signal (world.percept (world.step state action)) = true ↔
      satisfied (world.step state action))
    (explore : ℕ → ℕ → Act interface) (visit gap : ℕ) (walk : Fin (last + 1))
    (holds : (retraceStart world start length last signal explore visit).found = some walk) :
    (retraceStart world start length last signal explore (visit + gap)).found = some walk := by
  induction gap with
  | zero => exact holds
  | succ gap ih =>
    have zero := (retraceStart_invariant world start length last satisfied signal decodes explore
      (visit + gap)).1
    exact (retraceStart_step world start length last satisfied signal decodes explore
      (visit + gap) zero).2.2.1 walk ih

variable (family : WorldClass interface) (goals : family.Goals)

theorem retrace_solves_iff (length last : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (index : family.Index)
    (decodes : ∀ state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (visit : ℕ) :
    SolvesOnVisit family goals length (retrace interface length last signal explore) visit
        index ↔
      ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
        (path (family.world index) (family.start index)
          (explore (((retraceStart (family.world index) (family.start index) length last signal
            explore visit).found.getD
              (retraceStart (family.world index) (family.start index) length last signal explore
                visit).count).val))
          step) := by
  have zero := (retraceStart_invariant (family.world index) (family.start index) length last
    (goals index).satisfied signal decodes explore visit).1
  have along : ∀ step, step ≤ length →
      stateAt (family.world index)
        ((retrace interface length last signal explore).resume
          (retraceStart (family.world index) (family.start index) length last signal explore
            visit))
        (family.start index) step =
      path (family.world index) (family.start index)
        (explore (((retraceStart (family.world index) (family.start index) length last signal
          explore visit).found.getD
            (retraceStart (family.world index) (family.start index) length last signal explore
              visit).count).val))
        step := by
    intro step within
    exact (retrace_within (family.world index) (family.start index) length last
      (goals index).satisfied signal decodes explore _ zero step within).1
  rw [solvesOnVisit_iff]
  constructor
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    rw [← along step high]
    exact met
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    change (goals index).satisfied _
    rw [show memoryAt (visits (family.world index) (family.start index) length)
        (retrace interface length last signal explore)
        (visitStart (family.world index) (family.start index) length) (visit * (length + 1)) =
      retraceStart (family.world index) (family.start index) length last signal explore visit
      from rfl, along step high]
    exact met

theorem retrace_solves (length last : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (index : family.Index)
    (decodes : ∀ state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (count later : ℕ) (after : count < later)
    (solved : SolvesOnVisit family goals length (retrace interface length last signal explore)
      count index) :
    SolvesOnVisit family goals length (retrace interface length last signal explore) later
      index := by
  obtain ⟨step, low, high, met⟩ :=
    (retrace_solves_iff family goals length last signal explore index decodes count).mp solved
  have zero := (retraceStart_invariant (family.world index) (family.start index) length last
    (goals index).satisfied signal decodes explore count).1
  obtain ⟨-, -, held⟩ := retraceStart_step (family.world index) (family.start index) length last
    (goals index).satisfied signal decodes explore count zero
  have found : ∃ walk : Fin (last + 1),
      (retraceStart (family.world index) (family.start index) length last signal explore
        (count + 1)).found = some walk ∧
      (goals index).satisfied
        (path (family.world index) (family.start index) (explore walk.val) step) := by
    cases known : (retraceStart (family.world index) (family.start index) length last signal
        explore count).found with
    | some walk =>
      rw [known] at met
      exact ⟨walk, held.1 walk known, met⟩
    | none =>
      rw [known] at met held
      rcases held.2 rfl with ⟨-, unmet⟩ | ⟨filled, -⟩
      · exact absurd met (unmet step low (Nat.lt_succ_of_le high))
      · exact ⟨_, filled, met⟩
  obtain ⟨walk, holds, reached⟩ := found
  obtain ⟨gap, split⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt after)
  have kept := retraceStart_keeps (family.world index) (family.start index) length last
    (goals index).satisfied signal decodes explore (count + 1) gap walk holds
  rw [← split] at kept
  refine (retrace_solves_iff family goals length last signal explore index decodes later).mpr
    ⟨step, low, high, ?_⟩
  rw [kept]
  exact reached

theorem retrace_solves_explored (length last : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface) (index : family.Index)
    (decodes : ∀ state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (visit later : ℕ) (exploring : visit ≤ last) (after : visit ≤ later)
    (meets : ∃ step, 1 ≤ step ∧ step ≤ length ∧
      (goals index).satisfied
        (path (family.world index) (family.start index) (explore visit) step)) :
    SolvesOnVisit family goals length (retrace interface length last signal explore) later
      index := by
  obtain ⟨-, counted, kept⟩ := retraceStart_invariant (family.world index) (family.start index)
    length last (goals index).satisfied signal decodes explore visit
  have first : SolvesOnVisit family goals length (retrace interface length last signal explore)
      visit index := by
    refine (retrace_solves_iff family goals length last signal explore index decodes visit).mpr ?_
    cases known : (retraceStart (family.world index) (family.start index) length last signal
        explore visit).found with
    | some walk => exact kept walk known
    | none =>
      have same : (retraceStart (family.world index) (family.start index) length last signal
          explore visit).count.val = visit := by
        rw [counted]
        exact Nat.min_eq_left exploring
      change ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
        (path (family.world index) (family.start index)
          (explore (retraceStart (family.world index) (family.start index) length last signal
            explore visit).count.val) step)
      rw [same]
      exact meets
  rcases Nat.lt_or_eq_of_le after with sooner | same
  · exact retrace_solves family goals length last signal explore index decodes visit later sooner
      first
  · rw [← same]
    exact first

theorem retrace_retains (family : WorldClass interface) (goals : family.Goals) (length last : ℕ)
    (signal : Percept interface → Bool) (explore : ℕ → ℕ → Act interface)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action)) :
    Retains family goals length (retrace interface length last signal explore) :=
  fun index visit later after solved =>
    retrace_solves family goals length last signal explore index (decodes index) visit later
      after solved

theorem retrace_finds (family : WorldClass interface) (goals : family.Goals)
    (length last bound : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (counted : List family.Index) (distinct : counted.Nodup) (many : bound < counted.length)
    (explored : ∀ index ∈ counted, ∃ visit, visit ≤ last ∧
      ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
        (path (family.world index) (family.start index) (explore visit) step)) :
    FindsBy family goals length bound counted (last + 1)
      (retrace interface length last signal explore) := by
  classical
  refine ⟨counted.toFinset, by rwa [List.toFinset_card_of_nodup distinct],
    fun index inside => ?_⟩
  have listed := List.mem_toFinset.mp inside
  obtain ⟨visit, exploring, meets⟩ := explored index listed
  exact ⟨listed, visit, Nat.lt_succ_of_le exploring,
    retrace_solves_explored family goals length last signal explore index (decodes index) visit
      visit exploring (Nat.le_refl visit) meets⟩

end AcornVerif.Kernel
