/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Visits
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The campaign counting bound

A `campaign` presents the slots of a class in one stream: one visit of a fixed length to each
slot in turn, cycle after cycle, with the agent never restarted and each slot's world starting
each visit from its own start state. An assignment picks a member for each slot, so a campaign
holds at least one slot. A visit takes `length + 1` decisions, as in `Kernel.visits`.

This is condition (d) of the mission contract's contract 2. For a class that conceals its goals
behind one reference world, with a covering bound `k` for one visit, take a set of assignments
of `N` slots on each of which an agent solves every slot on a given cycle. Then the set holds at
most `m · k ^ N` assignments, where `m` is the size of any set holding the memories the agent has
at that cycle's start (`campaign_count`), and at most `2 ^ b · k ^ N` for an agent whose memory
fits `b` bits (`campaign_count_bits`). Both hold for every agent, number of slots and cycle.

The proof follows the argument in the contract. A slot solved on a cycle is its member solved in
its own world from the memory at its visit's start (`solvesSlot_solves`), and concealment bounds
by `k` the members solved from one memory. The memory at the next slot is a function of this
slot's memory and member (`campaign_memory_next`), so fixing the memory at a slot leaves at most
`k` members for it, each fixing the memory at the next: `tracked_count`. Grouping the assignments
by the memory at the cycle's start gives the bound.

This is a lemma the mission theorem on campaigns uses, and not a mission result about learning.
`campaign_count` holds of the executed agent as of every agent, but says little of it yet: that
agent's memory type holds exact naturals, so `MemoryWithin` holds of it at no width and
`campaign_count_bits` gives nothing, and no theorem bounds the size of a set holding the memories
it reaches.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-- A campaign: one visit of `length` steps to each slot in turn, cycle after cycle. A visit takes
`length + 1` decisions, as in `Kernel.visits`, and the next slot's world starts from its own
start state. -/
def campaign (family : WorldClass interface) (length slots : ℕ)
    (assignment : Fin (slots + 1) → family.Index) : World interface where
  State := Σ slot : Fin (slots + 1), (family.world (assignment slot)).State × Fin (length + 1)
  step := fun state action =>
    if within : state.2.2.val < length then
      ⟨state.1, (family.world (assignment state.1)).step state.2.1 action,
        ⟨state.2.2.val + 1, by omega⟩⟩
    else
      ⟨⟨(state.1.val + 1) % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩,
        family.start _, ⟨0, Nat.succ_pos length⟩⟩
  percept := fun state => (family.world (assignment state.1)).percept state.2.1

/-- The first state of a campaign: the first slot's start. -/
def campaignStart (family : WorldClass interface) (length slots : ℕ)
    (assignment : Fin (slots + 1) → family.Index) :
    (campaign family length slots assignment).State :=
  ⟨0, family.start _, ⟨0, Nat.succ_pos length⟩⟩

/-- The decisions before a slot's visit of a cycle. -/
def campaignTime (length slots cycle : ℕ) (slot : Fin (slots + 1)) : ℕ :=
  (cycle * (slots + 1) + slot.val) * (length + 1)

/-- An agent solves a slot on a cycle when, in that slot's visit of that cycle, some state after
one to `length` steps satisfies the slot's goal. -/
def SolvesSlot (family : WorldClass interface) (goals : family.Goals) (length slots : ℕ)
    (assignment : Fin (slots + 1) → family.Index) (agent : Agent interface)
    (cycle : ℕ) (slot : Fin (slots + 1)) : Prop :=
  ∃ step, 1 ≤ step ∧ step ≤ length ∧
    let state := stateAt (campaign family length slots assignment) agent
      (campaignStart family length slots assignment) (campaignTime length slots cycle slot + step)
    state.1 = slot ∧ (goals (assignment state.1)).satisfied state.2.1

/-! ## One visit in the campaign -/

variable {family : WorldClass interface} {length slots : ℕ}
  {assignment : Fin (slots + 1) → family.Index}

/-- The first state of a slot's visit. -/
def slotStart (family : WorldClass interface) (length slots : ℕ)
    (assignment : Fin (slots + 1) → family.Index) (slot : Fin (slots + 1)) :
    (campaign family length slots assignment).State :=
  ⟨slot, family.start _, ⟨0, Nat.succ_pos length⟩⟩

/-- Within a visit the campaign's closed loop is the member's own. -/
theorem campaign_loop (agent : Agent interface) (slot : Fin (slots + 1)) (time : ℕ)
    (within : time ≤ length) :
    loop (campaign family length slots assignment) agent
        (slotStart family length slots assignment slot) time =
      (⟨slot, (loop (family.world (assignment slot)) agent (family.start _) time).1,
        ⟨time, Nat.lt_succ_of_le within⟩⟩,
        (loop (family.world (assignment slot)) agent (family.start _) time).2) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have earlier := ih (Nat.le_of_succ_le within)
    have short : time < length := Nat.lt_of_succ_le within
    change interact (campaign family length slots assignment) agent
      (loop (campaign family length slots assignment) agent
        (slotStart family length slots assignment slot) time) = _
    rw [earlier]
    simp only [interact, campaign, dite_eq_left short]
    rfl

/-- The memory after one visit of a member from a memory. -/
def visitEnd (agent : Agent interface) (family : WorldClass interface) (memory : agent.Memory)
    (index : family.Index) (length : ℕ) : agent.Memory :=
  (agent.act (memoryAt (family.world index) (agent.resume memory) (family.start index) length)
    (perceptAt (family.world index) (agent.resume memory) (family.start index) length)).2

/-- A visit's last decision moves the campaign to the next slot's start. -/
theorem campaign_return (agent : Agent interface) (slot : Fin (slots + 1))
    (memory : agent.Memory) :
    loop (campaign family length slots assignment) (agent.resume memory)
        (slotStart family length slots assignment slot) (length + 1) =
      (slotStart family length slots assignment
        ⟨(slot.val + 1) % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩,
        visitEnd agent family memory (assignment slot) length) := by
  have last := campaign_loop (family := family) (assignment := assignment) (length := length)
    (agent.resume memory) slot length (Nat.le_refl length)
  change interact (campaign family length slots assignment) (agent.resume memory)
    (loop (campaign family length slots assignment) (agent.resume memory)
      (slotStart family length slots assignment slot) length) = _
  rw [last]
  simp only [interact, campaign, dite_eq_right (Nat.lt_irrefl length)]
  rfl

/-- At each multiple of a visit's decisions the campaign is at the start of a slot's visit. -/
theorem campaign_period (agent : Agent interface) (count : ℕ) :
    stateAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment) (count * (length + 1)) =
      slotStart family length slots assignment
        ⟨count % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩ := by
  induction count with
  | zero =>
    rw [Nat.zero_mul]
    have first : (⟨0 % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩ : Fin (slots + 1)) = 0 :=
      Fin.ext (by simp)
    rw [first]
    rfl
  | succ count ih =>
    rw [Nat.add_mul, Nat.one_mul, stateAt_add, ih]
    have back := congrArg Prod.fst (campaign_return (family := family) (assignment := assignment)
      (length := length) agent ⟨count % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩
      (memoryAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment) (count * (length + 1))))
    refine back.trans (congrArg (slotStart family length slots assignment) (Fin.ext ?_))
    exact Nat.mod_add_mod count (slots + 1) 1

/-- The slot of the visit at a campaign time. -/
theorem visitNumber_slot (cycle : ℕ) (slot : Fin (slots + 1)) :
    (⟨(cycle * (slots + 1) + slot.val) % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩ :
      Fin (slots + 1)) = slot :=
  Fin.ext (by
    change (cycle * (slots + 1) + slot.val) % (slots + 1) = slot.val
    rw [Nat.mul_comm cycle, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt slot.isLt)

/-- At a slot's time of a cycle the campaign is at the start of that slot's visit. -/
theorem campaign_state_slot (agent : Agent interface) (cycle : ℕ) (slot : Fin (slots + 1)) :
    stateAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment) (campaignTime length slots cycle slot) =
      slotStart family length slots assignment slot :=
  (campaign_period agent _).trans (congrArg _ (visitNumber_slot cycle slot))

/-- A slot solved on a cycle is its member solved from the memory at its visit's start. -/
theorem solvesSlot_solves (goals : family.Goals) (agent : Agent interface) (cycle : ℕ)
    (slot : Fin (slots + 1))
    (solved : SolvesSlot family goals length slots assignment agent cycle slot) :
    Solves family (visitGoals goals length)
      (agent.resume (memoryAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment) (campaignTime length slots cycle slot)))
      (assignment slot) := by
  obtain ⟨step, low, high, same, met⟩ := solved
  refine ⟨step, low, high, ?_⟩
  have split := stateAt_add (campaign family length slots assignment) agent
    (campaignStart family length slots assignment) (campaignTime length slots cycle slot) step
  rw [campaign_state_slot] at split
  have inner := congrArg Prod.fst (campaign_loop (family := family) (assignment := assignment)
    (length := length) (agent.resume (memoryAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment) (campaignTime length slots cycle slot)))
    slot step high)
  have whole := split.trans inner
  have reduce : ∀ (state : (campaign family length slots assignment).State)
      (x : (family.world (assignment slot)).State) (c : Fin (length + 1)),
      state = ⟨slot, x, c⟩ → (goals (assignment state.1)).satisfied state.2.1 →
        (goals (assignment slot)).satisfied x := by
    intro state x c same held
    subst same
    exact held
  exact reduce _ _ _ whole met

/-- The memory at the next slot's visit is the memory after this slot's visit. -/
theorem campaign_memory_next (agent : Agent interface) (cycle : ℕ) (slot : Fin (slots + 1))
    (next : Fin (slots + 1)) (following : next.val = slot.val + 1) :
    memoryAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment) (campaignTime length slots cycle next) =
      visitEnd agent family (memoryAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment) (campaignTime length slots cycle slot))
        (assignment slot) length := by
  have time : campaignTime length slots cycle next =
      campaignTime length slots cycle slot + (length + 1) := by
    unfold campaignTime
    rw [following, ← Nat.add_assoc, Nat.add_mul, Nat.one_mul]
  rw [time, memoryAt_add, campaign_state_slot]
  exact congrArg Prod.snd (campaign_return (family := family) (assignment := assignment)
    (length := length) agent slot (memoryAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment) (campaignTime length slots cycle slot)))

/-! ## Counting -/

/-- Assignments of `count` slots each solved from the memory the earlier visits leave. -/
def Tracked {Memory Index : Type} (solves : Memory → Index → Prop)
    (advance : Memory → Index → Memory) : (count : ℕ) → Memory → (Fin count → Index) → Prop
  | 0, _, _ => True
  | count + 1, memory, chosen =>
    solves memory (chosen 0) ∧
      Tracked solves advance count (advance memory (chosen 0)) (Fin.tail chosen)

/-- If at most `bound` members are solved from each memory, at most `bound ^ count` assignments
of `count` slots are tracked from one memory. -/
theorem tracked_count {Memory Index : Type} (solves : Memory → Index → Prop)
    (advance : Memory → Index → Memory) (bound : ℕ)
    (few : ∀ (memory : Memory) (solved : Finset Index),
      (∀ index ∈ solved, solves memory index) → solved.card ≤ bound)
    (count : ℕ) (memory : Memory) (chosen : Finset (Fin count → Index))
    (each : ∀ assignment ∈ chosen, Tracked solves advance count memory assignment) :
    chosen.card ≤ bound ^ count := by
  classical
  induction count generalizing memory with
  | zero =>
    have single : chosen ⊆ {fun i => i.elim0} := by
      intro assignment _
      exact Finset.mem_singleton.mpr (funext fun i => i.elim0)
    simpa using Finset.card_le_card single
  | succ count ih =>
    have heads : (chosen.image fun assignment => assignment 0).card ≤ bound := by
      apply few memory
      intro index member
      obtain ⟨assignment, inside, rfl⟩ := Finset.mem_image.mp member
      exact (each assignment inside).1
    have fibers : ∀ head ∈ chosen.image (fun assignment => assignment 0),
        (chosen.filter fun assignment => assignment 0 = head).card ≤ bound ^ count := by
      intro head _
      have injective : Set.InjOn (Fin.tail (n := count) (α := fun _ => Index))
          (chosen.filter fun assignment => assignment 0 = head : Finset _) := by
        intro first firstIn second secondIn same
        have firstHead := (Finset.mem_filter.mp (Finset.mem_coe.mp firstIn)).2
        have secondHead := (Finset.mem_filter.mp (Finset.mem_coe.mp secondIn)).2
        rw [← Fin.cons_self_tail first, ← Fin.cons_self_tail second, same, firstHead, secondHead]
      rw [← Finset.card_image_of_injOn injective]
      apply ih (advance memory head)
      intro tail member
      obtain ⟨assignment, inside, rfl⟩ := Finset.mem_image.mp member
      obtain ⟨present, isHead⟩ := Finset.mem_filter.mp inside
      have tracked := (each assignment present).2
      rwa [isHead] at tracked
    calc chosen.card
        ≤ bound ^ count * (chosen.image fun assignment => assignment 0).card :=
          Finset.card_le_mul_card_image chosen _ fibers
      _ ≤ bound ^ count * bound := Nat.mul_le_mul_left _ heads
      _ = bound ^ (count + 1) := (Nat.pow_succ _ _).symm

/-- The slots from one on, solved along the campaign, are tracked from that slot's memory. -/
theorem tracked_of_solved (goals : family.Goals) (agent : Agent interface) (cycle : ℕ)
    (each : ∀ slot, SolvesSlot family goals length slots assignment agent cycle slot)
    (remaining first : ℕ) (fits : first + remaining = slots + 1) :
    Tracked
      (fun memory index => Solves family (visitGoals goals length) (agent.resume memory) index)
      (fun memory index => visitEnd agent family memory index length) remaining
      (memoryAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment)
        (campaignTime length slots cycle ⟨first % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩))
      (fun position => assignment ⟨first + position.val, by have := position.isLt; omega⟩) := by
  induction remaining generalizing first with
  | zero => exact trivial
  | succ remaining ih =>
    have small : first < slots + 1 := by omega
    have name : (⟨first % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩ : Fin (slots + 1)) =
        ⟨first, small⟩ := Fin.ext (Nat.mod_eq_of_lt small)
    rw [name]
    refine ⟨solvesSlot_solves goals agent cycle ⟨first, small⟩ (each _), ?_⟩
    have nextMemory := ih (first + 1) (by omega)
    by_cases more : first + 1 < slots + 1
    · have nextName : (⟨(first + 1) % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩ :
          Fin (slots + 1)) = ⟨first + 1, more⟩ := Fin.ext (Nat.mod_eq_of_lt more)
      rw [nextName, campaign_memory_next agent cycle ⟨first, small⟩ ⟨first + 1, more⟩ rfl]
        at nextMemory
      have tails : (fun position : Fin remaining =>
          assignment ⟨first + 1 + position.val, by have := position.isLt; omega⟩) =
          Fin.tail (fun position : Fin (remaining + 1) =>
            assignment ⟨first + position.val, by have := position.isLt; omega⟩) := by
        funext position
        refine congrArg assignment (Fin.ext ?_)
        change first + 1 + position.val = first + (position.val + 1)
        omega
      rw [tails] at nextMemory
      exact nextMemory
    · have none : remaining = 0 := by omega
      subst none
      exact trivial

/-- **The campaign counting bound.** For a class that conceals its goals, with a covering bound
for one visit: take a set of assignments of `slots + 1` slots on each of which an agent solves
every slot on one cycle, and a set of memories holding the agent's memory at that cycle's start
under each. The assignments number at most the memories times the bound to the power of the
slots. It holds for every agent, number of slots and cycle, the first cycle included. -/
theorem campaign_count {goals : family.Goals}
    {reference : World interface} {origin : reference.State}
    (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound)
    (agent : Agent interface) (slots cycle : ℕ) (memories : Finset agent.Memory)
    (assignments : Finset (Fin (slots + 1) → family.Index))
    (reach : ∀ assignment ∈ assignments,
      memoryAt (campaign family length slots assignment) agent
        (campaignStart family length slots assignment)
        (campaignTime length slots cycle 0) ∈ memories)
    (each : ∀ assignment ∈ assignments, ∀ slot,
      SolvesSlot family goals length slots assignment agent cycle slot) :
    assignments.card ≤ memories.card * bound ^ (slots + 1) := by
  classical
  have few : ∀ (memory : agent.Memory) (solved : Finset family.Index),
      (∀ index ∈ solved, Solves family (visitGoals goals length) (agent.resume memory) index) →
        solved.card ≤ bound :=
    fun memory solved all =>
      (hidden.withLength length).need covered (agent.resume memory) trivial solved all
  let start : (Fin (slots + 1) → family.Index) → agent.Memory := fun assignment =>
    memoryAt (campaign family length slots assignment) agent
      (campaignStart family length slots assignment) (campaignTime length slots cycle 0)
  have fibers : ∀ memory ∈ assignments.image start,
      (assignments.filter fun assignment => start assignment = memory).card ≤
        bound ^ (slots + 1) := by
    intro memory _
    apply tracked_count _ (fun memory index => visitEnd agent family memory index length) bound few
      (slots + 1) memory
    intro assignment inside
    obtain ⟨present, same⟩ := Finset.mem_filter.mp inside
    have tracked := tracked_of_solved (assignment := assignment) goals agent cycle
      (each assignment present) (slots + 1) 0 (by omega)
    have name : (⟨0 % (slots + 1), Nat.mod_lt _ (Nat.succ_pos slots)⟩ : Fin (slots + 1)) = 0 :=
      Fin.ext (by simp)
    rw [name] at tracked
    have rename : (fun position : Fin (slots + 1) =>
        assignment ⟨0 + position.val, by have := position.isLt; omega⟩) = assignment := by
      funext position
      congr 1
      exact Fin.ext (by simp)
    rw [rename] at tracked
    rw [← same]
    exact tracked
  have image : (assignments.image start).card ≤ memories.card :=
    Finset.card_le_card (fun memory member => by
      obtain ⟨assignment, present, rfl⟩ := Finset.mem_image.mp member
      exact reach assignment present)
  calc assignments.card
      ≤ bound ^ (slots + 1) * (assignments.image start).card :=
        Finset.card_le_mul_card_image assignments _ fibers
    _ ≤ bound ^ (slots + 1) * memories.card := Nat.mul_le_mul_left _ image
    _ = memories.card * bound ^ (slots + 1) := Nat.mul_comm _ _

/-- The count for an agent whose memory fits `bits` bits: at most `2 ^ bits` times the bound to
the power of the slots. -/
theorem campaign_count_bits {goals : family.Goals}
    {reference : World interface} {origin : reference.State}
    (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound)
    (agent : Agent interface) (bits : ℕ) (fits : MemoryWithin agent bits) (slots cycle : ℕ)
    (assignments : Finset (Fin (slots + 1) → family.Index))
    (each : ∀ assignment ∈ assignments, ∀ slot,
      SolvesSlot family goals length slots assignment agent cycle slot) :
    assignments.card ≤ 2 ^ bits * bound ^ (slots + 1) := by
  classical
  obtain ⟨embed⟩ := fits
  let start : (Fin (slots + 1) → family.Index) → agent.Memory := fun assignment =>
    memoryAt (campaign family length slots assignment) agent
      (campaignStart family length slots assignment) (campaignTime length slots cycle 0)
  have reached := campaign_count hidden covered agent slots cycle (assignments.image start)
    assignments (fun assignment present => Finset.mem_image_of_mem start present) each
  have few : (assignments.image start).card ≤ 2 ^ bits := by
    have injective : Function.Injective embed := embed.injective
    have mapped := Finset.card_image_of_injective (assignments.image start) injective
    rw [← mapped]
    exact (Finset.card_le_univ _).trans (by simp)
  exact reached.trans (Nat.mul_le_mul_right _ few)

end AcornVerif.Kernel
