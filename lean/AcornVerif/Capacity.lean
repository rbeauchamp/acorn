/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Campaign
import Mathlib.Data.Fintype.BigOperators

/-!
# Candidates for contract 2 (d), tried against the kernel, and padded classes

* Padding. `covered_copies`: repeating every member of a class raises every covering bound as
  fast as it raises the member count, so copies buy no margin for (c) or (d).
  `not_concealed_of_blindSolvable`: a class one action sequence solves is never a `ConcealedClass`.
* `Diverse` (adapted from the owner's earlier work, reachable diversity): a count of the states a
  world enters. `idle_not_diverse` shows it rejects states that are never entered;
  `tally_diverse` shows it admits a world that only counts its steps, whatever the agent does, so
  by itself it counts states no goal needs.
* `ActionsDistinct` (adapted from the owner's earlier work, policy irreducibility): every action
  sequence passes through `count` states at which a tracked policy asks pairwise different
  actions. `actionsDistinct_small` shows that no world meets it beyond the interface's number of
  actions, so over Acorn's fixed interface it is unsatisfiable at any real memory width.
* `CapacityDependent` (adapted from the owner's earlier work, capacity dependence): a decision
  indexed by a memory width holds at the tight width and fails at the loose one.
  `not_dependent_of_always` and `not_dependent_of_never` are its two failing examples.
* `BeyondCapacity`: contract 2 (d) in Acorn's counted form with an explicit margin in bits, as a
  structure a class can be proved to meet. `BeyondCapacity.unsolved`: on such a class, for every
  agent whose memory fits the width and every cycle, some assignment of the class's members to the
  campaign's slots has a slot the agent does not solve on that cycle.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {family : WorldClass interface} {goals : family.Goals}

/-! ## Padded classes -/

/-- A class with every member repeated a number of times. -/
abbrev WorldClass.copies (family : WorldClass interface) (count : ℕ) : WorldClass interface where
  Index := family.Index × Fin count
  world := fun index => family.world index.1
  start := fun index => family.start index.1

/-- The goals of a class with repeated members: each copy has its member's goal. -/
def copiesGoals (goals : family.Goals) (count : ℕ) : (family.copies count).Goals :=
  fun index => goals index.1

/-- **Copies raise the covering bound with the member count.** Where one action sequence meets
the goals of a set of members, every covering bound of the class with each member repeated
`count` times is at least `count` times the size of that set. -/
theorem covered_copies {count bound : ℕ}
    (covered : Covered (family.copies count) (copiesGoals goals count) bound)
    (actions : ℕ → Act interface) (solved : Finset family.Index)
    (each : ∀ index ∈ solved, (goals index).MetBy (family.start index) actions) :
    solved.card * count ≤ bound := by
  have all := covered actions (solved ×ˢ (Finset.univ : Finset (Fin count)))
    (fun index member => each index.1 (Finset.mem_product.mp member).1)
  rwa [Finset.card_product, Finset.card_univ, Fintype.card_fin] at all

/-- **A class one action sequence solves is not big**, at any visit length and covering bound:
the margin of condition (c) cannot hold of it. A class of copies of one problem is such a class. -/
theorem not_concealed_of_blindSolvable {length bound : ℕ} (actions : ℕ → Act interface)
    (solves : ∀ index, (visitGoals goals length index).MetBy (family.start index) actions) :
    IsEmpty (ConcealedClass family goals length bound) :=
  ⟨fun big => absurd big.large
    (Nat.not_lt.mpr (blindSolvable_covered actions solves big.covered big.members))⟩

/-! ## Reachable diversity -/

/-- Adapted from the owner's earlier work (reachable diversity). A world enters at least `count`
different states from a start state. -/
def Diverse (world : World interface) (start : world.State) (count : ℕ) : Prop :=
  ∃ states : Fin count → world.State, Function.Injective states ∧
    ∀ index, Reachable world start (states index)

/-- A world that never leaves its state, however large its state type. -/
def idleWorld (interface : Interface) (shown : Percept interface) : World interface where
  State := ℕ
  step := fun state _ => state
  percept := fun _ => shown

/-- A world that counts its steps and nothing else: one percept, and the same next state whatever
the action. -/
def tallyWorld (interface : Interface) (shown : Percept interface) : World interface where
  State := ℕ
  step := fun state _ => state + 1
  percept := fun _ => shown

/-- The idle world stays where it starts. -/
theorem idle_reach (shown : Percept interface) (start state : (idleWorld interface shown).State)
    (reach : Reachable (idleWorld interface shown) start state) : state = start := by
  induction reach with
  | here => rfl
  | next _ _ ih => exact ih

/-- **States that are never entered do not count.** The idle world enters one state. -/
theorem idle_not_diverse (shown : Percept interface) :
    ¬ Diverse (idleWorld interface shown) (0 : ℕ) 2 := by
  rintro ⟨states, apart, reached⟩
  have same : states 0 = states 1 :=
    (idle_reach shown _ _ (reached 0)).trans (idle_reach shown _ _ (reached 1)).symm
  exact absurd (apart same) (by decide)

/-- The tally world's state after a number of steps is that number, whatever the actions. -/
theorem tally_path (shown : Percept interface) (actions : ℕ → Act interface) (time : ℕ) :
    path (tallyWorld interface shown) (0 : ℕ) actions time = time := by
  induction time with
  | zero => rfl
  | succ time ih => exact congrArg Nat.succ ih

/-- **Reachable diversity alone counts states no goal needs.** The tally world enters as many
states as asked, over any interface with an action, though it shows one percept and its state
does not depend on what the agent does. -/
theorem tally_diverse (shown : Percept interface) (actions : ℕ → Act interface) (count : ℕ) :
    Diverse (tallyWorld interface shown) (0 : ℕ) count :=
  ⟨fun index => index.val, fun _ _ same => Fin.ext same, fun index => by
    have reach := path_reachable (tallyWorld interface shown) (0 : ℕ) actions index.val
    rwa [tally_path] at reach⟩

/-! ## A tracked policy with pairwise different actions -/

/-- Adapted from the owner's earlier work (policy irreducibility). Every action sequence passes
through `count` states at which the tracked policy asks pairwise different actions. It has no
witness beyond the interface's number of actions: `actionsDistinct_small` is its failing side. -/
def ActionsDistinct (world : World interface) (start : world.State)
    (policy : world.State → Act interface) (count : ℕ) : Prop :=
  ∀ actions : ℕ → Act interface, ∃ times : Fin count → ℕ, ∀ first second, first ≠ second →
    policy (path world start actions (times first)) ≠
      policy (path world start actions (times second))

/-- **Over a fixed interface the form is unsatisfiable beyond the number of actions.** A tracked
policy asks at most as many pairwise different actions as the interface has. -/
theorem actionsDistinct_small {world : World interface} {start : world.State}
    {policy : world.State → Act interface} {count : ℕ} (actions : ℕ → Act interface)
    (distinct : ActionsDistinct world start policy count) :
    count ≤ interface.actions.word.toNat := by
  obtain ⟨times, apart⟩ := distinct actions
  have injective : Function.Injective
      (fun index : Fin count => policy (path world start actions (times index))) := by
    intro first second same
    by_contra differ
    exact apart first second differ same
  have card := Fintype.card_le_of_injective _ injective
  rwa [Fintype.card_fin, Fintype.card_fin] at card

/-! ## Capacity dependence -/

/-- Adapted from the owner's earlier work (capacity dependence), with the direction fixed. A
decision indexed by a memory width in bits holds at the tight width and fails at a looser one. -/
def CapacityDependent (decision : ℕ → Prop) (tight loose : ℕ) : Prop :=
  tight ≤ loose ∧ decision tight ∧ ¬ decision loose

/-- A decision that holds at every width does not depend on capacity: an infeasible goal, which
nobody of any size achieves, is such a decision. -/
theorem not_dependent_of_always {decision : ℕ → Prop} (always : ∀ bits, decision bits)
    (tight loose : ℕ) : ¬ CapacityDependent decision tight loose :=
  fun dependent => dependent.2.2 (always loose)

/-- A decision that fails at the tight width does not depend on capacity: a goal the small agent
already achieves is such a decision. -/
theorem not_dependent_of_never {decision : ℕ → Prop} {tight : ℕ} (never : ¬ decision tight)
    (loose : ℕ) : ¬ CapacityDependent decision tight loose :=
  fun dependent => never dependent.2.1

/-! ## Contract 2 (d) in counted form -/

/-- **Beyond capacity, by a margin.** The class conceals its goals, one action sequence meets at
most `cover` members within a visit, and a finite set of its members is so large that the
assignments of its members to `slots + 1` campaign slots outnumber `2 ^ (bits + margin)` times
the assignments one memory can solve wholly. No class is yet proved to meet it, and no class is
proved to fail it for the reason it exists: it has neither a witness nor a failing example here,
only its consequence `BeyondCapacity.unsolved`. -/
structure BeyondCapacity (family : WorldClass interface) (goals : family.Goals)
    (length slots bits margin : ℕ) where
  /-- The reference world behind which the class conceals its goals. -/
  reference : World interface
  /-- The reference world's start state. -/
  origin : reference.State
  /-- Condition (b). -/
  conceals : Conceals family goals reference origin
  /-- How many members one action sequence meets within a visit, at most. -/
  cover : ℕ
  /-- The covering bound. -/
  covered : Covered family (visitGoals goals length) cover
  /-- The members the campaign's slots are filled from. -/
  members : Finset family.Index
  /-- The count: more assignments than a memory of `bits + margin` bits can solve wholly. -/
  beyond : 2 ^ (bits + margin) * cover ^ (slots + 1) < members.card ^ (slots + 1)

/-- **On a class beyond its capacity no agent solves every campaign on any cycle.** For every
agent whose memory fits `bits` bits and every cycle, some assignment of the class's members to the
slots has a slot the agent does not solve on that cycle. -/
theorem BeyondCapacity.unsolved {length slots bits margin : ℕ}
    (beyond : BeyondCapacity family goals length slots bits margin) (agent : Agent interface)
    (fits : MemoryWithin agent bits) (cycle : ℕ) :
    ∃ assignment : Fin (slots + 1) → family.Index,
      (∀ slot, assignment slot ∈ beyond.members) ∧
        ¬ ∀ slot, SolvesSlot family goals length slots assignment agent cycle slot := by
  classical
  by_contra none
  have each : ∀ assignment ∈ Fintype.piFinset (fun _ : Fin (slots + 1) => beyond.members),
      ∀ slot, SolvesSlot family goals length slots assignment agent cycle slot := by
    intro assignment member
    by_contra unsolved
    exact none ⟨assignment, Fintype.mem_piFinset.mp member, unsolved⟩
  have count := campaign_count_bits beyond.conceals beyond.covered agent bits fits slots cycle
    _ each
  rw [Fintype.card_piFinset_const] at count
  have wider : 2 ^ bits * beyond.cover ^ (slots + 1) ≤
      2 ^ (bits + margin) * beyond.cover ^ (slots + 1) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.le_add_right bits margin))
  exact absurd beyond.beyond (Nat.not_lt.mpr (count.trans wider))

end AcornVerif.Kernel
