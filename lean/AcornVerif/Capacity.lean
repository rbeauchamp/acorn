import AcornVerif.Campaign
import Mathlib.Data.Fintype.BigOperators

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {family : WorldClass interface} {goals : family.Goals}

abbrev WorldClass.copies (family : WorldClass interface) (count : ℕ) : WorldClass interface where
  Index := family.Index × Fin count
  world := fun index => family.world index.1
  start := fun index => family.start index.1

def copiesGoals (goals : family.Goals) (count : ℕ) : (family.copies count).Goals :=
  fun index => goals index.1

theorem covered_copies {count bound : ℕ}
    (covered : Covered (family.copies count) (copiesGoals goals count) bound)
    (actions : ℕ → Act interface) (solved : Finset family.Index)
    (each : ∀ index ∈ solved, (goals index).MetBy (family.start index) actions) :
    solved.card * count ≤ bound := by
  have all := covered actions (solved ×ˢ (Finset.univ : Finset (Fin count)))
    (fun index member => each index.1 (Finset.mem_product.mp member).1)
  rwa [Finset.card_product, Finset.card_univ, Fintype.card_fin] at all

theorem not_concealed_of_blindSolvable {length bound : ℕ} (actions : ℕ → Act interface)
    (solves : ∀ index, (visitGoals goals length index).MetBy (family.start index) actions) :
    IsEmpty (ConcealedClass family goals length bound) :=
  ⟨fun big => absurd big.large
    (Nat.not_lt.mpr (blindSolvable_covered actions solves big.covered big.members))⟩

def Diverse (world : World interface) (start : world.State) (count : ℕ) : Prop :=
  ∃ states : Fin count → world.State, Function.Injective states ∧
    ∀ index, Reachable world start (states index)

def idleWorld (interface : Interface) (shown : Percept interface) : World interface where
  State := ℕ
  step := fun state _ => state
  percept := fun _ => shown

def tallyWorld (interface : Interface) (shown : Percept interface) : World interface where
  State := ℕ
  step := fun state _ => state + 1
  percept := fun _ => shown

theorem idle_reach (shown : Percept interface) (start state : (idleWorld interface shown).State)
    (reach : Reachable (idleWorld interface shown) start state) : state = start := by
  induction reach with
  | here => rfl
  | next _ _ ih => exact ih

theorem idle_not_diverse (shown : Percept interface) :
    ¬ Diverse (idleWorld interface shown) (0 : ℕ) 2 := by
  rintro ⟨states, apart, reached⟩
  have same : states 0 = states 1 :=
    (idle_reach shown _ _ (reached 0)).trans (idle_reach shown _ _ (reached 1)).symm
  exact absurd (apart same) (by decide)

theorem tally_path (shown : Percept interface) (actions : ℕ → Act interface) (time : ℕ) :
    path (tallyWorld interface shown) (0 : ℕ) actions time = time := by
  induction time with
  | zero => rfl
  | succ time ih => exact congrArg Nat.succ ih

theorem tally_diverse (shown : Percept interface) (actions : ℕ → Act interface) (count : ℕ) :
    Diverse (tallyWorld interface shown) (0 : ℕ) count :=
  ⟨fun index => index.val, fun _ _ same => Fin.ext same, fun index => by
    have reach := path_reachable (tallyWorld interface shown) (0 : ℕ) actions index.val
    rwa [tally_path] at reach⟩

def ActionsDistinct (world : World interface) (start : world.State)
    (policy : world.State → Act interface) (count : ℕ) : Prop :=
  ∀ actions : ℕ → Act interface, ∃ times : Fin count → ℕ, ∀ first second, first ≠ second →
    policy (path world start actions (times first)) ≠
      policy (path world start actions (times second))

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

def CapacityDependent (decision : ℕ → Prop) (tight loose : ℕ) : Prop :=
  tight ≤ loose ∧ decision tight ∧ ¬ decision loose

theorem not_dependent_of_always {decision : ℕ → Prop} (always : ∀ bits, decision bits)
    (tight loose : ℕ) : ¬ CapacityDependent decision tight loose :=
  fun dependent => dependent.2.2 (always loose)

theorem not_dependent_of_never {decision : ℕ → Prop} {tight : ℕ} (never : ¬ decision tight)
    (loose : ℕ) : ¬ CapacityDependent decision tight loose :=
  fun dependent => never dependent.2.1

structure BeyondCapacity (family : WorldClass interface) (goals : family.Goals)
    (length slots bits margin : ℕ) where
  reference : World interface
  origin : reference.State
  conceals : Conceals family goals reference origin
  cover : ℕ
  covered : Covered family (visitGoals goals length) cover
  members : Finset family.Index
  beyond : 2 ^ (bits + margin) * cover ^ (slots + 1) < members.card ^ (slots + 1)

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
