/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LeanIntentBridge

/-!
# Intent record: where the hash functions send their inputs

The owner holds intent for Acorn at the level of what a world and an agent should do, not per
function. For the two hash functions `Acorn.Rng.hash2` and `Acorn.Rng.hash3` the owner adopted, on
2026-10-29, a statement proposed by the assistant supervising this work after it had read the
functions' callers and an issue about them: different things the agent senses, different places, and different goals
should land in the same spot only about as rarely as pure chance, never systematically; the same
inputs always give the same result, so a run can be replayed. That statement is this record's only
source. The record was written knowing only the functions' types, read from Lean's environment,
each taking three 64-bit words to one; neither function's source was read before it.

The subject, `Hashes`, is the pair of functions. Each property is a part of the statement that a
theorem can carry:

* `oneInputMoves`: changing any one input, the others kept, always moves the spot. Pure chance
  would let such a change land in the same spot about once in 2^64 tries; the record asks for
  never, which is stronger than the statement by that margin. It is an interpretation, shown to the
  owner, because without it the record would admit a function that sends almost every input to
  one spot.
* `noRuleKeepsSpots`: no fixed rule moves every input to a different input in the same spot. A
  rule (`Rule`) reorders the three inputs and then shifts them by fixed amounts, by flipping fixed
  bits or by adding fixed numbers, the two arithmetics of a machine word. This is "never
  systematically" for the rules a combination of words by exclusive or, addition and reordering
  can obey.
* `pairsApart`: no rule makes one function agree with the other at every input, so the two never
  systematically share their spots. The statement says the two serve one purpose; reading that as
  sending into one space of spots is an interpretation, shown to the owner.

Not stated: "only about as rarely as pure chance" is a claim about how often inputs collide, a
rate, and no property here bounds a rate; rules outside the class above, such as multiplying the
inputs by a fixed factor, are not excluded. "The same inputs always give the same result" holds of
every subject of this type by construction, since a Lean function returns one result for each
input, so it is no property, which no subject could fail; the record shows it to the owner as a
consequence, and replay further trusts the compiler and runtime to compute 64-bit words alike on
every machine.
-/

namespace AcornVerif.Intent.Hash

open LeanIntent

/-- Three 64-bit inputs. -/
abbrev Inputs := UInt64 × UInt64 × UInt64

/-- The two hash functions, each taking three 64-bit inputs to a 64-bit spot. -/
structure Hashes where
  /-- The first function, `Acorn.Rng.hash2` in Acorn. -/
  hash2 : Inputs → UInt64
  /-- The second function, `Acorn.Rng.hash3` in Acorn. -/
  hash3 : Inputs → UInt64

/-- An order of three inputs: which input goes first, second and third. -/
inductive Order where
  /-- The inputs as given. -/
  | abc
  /-- The first two exchanged. -/
  | bac
  /-- The last two exchanged. -/
  | acb
  /-- The first and last exchanged. -/
  | cba
  /-- Each moved one place left. -/
  | bca
  /-- Each moved one place right. -/
  | cab

/-- The inputs put in the order `o`. -/
def Order.apply : Order → Inputs → Inputs
  | .abc, (a, b, c) => (a, b, c)
  | .bac, (a, b, c) => (b, a, c)
  | .acb, (a, b, c) => (a, c, b)
  | .cba, (a, b, c) => (c, b, a)
  | .bca, (a, b, c) => (b, c, a)
  | .cab, (a, b, c) => (c, a, b)

/-- The two ways a rule shifts each input by a fixed amount. -/
inductive Shift where
  /-- Flipping the bits set in the amount: exclusive or. -/
  | flip
  /-- Adding the amount, wrapping around at 2^64. -/
  | add

/-- One input shifted by `d`. -/
def Shift.apply : Shift → UInt64 → UInt64 → UInt64
  | .flip, x, d => x ^^^ d
  | .add, x, d => x + d

/-- A fixed rule that moves every input tuple to another: reorder the inputs, then shift each by
its own fixed amount. -/
structure Rule where
  /-- The reordering. -/
  order : Order
  /-- How the amounts are applied. -/
  shift : Shift
  /-- The amounts, one for each input in its new place. -/
  amount : Inputs

/-- The inputs the rule `r` moves `x` to. -/
def Rule.apply (r : Rule) (x : Inputs) : Inputs :=
  let (a, b, c) := r.order.apply x
  (r.shift.apply a r.amount.1, r.shift.apply b r.amount.2.1, r.shift.apply c r.amount.2.2)

/-- The rule `r` moves inputs: it is not the rule that keeps the inputs in their given order and
shifts them by nothing. -/
def Rule.Moves (r : Rule) : Prop := ¬ (r.order = .abc ∧ r.amount = (0, 0, 0))

/-- Changing exactly one input of `f`, the others kept, always changes the spot. -/
def OneInputMoves (f : Inputs → UInt64) : Prop :=
  (∀ a a' b c, f (a, b, c) = f (a', b, c) → a = a') ∧
    (∀ a b b' c, f (a, b, c) = f (a, b', c) → b = b') ∧
    (∀ a b c c', f (a, b, c) = f (a, b, c') → c = c')

/-- No rule that moves inputs keeps the spot of every input of `f`. -/
def NoRuleKeepsSpots (f : Inputs → UInt64) : Prop :=
  ∀ r : Rule, r.Moves → ∃ x, f (r.apply x) ≠ f x

/-- Changing any one input of either function always moves its spot. -/
def oneInputMoves : Clause Hashes :=
  ⟨"changing any one input always moves the spot", fun w =>
    OneInputMoves w.hash2 ∧ OneInputMoves w.hash3⟩

/-- No fixed rule of reordering and shifting keeps every spot of either function. -/
def noRuleKeepsSpots : Clause Hashes :=
  ⟨"no fixed rule of reordering and shifting the inputs keeps every spot", fun w =>
    NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3⟩

/-- No rule makes the second function agree with the first at every input. -/
def pairsApart : Clause Hashes :=
  ⟨"the two functions never systematically share their spots", fun w =>
    ∀ r : Rule, ∃ x, w.hash3 x ≠ w.hash2 (r.apply x)⟩

/-- The intent record of the hash functions. -/
def hashes : IntentRecord Hashes where
  shape := .value _
  dom := []
  props := [oneInputMoves, noRuleKeepsSpots, pairsApart]
  vocab := [⟨"same spot", UInt64 × UInt64, fun p => p.1 = p.2⟩]

/-- A pair of functions meets the record exactly when each moves its spot on any one changed
input, no moving rule keeps every spot of either, and no rule makes the second a copy of the
first. -/
theorem hashes_meets {w : Hashes} :
    hashes.Meets w ↔
      (OneInputMoves w.hash2 ∧ OneInputMoves w.hash3) ∧
      (NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3) ∧
      (∀ r : Rule, ∃ x, w.hash3 x ≠ w.hash2 (r.apply x)) := by
  constructor
  · intro h
    exact ⟨h.2 _ (List.mem_cons_self ..),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3

/-! ## Adequacy -/

/-- The pair whose functions both send every input to spot 0. -/
def constantZero : Hashes := ⟨fun _ => 0, fun _ => 0⟩

/-- O2: the record has a model of its (empty) domain hypotheses and an instance of its one
vocabulary predicate. -/
theorem hashes_o2 : O2 hashes := by
  refine (o2_correct _).mpr ⟨⟨constantZero, fun _ h => nomatch h⟩, ?_⟩
  intro p hp
  simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨(0, 0), rfl⟩

/-- O3: each property fails of the pair that sends everything to spot 0. Changing the first
input does not move its spot; adding 1 to the first input keeps every spot; and the second
function agrees with the first everywhere. -/
theorem hashes_o3 : O3 hashes := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨constantZero, fun h => absurd (h.1.1 0 1 0 0 rfl) (by decide)⟩
  · refine ⟨constantZero, fun h => ?_⟩
    obtain ⟨x, hx⟩ := h.1 ⟨.abc, .add, (1, 0, 0)⟩ (fun h => absurd (congrArg (·.1) h.2) (by decide))
    exact hx rfl
  · exact ⟨constantZero, fun h => let ⟨_, hx⟩ := h ⟨.abc, .flip, (0, 0, 0)⟩; hx rfl⟩

/-- O4: the subject is a pair of functions with no state carried from one call to the next,
declared `.value`, of which O4 asks nothing. -/
theorem hashes_o4 : O4 hashes := (o4_correct _).mpr trivial

/-- O5 with the widest freedom, which every record meets. -/
theorem hashes_o5_widest : O5 hashes .widest := o5_widest _

end AcornVerif.Intent.Hash
