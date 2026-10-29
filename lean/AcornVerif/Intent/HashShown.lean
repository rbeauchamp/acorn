/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.Hash

/-!
# The hash record's consequences, as shown to the owner

Each consequence the owner is asked to confirm or decline is proved to hold of the record as shown
(`LeanIntent.Shown`), and `hashesExplained` glosses every statement of the record in plain words.
A second, blind formalization of the same words by a model of another provider wrote "about as
rarely as pure chance" as a bound on a collision probability whose tolerance and whose relevant
patterns it left for the owner to choose, allowed a single changed input to collide at that rate,
and left open whether the two functions share their spots; the glosses of `oneInputMoves`,
`noRuleKeepsSpots` and `pairsApart` show the owner where this record decides those points.
-/

namespace AcornVerif.Intent.Hash

open LeanIntent

/-- Combining the three inputs by exclusive or. -/
def xorAll (x : Inputs) : UInt64 := x.1 ^^^ x.2.1 ^^^ x.2.2

/-- Combining the three inputs by addition. -/
def addAll (x : Inputs) : UInt64 := x.1 + x.2.1 + x.2.2

/-- The rule that exchanges the first two inputs and shifts nothing. -/
def exchangeFirstTwo : Rule := ⟨.bac, .flip, (0, 0, 0)⟩

theorem exchangeFirstTwo_moves : exchangeFirstTwo.Moves := fun h => nomatch h.1

/-- A function that gives every input the spot of the same input with its first two exchanged
meets no part of `noRuleKeepsSpots`. -/
theorem not_noRuleKeepsSpots_of_symmetric {f : Inputs → UInt64}
    (hsym : ∀ a b c, f (b, a, c) = f (a, b, c)) : ¬ NoRuleKeepsSpots f := fun h =>
  let ⟨(a, b, c), hx⟩ := h exchangeFirstTwo exchangeFirstTwo_moves
  hx (by
    show f (b ^^^ 0, a ^^^ 0, c ^^^ 0) = f (a, b, c)
    rw [UInt64.xor_zero, UInt64.xor_zero, UInt64.xor_zero]
    exact hsym a b c)

/-- The record rules out combining the inputs by exclusive or or by addition, in either function:
exchanging the first two inputs keeps every spot. -/
def rulesOutPlainCombinations : Consequence Hashes :=
  ⟨"neither function combines its inputs by plain exclusive or or plain addition", .entailment,
    fun w => w.hash2 ≠ xorAll ∧ w.hash2 ≠ addAll ∧ w.hash3 ≠ xorAll ∧ w.hash3 ≠ addAll⟩

theorem rulesOutPlainCombinations_holds : rulesOutPlainCombinations.HoldsOf hashes := by
  intro w hw
  obtain ⟨-, ⟨h2, h3⟩, -⟩ := hashes_meets.mp hw
  have hx : ∀ a b c : UInt64, xorAll (b, a, c) = xorAll (a, b, c) := fun a b c => by
    show b ^^^ a ^^^ c = a ^^^ b ^^^ c
    rw [UInt64.xor_comm b a]
  have hp : ∀ a b c : UInt64, addAll (b, a, c) = addAll (a, b, c) := fun a b c => by
    show b + a + c = a + b + c
    rw [UInt64.add_comm b a]
  exact ⟨fun he => not_noRuleKeepsSpots_of_symmetric hx (he ▸ h2),
    fun he => not_noRuleKeepsSpots_of_symmetric hp (he ▸ h2),
    fun he => not_noRuleKeepsSpots_of_symmetric hx (he ▸ h3),
    fun he => not_noRuleKeepsSpots_of_symmetric hp (he ▸ h3)⟩

/-- Changing any one input always moves the spot, in both functions. -/
def oneChangeMoves : Consequence Hashes :=
  ⟨"changing any one input always moves the spot", .entailment,
    fun w => OneInputMoves w.hash2 ∧ OneInputMoves w.hash3⟩

theorem oneChangeMoves_holds : oneChangeMoves.HoldsOf hashes :=
  fun _ hw => (hashes_meets.mp hw).1

/-- No fixed rule of reordering and shifting keeps every spot of either function. -/
def noFixedRule : Consequence Hashes :=
  ⟨"no fixed rule of reordering and shifting the inputs keeps every spot", .entailment,
    fun w => NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3⟩

theorem noFixedRule_holds : noFixedRule.HoldsOf hashes :=
  fun _ hw => (hashes_meets.mp hw).2.1

/-- The two functions never systematically share their spots. -/
def apart : Consequence Hashes :=
  ⟨"the two functions never systematically share their spots", .entailment,
    fun w => ∀ r : Rule, ∃ x, w.hash3 x ≠ w.hash2 (r.apply x)⟩

theorem apart_holds : apart.HoldsOf hashes := fun _ hw => (hashes_meets.mp hw).2.2

/-- The same inputs always give the same spot. It holds of every pair of functions, the record's
models among them: a Lean function gives one result for each input. -/
def replay : Consequence Hashes :=
  ⟨"the same inputs always give the same spot", .entailment,
    fun w => ∀ x y, x = y → w.hash2 x = w.hash2 y ∧ w.hash3 x = w.hash3 y⟩

theorem replay_holds : replay.HoldsOf hashes := fun _ _ _ _ h => h ▸ ⟨rfl, rfl⟩

/-! ## The record explained -/

/-- The hash record explained for its owner. -/
def hashesExplained : Explanation hashes where
  shape :=
    { requires := "The subject is the pair of hash functions, each taking three 64-bit inputs \
        to one 64-bit spot."
      rulesOut := "Nothing by itself."
      allows := "Any pair of such functions, until the properties narrow it."
      freedom := "None of its own. The pair carries no state from one call to the next, so it \
        is declared a plain value, of which obligation O4 asks nothing." }
  dom := []
  props := [
    { requires := "In each function, changing exactly one input, the others kept, always \
        changes the spot: never the same spot, not merely rarely."
      rulesOut := "A function that ignores an input, and one where two values of one input \
        share a spot for some values of the others."
      allows := "Any amount of sharing between inputs that differ in two or three places."
      freedom := "Everything about inputs that differ in more than one place. Pure chance \
        would let one changed input share a spot about once in 2^64 tries; a second, blind \
        reading of your words allowed that." },
    { requires := "No fixed rule moves every input to a different input in the same spot. A \
        rule here puts the three inputs in some order, then adds a fixed amount to each, or \
        flips fixed bits of each."
      rulesOut := "Combining the inputs by plain exclusive or or plain addition, where swapping \
        two inputs keeps the spot; and any function where adding the same amounts, or \
        flipping the same bits, keeps every spot."
      allows := "Rules of other kinds, such as multiplying the inputs by fixed numbers; and any \
        number of inputs sharing spots without a fixed rule behind it."
      freedom := "How often inputs share spots overall: the record bounds no rate. A second, \
        blind reading of your words wrote 'about as rarely as pure chance' as a bound on that \
        rate, with the tolerance and the patterns that count left for you to choose." },
    { requires := "No fixed rule of the same kind makes the second function give every input \
        the spot the first gives the moved input, so the two never systematically share \
        their spots."
      rulesOut := "The second function being the first, or the first with its inputs \
        reordered or shifted."
      allows := "Two functions that share spots for some inputs."
      freedom := "Whether the two functions send their inputs into one space of spots at all, \
        which this reading assumes and a second, blind reading left open." }]
  vocab := [
    { requires := "Two spots are the same 64-bit value."
      rulesOut := "Spots 0 and 1."
      allows := "Spots 0 and 0."
      freedom := "None: it is equality." }]
  consequences := [
    ⟨oneChangeMoves, oneChangeMoves_holds,
      { requires := "Changing any one input always moves the spot, in both functions."
        rulesOut := "Any single changed input landing in the same spot."
        allows := "Inputs that differ in two or three places sharing a spot."
        freedom := "None beyond the property's." }⟩,
    ⟨noFixedRule, noFixedRule_holds,
      { requires := "No fixed reordering and shifting of the inputs keeps every spot."
        rulesOut := "Systematic sharing by any such rule."
        allows := "Sharing by rules of other kinds, and sharing with no fixed rule."
        freedom := "Which rules count as systematic beyond these." }⟩,
    ⟨rulesOutPlainCombinations, rulesOutPlainCombinations_holds,
      { requires := "Neither function combines its three inputs by plain exclusive or or by \
          plain addition."
        rulesOut := "Those two combinations, since swapping two inputs keeps their spot."
        allows := "Combinations that mix the inputs before combining them."
        freedom := "None that this consequence adds." }⟩,
    ⟨apart, apart_holds,
      { requires := "The two functions never systematically share their spots."
        rulesOut := "One function being a copy of the other, up to a fixed rule."
        allows := "The two sharing some spots."
        freedom := "None beyond the property's." }⟩,
    ⟨replay, replay_holds,
      { requires := "The same inputs always give the same spot, so a run can be replayed."
        rulesOut := "Nothing: every function of this type meets it."
        allows := "Every pair of functions."
        freedom := "None. It holds by construction; replay further trusts the compiler and \
          the machine to compute 64-bit words alike everywhere." }⟩]

end AcornVerif.Intent.Hash
