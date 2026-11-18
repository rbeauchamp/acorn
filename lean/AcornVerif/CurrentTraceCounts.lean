/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentFirstChoice
import AcornVerif.FloatLibBridge
import Mathlib.Tactic.IntervalCases

/-!
# Trace totals of rows taken once, and the candidate they name

After a first reward of one, the value of each action at a frame is its row's trace total there
(`AcornVerif.CurrentFirstChoice.reward_values`), and the first decision after the reward compares
those totals (`AcornVerif.CurrentFirstChoice.first_choice`). This module says what a total is for
a row whose action was taken once before the reward: the ordered sum of one named word, taken
once for each slot the frame shares with the frame the row laid. It then says, under the
discounted criterion, which action is the one candidate, from the counts of shared slots alone.

**A row taken once.** Take a controller whose rewards have all been zero. A row that holds no
trace reads a zero word for the trace total of the frame it lays, so on a frame of at most 1999
slots the laid increment is the whole stored step size: after the step, each slot of the frame
holds `AcornVerif.CurrentCreditHorizon.stepWord` in that row, and no other slot is eligible
(`fresh_laid`). Each later reward-free step that takes another action multiplies those traces by
the trace decay, and prunes none while the decayed trace is above the pruning threshold
(`fresh_after`), which it is for eighty such steps (`freshChain_above`). Call the stored step
size decayed a number of times, as one executed word, the *fresh trace* of that age
(`freshChain`), and call a row *fresh* at a frame and an age when each slot of the frame holds
that word in the row and no other slot of the row holds a trace (`Fresh`). `fresh_laid`,
`fresh_after` and `fresh_total` below are stated for either criterion.

**Its total.** The trace total of a fresh row on any frame of at most 1999 slots reads the
ordered sum of as many copies of the fresh trace as the frame holds slots of the laid frame
(`fresh_total`): the frame's other slots hold positive zero in that row. The only fact of the
two frames the total reads is that count. The sum is the executed one, added copy by copy. It is
near the product of the count and the word (`repeatSum_near`); no theorem here says that it is
the rounded product.

**The fresh trace as a number.** Under the discounted criterion the trace decay is the word
`0x3f641893`, which reads `14948499 · 2^(-24)`, a little below `0.891` (`decay_word`,
`decay_value`; it is one executed product, which the kernel evaluates). A fresh trace of an age
of at most 80 is above the pruning threshold, and the executed product that makes the next one
differs from the exact product by at most `2^(-24)` of it and `2^(-150)`
(`AcornVerif.FloatLibBridge.binary32_mul_relative`), so the next fresh trace lies between
`0.89099` and `0.89101` of it (`fresh_step`). So a fresh trace lies between those two numbers,
each raised to a number of ages, times the fresh trace that many ages younger (`fresh_ratio`),
and the fresh trace of every age up to 81 lies between the step size times `0.89099` raised to
its age and the step size times `0.89101` raised to its age (`fresh_bounds`). These are bounds
and not values: only the ages zero and one have their exact word here (`stepWord`, `fresh_one`).

**The comparison.** Say that `copies` copies of a word `lead` *lead* `fewer` copies of a word
`trail` when the exact multiple `copies · lead` exceeds `fewer · trail` by more than the tie
window and `2^(-28)` for each copy of either sum and once more (`Leads`). The last terms bound
the rounding of the two ordered sums (`repeatSum_near`) and of the subtraction of the tie
window. For any two finite nonnegative words of at most `2^(-14)` and counts of at most 1999,
where `copies` of `lead` lead `fewer` of `trail`, the ordered sum of `copies` copies of `lead`,
less the tie window, is above the ordered sum of `fewer` copies of `trail` (`counted_lead`). Its
proof evaluates neither sum. So in a policy of finite values in which one action's value reads
such a sum of `lead`, while every other value is at most a counted sum of some such word that
the first leads, that action is the one near-maximum candidate (`margin_candidate`).

That margin is proved from the stored numbers in two cases. The step size reads
`13743900 · 2^(-38)` (`AcornVerif.CurrentCreditHorizon.step_value`) and a fresh trace of any age
of at least one reads at most `12245815 · 2^(-38)` (`fresh_one_value`): step sizes lead fresh
traces of such an age whenever their count is at least one and more than `0.892` of the other
count (`recent_leads`). `fresh_lead` and `counted_candidate` are the case of at most as many.
And fresh traces of an age of at most 14 lead those of another age under the conditions of the
paragraph on the action taken on a frame, below (`own_alone`, `earlier_leads`, `later_leads`).

**A kernel run.** For a profile with no hierarchy under per-step credit and the discounted
criterion, before a unit of the feature bank matures: take a kernel run, from an agent state
whose learners are at rest and whose primitive controller holds no trace, whose rewards are zero
words and whose frames hold at most 1999 slots. A row whose action the run took at one time, and
at no other from 119 steps before that time on, is fresh at the frame laid then, for eighty
steps (`loop_fresh`). Where the actions before a time are pairwise different, every row that was
taken is fresh and every other row holds no trace. So right before the step that learns a
reward, on any frame of at most 1999 slots, the trace total of each action taken reads the
ordered sum of as many copies of the fresh trace of the action's age as the frame holds slots of
the frame laid at the action's step, and the total of an action not taken is a zero word
(`loop_totals`). The comparison of two such actions is then a comparison of two counts and two
named words.

**The criterion.** Write `shared frame laid` for the number of slots of `frame` that the frame
`laid` holds. Under the hypotheses of `loop_totals`, at a frame of at most 1999 slots, take a
time up to `last`. Suppose the fresh traces of that time's age, counted once for each slot the
frame holds of the frame laid then, lead the counted fresh traces of every other time up to
`last`, each with its own count and its own age, and lead a count of zero. Then the action taken
at that time is the one candidate of the trace policy at that frame, at any rate, and the greedy
draw returns it whatever the generator (`leading_candidate`). The count of zero covers every
action not taken, whose total is a zero word. With
`AcornVerif.CurrentFirstChoice.first_choice`, under the declared rate at the default step order:
when a first reward of one comes after pairwise different actions, and that holds at the frame
the next decision reads, then outside a committed run, when the generator begins none, the
agent's first decision after the reward takes the action of that time (`first_choice_leading`).

**The most recent action.** At a frame that holds a slot of the last frame laid before the
reward, and more slots of it than `0.892` of what it holds of each earlier frame, the last action
taken is the one candidate (`recent_candidate`), and outside a run it is the agent's first action
after the reward (`first_choice_recent`). `last_candidate` and `first_choice_last` are the case
of at least as many slots. The share is `223/250`. The margin itself asks the last frame's count
to exceed about `0.8911` of the other count, the ratio of the two words with the rounding of
each copy, by about a fiftieth of a slot, for the tie window; whole counts in that share meet it
(`share_counts`).

**The action taken on a frame.** Take an action taken at most 14 steps before the last one, on a
frame that holds a slot. At that frame it is the one candidate whenever each frame laid a number
of steps later holds at most `0.89` raised to that number of the frame's slots but one
(`own_candidate`). Nothing is assumed of the frames laid earlier: such a frame holds at most
every slot of the frame, and its trace is at least one age older. The slot set aside pays for the
tie window: the share cannot be the decay itself, because the tie window is an absolute number
and the two totals can otherwise lie within it. The age of 14 is derived from the stored
numbers. It is the last at which the loss of one slot's trace over one step of decay exceeds the
tie window and the rounding of the two sums (`fresh_fourteen`, `earlier_leads`). One step past
it the statement is false without a condition on the earlier frames: in a policy whose values
are all at most one fresh trace of age 15, an action whose value reads one fresh trace of age 16
is a candidate as well (`stale_candidate`). Those are the totals at a frame of one slot, of the
action taken on it 15 steps before the last and of the action taken on the frame before it,
where that frame holds the same slot.

What this does not say.

- Anything of a row whose action was taken more than once before the reward. Its second laying
  can read a total that is not zero, its slots can then hold more than one word, and an ordered
  sum of different words depends on their order; this module says nothing of such a total.
- How many slots two frames share. That is a fact of the frames: of the words of their percepts,
  of the words the agent feeds back from its own predictions, of the units its percepts turn on,
  and of which of those hash to one slot. So no theorem here says that a frame of a run meets
  one of the conditions above on its counts; each is a hypothesis.
- Which action is the candidate where no action's counted traces lead every other's. The
  criterion names a candidate only under its margin, and where two totals lie within the tie
  window and the rounding of each other it names none.
- The exact word of a fresh trace of an age above one, or of an ordered sum.
- Anything of a later decision, of an exploratory run that begins after the reward, of a first
  reward after a unit of the feature bank matures, which under the declared tester is after the
  agent's first 1000 decisions, or of a kernel run or a comparison under the differential
  criterion.

Trust. The statements are about executed binary32 words. Lean's kernel, its model of binary32
arithmetic and the agreement of the native operations with that model on finite operands remain
trusted, as for every proof of executed words in this library. The bounds on the fresh traces
use FloatLib's theorem that the model's product is the exact product rounded once, through the
proof bridge; that theorem is checked and adds nothing to what is trusted.
-/

namespace AcornVerif.CurrentTraceCounts
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds
open AcornVerif.CurrentLearner AcornVerif.CurrentPreReward AcornVerif.CurrentFeatureConsumers
open AcornVerif.CurrentControl AcornVerif.CurrentCreditHorizon AcornVerif.CurrentFirstChoice
open SwiftTd (ActiveSet)

/-! ## The trace of a slot laid once -/

section Words

/-- The trace a row holds on a slot it laid once, from no trace, `age` steps before: the stored
step size, multiplied by the trace decay once for each later step. -/
def freshChain (criterion : Criterion) : Nat → Binary32
  | 0 => stepWord
  | age + 1 => (freshChain criterion age).mul (decayOf criterion)

/-- The fresh trace of every age is small, nonnegative and at most the step size. -/
theorem freshChain_facts (criterion : Criterion) (age : Nat) :
    Small (freshChain criterion age) ∧ 0 ≤ numerical32 (freshChain criterion age) ∧
      numerical32 (freshChain criterion age) ≤ numerical32 stepWord := by
  induction age with
  | zero => exact ⟨small_step, step_nonneg, le_rfl⟩
  | succ age ih =>
    have product := mul_small ih.1 (small_decay criterion)
    have lower := mul_nonneg' ih.1 (small_decay criterion) ih.2.1 (decay_nonneg criterion)
    have upper := mul_le_self ih.1 (small_decay criterion) ih.2.1 (decay_le_one criterion)
    exact ⟨small_between product.1 small_zero ih.1 (by rw [zero_value]; exact lower) upper,
      lower, le_trans upper ih.2.2⟩

/-- A fresh trace is at least the least laid trace of the same age. -/
theorem low_le_fresh (criterion : Criterion) (age : Nat) :
    numerical32 (lowChain criterion age) ≤ numerical32 (freshChain criterion age) := by
  induction age with
  | zero =>
    exact num_le (lowChain_facts criterion 0).1.1 small_step.1
      (by cases criterion <;> decide +kernel)
  | succ age ih =>
    exact mul_mono (lowChain_facts criterion age).1 (small_decay criterion)
      (freshChain_facts criterion age).1 (small_decay criterion)
      (lowChain_facts criterion age).2.1 (decay_nonneg criterion) ih le_rfl

/-- The fresh trace of an age of at most eighty is above the pruning threshold. -/
theorem freshChain_above (criterion : Criterion) (age : Nat) (near : age ≤ 80) :
    numerical32 pruneWord < numerical32 (freshChain criterion age) :=
  lt_of_lt_of_le (lowChain_above criterion age near) (low_le_fresh criterion age)

/-- A fresh trace does not grow with its age. -/
theorem freshChain_antitone (criterion : Criterion) (age more : Nat) :
    numerical32 (freshChain criterion (age + more)) ≤ numerical32 (freshChain criterion age) := by
  induction more with
  | zero => exact le_rfl
  | succ more ih =>
    have facts := freshChain_facts criterion (age + more)
    exact le_trans (mul_le_self facts.1 (small_decay criterion) facts.2.1 (decay_le_one criterion))
      ih

/-- A fresh trace of any age is a finite nonnegative word of at most `2^(-14)`: the form the
comparisons of counted sums take their words in. -/
theorem fresh_word (criterion : Criterion) (age : Nat) :
    (freshChain criterion age).Finite ∧ 0 ≤ numerical32 (freshChain criterion age) ∧
      numerical32 (freshChain criterion age) ≤ (2 : ℚ) ^ (-14 : Int) := by
  have facts := freshChain_facts criterion age
  refine ⟨facts.1.1, facts.2.1, facts.2.2.trans ?_⟩
  rw [step_value]
  norm_num

end Words

/-! ## The fresh trace as a number -/

section Numbers

open AcornVerif.FloatLibBridge

/-- Under the discounted criterion the trace decay is the word `0x3f641893`: one executed
product of the control configuration's discount and trace parameter, which the kernel
evaluates. -/
theorem decay_word : decayOf .discounted = ⟨0x3f641893⟩ := by
  decide +kernel

/-- Under the discounted criterion the trace decay reads `14948499 · 2^(-24)`, a little below
`0.891`. -/
theorem decay_value :
    numerical32 (decayOf .discounted) = 14948499 * (2 : ℚ) ^ (-24 : Int) := by
  rw [decay_word]
  change (1 : ℚ) * 14948499 * (2 : ℚ) ^ (-24 : Int) = _
  ring

/-- The pruning threshold of a slot laid at the stored step size reads `9007202 · 2^(-54)`, a
little above `5 · 10^(-10)`. -/
theorem prune_value : numerical32 pruneWord = 9007202 * (2 : ℚ) ^ (-54 : Int) := by
  change (1 : ℚ) * 9007202 * (2 : ℚ) ^ (-54 : Int) = _
  ring

/-- **One step of decay, as numbers.** Under the discounted criterion, the fresh trace of an age
of at most 80 is multiplied by between `0.89099` and `0.89101` to give the next one. The
executed product differs from the exact one by at most `2^(-24)` of it and `2^(-150)`
(`AcornVerif.FloatLibBridge.binary32_mul_relative`), the decay reads `14948499 · 2^(-24)`
(`decay_value`), and the trace is above the pruning threshold (`freshChain_above`), which is far
above `2^(-150)`. The statement bounds the next trace and does not give its word. -/
theorem fresh_step (age : Nat) (near : age ≤ 80) :
    (89099 / 100000 : ℚ) * numerical32 (freshChain .discounted age) ≤
        numerical32 (freshChain .discounted (age + 1)) ∧
      numerical32 (freshChain .discounted (age + 1)) ≤
        (89101 / 100000 : ℚ) * numerical32 (freshChain .discounted age) := by
  have facts := freshChain_facts .discounted age
  have next := freshChain_facts .discounted (age + 1)
  have above := freshChain_above .discounted age near
  have same : freshChain .discounted (age + 1) =
      (freshChain .discounted age).mul (decayOf .discounted) := rfl
  rw [same] at next ⊢
  have error := binary32_mul_relative (freshChain .discounted age) (decayOf .discounted)
    facts.1.1 (small_decay .discounted).1 next.1.1
  have e24 : (2 : ℚ) ^ (-24 : Int) = 1 / 16777216 := by norm_num
  have e54 : (2 : ℚ) ^ (-54 : Int) = 1 / 18014398509481984 := by norm_num
  rw [decay_value, e24] at error
  rw [prune_value, e54] at above
  have product : 0 ≤ numerical32 (freshChain .discounted age) * (14948499 * (1 / 16777216)) :=
    mul_nonneg facts.2.1 (by norm_num)
  rw [abs_of_nonneg product] at error
  have bounds := abs_le.mp error
  have tiny : (1 : ℚ) / 2 ^ 150 ≤ 1 / 2 ^ 100 := by norm_num
  constructor <;> linarith [bounds.1, bounds.2]

/-- **A fresh trace against a younger one.** Under the discounted criterion, the fresh trace
`more` ages older than that of an age lies between `0.89099` and `0.89101`, each raised to
`more`, times that trace, up to an age of 81 (`fresh_step`, once for each age). -/
theorem fresh_ratio (age more : Nat) (near : age + more ≤ 81) :
    (89099 / 100000 : ℚ) ^ more * numerical32 (freshChain .discounted age) ≤
        numerical32 (freshChain .discounted (age + more)) ∧
      numerical32 (freshChain .discounted (age + more)) ≤
        (89101 / 100000 : ℚ) ^ more * numerical32 (freshChain .discounted age) := by
  induction more with
  | zero => simp
  | succ more ih =>
    obtain ⟨low, high⟩ := ih (by omega)
    obtain ⟨stepLow, stepHigh⟩ := fresh_step (age + more) (by omega)
    change _ ≤ numerical32 (freshChain .discounted (age + more + 1)) ∧
      numerical32 (freshChain .discounted (age + more + 1)) ≤ _
    constructor
    · calc (89099 / 100000 : ℚ) ^ (more + 1) * numerical32 (freshChain .discounted age)
          = 89099 / 100000 *
            ((89099 / 100000 : ℚ) ^ more * numerical32 (freshChain .discounted age)) := by ring
        _ ≤ 89099 / 100000 * numerical32 (freshChain .discounted (age + more)) :=
          mul_le_mul_of_nonneg_left low (by norm_num)
        _ ≤ _ := stepLow
    · calc numerical32 (freshChain .discounted (age + more + 1))
          ≤ 89101 / 100000 * numerical32 (freshChain .discounted (age + more)) := stepHigh
        _ ≤ 89101 / 100000 *
            ((89101 / 100000 : ℚ) ^ more * numerical32 (freshChain .discounted age)) :=
          mul_le_mul_of_nonneg_left high (by norm_num)
        _ = _ := by ring

/-- **The fresh trace of every age, between two numbers.** Under the discounted criterion, the
fresh trace of an age of at most 81 lies between the stored step size, `13743900 · 2^(-38)`,
times `0.89099` raised to the age and the step size times `0.89101` raised to the age
(`fresh_ratio` from age zero, `AcornVerif.CurrentCreditHorizon.step_value`). -/
theorem fresh_bounds (age : Nat) (near : age ≤ 81) :
    (89099 / 100000 : ℚ) ^ age * (13743900 * (2 : ℚ) ^ (-38 : Int)) ≤
        numerical32 (freshChain .discounted age) ∧
      numerical32 (freshChain .discounted age) ≤
        (89101 / 100000 : ℚ) ^ age * (13743900 * (2 : ℚ) ^ (-38 : Int)) := by
  have ratio := fresh_ratio 0 age (by omega)
  rw [Nat.zero_add] at ratio
  have start : numerical32 (freshChain .discounted 0) = 13743900 * (2 : ℚ) ^ (-38 : Int) :=
    step_value
  rw [start] at ratio
  exact ratio

end Numbers

/-! ## Ordered sums of one small word -/

section Sums

/-- **An ordered sum of a small word is near the exact multiple.** For a finite nonnegative word
of at most `2^(-14)`, the ordered sum of at most 1999 copies is finite and within `2^(-28)` of
the exact multiple for each copy: half a unit in the last place of a sum below an eighth. -/
theorem repeatSum_near (word : Binary32) (finite : word.Finite)
    (nonneg : 0 ≤ numerical32 word) (small : numerical32 word ≤ (2 : ℚ) ^ (-14 : Int)) :
    ∀ count ≤ 1999, (repeatSum word count).Finite ∧
      |numerical32 (repeatSum word count) - count * numerical32 word| ≤
        count * (2 : ℚ) ^ (-28 : Int) := by
  intro count
  induction count with
  | zero =>
    intro _
    rw [repeatSum_zero]
    refine ⟨by decide, ?_⟩
    rw [zero_value]
    norm_num
  | succ count ih =>
    intro fits
    obtain ⟨sumFinite, near⟩ := ih (by omega)
    have counted : (count : ℚ) ≤ 1998 := by exact_mod_cast (by omega : count ≤ 1998)
    have product : (count : ℚ) * numerical32 word ≤ 1998 * (2 : ℚ) ^ (-14 : Int) :=
      mul_le_mul counted small nonneg (by norm_num)
    have productNonneg : 0 ≤ (count : ℚ) * numerical32 word :=
      mul_nonneg (Nat.cast_nonneg count) nonneg
    have bounds := abs_le.mp near
    have e14 : (2 : ℚ) ^ (-14 : Int) = 1 / 16384 := by norm_num
    have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
    have e3 : (2 : ℚ) ^ (-3 : Int) = 1 / 8 := by norm_num
    rw [e14] at small product
    rw [e28] at bounds near ⊢
    have step := AcornVerif.CurrentPrediction.binary32_add_finite_strict_error
      (repeatSum word count) word sumFinite finite (-3) (by norm_num) (by
        rw [e3, abs_lt]
        constructor <;> nlinarith [bounds.1, bounds.2])
    have radius : (2 : ℚ) ^ (max ((-3 : Int) - 24) (-149)) / 2 = 1 / 268435456 := by norm_num
    rw [radius] at step
    rw [repeatSum_succ]
    refine ⟨step.1, ?_⟩
    have stepBounds := abs_le.mp step.2
    rw [abs_le]
    push_cast
    constructor <;> nlinarith [bounds.1, bounds.2, stepBounds.1, stepBounds.2]

/-- Every ordered sum of at most 1999 copies of a finite nonnegative word of at most `2^(-14)`
is small. -/
theorem repeatSum_small (word : Binary32) (finite : word.Finite)
    (nonneg : 0 ≤ numerical32 word) (small : numerical32 word ≤ (2 : ℚ) ^ (-14 : Int))
    (count : Nat) (fits : count ≤ 1999) : Small (repeatSum word count) := by
  obtain ⟨sumFinite, near⟩ := repeatSum_near word finite nonneg small count fits
  have counted : (count : ℚ) ≤ 1999 := by exact_mod_cast fits
  have product : (count : ℚ) * numerical32 word ≤ 1999 * (2 : ℚ) ^ (-14 : Int) :=
    mul_le_mul counted small nonneg (by norm_num)
  have productNonneg : 0 ≤ (count : ℚ) * numerical32 word :=
    mul_nonneg (Nat.cast_nonneg count) nonneg
  have bounds := abs_le.mp near
  have e14 : (2 : ℚ) ^ (-14 : Int) = 1 / 16384 := by norm_num
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  rw [e14] at product
  rw [e28] at bounds
  refine ⟨sumFinite, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith [bounds.1, bounds.2]

/-- The stored step size is at most `2^(-14)`. -/
theorem step_bound : numerical32 stepWord ≤ (2 : ℚ) ^ (-14 : Int) := by
  rw [step_value]
  norm_num

/-- Every ordered sum of at most 1999 fresh traces of one age is small, nonnegative and at most
the sum of as many stored step sizes. -/
theorem freshSum_small (criterion : Criterion) (age count : Nat) (fits : count ≤ 1999) :
    Small (repeatSum (freshChain criterion age) count) ∧
      0 ≤ numerical32 (repeatSum (freshChain criterion age) count) ∧
      numerical32 (repeatSum (freshChain criterion age) count) ≤
        numerical32 (repeatSum stepWord count) := by
  have facts := freshChain_facts criterion age
  have total := sumFrom_le_repeat stepWord small_step
    (List.replicate count (freshChain criterion age)) .zero 0
    (fun k bound => repeatSum_small stepWord small_step.1 step_nonneg step_bound k
      (by simp only [List.length_replicate] at bound; omega))
    small_zero (le_of_eq zero_value.symm) (le_of_eq (by rw [repeatSum_zero]))
    (fun term member => by
      rw [List.eq_of_mem_replicate member]
      exact facts)
  simp only [List.length_replicate, Nat.zero_add] at total
  exact total

/-- An ordered sum of at most 1999 fresh traces of an age of at least one is at most the sum of
as many fresh traces of age one. -/
theorem freshSum_older (criterion : Criterion) (age count : Nat) (old : 1 ≤ age)
    (fits : count ≤ 1999) :
    numerical32 (repeatSum (freshChain criterion age) count) ≤
      numerical32 (repeatSum (freshChain criterion 1) count) := by
  have onceSmall : ∀ k ≤ 1999, Small (repeatSum (freshChain criterion 1) k) :=
    fun k bound => (freshSum_small criterion 1 k bound).1
  have facts := freshChain_facts criterion age
  have below : numerical32 (freshChain criterion age) ≤ numerical32 (freshChain criterion 1) := by
    have far := freshChain_antitone criterion 1 (age - 1)
    rwa [show 1 + (age - 1) = age by omega] at far
  have total := sumFrom_le_repeat (freshChain criterion 1) (freshChain_facts criterion 1).1
    (List.replicate count (freshChain criterion age)) .zero 0
    (fun k bound => onceSmall k (by simp only [List.length_replicate] at bound; omega))
    small_zero (le_of_eq zero_value.symm) (le_of_eq (by rw [repeatSum_zero]))
    (fun term member => by
      rw [List.eq_of_mem_replicate member]
      exact ⟨facts.1, facts.2.1, below⟩)
  simp only [List.length_replicate, Nat.zero_add] at total
  exact total.2.2

/-- The ordered sum of one copy of a finite word reads the word. -/
theorem repeatSum_one (word : Binary32) (finite : word.Finite) :
    numerical32 (repeatSum word 1) = numerical32 word := by
  rw [repeatSum_succ, repeatSum_zero]
  exact zero_add_same .zero word (by decide) finite

/-- `copies` copies of the word `lead` *lead* `fewer` copies of the word `trail`: the exact
multiple `copies · lead` exceeds the exact multiple `fewer · trail` by more than the tie window
and `2^(-28)` for each copy of either and once more. Those last terms bound the rounding of the
two ordered sums and of the subtraction of the tie window (`counted_lead`). It is a statement of
two counts and two exact readings. For a nonnegative `trail` it holds of no pair of counts whose
first is zero. -/
def Leads (lead : Binary32) (copies : Nat) (trail : Binary32) (fewer : Nat) : Prop :=
  (fewer : ℚ) * numerical32 trail + numerical32 tieWindow +
    ((copies : ℚ) + fewer + 1) * (2 : ℚ) ^ (-28 : Int) < (copies : ℚ) * numerical32 lead

/-- **A counted sum that leads is above the other, by more than the tie window.** For two finite
nonnegative words of at most `2^(-14)` and two counts of at most 1999, where `copies` of `lead`
lead `fewer` of `trail` (`Leads`), the ordered sum of `copies` copies of `lead`, less the tie
window, is above the ordered sum of `fewer` copies of `trail`. Each sum is within `2^(-28)` for
each copy of its exact multiple (`repeatSum_near`), and the subtraction of the tie window from a
sum below an eighth is rounded by at most `2^(-28)`. Neither sum is evaluated. The converse is
not claimed: two sums can be so ordered without the margin. -/
theorem counted_lead (lead trail : Binary32) (leadFinite : lead.Finite)
    (trailFinite : trail.Finite) (leadNonneg : 0 ≤ numerical32 lead)
    (trailNonneg : 0 ≤ numerical32 trail) (leadSmall : numerical32 lead ≤ (2 : ℚ) ^ (-14 : Int))
    (trailSmall : numerical32 trail ≤ (2 : ℚ) ^ (-14 : Int)) (copies fewer : Nat)
    (fitsCopies : copies ≤ 1999) (fitsFewer : fewer ≤ 1999)
    (margin : Leads lead copies trail fewer) :
    (repeatSum trail fewer).key < ((repeatSum lead copies).sub tieWindow).key := by
  have e14 : (2 : ℚ) ^ (-14 : Int) = 1 / 16384 := by norm_num
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  have e3 : (2 : ℚ) ^ (-3 : Int) = 1 / 8 := by norm_num
  have tieRead := tie_value
  rw [e43] at tieRead
  unfold Leads at margin
  obtain ⟨sumFinite, leadNear⟩ := repeatSum_near lead leadFinite leadNonneg leadSmall copies
    fitsCopies
  obtain ⟨lessFinite, trailNear⟩ := repeatSum_near trail trailFinite trailNonneg trailSmall
    fewer fitsFewer
  rw [e28] at leadNear trailNear margin
  rw [e14] at leadSmall
  rw [tieRead] at margin
  have leadBounds := abs_le.mp leadNear
  have trailBounds := abs_le.mp trailNear
  have counted : (copies : ℚ) ≤ 1999 := by exact_mod_cast fitsCopies
  have product : (copies : ℚ) * numerical32 lead ≤ 1999 * (1 / 16384) :=
    mul_le_mul counted leadSmall leadNonneg (by norm_num)
  have productNonneg : 0 ≤ (copies : ℚ) * numerical32 lead :=
    mul_nonneg (Nat.cast_nonneg copies) leadNonneg
  have copiesNonneg : (0 : ℚ) ≤ copies := Nat.cast_nonneg copies
  obtain ⟨gapFinite, gapNear⟩ := binary32_sub_finite_strict_error (repeatSum lead copies)
    tieWindow sumFinite (by decide) (-3) (by norm_num) (by
      rw [tieRead, e3, abs_lt]
      constructor <;> linarith [leadBounds.1, leadBounds.2])
  have radius : (2 : ℚ) ^ (max ((-3 : Int) - 24) (-149)) / 2 = 1 / 268435456 := by norm_num
  rw [radius, tieRead] at gapNear
  have gapBounds := abs_le.mp gapNear
  apply (numerical32_strict_order _ _ lessFinite gapFinite).mp
  linarith [trailBounds.2, leadBounds.1, gapBounds.1]

end Sums

/-! ## A row taken once -/

section Rows

variable {criterion : Criterion} {dimension : Dimension} {actions : Nat}

/-- A row whose one laid frame, `age` steps before, is `frame`: every slot of the frame is
eligible in the row with the fresh trace of that age, and no other slot is eligible. -/
def Fresh (criterion : Criterion)
    (controller : Controller (criterion.config .control) dimension actions) (row : Fin actions)
    (frame : ActiveSet dimension) (age : Nat) : Prop :=
  (∀ slot ∈ frame.indices,
      slot ∈ (controller.learners.get row).state.transient.eligible ∧
        (slotOf (controller.learners.get row).state slot).z = freshChain criterion age) ∧
    ∀ slot, slot ∉ frame.indices →
      slot ∉ (controller.learners.get row).state.transient.eligible

/-- **A row that holds no trace lays the stored step size.** From a quiet controller, a
reward-free step at a row with no eligible slot, on a frame of at most 1999 slots, leaves each
slot of the frame eligible in that row with the stored step size for its trace, and no other
slot eligible: the trace total it reads is a zero word, so the laid increment is the whole step
size. -/
theorem fresh_laid {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (row : Action actions) (fits : features.indices.length ≤ 1999)
    (empty : ∀ slot, slot ∉ (controller.learners.get row).state.transient.eligible) :
    Fresh criterion (controller.step features row .zero).1 row features 0 := by
  unfold Fresh
  obtain ⟨δ, delta, stepped⟩ := quiet_step_row quiet features row
  rw [stepped row]
  simp only [↓reduceIte]
  have first := quiet_first_loop (controller.learners.get row).state history row (quiet.rows row)
    (row_unique controller row) (row_supported controller row) delta quiet.vDelta
  have entry := quiet_first_entry (controller.learners.get row).state history row
    (quiet.rows row) (row_unique controller row) (row_supported controller row) delta
    quiet.vDelta
  have out : ∀ slot, slot ∉ ((controller.learners.get row).state.learnFirstLoop
      (criterion.config .control) δ controller.vDelta (decayOf criterion)).transient.eligible :=
    fun slot => (first_loop_dormant _ δ controller.vDelta (decayOf criterion) slot
      (row_unique controller row) (empty slot) ((quiet.rows row).slots slot).weight).1
  have cleared := fun slot => first.2.2 slot (out slot)
  obtain ⟨noOvershoot, -⟩ := quiet_entry _ features fits entry
  have total : (Binary32.sumFrom .zero (features.indices.map fun idx =>
      (((controller.learners.get row).state.learnFirstLoop (criterion.config .control) δ
        controller.vDelta (decayOf criterion)).transient.z.get idx).value)).isZero = true := by
    rw [Binary32.sumFrom_def]
    apply zeroWord_foldlAdd _ _ (by decide)
    intro value member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    have zero := (cleared slot).zero
    rw [slotOf_z] at zero
    rw [zero]
    decide
  have result := second_loop_slots (fun _ words => Cleared criterion words)
    (fun _ words => words.z = stepWord) (fun _ => True)
    (StepSizeRails.ofConfig (criterion.config .control)) _ features .zero ?_ first.1 trivial
    (fun idx _ => cleared idx)
  · refine ⟨fun slot held => ⟨?_, result.2.2.1 slot held⟩, fun slot absent => ?_⟩
    · rw [← Array.mem_toList_iff, second_loop_eligible]
      refine List.mem_append_right _ (List.mem_filter.mpr ⟨held, ?_⟩)
      have zero := (cleared slot).zero
      rw [slotOf_z] at zero
      rw [zero]
      decide
    · rw [← Array.mem_toList_iff, second_loop_eligible]
      intro member
      rcases List.mem_append.mp member with old | fresh
      · exact out slot (Array.mem_toList_iff.mp old)
      · exact absent (List.mem_filter.mp fresh).1
  · intro current vd idx _ _ pre
    simp only [noOvershoot, Bool.false_eq_true, ite_false]
    obtain ⟨words, _⟩ := quiet_second current idx _ vd pre.quiet.beta
    rw [words]
    refine ⟨?_, trivial⟩
    change (slotOf current idx).z.add (stepWord.mul (Binary32.one.sub _)) = stepWord
    rw [pre.zero, one_sub_zero total]
    decide +kernel

/-- **A reward-free step at another row decays a fresh trace once.** From a quiet controller, a
reward-free step that does not take a row whose one laid frame is fresh leaves that frame fresh
one step older, while the decayed trace stays above the pruning threshold: the first loop
multiplies each of the frame's traces by the trace decay and prunes none, and the row's second
loop does not run. -/
theorem fresh_after {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (action row : Action actions) (frame : ActiveSet dimension) (age : Nat)
    (fresh : Fresh criterion controller row frame age) (other : action ≠ row)
    (above : numerical32 pruneWord < numerical32 (freshChain criterion (age + 1))) :
    Fresh criterion (controller.step features action .zero).1 row frame (age + 1) := by
  unfold Fresh
  obtain ⟨δ, delta, stepped⟩ := quiet_step_row quiet features action
  rw [stepped row]
  simp only [other, ↓reduceIte]
  have facts := freshChain_facts criterion age
  have result := first_loop_slots
    (fun _ words => SlotQuiet criterion words ∧ words.z = freshChain criterion age)
    (fun _ words => words.z = freshChain criterion (age + 1))
    (fun idx _ => idx ∉ frame.indices) δ controller.vDelta (decayOf criterion)
    (StepSizeRails.ofConfig (criterion.config .control)) ?_
    (controller.learners.get row).state (quiet.rows row).rails (row_unique controller row)
    (fun idx member => ⟨(quiet.rows row).slots idx,
      (fresh.1 idx (by_contra fun absent => fresh.2 idx absent member)).2⟩)
    (fun idx absent inside => absent (fresh.1 idx inside).1)
  · refine ⟨fun slot held => ?_, fun slot absent => ?_⟩
    · have member : slot ∈ ((controller.learners.get row).state.learnFirstLoop
          (criterion.config .control) δ controller.vDelta (decayOf criterion)).transient.eligible :=
        by_contra fun gone => result.2.2.2 slot gone held
      exact ⟨member, result.2.2.1 slot member⟩
    · exact (first_loop_dormant _ δ controller.vDelta (decayOf criterion) slot
        (row_unique controller row) (fresh.2 slot absent) ((quiet.rows row).slots slot).weight).1
  · intro current idx sameRails pre
    obtain ⟨words, same⟩ := pre
    obtain ⟨_, _, z, _, _, lastAlpha, _, _, _, _, _, prune⟩ :=
      quiet_first current idx sameRails delta quiet.vDelta words
    have lowered := mul_le_self facts.1 (small_decay criterion) facts.2.1 (decay_le_one criterion)
    have nonzero : (slotOf current idx).z.isZero = false := by
      apply Bool.eq_false_iff.mpr
      intro zero
      have zeroRead := zero_reads zero
      rw [same] at zeroRead
      have prunePositive : 0 ≤ numerical32 pruneWord := prune_nonneg
      change numerical32 pruneWord <
        numerical32 ((freshChain criterion age).mul (decayOf criterion)) at above
      linarith
    have threshold := words.reference nonzero
    have keep : (current.firstLoopElement idx δ controller.vDelta (decayOf criterion)).2 =
        false := by
      rw [prune, threshold, prune_eq, same, finite_lessOrEqual _ _
        (mul_small facts.1 (small_decay criterion)).1 (by decide)]
      simp only [decide_eq_false_iff_not, not_le]
      exact above
    refine ⟨fun pruned => absurd (keep ▸ pruned) (by decide), fun _ => ?_⟩
    rw [z, same]
    rfl

/-- **The trace total of a fresh row sums the fresh trace over the shared slots.** On a quiet
controller, a row whose one laid frame is fresh at some age has, on every frame of at most 1999
slots, a trace total that reads the ordered sum of as many copies of the fresh trace of that age
as the frame holds slots of the laid frame: each such slot holds that word, and every other slot
holds positive zero. -/
theorem fresh_total {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (row : Fin actions)
    (frame : ActiveSet dimension) (age : Nat) (fresh : Fresh criterion controller row frame age)
    (features : ActiveSet dimension) (fits : features.indices.length ≤ 1999) :
    numerical32 (traceTotal controller features row) =
      numerical32 (repeatSum (freshChain criterion age)
        (features.indices.countP fun slot => decide (slot ∈ frame.indices))) := by
  unfold traceTotal
  have bounded : ∀ slots : List (FeatIdx dimension), slots.length ≤ features.indices.length →
      numerical32 (Binary32.sumFrom .zero (slots.map fun slot =>
        ((controller.learners.get row).state.transient.z.get slot).value)) =
      numerical32 (repeatSum (freshChain criterion age)
        (slots.countP fun slot => decide (slot ∈ frame.indices))) := by
    intro slots
    induction slots using List.reverseRecOn with
    | nil => intro _; rfl
    | append_singleton slots last ih =>
      intro short
      rw [List.length_append, List.length_singleton] at short
      have previous := ih (by omega)
      have leftFinite := (traces_sum_small quiet row slots (by omega)).1.1
      have counted : slots.countP (fun slot => decide (slot ∈ frame.indices)) ≤ 1999 :=
        Nat.le_trans (List.countP_le_length) (by omega)
      have rightFinite := (freshSum_small criterion age _ counted).1.1
      simp only [List.map_append, List.map_cons, List.map_nil, Binary32.sumFrom_append,
        List.countP_append, List.countP_cons, List.countP_nil]
      change numerical32 ((Binary32.sumFrom .zero (slots.map fun slot =>
        ((controller.learners.get row).state.transient.z.get slot).value)).add
          (slotOf (controller.learners.get row).state last).z) = _
      by_cases inside : last ∈ frame.indices
      · simp only [inside, decide_true, ite_true, Nat.zero_add]
        rw [repeatSum_succ, (fresh.1 last inside).2]
        exact add_same_value _ _ _ leftFinite rightFinite (freshChain_facts criterion age).1.1
          previous
      · simp only [inside, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
        rw [slotOf_z, registers_zero_trace _ last
          (row_supported controller row last (fresh.2 last inside))]
        exact (add_zero_same _ _ leftFinite (by decide)).trans previous
  exact bounded features.indices le_rfl

end Rows

/-! ## The freshest trace leads -/

section Lead

/-- Under the discounted criterion the fresh trace of age one is the word `0x383adb37`. -/
theorem fresh_one : freshChain .discounted 1 = ⟨0x383adb37⟩ := by
  decide +kernel

/-- Under the discounted criterion the fresh trace of age one reads `12245815 · 2^(-38)`. -/
theorem fresh_one_value :
    numerical32 (freshChain .discounted 1) = 12245815 * (2 : ℚ) ^ (-38 : Int) := by
  rw [fresh_one]
  change (1 : ℚ) * 12245815 * (2 : ℚ) ^ (-38 : Int) = _
  ring

/-- The arithmetic of the share `223/250` in whole counts: a count of at least one that is more
than `0.892` of another exceeds it by enough to pay for the tie window and the rounding of both
sums, in units of `2^(-43)` (`recent_leads`). The counts below 24 are checked one by one, because
there the margin rests on the counts being whole. -/
theorem share_counts (fewer copies : Nat) (share : 223 * fewer < 250 * copies)
    (positive : 1 ≤ copies) : fewer * 391898848 + 8828861 < copies * 439772032 := by
  rcases Nat.lt_or_ge fewer 24 with small | large
  · interval_cases fewer <;> omega
  · omega

/-- **Step sizes lead older traces at a share of `0.892`.** Under the discounted criterion,
`copies` stored step sizes lead `fewer` fresh traces of any age of at least one whenever `copies`
is at least one and more than `223/250` of `fewer`. The step size reads `13743900 · 2^(-38)` and
such a trace at most `12245815 · 2^(-38)` (`fresh_one_value`, `freshChain_antitone`). No bound
on the counts is needed. A frame's counts meet it without the first being the larger: nine
against ten do. -/
theorem recent_leads (copies fewer age : Nat) (old : 1 ≤ age) (positive : 1 ≤ copies)
    (share : 223 * fewer < 250 * copies) :
    Leads stepWord copies (freshChain .discounted age) fewer := by
  have counts : (fewer : ℚ) * 391898848 + 8828861 < (copies : ℚ) * 439772032 := by
    exact_mod_cast share_counts fewer copies share positive
  have below : numerical32 (freshChain .discounted age) ≤
      numerical32 (freshChain .discounted 1) := by
    have far := freshChain_antitone .discounted 1 (age - 1)
    rwa [show 1 + (age - 1) = age by omega] at far
  have scaled := mul_le_mul_of_nonneg_left below (Nat.cast_nonneg (α := ℚ) fewer)
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e38 : (2 : ℚ) ^ (-38 : Int) = 1 / 274877906944 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  rw [fresh_one_value, e38] at scaled
  unfold Leads
  rw [step_value, tie_value, e28, e38, e43]
  linarith

/-- **The freshest trace leads by more than the tie window.** Under the discounted criterion, the
ordered sum of `copies` stored step sizes, for at least one and at most 1999 copies, less the tie
window, is above the ordered sum of at most as many fresh traces of age one. It is the case of
`counted_lead` in which the counts are in that order (`recent_leads`). -/
theorem fresh_lead (fewer copies : Nat) (order : fewer ≤ copies) (positive : 1 ≤ copies)
    (fits : copies ≤ 1999) :
    (repeatSum (freshChain .discounted 1) fewer).key <
      ((repeatSum stepWord copies).sub tieWindow).key :=
  counted_lead stepWord (freshChain .discounted 1) small_step.1 (fresh_word .discounted 1).1
    step_nonneg (fresh_word .discounted 1).2.1 step_bound (fresh_word .discounted 1).2.2 copies
    fewer fits (by omega) (recent_leads copies fewer 1 le_rfl positive (by omega))

/-- Under the discounted criterion the fresh trace of an age of at most 14 reads at least
`9.9 · 10^(-6)`, from the lower bound of `fresh_bounds` at age 14 and `freshChain_antitone`. -/
theorem fresh_fourteen (age : Nat) (recent : age ≤ 14) :
    (99 : ℚ) / 10000000 ≤ numerical32 (freshChain .discounted age) := by
  have low := (fresh_bounds 14 (by omega)).1
  have far := freshChain_antitone .discounted age (14 - age)
  rw [show age + (14 - age) = 14 by omega] at far
  have number : (99 : ℚ) / 10000000 ≤
      (89099 / 100000 : ℚ) ^ 14 * (13743900 * (2 : ℚ) ^ (-38 : Int)) := by norm_num
  linarith

/-- Under the discounted criterion, at least one fresh trace of an age of at most 14 leads a
count of zero: such a trace is more than nine tie windows (`fresh_fourteen`). This is the margin
over an action that was not taken. -/
theorem own_alone (age copies : Nat) (recent : age ≤ 14) (positive : 1 ≤ copies) :
    Leads (freshChain .discounted age) copies .zero 0 := by
  have word := fresh_fourteen age recent
  have atLeast : (1 : ℚ) ≤ copies := by exact_mod_cast positive
  have big := mul_le_mul_of_nonneg_left word (by linarith : (0 : ℚ) ≤ copies)
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  unfold Leads
  rw [tie_value, e28, e43]
  simp only [Nat.cast_zero, zero_mul, zero_add, add_zero]
  linarith

/-- **Up to age 14, a trace leads as many older ones.** Under the discounted criterion, at least
one fresh trace of an age of at most 14 leads at most as many fresh traces of any greater age.
An older trace is at most `0.89101` of it (`fresh_ratio`, `freshChain_antitone`), and at such an
age that loss on one slot, at least `0.10899 · 9.9 · 10^(-6)`, exceeds the tie window and the
rounding of both sums (`fresh_fourteen`). The bound on the age is needed: `stale_candidate`
gives the failure at age 15. -/
theorem earlier_leads (age more copies fewer : Nat) (recent : age ≤ 14) (older : 1 ≤ more)
    (positive : 1 ≤ copies) (order : fewer ≤ copies) :
    Leads (freshChain .discounted age) copies (freshChain .discounted (age + more)) fewer := by
  have word := fresh_fourteen age recent
  have step := (fresh_ratio age 1 (by omega)).2
  rw [pow_one] at step
  have far := freshChain_antitone .discounted (age + 1) (more - 1)
  rw [show age + 1 + (more - 1) = age + more by omega] at far
  have trailNonneg := (fresh_word .discounted (age + more)).2.1
  have atLeast : (1 : ℚ) ≤ copies := by exact_mod_cast positive
  have ordered : (fewer : ℚ) ≤ copies := by exact_mod_cast order
  have copiesNonneg : (0 : ℚ) ≤ copies := by linarith
  have first := mul_le_mul_of_nonneg_right ordered trailNonneg
  have second := mul_le_mul_of_nonneg_left (far.trans step) copiesNonneg
  have big := mul_le_mul_of_nonneg_left word copiesNonneg
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  unfold Leads
  rw [tie_value, e28, e43]
  linarith

/-- **Up to age 14, a trace leads younger ones at a share of `0.89` for each age, of all its
copies but one.** Under the discounted criterion, take `copies` fresh traces of an age of at
most 14, at least one, and `fewer` fresh traces `more` ages younger, for `more` of at least one,
with `fewer` at most `0.89^more` of `copies - 1`. The first lead the second. A trace is at least
`0.89099^more` of one `more` ages younger (`fresh_ratio`), so the `fewer` younger traces are
together below `copies - 1` of the older ones, and the one copy set aside, at least
`9.9 · 10^(-6)` (`fresh_fourteen`), exceeds the tie window and the rounding of both sums.
Without that copy the margin can fail (`slack_needed`). -/
theorem later_leads (age more copies fewer : Nat) (recent : age ≤ 14) (newer : 1 ≤ more)
    (within : more ≤ age) (positive : 1 ≤ copies)
    (share : fewer * 100 ^ more ≤ 89 ^ more * (copies - 1)) :
    Leads (freshChain .discounted age) copies (freshChain .discounted (age - more)) fewer := by
  have word := fresh_fourteen age recent
  have ratio := (fresh_ratio (age - more) more (by omega)).1
  rw [show age - more + more = age by omega] at ratio
  have trailNonneg := (fresh_word .discounted (age - more)).2.1
  have atLeast : (1 : ℚ) ≤ copies := by exact_mod_cast positive
  have restNonneg : (0 : ℚ) ≤ (copies : ℚ) - 1 := by linarith
  have cast : ((fewer * 100 ^ more : ℕ) : ℚ) ≤ ((89 ^ more * (copies - 1) : ℕ) : ℚ) :=
    Nat.cast_le.mpr share
  push_cast [Nat.cast_sub positive] at cast
  have shareLe : (fewer : ℚ) ≤ (89 / 100 : ℚ) ^ more * ((copies : ℚ) - 1) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact cast
  have powLe : (89 / 100 : ℚ) ^ more ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have fewerLe : (fewer : ℚ) ≤ (copies : ℚ) - 1 :=
    shareLe.trans (mul_le_of_le_one_left restNonneg powLe)
  have split : (89 / 100 : ℚ) ^ more = (89000 / 89099 : ℚ) ^ more * (89099 / 100000) ^ more := by
    rw [← mul_pow]
    norm_num
  have shrink : (89000 / 89099 : ℚ) ^ more ≤ 89000 / 89099 :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have key : (89 / 100 : ℚ) ^ more * numerical32 (freshChain .discounted (age - more)) ≤
      89000 / 89099 * numerical32 (freshChain .discounted age) := by
    rw [split, mul_assoc]
    exact mul_le_mul shrink ratio (mul_nonneg (by positivity) trailNonneg) (by norm_num)
  have first := mul_le_mul_of_nonneg_right shareLe trailNonneg
  have second := mul_le_mul_of_nonneg_left key restNonneg
  have big := mul_le_mul_of_nonneg_left word restNonneg
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  unfold Leads
  rw [tie_value, e28, e43]
  nlinarith [first, second, big, word, fewerLe]

/-- **The share cannot be the decay with no copy set aside.** Under the discounted criterion,
nine fresh traces of age one exceed eight stored step sizes by less than the tie window, though
eight is less than `0.89` of nine. So a frame of nine slots whose next frame holds eight of them
does not meet the margin of `later_leads`, which sets one copy aside. This compares exact
multiples; it does not evaluate the two ordered sums. -/
theorem slack_needed :
    9 * numerical32 (freshChain .discounted 1) - 8 * numerical32 stepWord <
      numerical32 tieWindow := by
  rw [fresh_one_value, step_value, tie_value]
  norm_num

end Lead

/-! ## The candidate of counted sums -/

section Candidate

variable {count : Word.Count}

/-- **A counted value that leads every other is the one candidate.** Take a policy of finite
values in which one action's value reads the ordered sum of `copies` copies of a finite
nonnegative word `lead` of at most `2^(-14)`, for at most 1999 copies, and every other value
reads at most the ordered sum of at most 1999 copies of some such word, which `copies` of `lead`
lead (`Leads`). That action is the one near-maximum candidate, and the greedy draw returns it
whatever the generator. The other words and counts may differ from action to action. Where no
action's value leads in that sense, this names no candidate. -/
theorem margin_candidate (snapshot : PolicySnapshot count) (winner : Action count.word.toNat)
    (lead : Binary32) (copies : Nat) (leadFinite : lead.Finite)
    (leadNonneg : 0 ≤ numerical32 lead) (leadSmall : numerical32 lead ≤ (2 : ℚ) ^ (-14 : Int))
    (fits : copies ≤ 1999) (finite : ∀ action, (snapshot.values.get action).Finite)
    (leads : numerical32 (snapshot.values.get winner) = numerical32 (repeatSum lead copies))
    (trails : ∀ action, action ≠ winner → ∃ (trail : Binary32) (fewer : Nat),
      trail.Finite ∧ 0 ≤ numerical32 trail ∧ numerical32 trail ≤ (2 : ℚ) ^ (-14 : Int) ∧
        fewer ≤ 1999 ∧
        numerical32 (snapshot.values.get action) ≤ numerical32 (repeatSum trail fewer) ∧
        Leads lead copies trail fewer) :
    snapshot.candidates = [winner] ∧ ∀ rng, (snapshot.greedy rng).1 = winner := by
  have sumFinite : (repeatSum lead copies).Finite :=
    (repeatSum_near lead leadFinite leadNonneg leadSmall copies fits).1
  have key : (snapshot.values.get winner).key = (repeatSum lead copies).key :=
    le_antisymm ((numerical32_order _ _ (finite winner) sumFinite).mp leads.le)
      ((numerical32_order _ _ sumFinite (finite winner)).mp leads.ge)
  have threshold : (snapshot.values.get winner).sub tieWindow =
      (repeatSum lead copies).sub tieWindow := by
    rcases key_inj _ _ key with equal | ⟨leftZero, rightZero⟩
    · rw [equal]
    · exact zero_sub_tie _ _ leftZero rightZero
  apply candidates_of_gap snapshot winner (finite winner)
  intro action other
  obtain ⟨trail, fewer, trailFinite, trailNonneg, trailSmall, fitsFewer, below, margin⟩ :=
    trails action other
  have lessFinite := (repeatSum_near trail trailFinite trailNonneg trailSmall fewer fitsFewer).1
  have belowKey := (numerical32_order _ _ (finite action) lessFinite).mp below
  have gap := counted_lead lead trail leadFinite trailFinite leadNonneg trailNonneg leadSmall
    trailSmall copies fewer fits fitsFewer margin
  rw [threshold]
  exact ⟨finite_not_isNaN (finite action), (sub_tie_le _ sumFinite).1,
    lt_of_le_of_lt belowKey gap⟩

/-- **The freshest counted value is the one candidate.** Under the discounted criterion, take a
policy of finite values in which one action's value reads the ordered sum of `copies` stored step
sizes, for at least one and at most 1999 copies, and every other value reads at most the ordered
sum of at most as many fresh traces of age one. That action is the one near-maximum candidate,
and the greedy draw returns it whatever the generator. It is the case of `margin_candidate` in
which every other word is the fresh trace of age one and the counts are in that order. -/
theorem counted_candidate (snapshot : PolicySnapshot count) (winner : Action count.word.toNat)
    (copies : Nat) (positive : 1 ≤ copies) (fits : copies ≤ 1999)
    (finite : ∀ action, (snapshot.values.get action).Finite)
    (leads : numerical32 (snapshot.values.get winner) = numerical32 (repeatSum stepWord copies))
    (trails : ∀ action, action ≠ winner → ∃ fewer, fewer ≤ copies ∧
      numerical32 (snapshot.values.get action) ≤
        numerical32 (repeatSum (freshChain .discounted 1) fewer)) :
    snapshot.candidates = [winner] ∧ ∀ rng, (snapshot.greedy rng).1 = winner := by
  have once := fresh_word .discounted 1
  refine margin_candidate snapshot winner stepWord copies small_step.1 step_nonneg step_bound
    fits finite leads fun action other => ?_
  obtain ⟨fewer, order, below⟩ := trails action other
  exact ⟨freshChain .discounted 1, fewer, once.1, once.2.1, once.2.2, by omega, below,
    recent_leads copies fewer 1 le_rfl positive (by omega)⟩

/-- **One step past fourteen, a second candidate.** Under the discounted criterion, take a
policy of finite values, none above one fresh trace of age 15. An action whose value reads one
fresh trace of age 16 is a near-maximum candidate: a trace of age 15 loses less than the tie
window over one step of decay (`fresh_step`, `fresh_bounds`). Those are the trace totals, at a
frame of one slot, of the action taken on it 15 steps before the last and of the action taken
one step earlier on a frame that holds the same slot, so `own_candidate` does not extend to that
age without a condition on the earlier frames. This is a statement of values; no theorem here
says that a run lays such frames. -/
theorem stale_candidate (snapshot : PolicySnapshot count) (earlier : Action count.word.toNat)
    (finite : ∀ action, (snapshot.values.get action).Finite)
    (top : ∀ action, numerical32 (snapshot.values.get action) ≤
      numerical32 (repeatSum (freshChain .discounted 15) 1))
    (second : numerical32 (snapshot.values.get earlier) =
      numerical32 (repeatSum (freshChain .discounted 16) 1)) :
    earlier ∈ snapshot.candidates := by
  obtain ⟨⟨best, bestIs⟩, keys⟩ := best_bounds snapshot finite
  have bestFinite : snapshot.best.Finite := bestIs ▸ finite best
  have upper : numerical32 snapshot.best ≤ numerical32 (freshChain .discounted 15) := by
    rw [bestIs, ← repeatSum_one _ (fresh_word .discounted 15).1]
    exact top best
  have lower : numerical32 (snapshot.values.get earlier) ≤ numerical32 snapshot.best :=
    (numerical32_order _ _ (finite earlier) bestFinite).mpr (keys earlier)
  rw [repeatSum_one _ (fresh_word .discounted 16).1] at second
  have step := (fresh_step 15 (by omega)).1
  have high := (fresh_bounds 15 (by omega)).2
  have number : (89101 / 100000 : ℚ) ^ 15 * (13743900 * (2 : ℚ) ^ (-38 : Int)) ≤
      886 / 100000000 := by norm_num
  have nonneg := (fresh_word .discounted 16).2.1
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  have e3 : (2 : ℚ) ^ (-3 : Int) = 1 / 8 := by norm_num
  have tieRead := tie_value
  rw [e43] at tieRead
  obtain ⟨gapFinite, gapNear⟩ := binary32_sub_finite_strict_error snapshot.best tieWindow
    bestFinite (by decide) (-3) (by norm_num) (by
      rw [tieRead, e3, abs_lt]
      constructor <;> linarith)
  have radius : (2 : ℚ) ^ (max ((-3 : Int) - 24) (-149)) / 2 = 1 / 268435456 := by norm_num
  rw [radius, tieRead] at gapNear
  have gapBounds := abs_le.mp gapNear
  rw [PolicySnapshot.candidates_def]
  dsimp only
  refine List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true ⟨finite_not_isNaN gapFinite,
    finite_not_isNaN (finite earlier), ?_⟩⟩
  exact (numerical32_order _ _ gapFinite (finite earlier)).mp (by linarith [gapBounds.2])

end Candidate

/-! ## Slots two frames share -/

section Shared

variable {dimension : Dimension}

/-- How many of the slots of `frame` the frame `laid` holds, counted with the multiplicity the
frame's own list gives them: the count `fresh_total` reads. It is not symmetric. -/
def shared (frame laid : ActiveSet dimension) : Nat :=
  frame.indices.countP fun slot => decide (slot ∈ laid.indices)

/-- A frame shares at most its own slots with another. -/
theorem shared_le (frame laid : ActiveSet dimension) :
    shared frame laid ≤ frame.indices.length :=
  List.countP_le_length

/-- A frame shares every one of its slots with itself. -/
theorem shared_self (frame : ActiveSet dimension) :
    shared frame frame = frame.indices.length :=
  List.countP_eq_length.mpr fun _ member => decide_eq_true member

end Shared

/-! ## A kernel run -/

section Run

open AcornVerif.CurrentFirstCredit AcornVerif.CurrentExplorer AcornVerif.CurrentGridWorld

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {dimension : Dimension} {planning : PlanningSelection}

/-- **In a kernel run, the frame of an action taken once stays fresh.** For a profile with no
hierarchy under per-step credit and the discounted criterion, from an agent state whose learners
are at rest and whose primitive controller holds no trace: in a kernel run in which every reward
word is the zero word, over frames of at most 1999 slots and before a unit of the feature bank
matures, take a time whose action the run takes at none of the 119 times before it and at no
time up to `gap` steps after it, for a `gap` of at most 80. Then `gap` steps after that step,
the row of that action holds the fresh trace of age `gap` on every slot of the frame laid at
that time, and no trace elsewhere. -/
theorem loop_fresh (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (laid : Nat) :
    ∀ gap : Nat, gap ≤ 80 →
      agent.clock.toNat + (laid + 1 + gap) ≤ config.tester.maturity →
      (∀ earlier, earlier < laid + 1 + gap →
        (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero) →
      (∀ earlier, earlier < laid + 1 + gap →
        (laidAt agent world start earlier).features.indices.length ≤ 1999) →
      (∀ other, other < laid + 1 + gap → other ≠ laid →
        laid ≤ other + creditReach .discounted →
        Kernel.actionAt world (executedAgent agent) start other ≠
          Kernel.actionAt world (executedAgent agent) start laid) →
      Fresh .discounted
        (controlOf (Kernel.memoryAt world (executedAgent agent) start (laid + 1 + gap)))
        (laidAt agent world start laid).row (laidAt agent world start laid).features gap := by
  intro gap
  induction gap with
  | zero =>
    intro _ young silent fits once
    obtain ⟨ctrlLaid, equation⟩ := loop_silent primitive perStep agent [] quiet ctrl world
      start laid young silent fits
    rw [List.nil_append] at ctrlLaid
    change Fresh .discounted
      (controlOf (Kernel.memoryAt world (executedAgent agent) start (laid + 1))) _ _ 0
    rw [equation]
    refine fresh_laid ctrlLaid _ _ (fits laid (by omega)) fun slot => ?_
    exact (ctrlQuiet_dormant ctrlLaid _ slot (unlaid_window agent world start laid _ _ slot
      fun earlier early within same => absurd (same.trans (laidAt_row agent world start laid))
        (once earlier (by omega) (by omega) within))).1
  | succ gap ih =>
    intro near young silent fits once
    have before := ih (by omega) (by omega) (fun earlier early => silent earlier (by omega))
      (fun earlier early => fits earlier (by omega))
      (fun other early apart within => once other (by omega) apart within)
    obtain ⟨ctrlHere, equation⟩ := loop_silent primitive perStep agent [] quiet ctrl world
      start (laid + 1 + gap) young silent fits
    rw [List.nil_append] at ctrlHere
    change Fresh .discounted
      (controlOf (Kernel.memoryAt world (executedAgent agent) start (laid + 1 + gap + 1))) _ _
      (gap + 1)
    rw [equation]
    refine fresh_after ctrlHere _ _ _ _ gap before ?_
      (freshChain_above .discounted (gap + 1) near)
    rw [laidAt_row, laidAt_row]
    exact once (laid + 1 + gap) (by omega) (by omega) (by omega)

/-- **In a run of pairwise different actions, every trace total sums one word over the shared
slots.** For a profile with no hierarchy under per-step credit and the discounted criterion, from
an agent state whose learners are at rest and whose primitive controller holds no trace: in a
kernel run in which every reward word up to the time `last` is the zero word, over frames of at
most 1999 slots and before a unit of the feature bank matures, suppose the actions at the times
up to `last` are pairwise different. Then, right before the step at the time `last + 1`, on every
frame of at most 1999 slots: the trace total of the action taken `age` steps before the time
`last` reads the ordered sum of as many copies of the fresh trace of that age as the frame holds
slots of the frame laid at that time; and the trace total of an action taken at none of those
times is a zero word. -/
theorem loop_totals (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999) :
    (∀ earlier age, earlier + age = last →
      numerical32 (traceTotal
          (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
          (Kernel.actionAt world (executedAgent agent) start earlier)) =
        numerical32 (repeatSum (freshChain .discounted age) (frame.indices.countP fun slot =>
          decide (slot ∈ (laidAt agent world start earlier).features.indices)))) ∧
      ∀ action, (∀ earlier, earlier < last + 1 →
          Kernel.actionAt world (executedAgent agent) start earlier ≠ action) →
        (traceTotal (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
          frame action).isZero = true := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start
    (last + 1) young silent fits
  rw [List.nil_append] at ctrlPaid
  refine ⟨fun earlier age sum => ?_, fun action untaken => ?_⟩
  · subst sum
    have fresh := loop_fresh primitive perStep agent quiet ctrl world start earlier age
      (by omega) (by omega) (fun other early => silent other (by omega))
      (fun other early => fits other (by omega))
      (fun other early apart _ => distinct other earlier (by omega) (by omega) apart)
    rw [laidAt_row, show earlier + 1 + age = earlier + age + 1 by omega] at fresh
    exact fresh_total ctrlPaid _ _ age fresh frame fitsFrame
  · exact unlaid_total ctrlPaid frame action fun held _ =>
      unlaid_window agent world start (last + 1) _ action held
        fun earlier early _ same => absurd same (untaken earlier early)

/-- **The criterion: the action whose counted traces lead every other's is the one candidate.**
Under the hypotheses of `loop_totals`, take a frame of at most 1999 slots and a time `taken` up
to `last`. Count the fresh trace of that time's age once for each slot the frame holds of the
frame laid then (`shared`). Suppose those lead the fresh trace of every other time up to `last`,
of that time's age and counted for that time's frame, and lead a count of zero (`Leads`). Then
the action taken at the time `taken` is the one near-maximum candidate of the trace policy at
that frame, at any rate, and the greedy draw returns it whatever the generator. The count of
zero is the margin over an action taken at none of those times, whose total is a zero word. The
hypotheses are of counts and of named words alone. Nothing here says that a frame of a run meets
them, and where no time's traces lead, this names no candidate. -/
theorem leading_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (taken : Nat) (early : taken ≤ last)
    (alone : Leads (freshChain .discounted (last - taken))
      (shared frame (laidAt agent world start taken).features) .zero 0)
    (margin : ∀ other, other ≤ last → other ≠ taken →
      Leads (freshChain .discounted (last - taken))
        (shared frame (laidAt agent world start taken).features)
        (freshChain .discounted (last - other))
        (shared frame (laidAt agent world start other).features))
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
        epsilon).candidates = [Kernel.actionAt world (executedAgent agent) start taken] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) frame epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start taken := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start
    (last + 1) young silent fits
  rw [List.nil_append] at ctrlPaid
  obtain ⟨totals, untaken⟩ := loop_totals primitive perStep agent quiet ctrl world start last
    near young silent fits distinct frame fitsFrame
  have word := fresh_word .discounted
  have counted : ∀ laid : ActiveSet dimension, shared frame laid ≤ 1999 :=
    fun laid => Nat.le_trans (shared_le frame laid) fitsFrame
  refine margin_candidate _ _ (freshChain .discounted (last - taken))
    (shared frame (laidAt agent world start taken).features) (word _).1 (word _).2.1
    (word _).2.2 (counted _) (fun action => ?_) ?_ fun action other => ?_
  · rw [tracePolicy_value]
    exact (traces_sum_small ctrlPaid action frame.indices fitsFrame).1.1
  · rw [tracePolicy_value]
    exact totals taken (last - taken) (by omega)
  · rw [tracePolicy_value]
    by_cases once : ∃ earlier, earlier < last + 1 ∧
        Kernel.actionAt world (executedAgent agent) start earlier = action
    · obtain ⟨earlier, before, rfl⟩ := once
      have apart : earlier ≠ taken := fun same => other (by rw [same])
      exact ⟨freshChain .discounted (last - earlier),
        shared frame (laidAt agent world start earlier).features, (word _).1, (word _).2.1,
        (word _).2.2, counted _, le_of_eq (totals earlier (last - earlier) (by omega)),
        margin earlier (by omega) apart⟩
    · refine ⟨.zero, 0, by decide, le_of_eq zero_value.symm, ?_, Nat.zero_le _, ?_, alone⟩
      · rw [zero_value]
        positivity
      · rw [zero_reads (untaken action fun earlier before same => once ⟨earlier, before, same⟩),
          repeatSum_zero, zero_value]

/-- **Outside a run, the first decision after a first reward takes the action whose counted
traces lead.** For a profile with no hierarchy under per-step credit, the declared rate and the
discounted criterion, at the default step order, from an agent state whose learners are at rest
and whose primitive controller holds no trace: in a kernel run in which every reward word up to
the time `last` is the zero word and the next one is the word one, before a unit of the feature
bank matures and over frames of at most 1999 slots, suppose the actions at the times up to `last`
are pairwise different, and at the frame the decision at the time `last + 2` reads the counted
fresh traces of a time `taken` lead those of every other time up to `last` and a count of zero,
as in `leading_candidate`. Then, when the explorer's state after `last + 2` decisions holds no
committed run with a step left and its generator begins none at the declared rate, the action at
the time `last + 2` is the action at the time `taken`. Inside a committed run, or when the
generator begins one, this says nothing of that action. -/
theorem first_choice_leading (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) < config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start (last + 1)).reward = .one)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsNext : (laidAt agent world start (last + 2)).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (taken : Nat) (early : taken ≤ last)
    (alone : Leads (freshChain .discounted (last - taken))
      (shared (laidAt agent world start (last + 2)).features
        (laidAt agent world start taken).features) .zero 0)
    (margin : ∀ other, other ≤ last → other ≠ taken →
      Leads (freshChain .discounted (last - taken))
        (shared (laidAt agent world start (last + 2)).features
          (laidAt agent world start taken).features)
        (freshChain .discounted (last - other))
        (shared (laidAt agent world start (last + 2)).features
          (laidAt agent world start other).features))
    (unserved : ((explorerOf agent.control).after (last + 2)).run.bind ExploratoryRun.serve =
      none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (last + 2)).rng).1 = none) :
    Kernel.actionAt world (executedAgent agent) start (last + 2) =
      Kernel.actionAt world (executedAgent agent) start taken := by
  have chosen := first_choice primitive perStep declared agent [] quiet ctrl world start
    (last + 1) young silent pays fits fitsNext
  have greedy := Explorer.stepOver_greedy ((explorerOf agent.control).after (last + 2))
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
      (laidAt agent world start (last + 2)).features declaredRate) unserved calm
  have candidate := (leading_candidate primitive perStep agent quiet ctrl world start last near
    (by omega) silent fits distinct (laidAt agent world start (last + 2)).features fitsNext
    taken early alone margin declaredRate).2
  rw [chosen, greedy]
  exact candidate _

/-- **Where the actions before a time are all different, the last one is the candidate where its
frame shares more than `0.892` of what each earlier one shares.** Under the hypotheses of
`loop_totals`, take a frame of at most 1999 slots that holds a slot of the frame laid at the time
`last`, and more slots of it than `223/250` of what it holds of the frame laid at each earlier
time. Then the action taken at the time `last` is the one near-maximum candidate of the trace
policy at that frame, at any rate, and the greedy draw returns it whatever the generator
(`leading_candidate`, `recent_leads`). The frame may hold fewer slots of the last frame than of
an earlier one: nine against ten meet the condition. -/
theorem recent_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (shares : 1 ≤ shared frame (laidAt agent world start last).features)
    (most : ∀ earlier, earlier < last →
      223 * shared frame (laidAt agent world start earlier).features <
        250 * shared frame (laidAt agent world start last).features)
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
        epsilon).candidates = [Kernel.actionAt world (executedAgent agent) start last] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) frame epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start last := by
  refine leading_candidate primitive perStep agent quiet ctrl world start last near young silent
    fits distinct frame fitsFrame last le_rfl ?_ (fun other before apart => ?_) epsilon
  · rw [Nat.sub_self]
    exact own_alone 0 _ (by omega) shares
  · rw [Nat.sub_self]
    exact recent_leads _ _ (last - other) (by omega) shares (most other (by omega))

/-- **A frame that holds more than `0.892` of its slots of the last frame has the last action for
its candidate.** Under the hypotheses of `loop_totals`, take a frame of at most 1999 slots that
holds more than `223/250` of its own slots of the frame laid at the time `last`. Then the action
taken at the time `last` is the one near-maximum candidate of the trace policy at that frame, at
any rate, and the greedy draw returns it whatever the generator: a frame holds at most all its
slots of any earlier frame (`recent_candidate`, `shared_le`). So in a run each of whose frames
holds that much of the last frame laid, the last action is the candidate at every frame. A frame
with no slot does not meet the condition. -/
theorem overlap_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (most : 223 * frame.indices.length <
      250 * shared frame (laidAt agent world start last).features)
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
        epsilon).candidates = [Kernel.actionAt world (executedAgent agent) start last] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) frame epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start last :=
  recent_candidate primitive perStep agent quiet ctrl world start last near young silent fits
    distinct frame fitsFrame (by omega)
    (fun earlier _ => by
      have fewer := shared_le frame (laidAt agent world start earlier).features
      omega)
    epsilon

/-- **Where the actions before a time are all different, the last one is the candidate where its
frame shares most.** Under the hypotheses of `loop_totals`, take a frame of at most 1999 slots
that holds a slot of the frame laid at the time `last`, and at least as many slots of it as of
the frame laid at each earlier time. Then the action taken at the time `last` is the one
near-maximum candidate of the trace policy at that frame, at any rate, and the greedy draw
returns it whatever the generator. It is the case of `recent_candidate` in which the frame holds
at least as many slots of the last frame as of each earlier one. -/
theorem last_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (shares : 1 ≤ frame.indices.countP fun slot =>
      decide (slot ∈ (laidAt agent world start last).features.indices))
    (most : ∀ earlier, earlier < last →
      (frame.indices.countP fun slot =>
        decide (slot ∈ (laidAt agent world start earlier).features.indices)) ≤
      frame.indices.countP fun slot =>
        decide (slot ∈ (laidAt agent world start last).features.indices))
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
        epsilon).candidates = [Kernel.actionAt world (executedAgent agent) start last] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) frame epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start last :=
  recent_candidate primitive perStep agent quiet ctrl world start last near young silent fits
    distinct frame fitsFrame shares
    (fun earlier before => by
      have fewer := most earlier before
      unfold shared
      omega)
    epsilon

/-- **Outside a run, the first decision after a first reward that follows pairwise different
actions takes the last of them again where its frame shares more than `0.892` of what each
earlier one shares.** For a profile with no hierarchy under per-step credit, the declared rate
and the discounted criterion, at the default step order, from an agent state whose learners are
at rest and whose primitive controller holds no trace: in a kernel run in which every reward word
up to the time `last` is the zero word and the next one is the word one, before a unit of the
feature bank matures and over frames of at most 1999 slots, suppose the actions at the times up
to `last` are pairwise different, and the frame the decision at the time `last + 2` reads holds a
slot of the frame laid at the time `last`, and more slots of it than `223/250` of what it holds
of the frame laid at each earlier time. Then, when the explorer's state after `last + 2`
decisions holds no committed run with a step left and its generator begins none at the declared
rate, the action at the time `last + 2` is the action at the time `last` (`first_choice`,
`recent_candidate`). -/
theorem first_choice_recent (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) < config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start (last + 1)).reward = .one)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsNext : (laidAt agent world start (last + 2)).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (shares : 1 ≤ shared (laidAt agent world start (last + 2)).features
      (laidAt agent world start last).features)
    (most : ∀ earlier, earlier < last →
      223 * shared (laidAt agent world start (last + 2)).features
          (laidAt agent world start earlier).features <
        250 * shared (laidAt agent world start (last + 2)).features
          (laidAt agent world start last).features)
    (unserved : ((explorerOf agent.control).after (last + 2)).run.bind ExploratoryRun.serve =
      none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (last + 2)).rng).1 = none) :
    Kernel.actionAt world (executedAgent agent) start (last + 2) =
      Kernel.actionAt world (executedAgent agent) start last := by
  have chosen := first_choice primitive perStep declared agent [] quiet ctrl world start
    (last + 1) young silent pays fits fitsNext
  have greedy := Explorer.stepOver_greedy ((explorerOf agent.control).after (last + 2))
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
      (laidAt agent world start (last + 2)).features declaredRate) unserved calm
  have candidate := (recent_candidate primitive perStep agent quiet ctrl world start last near
    (by omega) silent fits distinct (laidAt agent world start (last + 2)).features fitsNext
    shares most declaredRate).2
  rw [chosen, greedy]
  exact candidate _

/-- **Outside a run, the first decision after a first reward that follows pairwise different
actions takes the last of them again.** For a profile with no hierarchy under per-step credit,
the declared rate and the discounted criterion, at the default step order, from an agent state
whose learners are at rest and whose primitive controller holds no trace: in a kernel run in
which every reward word up to the time `last` is the zero word and the next one is the word one,
before a unit of the feature bank matures and over frames of at most 1999 slots, suppose the
actions at the times up to `last` are pairwise different, and the frame the decision at the time
`last + 2` reads holds a slot of the frame laid at the time `last`, and at least as many slots of
it as of the frame laid at each earlier time. Then, when the explorer's state after `last + 2`
decisions holds no committed run with a step left and its generator begins none at the declared
rate, the action at the time `last + 2` is the action at the time `last`. It is the case of
`first_choice_recent` in which that frame holds at least as many slots of the last frame as of
each earlier one. -/
theorem first_choice_last (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) < config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start (last + 1)).reward = .one)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsNext : (laidAt agent world start (last + 2)).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (shares : 1 ≤ (laidAt agent world start (last + 2)).features.indices.countP fun slot =>
      decide (slot ∈ (laidAt agent world start last).features.indices))
    (most : ∀ earlier, earlier < last →
      ((laidAt agent world start (last + 2)).features.indices.countP fun slot =>
        decide (slot ∈ (laidAt agent world start earlier).features.indices)) ≤
      (laidAt agent world start (last + 2)).features.indices.countP fun slot =>
        decide (slot ∈ (laidAt agent world start last).features.indices))
    (unserved : ((explorerOf agent.control).after (last + 2)).run.bind ExploratoryRun.serve =
      none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (last + 2)).rng).1 = none) :
    Kernel.actionAt world (executedAgent agent) start (last + 2) =
      Kernel.actionAt world (executedAgent agent) start last :=
  first_choice_recent primitive perStep declared agent quiet ctrl world start last near young
    silent pays fits fitsNext distinct shares
    (fun earlier before => by
      have fewer := most earlier before
      unfold shared
      omega)
    unserved calm

/-- **The action taken on a frame is the candidate at that frame where each later frame holds
at most `0.89` for each step of its slots but one.** Under the hypotheses of `loop_totals`, take
a time `taken` at most 14 steps before the time `last`, whose frame holds at least one slot.
Suppose that for each number of steps `more` from one up to `last - taken`, the frame laid
`more` steps after `taken` holds at most `0.89^more` of that frame's slots but one. Then at the
frame laid at the time `taken`, the action taken there is the one near-maximum candidate of the
trace policy, at any rate, and the greedy draw returns it whatever the generator
(`leading_candidate`, `later_leads`, `earlier_leads`, `own_alone`). Nothing is assumed of the
frames laid before the time `taken`. The 14 is the age up to which one slot's loss over one step
of decay exceeds the tie window and the rounding, by `fresh_fourteen` from the stored numbers;
at an age of 15 the statement fails without a condition on the earlier frames
(`stale_candidate`). The slot set aside is needed as well (`slack_needed`). This is a statement
at that one frame, and it says nothing of which frames a run lays. -/
theorem own_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (taken : Nat) (early : taken ≤ last) (recent : last ≤ taken + 14)
    (holds : 1 ≤ (laidAt agent world start taken).features.indices.length)
    (later : ∀ more, 1 ≤ more → taken + more ≤ last →
      shared (laidAt agent world start taken).features
          (laidAt agent world start (taken + more)).features * 100 ^ more ≤
        89 ^ more * ((laidAt agent world start taken).features.indices.length - 1))
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
        (laidAt agent world start taken).features epsilon).candidates =
          [Kernel.actionAt world (executedAgent agent) start taken] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) (laidAt agent world start taken).features epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start taken := by
  refine leading_candidate primitive perStep agent quiet ctrl world start last near young silent
    fits distinct _ (fits taken (by omega)) taken early ?_ (fun other before apart => ?_) epsilon
  · rw [shared_self]
    exact own_alone _ _ (by omega) holds
  · rw [shared_self]
    rcases Nat.lt_or_gt_of_ne apart with below | above
    · have lead := earlier_leads (last - taken) (taken - other)
        (laidAt agent world start taken).features.indices.length
        (shared (laidAt agent world start taken).features (laidAt agent world start other).features)
        (by omega) (by omega) holds (shared_le _ _)
      rwa [show last - taken + (taken - other) = last - other by omega] at lead
    · have share := later (other - taken) (by omega) (by omega)
      rw [show taken + (other - taken) = other by omega] at share
      have lead := later_leads (last - taken) (other - taken) _ _ (by omega) (by omega)
        (by omega) holds share
      rwa [show last - taken - (other - taken) = last - other by omega] at lead

end Run

end AcornVerif.CurrentTraceCounts
