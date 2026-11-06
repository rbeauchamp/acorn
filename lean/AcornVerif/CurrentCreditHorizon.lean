/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.StepParts
import AcornVerif.CurrentPreReward
import AcornVerif.CurrentControl

/-!
# How far back a first reward reaches in the executed primitive controller

The primitive learner clears a slot's trace once its decayed word falls to the pruning threshold,
`Config.epsilon` times the step size the slot was laid with (`NumericState.firstLoopElement`, the
eligible-set pruning that Acorn adds to Algorithm 1 of Javed, Sharifnassab & Sutton, *SwiftTD*,
Reinforcement Learning Journal 2 (2024)), and the first loop never visits a cleared slot again
until a step lays it. So on a run whose rewards are zero, a slot that a row has not laid on its
last `creditReach criterion` steps holds no trace in that row, and no later reward of any size
reaches its weight before a step lays it again. The limit is set by the trace decay and the
pruning threshold; it does not depend on the reward word or on the tie window.

`dormant_weight_rests` states this of the executed agent (`Agent.initial`, `Agent.choose` and
`Chosen.learn` through `traced`): from cold initialization, over reward-free percepts whose frames
hold at most 1999 slots, and then any percepts at all, a primitive weight is a zero word unless
its row laid its slot in the window, the last `creditReach criterion` reward-free steps and every
later step. `candidates_read_window` gives the consequence for the greedy choice through
`AcornVerif.CurrentControl.candidates_of_resting`: at any frame and exploration rate the
near-maximum candidates are those of the frame's slots that some window step laid.
`recent_weight_moves` shows that the limit is not met trivially: on a controller's cold run over
frames of at most 1900 slots, a slot laid at most 81 steps before a first reward of one has a weight
that the reward moves. The values 119 and 132 are upper limits; the theorems do not say that a
trace reaches them.

**Words.** Every statement is about the executed binary32 words. The primitive learner's stored
step size is `stepWord` (`0x3851b71c`), the portable exponential of its stored log step size
`logStepWord`; its pruning threshold is `pruneWord`; its trace decay is `decayOf criterion`.
Bounds are carried by the monotonicity of nearest rounding on exact readings
(`AcornVerif.CurrentBackupBounds.Rounded.mono`), with no rounding-error estimate: every bound is
itself an executed word, and the kernel decides each comparison between named words. Ordered sums
over a frame are bounded by the ordered sum of as many copies of the largest term
(`sumFrom_le_repeat`); one pass of `partialSums` checks every such sum up to the frame bound.

**While the rewards are zero** (`CtrlQuiet`). Every weight is a zero word, the shared lags are zero
words and no restart is pending; every slot keeps the initial log step size, zero update and
meta-gradient registers, a Dutch trace in `[0, 1]` and a trace between zero and `traceBound`, a
fixed point of laying; and a slot that a row has not laid on its last `j` steps has a trace at
most `chain criterion j`, the trace bound decayed `j` times, and is not eligible once that word is
at most the pruning threshold (`RowQuiet`). On a frame of at most 1999 slots the ordered sum of
step sizes stays at or below `Config.eta`, so the overshoot branch of the second loop is not taken
and its trace scale is one, and the trace total stays below one, so each laid increment lies
between zero and the step size (`quiet_entry`, `laid_trace`). Each controller step keeps this
against the history extended by the step (`ctrlQuiet_step`), and so does each retirement
(`ctrlQuiet_retire`); at `creditReach criterion` steps the bound is at most the threshold
(`reach_pruned`), so the slot is `Dormant`: not eligible, with a zero weight
(`ctrlQuiet_dormant`).

**Afterwards.** A step that does not lay a dormant slot in its row keeps it dormant for every
reward, lag, error and decay word and every pending restart (`creditStep_dormant`), and so does a
retirement (`retire_dormant`): the first loop visits only eligible slots, and only a laying step
admits one.

**From the agent to the controller.** The first part of a step writes no primitive row
(`Agent.choose_keeps`); neither do the owed writes and the deferred planning
(`TemporalControl.deferred_keeps`), the off-policy option learning or the span close
(`followOptions_control`, `closeSpan_control`). The completion boundary credits the controller with
`Controller.step` at the encoded frame and the executed action under per-step credit, and with
nothing under a frozen profile (`finish_control`); the tester then only retires slots
(`retire_closed`). The reward word the step sees is centred at the average-reward rate, which the
state of `AcornVerif.CurrentPreReward.Quiet` keeps inert, and a stored rate is finite, so it is a
zero word (`quiet_rate`).

**Not covered.** Nothing here bounds the credit inside the window, or says whether slots shared with
the window help the agent. Frames over 1999 slots in the reward-free part, profiles without per-step
credit, the meta-controller and the option policies are outside these statements. Lean's kernel, its
float model of binary32 and the agreement of native `Float32` with that model on finite operands
remain trusted, as for every proof of executed words in this library.
-/

namespace AcornVerif.CurrentCreditHorizon
open Acorn Acorn.Features Acorn.Handcrafted

/-- How many steps before a first reward a primitive controller's trace can still reach. -/
def creditReach : Criterion → Nat
  | .discounted => 119
  | .differential => 132

/-- One step the primitive controller took: the frame it encoded and the row it credited. -/
structure Laid (dimension : Dimension) (actions : Nat) where
  /-- The frame's active slots. -/
  features : SwiftTd.ActiveSet dimension
  /-- The executed action, the row whose traces this step lays. -/
  row : Action actions

/-- This step laid the slot in the row. -/
def Laid.Lays {dimension : Dimension} {actions : Nat} (step : Laid dimension actions)
    (row : Action actions) (slot : FeatIdx dimension) : Prop :=
  step.row = row ∧ slot ∈ step.features.indices

section Words

open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds

/-! ## Monotone rounding on small binary32 words

Every bound below compares exact rationals read from finite words (`numerical32`) and carries
them through the executed operations by the monotonicity of nearest rounding
(`AcornVerif.CurrentBackupBounds.Rounded.mono`). No rounding-error estimate is used: the bounds
are themselves executed words, and their comparisons are decided by the kernel. -/

/-- A finite word whose exact reading lies within four of zero. -/
def Small (word : Binary32) : Prop := word.Finite ∧ |numerical32 word| ≤ 4

/-- The word four. -/
def four : Binary32 := ⟨0x40800000⟩

/-- The word minus four. -/
def minusFour : Binary32 := ⟨0xc0800000⟩

/-- The word four reads four. -/
theorem four_value : numerical32 four = 4 := by
  change (1:ℚ) * 8388608 * (2:ℚ) ^ (-21:Int) = 4
  norm_num

/-- The word minus four reads minus four. -/
theorem minusFour_value : numerical32 minusFour = -4 := by
  change (-1:ℚ) * 8388608 * (2:ℚ) ^ (-21:Int) = -4
  norm_num

/-- Key order and exact order agree on finite words. -/
theorem num_le {left right : Binary32} (hl : left.Finite) (hr : right.Finite)
    (order : left.key ≤ right.key) : numerical32 left ≤ numerical32 right :=
  (numerical32_order left right hl hr).mpr order

/-- Exact order of finite words is key order. -/
theorem key_le {left right : Binary32} (hl : left.Finite) (hr : right.Finite)
    (order : numerical32 left ≤ numerical32 right) : left.key ≤ right.key :=
  (numerical32_order left right hl hr).mp order

/-- A finite word between the keys of minus four and four is small. -/
theorem small_of_key {word : Binary32} (finite : word.Finite) (lower : minusFour.key ≤ word.key)
    (upper : word.key ≤ four.key) : Small word := by
  have lo := num_le (by decide) finite lower
  have hi := num_le finite (by decide) upper
  rw [minusFour_value] at lo
  rw [four_value] at hi
  exact ⟨finite, abs_le.mpr ⟨lo, hi⟩⟩

/-- A finite word whose reading lies between two small words is small. -/
theorem small_between {word lower upper : Binary32} (finite : word.Finite) (hl : Small lower)
    (hu : Small upper) (lo : numerical32 lower ≤ numerical32 word)
    (hi : numerical32 word ≤ numerical32 upper) : Small word := by
  refine ⟨finite, abs_le.mpr ⟨?_, ?_⟩⟩
  · linarith [(abs_le.mp hl.2).1]
  · linarith [(abs_le.mp hu.2).2]

/-- Positive zero reads zero. -/
theorem zero_value : numerical32 Binary32.zero = 0 := rfl

/-- Positive zero is small. -/
theorem small_zero : Small Binary32.zero :=
  ⟨by decide, by rw [zero_value]; norm_num⟩

/-- Two roundings of one exact source are one reading. -/
theorem rounded_unique {source first second : ℚ} (left : Rounded source first)
    (right : Rounded source second) : first = second :=
  le_antisymm (left.mono right le_rfl) (right.mono left le_rfl)

/-- The executed sum of small words is finite and is the rounding of the exact sum. -/
theorem add_small {left right : Binary32} (hl : Small left) (hr : Small right) :
    (left.add right).Finite ∧
      Rounded (numerical32 left + numerical32 right) (numerical32 (left.add right)) :=
  binary32_rounded_add left right hl.1 hr.1 (by
    have := abs_add_le (numerical32 left) (numerical32 right)
    linarith [hl.2, hr.2])

/-- The executed product of small words is finite and is the rounding of the exact product. -/
theorem mul_small {left right : Binary32} (hl : Small left) (hr : Small right) :
    (left.mul right).Finite ∧
      Rounded (numerical32 left * numerical32 right) (numerical32 (left.mul right)) :=
  binary32_rounded_mul left right hl.1 hr.1 (by
    rw [abs_mul]
    nlinarith [hl.2, hr.2, abs_nonneg (numerical32 left), abs_nonneg (numerical32 right)])

/-- The executed difference of small words is finite and is the rounding of the exact
difference. -/
theorem sub_small {left right : Binary32} (hl : Small left) (hr : Small right) :
    (left.sub right).Finite ∧
      Rounded (numerical32 left - numerical32 right) (numerical32 (left.sub right)) :=
  binary32_rounded_sub left right hl.1 hr.1 (by
    have := abs_sub (numerical32 left) (numerical32 right)
    linarith [hl.2, hr.2])

/-- A finite word is its own rounding. -/
theorem exact_word {word : Binary32} (finite : word.Finite) :
    Rounded (numerical32 word) (numerical32 word) :=
  binary32_rounded_exact word finite

/-- Monotone executed sums. -/
theorem add_mono {a b c d : Binary32} (ha : Small a) (hb : Small b) (hc : Small c)
    (hd : Small d) (ac : numerical32 a ≤ numerical32 c) (bd : numerical32 b ≤ numerical32 d) :
    numerical32 (a.add b) ≤ numerical32 (c.add d) :=
  (add_small ha hb).2.mono (add_small hc hd).2 (by linarith)

/-- Monotone executed differences. -/
theorem sub_mono {a b c d : Binary32} (ha : Small a) (hb : Small b) (hc : Small c)
    (hd : Small d) (ac : numerical32 a ≤ numerical32 c) (db : numerical32 d ≤ numerical32 b) :
    numerical32 (a.sub b) ≤ numerical32 (c.sub d) :=
  (sub_small ha hb).2.mono (sub_small hc hd).2 (by linarith)

/-- Monotone executed products of nonnegative words. -/
theorem mul_mono {a b c d : Binary32} (ha : Small a) (hb : Small b) (hc : Small c)
    (hd : Small d) (a0 : 0 ≤ numerical32 a) (b0 : 0 ≤ numerical32 b)
    (ac : numerical32 a ≤ numerical32 c) (bd : numerical32 b ≤ numerical32 d) :
    numerical32 (a.mul b) ≤ numerical32 (c.mul d) :=
  (mul_small ha hb).2.mono (mul_small hc hd).2 (mul_le_mul ac bd b0 (le_trans a0 ac))

/-- A rounding of a nonnegative source is nonnegative. -/
theorem rounded_nonneg {source result : ℚ} (rounded : Rounded source result)
    (nonneg : 0 ≤ source) : 0 ≤ result :=
  rounded_zero.mono rounded nonneg

/-- An executed product of nonnegative small words is nonnegative. -/
theorem mul_nonneg' {a b : Binary32} (ha : Small a) (hb : Small b) (a0 : 0 ≤ numerical32 a)
    (b0 : 0 ≤ numerical32 b) : 0 ≤ numerical32 (a.mul b) :=
  rounded_nonneg (mul_small ha hb).2 (mul_nonneg a0 b0)

/-- An executed sum of nonnegative small words is nonnegative. -/
theorem add_nonneg' {a b : Binary32} (ha : Small a) (hb : Small b) (a0 : 0 ≤ numerical32 a)
    (b0 : 0 ≤ numerical32 b) : 0 ≤ numerical32 (a.add b) :=
  rounded_nonneg (add_small ha hb).2 (add_nonneg a0 b0)

/-- Multiplying a nonnegative small word by a factor at most one does not raise it. -/
theorem mul_le_self {a b : Binary32} (ha : Small a) (hb : Small b) (a0 : 0 ≤ numerical32 a)
    (b1 : numerical32 b ≤ 1) : numerical32 (a.mul b) ≤ numerical32 a :=
  (mul_small ha hb).2.mono (exact_word ha.1) (by nlinarith)

/-- Adding a nonnegative small word does not lower a small word. -/
theorem le_add_right {a b : Binary32} (ha : Small a) (hb : Small b) (b0 : 0 ≤ numerical32 b) :
    numerical32 a ≤ numerical32 (a.add b) :=
  (exact_word ha.1).mono (add_small ha hb).2 (by linarith)

/-- Adding a small word to a nonnegative small word does not lower the added word. -/
theorem le_add_left {a b : Binary32} (ha : Small a) (hb : Small b) (a0 : 0 ≤ numerical32 a) :
    numerical32 b ≤ numerical32 (a.add b) :=
  (exact_word hb.1).mono (add_small ha hb).2 (by linarith)

end Words

section Slots

open AcornVerif.CurrentLearner
open SwiftTd (ActiveSet swapRemove)

variable {cfg : Acorn.Config} {dimension : Dimension}

/-! ## What one learner holds at one slot

A first-loop visit, a second-loop visit and a register clear each write the words of one slot
and leave every other slot's words as they were (`first_element_frame`, `second_element_frame`,
`clear_feature_other`). So a property of one slot's words is carried through a loop by
following that slot alone. -/

/-- The words one learner holds at one slot: its weight, its log step size and its nine
transient registers, in the order of `AcornVerif.CurrentLearner.registers`. -/
structure Slot where
  /-- The weight word. -/
  weight : Binary32
  /-- The log step size word. -/
  beta : Binary32
  /-- The nine transient registers. -/
  regs : Vector Binary32 9

/-- The trace register. -/
abbrev Slot.z (slot : Slot) : Binary32 := slot.regs[0]
/-- The trace increment register. -/
abbrev Slot.zDelta (slot : Slot) : Binary32 := slot.regs[1]
/-- The Dutch-trace register. -/
abbrev Slot.zBar (slot : Slot) : Binary32 := slot.regs[2]
/-- The pruning reference. -/
abbrev Slot.lastAlpha (slot : Slot) : Binary32 := slot.regs[3]
/-- The per-weight update register. -/
abbrev Slot.deltaWeight (slot : Slot) : Binary32 := slot.regs[4]
/-- The auxiliary register. -/
abbrev Slot.h (slot : Slot) : Binary32 := slot.regs[5]
/-- The previous auxiliary register. -/
abbrev Slot.hOld (slot : Slot) : Binary32 := slot.regs[6]
/-- The accumulating auxiliary register. -/
abbrev Slot.hTemp (slot : Slot) : Binary32 := slot.regs[7]
/-- The meta-trace register. -/
abbrev Slot.p (slot : Slot) : Binary32 := slot.regs[8]

/-- The words a learner holds at a slot. -/
def slotOf (state : NumericState cfg dimension) (idx : FeatIdx dimension) : Slot :=
  ⟨(state.weights.get idx).value, (state.beta.get idx).value, registers state idx⟩

section Reads
variable (state : NumericState cfg dimension) (idx : FeatIdx dimension)
/-- The slot's `weight` word is the state's word at the slot. -/
theorem slotOf_weight : (slotOf state idx).weight = (state.weights.get idx).value := rfl
/-- The slot's `beta` word is the state's word at the slot. -/
theorem slotOf_beta : (slotOf state idx).beta = (state.beta.get idx).value := rfl
/-- The slot's `z` word is the state's word at the slot. -/
theorem slotOf_z : (slotOf state idx).z = (state.transient.z.get idx).value := rfl
/-- The slot's `zDelta` word is the state's word at the slot. -/
theorem slotOf_zDelta : (slotOf state idx).zDelta = (state.transient.zDelta.get idx).value := rfl
/-- The slot's `zBar` word is the state's word at the slot. -/
theorem slotOf_zBar : (slotOf state idx).zBar = (state.transient.zBar.get idx).value := rfl
/-- The slot's `lastAlpha` word is the state's word at the slot. -/
theorem slotOf_lastAlpha :
    (slotOf state idx).lastAlpha = (state.transient.lastAlpha.get idx).value := rfl
/-- The slot's `deltaWeight` word is the state's word at the slot. -/
theorem slotOf_deltaWeight :
    (slotOf state idx).deltaWeight = (state.transient.deltaWeight.get idx).value := rfl
/-- The slot's `h` word is the state's word at the slot. -/
theorem slotOf_h : (slotOf state idx).h = (state.transient.h.get idx).value := rfl
/-- The slot's `hOld` word is the state's word at the slot. -/
theorem slotOf_hOld : (slotOf state idx).hOld = (state.transient.hOld.get idx).value := rfl
/-- The slot's `hTemp` word is the state's word at the slot. -/
theorem slotOf_hTemp : (slotOf state idx).hTemp = (state.transient.hTemp.get idx).value := rfl
/-- The slot's `p` word is the state's word at the slot. -/
theorem slotOf_p : (slotOf state idx).p = (state.transient.p.get idx).value := rfl
end Reads

/-- A first-loop visit keeps every other slot's words. -/
theorem slotOf_first_other (state : NumericState cfg dimension) (idx other : FeatIdx dimension)
    (different : idx ≠ other) (delta vDelta decay : Binary32) :
    slotOf (state.firstLoopElement idx delta vDelta decay).1 other = slotOf state other := by
  have frame := first_element_frame state idx other different delta vDelta decay
  simp only [slotOf, frame.1, frame.2.1, frame.2.2]

/-- A register clear keeps every other slot's words. -/
theorem slotOf_clear_other (state : NumericState cfg dimension) (idx other : FeatIdx dimension)
    (different : idx ≠ other) :
    slotOf (state.clearFeatureRegisters idx) other = slotOf state other := by
  have knowledge := clear_feature_knowledge state idx other
  simp only [slotOf, knowledge.1, knowledge.2, clear_feature_other state idx other different]

/-- A second-loop visit keeps every other slot's words. -/
theorem slotOf_second_other (state : NumericState cfg dimension) (idx other : FeatIdx dimension)
    (different : idx ≠ other) (overshoot : Bool) (denominator total vDelta : Binary32) :
    slotOf (NumericState.secondLoopElement cfg overshoot denominator total state vDelta idx).1
      other = slotOf state other := by
  have frame := second_element_frame state idx other different overshoot denominator total vDelta
  simp only [slotOf, frame.1, frame.2.1, frame.2.2]

/-- A first-loop visit keeps the rails. -/
theorem first_element_rails (state : NumericState cfg dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    (state.firstLoopElement idx delta vDelta decay).1.rails = state.rails := rfl

/-- A register clear keeps the rails. -/
theorem clear_rails (state : NumericState cfg dimension) (idx : FeatIdx dimension) :
    (state.clearFeatureRegisters idx).rails = state.rails := by
  simp only [NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
    NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
    NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
    NumericState.writeLastAlpha]

/-- **The first-loop traversal, slot by slot.** Take three properties of a slot's words: one
that every slot still to be visited has, one that a visited slot kept eligible has, and one that
a slot outside the work list has. If a visit takes the first property to the second when it
keeps the slot and to the third when it prunes and clears it, the traversal ends with the second
property on every eligible slot and the third on every other slot. -/
theorem first_go_slots (Pre Post Out : FeatIdx dimension → Slot → Prop)
    (delta vDelta decay : Binary32) (rails : StepSizeRails cfg)
    (visit : ∀ (current : NumericState cfg dimension) (idx : FeatIdx dimension),
      current.rails = rails → Pre idx (slotOf current idx) →
      ((current.firstLoopElement idx delta vDelta decay).2 = true →
        Out idx (slotOf ((current.firstLoopElement idx delta vDelta decay).1.clearFeatureRegisters
          idx) idx)) ∧
      ((current.firstLoopElement idx delta vDelta decay).2 = false →
        Post idx (slotOf (current.firstLoopElement idx delta vDelta decay).1 idx)))
    (state : NumericState cfg dimension) (work : Array (FeatIdx dimension)) (pos : Nat)
    (sameRails : state.rails = rails) (unique : work.toList.Nodup)
    (done : ∀ (i : Nat) (inside : i < work.size), i < pos → Post work[i] (slotOf state work[i]))
    (todo : ∀ (i : Nat) (inside : i < work.size), pos ≤ i → Pre work[i] (slotOf state work[i]))
    (outside : ∀ idx, idx ∉ work → Out idx (slotOf state idx)) :
    let final := NumericState.learnFirstLoopGo cfg delta vDelta decay state work pos
    final.rails = rails ∧ final.transient.eligible.toList.Nodup ∧
      (∀ idx ∈ final.transient.eligible, Post idx (slotOf final idx)) ∧
      (∀ idx, idx ∉ final.transient.eligible → Out idx (slotOf final idx)) := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct cfg delta vDelta decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    have here := visit state work[pos] sameRails (todo pos valid le_rfl)
    rw [equation] at here
    have pruned := here.1 rfl
    have distinct : ∀ (i : Nat) (inside : i < work.size), i ≠ pos → work[pos] ≠ work[i] := by
      intro i inside different same
      exact different ((array_nodup_iff work).mp unique pos i valid inside same).symm
    have keep : ∀ other, work[pos] ≠ other →
        slotOf (next.clearFeatureRegisters work[pos]) other = slotOf state other := by
      intro other different
      rw [slotOf_clear_other next _ _ different]
      have first := slotOf_first_other state work[pos] other different delta vDelta decay
      rw [equation] at first
      exact first
    have nextRails : next.rails = state.rails := by
      have read := congrArg (fun result : NumericState cfg dimension × Bool => result.1.rails)
        equation
      exact read.symm.trans (first_element_rails state work[pos] delta vDelta decay)
    have result := ih (by rw [← sameRails, ← nextRails]; exact clear_rails next work[pos])
      (swap_remove_nodup work pos valid unique)
      (by
        intro i inside before
        have original : i < work.size := by rw [swap_remove_size] at inside; omega
        have untouched : (swapRemove work pos valid)[i] = work[i] := by
          rw [swap_remove_get, ite_eq_right (show pos ≠ i by omega)]
        rw [untouched, keep _ (distinct i original (by omega))]
        exact done i original before)
      (by
        intro i inside after
        have bound : i < work.size - 1 := by rw [swap_remove_size] at inside; exact inside
        rw [swap_remove_get]
        split
        · have last : work.size - 1 < work.size := by omega
          rw [keep _ (distinct _ last (by omega))]
          exact todo _ last (by omega)
        · rename_i different
          have original : i < work.size := by omega
          rw [keep _ (distinct i original (by omega))]
          exact todo i original (by omega))
      (by
        intro other absent
        by_cases same : work[pos] = other
        · subst other
          exact pruned
        · rw [keep other same]
          apply outside other
          intro member
          exact absent (swap_remove_preserves_other work pos valid other (Ne.symm same) member))
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simpa only [equation, ite_true] using result
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation ih
    have here := visit state work[pos] sameRails (todo pos valid le_rfl)
    rw [equation] at here
    have kept := here.2 (Bool.eq_false_iff.mpr noPrune)
    have distinct : ∀ (i : Nat) (inside : i < work.size), i ≠ pos → work[pos] ≠ work[i] := by
      intro i inside different same
      exact different ((array_nodup_iff work).mp unique pos i valid inside same).symm
    have keep : ∀ other, work[pos] ≠ other → slotOf next other = slotOf state other := by
      intro other different
      have first := slotOf_first_other state work[pos] other different delta vDelta decay
      rw [equation] at first
      exact first
    have nextRails : next.rails = state.rails := by
      have read := congrArg (fun result : NumericState cfg dimension × Bool => result.1.rails)
        equation
      exact read.symm.trans (first_element_rails state work[pos] delta vDelta decay)
    have result := ih (by rw [← sameRails, ← nextRails]) unique
      (by
        intro i inside before
        by_cases atPos : i = pos
        · subst i
          exact kept
        · rw [keep _ (distinct i inside atPos)]
          exact done i inside (by omega))
      (by
        intro i inside after
        rw [keep _ (distinct i inside (by omega))]
        exact todo i inside (by omega))
      (by
        intro other absent
        have different : work[pos] ≠ other := by
          intro same
          exact absent (same ▸ Array.getElem_mem valid)
        rw [keep other different]
        exact outside other absent)
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simpa only [equation, ite_eq_right noPrune] using result
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo_def, dite_eq_right finished]
    refine ⟨sameRails, unique, ?_, ?_⟩
    · intro other member
      obtain ⟨i, inside, rfl⟩ := Array.mem_iff_getElem.mp member
      change i < work.size at inside
      exact done i inside (by omega)
    · intro other absent
      exact outside other absent

/-- **The first loop, slot by slot.** The public first loop under the same hypotheses, from
the learner's eligible list. -/
theorem first_loop_slots (Pre Post Out : FeatIdx dimension → Slot → Prop)
    (delta vDelta decay : Binary32) (rails : StepSizeRails cfg)
    (visit : ∀ (current : NumericState cfg dimension) (idx : FeatIdx dimension),
      current.rails = rails → Pre idx (slotOf current idx) →
      ((current.firstLoopElement idx delta vDelta decay).2 = true →
        Out idx (slotOf ((current.firstLoopElement idx delta vDelta decay).1.clearFeatureRegisters
          idx) idx)) ∧
      ((current.firstLoopElement idx delta vDelta decay).2 = false →
        Post idx (slotOf (current.firstLoopElement idx delta vDelta decay).1 idx)))
    (state : NumericState cfg dimension) (sameRails : state.rails = rails)
    (unique : state.transient.eligible.toList.Nodup)
    (eligible : ∀ idx ∈ state.transient.eligible, Pre idx (slotOf state idx))
    (outside : ∀ idx, idx ∉ state.transient.eligible → Out idx (slotOf state idx)) :
    let final := state.learnFirstLoop cfg delta vDelta decay
    final.rails = rails ∧ final.transient.eligible.toList.Nodup ∧
      (∀ idx ∈ final.transient.eligible, Post idx (slotOf final idx)) ∧
      (∀ idx, idx ∉ final.transient.eligible → Out idx (slotOf final idx)) := by
  rw [NumericState.learnFirstLoop_def]
  exact first_go_slots Pre Post Out delta vDelta decay rails visit _ _ 0 sameRails unique
    (fun _ _ before => absurd before (Nat.not_lt_zero _))
    (fun i inside _ => eligible _ (Array.getElem_mem inside))
    outside

/-- A second-loop visit keeps the rails. -/
theorem second_element_rails (state : NumericState cfg dimension) (idx : FeatIdx dimension)
    (overshoot : Bool) (denominator total vDelta : Binary32) :
    (NumericState.secondLoopElement cfg overshoot denominator total state vDelta idx).1.rails =
      state.rails := by
  cases overshoot <;> rfl

/-- **The second-loop fold, slot by slot.** If a visit takes a property of an active slot's
words to a second property, and keeps a property of the shared accumulator, then the fold over
unique active slots ends with the second property on every active slot, the accumulator property,
and every other slot's words unchanged. -/
theorem second_fold_slots (Pre Post : FeatIdx dimension → Slot → Prop) (Acc : Binary32 → Prop)
    (overshoot : Bool) (denominator total : Binary32) (rails : StepSizeRails cfg)
    (visit : ∀ (current : NumericState cfg dimension) (vd : Binary32) (idx : FeatIdx dimension),
      current.rails = rails → Acc vd → Pre idx (slotOf current idx) →
      Post idx (slotOf (NumericState.secondLoopElement cfg overshoot denominator total current vd
        idx).1 idx) ∧
      Acc (NumericState.secondLoopElement cfg overshoot denominator total current vd idx).2) :
    ∀ (indices : List (FeatIdx dimension)) (state : NumericState cfg dimension) (vd : Binary32),
      indices.Nodup → state.rails = rails → Acc vd → (∀ idx ∈ indices, Pre idx (slotOf state idx)) →
      let final := indices.foldl (fun (current, vd) idx =>
        NumericState.secondLoopElement cfg overshoot denominator total current vd idx) (state, vd)
      final.1.rails = rails ∧ Acc final.2 ∧ (∀ idx ∈ indices, Post idx (slotOf final.1 idx)) ∧
        (∀ idx, idx ∉ indices → slotOf final.1 idx = slotOf state idx) := by
  intro indices
  induction indices with
  | nil =>
    intro state vd _ sameRails acc _
    exact ⟨sameRails, acc, fun _ member => absurd member List.not_mem_nil, fun _ _ => rfl⟩
  | cons head rest ih =>
    intro state vd unique sameRails acc todo
    have fresh := (List.nodup_cons.mp unique).1
    have restUnique := (List.nodup_cons.mp unique).2
    have here := visit state vd head sameRails acc (todo head (List.mem_cons_self ..))
    let next := NumericState.secondLoopElement cfg overshoot denominator total state vd head
    have keep : ∀ other, head ≠ other → slotOf next.1 other = slotOf state other :=
      fun other different =>
        slotOf_second_other state head other different overshoot denominator total vd
    have result := ih next.1 next.2 restUnique
      ((second_element_rails state head overshoot denominator total vd).trans sameRails) here.2
      (fun idx member => by
        have different : head ≠ idx := fun same => fresh (same ▸ member)
        rw [keep idx different]
        exact todo idx (List.mem_cons_of_mem _ member))
    rw [List.foldl_cons]
    refine ⟨result.1, result.2.1, ?_, ?_⟩
    · intro idx member
      rcases List.mem_cons.mp member with same | later
      · subst idx
        rw [result.2.2.2 head fresh]
        exact here.1
      · exact result.2.2.1 idx later
    · intro idx absent
      have different : head ≠ idx := fun same => absent (same ▸ List.mem_cons_self ..)
      rw [result.2.2.2 idx (fun member => absent (List.mem_cons_of_mem _ member))]
      exact keep idx different

/-- **The second loop, slot by slot.** The public second loop is the fold of
`second_fold_slots` at its entry words (`NumericState.learnSecondLoop_eq_sumFrom`). -/
theorem second_loop_slots (Pre Post : FeatIdx dimension → Slot → Prop) (Acc : Binary32 → Prop)
    (rails : StepSizeRails cfg) (state : NumericState cfg dimension)
    (features : ActiveSet dimension) (vd : Binary32)
    (visit : ∀ (current : NumericState cfg dimension) (vd : Binary32) (idx : FeatIdx dimension),
      current.rails = rails → Acc vd → Pre idx (slotOf current idx) →
      let rate := Binary32.sumFrom .zero
        (features.indices.map fun idx => (state.beta.get idx).alpha)
      let overshoot := cfg.eta.less rate
      let e := if overshoot then rate else cfg.eta
      let t := Binary32.sumFrom .zero
        (features.indices.map fun idx => (state.transient.z.get idx).value)
      Post idx (slotOf (NumericState.secondLoopElement cfg overshoot e t current vd idx).1 idx) ∧
      Acc (NumericState.secondLoopElement cfg overshoot e t current vd idx).2)
    (sameRails : state.rails = rails) (acc : Acc vd)
    (todo : ∀ idx ∈ features.indices, Pre idx (slotOf state idx)) :
    let final := state.learnSecondLoop cfg features vd
    final.1.rails = rails ∧ Acc final.2 ∧
      (∀ idx ∈ features.indices, Post idx (slotOf final.1 idx)) ∧
      (∀ idx, idx ∉ features.indices → slotOf final.1 idx = slotOf state idx) := by
  rw [NumericState.learnSecondLoop_eq_sumFrom]
  exact second_fold_slots Pre Post Acc _ _ _ rails visit features.indices state vd features.nodup
    sameRails acc todo

end Slots

section Rows

open AcornVerif.CurrentLearner AcornVerif.CurrentPreReward AcornVerif.CurrentFeatureConsumers
open SwiftTd (ActiveSet)

variable {cfg : Acorn.Config} {dimension : Dimension} {actions : Nat}

/-! ## What one controller step writes into one row -/

/-- A row's credit is its first loop, then a clear on a pending restart. -/
theorem credit_state (learner : Managed cfg dimension) (delta vd decay : Binary32)
    (restart : Bool) :
    (learner.credit delta vd decay restart).val.state =
      if restart then (learner.state.learnFirstLoop cfg delta vd decay).clearTransient
      else learner.state.learnFirstLoop cfg delta vd decay := by
  rw [Managed.credit_def]
  cases restart <;> rfl

/-- A shared-error update writes into each row its credit, and into the taken row the second loop
of that credit, from zero. -/
theorem creditStep_row (controller : Controller cfg dimension actions)
    (features : ActiveSet dimension) (action : Action actions) (lag delta decay : Binary32)
    (row : Fin actions) :
    ((controller.creditStep features action lag delta decay).learners.get row).state =
      if action = row then
        (((controller.learners.get row).credit delta controller.vDelta decay
          controller.restartPending).val.state.learnSecondLoop cfg features .zero).1
      else ((controller.learners.get row).credit delta controller.vDelta decay
          controller.restartPending).val.state := by
  rw [Controller.creditStep_eq]
  dsimp only
  rw [get_set_vec]
  split
  · rename_i same
    subst same
    rw [get_map_vec]
  · rw [get_map_vec, get_map_vec]

/-- A shared-error update stores the taken row's second-loop accumulator, the lag and no
pending restart. -/
theorem creditStep_lags (controller : Controller cfg dimension actions)
    (features : ActiveSet dimension) (action : Action actions) (lag delta decay : Binary32) :
    (controller.creditStep features action lag delta decay).vOld = lag ∧
      (controller.creditStep features action lag delta decay).vDelta =
        (((controller.learners.get action).credit delta controller.vDelta decay
          controller.restartPending).val.state.learnSecondLoop cfg features .zero).2 ∧
      (controller.creditStep features action lag delta decay).restartPending = false := by
  rw [Controller.creditStep_eq]
  dsimp only
  rw [get_map_vec]
  exact ⟨rfl, rfl, rfl⟩

/-- A controller step is the shared-error update at the taken row's value, with the rule's
discount and trace decay. -/
theorem step_eq (controller : Controller cfg dimension actions) (features : ActiveSet dimension)
    (action : Action actions) (reward : Binary32) :
    (controller.step features action reward).1 =
      controller.creditStep features action ((controller.predictAll features).get action)
        ((reward.add (cfg.rule.gamma.mul ((controller.predictAll features).get action))).sub
          controller.vOld) (cfg.rule.gamma.mul cfg.lambda) := rfl

/-- A retirement retires the slot in every row and keeps the shared words. -/
theorem retire_row (controller : Controller cfg dimension actions) (feature : FeatIdx dimension)
    (row : Fin actions) :
    ((controller.retire feature).learners.get row).state =
        ((controller.learners.get row).state).retireIndex feature ∧
      (controller.retire feature).vOld = controller.vOld ∧
      (controller.retire feature).vDelta = controller.vDelta ∧
      (controller.retire feature).restartPending = controller.restartPending := by
  rw [Controller.retire_def]
  dsimp only
  rw [get_map_vec, Managed.retire_def, Managed.apply_state, SwiftTd.Entry.apply_def]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every row's eligible list is unique: rows are admitted learners. -/
theorem row_unique (controller : Controller cfg dimension actions) (row : Fin actions) :
    (controller.learners.get row).state.transient.eligible.toList.Nodup :=
  (managed_schedule (controller.learners.get row)).2.1

/-- Every row's slots outside its eligible list hold nine positive-zero registers. -/
theorem row_supported (controller : Controller cfg dimension actions) (row : Fin actions) :
    Supported (controller.learners.get row).state
      (controller.learners.get row).state.transient.eligible :=
  (managed_schedule (controller.learners.get row)).1.1

/-! ## A slot no step lays rests -/

/-- A slot that is not eligible in a row and holds a zero weight there. -/
def Dormant (controller : Controller cfg dimension actions) (row : Fin actions)
    (slot : FeatIdx dimension) : Prop :=
  slot ∉ (controller.learners.get row).state.transient.eligible ∧
    ((controller.learners.get row).state.weights.get slot).value.isZero = true

/-- A first loop over any words keeps a slot outside the eligible list, and keeps its weight. -/
theorem first_loop_dormant (state : NumericState cfg dimension) (delta vDelta decay : Binary32)
    (slot : FeatIdx dimension) (unique : state.transient.eligible.toList.Nodup)
    (absent : slot ∉ state.transient.eligible)
    (weight : (state.weights.get slot).value.isZero = true) :
    slot ∉ (state.learnFirstLoop cfg delta vDelta decay).transient.eligible ∧
      ((state.learnFirstLoop cfg delta vDelta decay).weights.get slot).value.isZero = true := by
  have result := first_loop_slots (fun idx _ => idx ≠ slot) (fun idx _ => idx ≠ slot)
    (fun idx words => idx = slot → words.weight.isZero = true) delta vDelta decay state.rails
    (fun _ idx _ different => ⟨fun _ same => absurd same different, fun _ => different⟩)
    state rfl unique (fun idx member same => absent (same ▸ member))
    (fun idx _ same => by subst same; exact weight)
  have outside : slot ∉ (state.learnFirstLoop cfg delta vDelta decay).transient.eligible :=
    fun member => result.2.2.1 slot member rfl
  exact ⟨outside, result.2.2.2 slot outside rfl⟩

/-- A second loop over a frame without the slot keeps it outside the eligible list, and keeps its
weight. -/
theorem second_loop_dormant (state : NumericState cfg dimension) (features : ActiveSet dimension)
    (vd : Binary32) (slot : FeatIdx dimension) (unlaid : slot ∉ features.indices)
    (absent : slot ∉ state.transient.eligible) :
    slot ∉ (state.learnSecondLoop cfg features vd).1.transient.eligible ∧
      ((state.learnSecondLoop cfg features vd).1.weights.get slot).value =
        (state.weights.get slot).value := by
  have frame := second_loop_slots (fun _ _ => True) (fun _ _ => True) (fun _ => True) state.rails
    state features vd (fun _ _ _ _ _ _ => ⟨trivial, trivial⟩) rfl trivial (fun _ _ => trivial)
  refine ⟨?_, congrArg Slot.weight (frame.2.2.2 slot unlaid)⟩
  intro member
  have listed := Array.mem_toList_iff.mpr member
  rw [second_loop_eligible] at listed
  rcases List.mem_append.mp listed with old | fresh
  · exact absent (Array.mem_toList_iff.mp old)
  · exact unlaid (List.mem_filter.mp fresh).1

/-- **A step that does not lay a slot in a row keeps it dormant there**, for every reward, lag,
error and decay word and every pending restart. -/
theorem creditStep_dormant (controller : Controller cfg dimension actions)
    (features : ActiveSet dimension) (action : Action actions) (lag delta decay : Binary32)
    (row : Fin actions) (slot : FeatIdx dimension) (dormant : Dormant controller row slot)
    (unlaid : ¬(action = row ∧ slot ∈ features.indices)) :
    Dormant (controller.creditStep features action lag delta decay) row slot := by
  unfold Dormant
  rw [creditStep_row]
  have first := first_loop_dormant (controller.learners.get row).state delta controller.vDelta
    decay slot (row_unique controller row) dormant.1 dormant.2
  have credited : slot ∉ ((controller.learners.get row).credit delta controller.vDelta decay
        controller.restartPending).val.state.transient.eligible ∧
      (((controller.learners.get row).credit delta controller.vDelta decay
        controller.restartPending).val.state.weights.get slot).value.isZero = true := by
    rw [credit_state]
    split
    · refine ⟨?_, first.2⟩
      rw [NumericState.clearTransient_def, TransientState.zero_def]
      simp
    · exact first
  split
  · rename_i taken
    have unlisted : slot ∉ features.indices := fun member => unlaid ⟨taken, member⟩
    have second := second_loop_dormant _ features .zero slot unlisted credited.1
    exact ⟨second.1, second.2 ▸ credited.2⟩
  · exact credited

/-- A retirement writes no other slot's weight. -/
theorem retire_weight_other (state : NumericState cfg dimension) (feature slot : FeatIdx dimension)
    (different : feature ≠ slot) :
    ((state.retireIndex feature).weights.get slot).value = (state.weights.get slot).value := by
  have distinct : feature.val ≠ slot.val := fun equal => different (Fin.ext equal)
  rw [NumericState.retireIndex_def]
  dsimp only
  split <;>
  · simp only [NumericState.writeBetaValue, NumericState.writeWeight, vector_get,
      Vector.getElem_set_ne _ _ distinct]
    rw [← vector_get, ← vector_get, (clear_feature_knowledge _ feature slot).1]
    try rfl

/-- A retirement keeps every slot dormant. -/
theorem retire_dormant (controller : Controller cfg dimension actions) (feature : FeatIdx dimension)
    (row : Fin actions) (slot : FeatIdx dimension) (dormant : Dormant controller row slot) :
    Dormant (controller.retire feature) row slot := by
  unfold Dormant
  rw [(retire_row controller feature row).1, NumericState.retireIndex_def]
  dsimp only
  constructor
  · intro member
    apply dormant.1
    split at member
    · exact swap_remove_subset _ _ _ _ member
    · exact member
  · by_cases same : feature = slot
    · subst same
      simp only [NumericState.writeBetaValue, NumericState.writeWeight, vector_get,
        Vector.getElem_set_self]
      exact Inert32.project Inert32.zero cfg.rule
    · have kept := retire_weight_other (controller.learners.get row).state feature slot same
      rw [NumericState.retireIndex_def] at kept
      exact kept ▸ dormant.2

end Rows

section Constants

open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder

/-! ## The executed words of the primitive learner

Each fact below is a closed statement about named binary32 words and reduces in the kernel. -/

/-- The primitive learner's stored step size, the portable exponential of the portable logarithm
of the configured `0x3851b717`. -/
def stepWord : Binary32 := ⟨0x3851b71c⟩

/-- The primitive learner's stored initial log step size. -/
def logStepWord : Binary32 := ⟨0xc11e74af⟩

/-- The pruning threshold of a slot laid at the stored step size. -/
def pruneWord : Binary32 := ⟨0x30097062⟩

/-- A fixed point of laying: a trace at most this word is at most this word after a step that
lays it. -/
def traceBound : Criterion → Binary32
  | .discounted => ⟨0x39f07fbe⟩
  | .differential => ⟨0x3a03126b⟩

/-- The primitive learner's trace decay, `gamma * lambda` of the criterion's control
configuration. -/
def decayOf (criterion : Criterion) : Binary32 :=
  (criterion.config .control).rule.gamma.mul (criterion.config .control).lambda

/-- The trace bound decayed `j` times. -/
def chain (criterion : Criterion) : Nat → Binary32
  | 0 => traceBound criterion
  | j + 1 => (chain criterion j).mul (decayOf criterion)

set_option maxRecDepth 100000 in
/-- The initial log step size of the primitive learner is `logStepWord`. -/
theorem rails_initial_value (criterion : Criterion) :
    (StepSizeRails.ofConfig (criterion.config .control)).initial.value = logStepWord := by
  cases criterion <;> decide

set_option maxRecDepth 100000 in
/-- The step size of the initial log step size is `stepWord`. -/
theorem logStep_alpha {cfg : Acorn.Config} {rails : StepSizeRails cfg} (beta : LogStepSize rails)
    (value : beta.value = logStepWord) : beta.alpha = stepWord := by
  unfold LogStepSize.alpha
  rw [value]
  decide

/-- The pruning threshold of a slot laid at the stored step size is `pruneWord`. -/
theorem prune_eq (criterion : Criterion) :
    stepWord.mul (criterion.config .control).epsilon = pruneWord := by
  cases criterion <;> decide +kernel

/-- Without overshoot the trace scale is one, so a laying visit writes the stored step size
as its increment and its pruning reference. -/
theorem scale_one (criterion : Criterion) :
    ((criterion.config .control).eta.div (criterion.config .control).eta).mul stepWord =
      stepWord := by
  cases criterion <;> decide +kernel

/-- A trace at most the trace bound, decayed once and laid at the stored step size, is at most
the trace bound. -/
theorem fixed_point (criterion : Criterion) :
    (((traceBound criterion).mul (decayOf criterion)).add stepWord).key ≤
      (traceBound criterion).key := by
  cases criterion <;> decide +kernel

/-- The trace bound decayed `creditReach criterion` times is at most the pruning threshold. -/
theorem reach_pruned (criterion : Criterion) :
    (chain criterion (creditReach criterion)).key ≤ pruneWord.key := by
  cases criterion <;> decide +kernel

/-- The pruning threshold is below the trace bound. -/
theorem prune_below (criterion : Criterion) : pruneWord.key < (traceBound criterion).key := by
  cases criterion <;> decide +kernel

/-- The trace decay is a finite word in `[0, 1]`. -/
theorem decay_words (criterion : Criterion) :
    (decayOf criterion).Finite ∧ 0 ≤ (decayOf criterion).key ∧
      (decayOf criterion).key ≤ Binary32.one.key := by
  cases criterion <;> decide +kernel

/-- The trace bound is a finite word in `[0, 1]`. -/
theorem bound_words (criterion : Criterion) :
    (traceBound criterion).Finite ∧ 0 ≤ (traceBound criterion).key ∧
      (traceBound criterion).key ≤ Binary32.one.key := by
  cases criterion <;> decide +kernel

end Constants

section Sums

open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds

/-! ## Ordered sums of bounded words

A frame's step-size total and trace total are ordered sums over its slots. Each is bounded by
the ordered sum of as many copies of the largest term, and every such sum up to the frame bound is
checked once, in the kernel, by one pass over the partial sums (`partialSums`). -/

/-- The ordered sum of `count` copies of a word. -/
def repeatSum (word : Binary32) (count : Nat) : Binary32 :=
  Binary32.sumFrom .zero (List.replicate count word)

/-- Whether each of the next `count` partial sums of copies of `word` from `total` is finite and
lies between zero and `bound`. -/
def partialSums (word bound : Binary32) : Binary32 → Nat → Bool
  | _, 0 => true
  | total, count + 1 =>
    let next := total.add word
    decide next.Finite && decide (0 ≤ next.key) && decide (next.key ≤ bound.key) &&
      partialSums word bound next count

/-- A passing check bounds every partial sum it covers. -/
theorem partialSums_spec (word bound : Binary32) :
    ∀ (count : Nat) (total : Binary32), partialSums word bound total count = true →
      total.Finite → 0 ≤ total.key → total.key ≤ bound.key →
      ∀ k ≤ count, (Binary32.sumFrom total (List.replicate k word)).Finite ∧
        0 ≤ (Binary32.sumFrom total (List.replicate k word)).key ∧
        (Binary32.sumFrom total (List.replicate k word)).key ≤ bound.key := by
  intro count
  induction count with
  | zero =>
    intro total _ finite lower upper k bound
    have : k = 0 := by omega
    subst this
    exact ⟨finite, lower, upper⟩
  | succ count ih =>
    intro total check finite lower upper k bound
    cases k with
    | zero => exact ⟨finite, lower, upper⟩
    | succ k =>
      simp only [partialSums, Bool.and_eq_true, decide_eq_true_eq] at check
      rw [List.replicate_succ, Binary32.sumFrom_def, List.foldl_cons, ← Binary32.sumFrom_def]
      exact ih _ check.2 check.1.1.1 check.1.1.2 check.1.2 k (by omega)

/-- A pass of the check from zero bounds every sum of at most `count` copies. -/
theorem repeatSum_bound (word bound : Binary32) (count : Nat)
    (check : partialSums word bound .zero count = true) (positive : 0 ≤ bound.key) :
    ∀ k ≤ count, (repeatSum word k).Finite ∧ 0 ≤ (repeatSum word k).key ∧
      (repeatSum word k).key ≤ bound.key :=
  partialSums_spec word bound count .zero check (by decide) (by decide)
    (by have : (Binary32.zero).key = 0 := by decide
        omega)

/-- No copies sum to positive zero. -/
theorem repeatSum_zero (word : Binary32) : repeatSum word 0 = .zero := rfl

/-- Adding one more copy extends the ordered sum by one term. -/
theorem repeatSum_succ (word : Binary32) (count : Nat) :
    repeatSum word (count + 1) = (repeatSum word count).add word := by
  unfold repeatSum
  rw [List.replicate_succ', Binary32.sumFrom_append]
  rfl

/-- **Ordered sums are monotone in their terms.** An ordered sum from a nonnegative accumulator
of nonnegative words, each at most `word`, is at most the sum of as many copies of `word` from a
larger accumulator, when every partial sum of the copies is small. -/
theorem sumFrom_le_repeat (word : Binary32) (small : Small word) :
    ∀ (terms : List Binary32) (total : Binary32) (count : Nat),
      (∀ k ≤ count + terms.length, Small (repeatSum word k)) →
      Small total → 0 ≤ numerical32 total → numerical32 total ≤ numerical32 (repeatSum word count) →
      (∀ term ∈ terms, Small term ∧ 0 ≤ numerical32 term ∧ numerical32 term ≤ numerical32 word) →
      Small (Binary32.sumFrom total terms) ∧ 0 ≤ numerical32 (Binary32.sumFrom total terms) ∧
        numerical32 (Binary32.sumFrom total terms) ≤
          numerical32 (repeatSum word (count + terms.length)) := by
  intro terms
  induction terms with
  | nil =>
    intro total count _ smallTotal lower upper _
    have empty : Binary32.sumFrom total [] = total := rfl
    rw [empty]
    exact ⟨smallTotal, lower, upper⟩
  | cons term rest ih =>
    intro total count partials smallTotal lower upper bounded
    have here := bounded term (List.mem_cons_self ..)
    have before := partials count (by omega)
    have after := partials (count + 1) (by simp only [List.length_cons]; omega)
    have sum := add_small smallTotal here.1
    have grown : numerical32 (total.add term) ≤ numerical32 (repeatSum word (count + 1)) := by
      rw [repeatSum_succ]
      exact add_mono smallTotal here.1 before small upper here.2.2
    have lowerNext : 0 ≤ numerical32 (total.add term) :=
      add_nonneg' smallTotal here.1 lower here.2.1
    have smallNext : Small (total.add term) :=
      small_between sum.1 small_zero after
        (by rw [show numerical32 Binary32.zero = 0 from rfl]; exact lowerNext) grown
    rw [Binary32.sumFrom_def, List.foldl_cons, ← Binary32.sumFrom_def]
    have result := ih (total.add term) (count + 1)
      (fun k bound => partials k (by simp at bound ⊢; omega)) smallNext lowerNext grown
      (fun other member => bounded other (List.mem_cons_of_mem _ member))
    simpa [Nat.add_assoc, Nat.add_comm 1] using result

end Sums

section ZeroWords

open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentPreReward
open Float.Model (Format UnpackedFloat)

/-! ## Zero words -/

/-- A zero word is finite. -/
theorem zero_finite {word : Binary32} (zero : word.isZero = true) : word.Finite := by
  rcases isZero_bits word zero with bits | bits <;>
  · obtain ⟨raw⟩ := word
    simp only at bits
    subst bits
    decide

/-- A zero word reads zero. -/
theorem zero_reads {word : Binary32} (zero : word.isZero = true) : numerical32 word = 0 := by
  rcases isZero_bits word zero with bits | bits <;>
  · obtain ⟨raw⟩ := word
    simp only at bits
    subst bits
    rfl

/-- A zero word is small. -/
theorem zero_small {word : Binary32} (zero : word.isZero = true) : Small word :=
  ⟨zero_finite zero, by rw [zero_reads zero]; norm_num⟩

/-- A product of a finite word and a zero word is a zero word. -/
theorem finite_mul_zero {left right : Binary32} (hl : left.Finite) (hr : right.isZero = true) :
    (left.mul right).isZero = true := by
  obtain ⟨sr, er⟩ := zeroWord_model hr
  have decoded := AcornVerif.CurrentArithmetic.model_ofBits32_decoded left hl
  have finiteModel := (AcornVerif.CurrentArithmetic.model_decoded32_finite left).mpr hl
  change (⟨(Float32.Model.pack (UnpackedFloat.mul Format.binary32
    (Float32.ofBits left.bits).toModel.unpack (Float32.ofBits right.bits).toModel.unpack)).toBits⟩ :
      Binary32).isZero = true
  rw [er]
  change (⟨(Float32.Model.pack (UnpackedFloat.mul Format.binary32
    (Float32.Model.ofBits left.bits).unpack (.zero sr))).toBits⟩ : Binary32).isZero = true
  rw [decoded]
  cases hd : AcornVerif.CurrentArithmetic.decoded32 left with
  | notANumber => rw [hd] at finiteModel; contradiction
  | infinity sign => rw [hd] at finiteModel; contradiction
  | zero sign => exact zeroWord_pack _
  | finite sign mantissa exponent positive => exact zeroWord_pack _

/-- Two zero words compare numerically equal. -/
theorem zeros_equal {left right : Binary32} (hl : left.isZero = true) (hr : right.isZero = true) :
    left.numericallyEqual right = true := by
  rw [Binary32.numericallyEqual_eq_key, Binary32.finite_not_nan left (zero_finite hl),
    Binary32.finite_not_nan right (zero_finite hr), AcornVerif.CurrentLearner.zero_key left hl,
    AcornVerif.CurrentLearner.zero_key right hr]
  decide

/-- Adding a zero word keeps the initial log step size. -/
theorem logStep_add_zero {word : Binary32} (zero : word.isZero = true) :
    logStepWord.add word = logStepWord := by
  rcases isZero_bits word zero with bits | bits <;>
  · obtain ⟨raw⟩ := word
    simp only at bits
    subst bits
    decide +kernel

end ZeroWords

section Laying

open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds

/-! ## The words a laying visit writes -/

/-- The word one reads one. -/
theorem one_value : numerical32 Binary32.one = 1 := by
  change (1:ℚ) * 8388608 * (2:ℚ) ^ (-23:Int) = 1
  norm_num

/-- The word one is small. -/
theorem small_one : Small Binary32.one := ⟨by decide, by rw [one_value]; norm_num⟩

/-- A named word between minus four and four is small. -/
theorem small_named {word : Binary32}
    (check : word.Finite ∧ minusFour.key ≤ word.key ∧ word.key ≤ four.key) : Small word :=
  small_of_key check.1 check.2.1 check.2.2

/-- The stored step size is small. -/
theorem small_step : Small stepWord := small_named (by decide)

/-- The stored step size is nonnegative. -/
theorem step_nonneg : 0 ≤ numerical32 stepWord := by
  rw [← zero_value]; exact num_le (by decide) (by decide) (by decide)

/-- The stored step size is at most one. -/
theorem step_le_one : numerical32 stepWord ≤ 1 := by
  rw [← one_value]; exact num_le (by decide) (by decide) (by decide)

/-- The trace bound is small. -/
theorem small_bound (criterion : Criterion) : Small (traceBound criterion) :=
  small_named (by cases criterion <;> decide)

/-- The trace decay is small. -/
theorem small_decay (criterion : Criterion) : Small (decayOf criterion) :=
  small_named (by cases criterion <;> decide +kernel)

/-- The trace decay is nonnegative. -/
theorem decay_nonneg (criterion : Criterion) : 0 ≤ numerical32 (decayOf criterion) := by
  rw [← zero_value]
  exact num_le (by decide) (decay_words criterion).1 (decay_words criterion).2.1

/-- The trace decay is at most one. -/
theorem decay_le_one (criterion : Criterion) : numerical32 (decayOf criterion) ≤ 1 := by
  rw [← one_value]
  exact num_le (decay_words criterion).1 (by decide) (decay_words criterion).2.2

/-- The trace bound is nonnegative. -/
theorem bound_nonneg (criterion : Criterion) : 0 ≤ numerical32 (traceBound criterion) := by
  rw [← zero_value]
  exact num_le (by decide) (bound_words criterion).1 (bound_words criterion).2.1

/-- Multiplication by a fixed nonnegative small word is monotone, whatever the signs. -/
theorem mul_mono_right {a b c : Binary32} (ha : Small a) (hb : Small b) (hc : Small c)
    (a0 : 0 ≤ numerical32 a) (bc : numerical32 b ≤ numerical32 c) :
    numerical32 (a.mul b) ≤ numerical32 (a.mul c) :=
  (mul_small ha hb).2.mono (mul_small ha hc).2 (mul_le_mul_of_nonneg_left bc a0)

/-- The decayed trace bound. -/
def decayedBound (criterion : Criterion) : Binary32 :=
  (traceBound criterion).mul (decayOf criterion)

/-- The decayed trace bound is small. -/
theorem small_decayedBound (criterion : Criterion) : Small (decayedBound criterion) :=
  small_named (by cases criterion <;> decide +kernel)

/-- **The trace a laying visit writes.** From a trace in `[0, decayedBound]` and a complement in
`[0, 1]`, the laid trace is finite, at least the increment, which is nonnegative, and at most the
trace bound. -/
theorem laid_trace (criterion : Criterion) {z complement : Binary32} (zs : Small z)
    (z0 : 0 ≤ numerical32 z) (zh : numerical32 z ≤ numerical32 (decayedBound criterion))
    (cs : Small complement) (c0 : 0 ≤ numerical32 complement)
    (c1 : numerical32 complement ≤ 1) :
    (z.add (stepWord.mul complement)).Finite ∧
      0 ≤ numerical32 (stepWord.mul complement) ∧
      numerical32 (stepWord.mul complement) ≤ numerical32 (z.add (stepWord.mul complement)) ∧
      numerical32 (z.add (stepWord.mul complement)) ≤ numerical32 (traceBound criterion) := by
  have product := mul_small small_step cs
  have inc0 := mul_nonneg' small_step cs step_nonneg c0
  have incHigh : numerical32 (stepWord.mul complement) ≤ numerical32 stepWord := by
    have below := mul_mono_right small_step cs small_one step_nonneg (by rw [one_value]; exact c1)
    rwa [show stepWord.mul Binary32.one = stepWord by decide] at below
  have incSmall : Small (stepWord.mul complement) :=
    small_between product.1 small_zero small_step (by rw [zero_value]; exact inc0) incHigh
  have sum := add_small zs incSmall
  refine ⟨sum.1, inc0, le_add_left zs incSmall z0, ?_⟩
  have upper := add_mono zs incSmall (small_decayedBound criterion) small_step zh incHigh
  have fixed := num_le (by cases criterion <;> decide +kernel) (bound_words criterion).1
    (fixed_point criterion)
  exact le_trans upper fixed

/-- The threshold of the Dutch-trace bound. -/
def nearOne : Binary32 := ⟨0x3f7fbe77⟩

/-- **The Dutch trace a laying visit writes stays in `[0, 1]`.** -/
theorem laid_dutch {zBar complement : Binary32} (finite : zBar.Finite)
    (z0 : 0 ≤ numerical32 zBar) (z1 : numerical32 zBar ≤ 1) (cs : Small complement)
    (c0 : 0 ≤ numerical32 complement) (c1 : numerical32 complement ≤ 1) :
    (zBar.add (stepWord.mul (complement.sub zBar))).Finite ∧
      0 ≤ numerical32 (zBar.add (stepWord.mul (complement.sub zBar))) ∧
      numerical32 (zBar.add (stepWord.mul (complement.sub zBar))) ≤ 1 := by
  have zs : Small zBar := ⟨finite, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have difference := sub_small cs zs
  have diffHigh : numerical32 (complement.sub zBar) ≤ numerical32 (Binary32.one.sub zBar) :=
    sub_mono cs zs small_one zs (by rw [one_value]; exact c1) le_rfl
  have oneSub := sub_small small_one zs
  have oneSubLow : 0 ≤ numerical32 (Binary32.one.sub zBar) :=
    rounded_nonneg oneSub.2 (by rw [one_value]; linarith)
  have oneSubHigh : numerical32 (Binary32.one.sub zBar) ≤ 1 := by
    have := sub_mono small_one zs small_one small_zero le_rfl (by rw [zero_value]; exact z0)
    rwa [show Binary32.one.sub Binary32.zero = Binary32.one by decide, one_value] at this
  have oneSubSmall : Small (Binary32.one.sub zBar) :=
    ⟨oneSub.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have negative : numerical32 (Binary32.zero.sub zBar) = -numerical32 zBar :=
    rounded_unique (sub_small small_zero zs).2
      (by rw [zero_value, zero_sub]; exact Rounded.neg (exact_word finite))
  have diffLow : -numerical32 zBar ≤ numerical32 (complement.sub zBar) := by
    rw [← negative]
    exact sub_mono small_zero zs cs zs (by rw [zero_value]; exact c0) le_rfl
  have diffSmall : Small (complement.sub zBar) :=
    ⟨difference.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have incSmall : Small (stepWord.mul (complement.sub zBar)) := by
    refine ⟨(mul_small small_step diffSmall).1, abs_le.mpr ⟨?_, ?_⟩⟩
    · have := mul_mono_right small_step (small_named (by decide) : Small minusFour) diffSmall
        step_nonneg (by rw [minusFour_value]; linarith)
      have bound : numerical32 (stepWord.mul minusFour) = numerical32 ⟨0xb951b71c⟩ := by
        rw [show stepWord.mul minusFour = ⟨0xb951b71c⟩ by decide]
      have floor : (-4 : ℚ) ≤ numerical32 (⟨0xb951b71c⟩ : Binary32) := by
        rw [← minusFour_value]; exact num_le (by decide) (by decide) (by decide)
      linarith
    · have := mul_mono_right small_step diffSmall (small_named (by decide) : Small four)
        step_nonneg (by rw [four_value]; linarith)
      have bound : numerical32 (stepWord.mul four) = numerical32 ⟨0x3951b71c⟩ := by
        rw [show stepWord.mul four = ⟨0x3951b71c⟩ by decide]
      have ceiling : numerical32 (⟨0x3951b71c⟩ : Binary32) ≤ 4 := by
        rw [← four_value]; exact num_le (by decide) (by decide) (by decide)
      linarith
  have sum := add_small zs incSmall
  refine ⟨sum.1, ?_, ?_⟩
  · have scaled : numerical32 (stepWord.mul zBar) ≤ numerical32 zBar :=
      (mul_small small_step zs).2.mono (exact_word finite) (by nlinarith [step_le_one])
    have negated : numerical32 (stepWord.mul (Binary32.zero.sub zBar)) =
        -numerical32 (stepWord.mul zBar) := by
      have zeroSubSmall : Small (Binary32.zero.sub zBar) :=
        ⟨(sub_small small_zero zs).1, by rw [negative, abs_neg]; exact zs.2⟩
      exact rounded_unique (mul_small small_step zeroSubSmall).2
        (by rw [negative, mul_neg]; exact Rounded.neg (mul_small small_step zs).2)
    have lower : numerical32 (stepWord.mul (Binary32.zero.sub zBar)) ≤
        numerical32 (stepWord.mul (complement.sub zBar)) := by
      have zeroSubSmall : Small (Binary32.zero.sub zBar) :=
        ⟨(sub_small small_zero zs).1, by rw [negative, abs_neg]; exact zs.2⟩
      exact mul_mono_right small_step zeroSubSmall diffSmall step_nonneg
        (by rw [negative]; exact diffLow)
    exact rounded_nonneg sum.2 (by linarith)
  · have incUpper := mul_mono_right small_step diffSmall oneSubSmall step_nonneg diffHigh
    rcases le_total (numerical32 zBar) (numerical32 nearOne) with low | high
    · have further := mul_mono_right small_step oneSubSmall small_one step_nonneg
        (by rw [one_value]; exact oneSubHigh)
      have total := add_mono zs incSmall (small_named (by decide) : Small nearOne)
        (small_named (by decide) : Small (stepWord.mul Binary32.one)) low
        (le_trans incUpper further)
      have closed : numerical32 (nearOne.add (stepWord.mul Binary32.one)) ≤ 1 := by
        rw [← one_value]; exact num_le (by decide +kernel) (by decide) (by decide +kernel)
      linarith
    · have nearSmall : Small (Binary32.one.sub nearOne) := small_named (by decide +kernel)
      have shrink : numerical32 (Binary32.one.sub zBar) ≤ numerical32 (Binary32.one.sub nearOne) :=
        sub_mono small_one zs small_one (small_named (by decide)) le_rfl high
      have further := mul_mono_right small_step oneSubSmall nearSmall step_nonneg shrink
      have total := add_mono zs incSmall small_one
        (small_named (by decide +kernel) : Small (stepWord.mul (Binary32.one.sub nearOne)))
        (by rw [one_value]; exact z1) (le_trans incUpper further)
      have closed :
          numerical32 (Binary32.one.add (stepWord.mul (Binary32.one.sub nearOne))) ≤ 1 := by
        rw [← one_value]; exact num_le (by decide +kernel) (by decide) (by decide +kernel)
      linarith

end Laying

section Quiet

open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds
open AcornVerif.CurrentLearner AcornVerif.CurrentPreReward
open SwiftTd (ActiveSet)

variable {criterion : Criterion} {dimension : Dimension}

/-! ## One slot of a primitive learner while the rewards are zero -/

/-- The words of one primitive slot on a reward-free run: a zero weight, the initial log step size,
zero update and meta-gradient registers, a finite trace increment, a Dutch trace in `[0, 1]`, a
trace between zero and the trace bound, and the stored step size as the pruning reference of every
nonzero trace. -/
structure SlotQuiet (criterion : Criterion) (words : Slot) : Prop where
  /-- The weight is a zero word. -/
  weight : words.weight.isZero = true
  /-- The log step size is the initial one. -/
  beta : words.beta = logStepWord
  /-- The per-weight update register is a zero word. -/
  deltaWeight : words.deltaWeight.isZero = true
  /-- The auxiliary register is a zero word. -/
  h : words.h.isZero = true
  /-- The previous auxiliary register is a zero word. -/
  hOld : words.hOld.isZero = true
  /-- The accumulating auxiliary register is a zero word. -/
  hTemp : words.hTemp.isZero = true
  /-- The meta-trace register is a zero word. -/
  p : words.p.isZero = true
  /-- The trace increment is finite. -/
  zDelta : words.zDelta.Finite
  /-- The Dutch trace is finite. -/
  zBarFinite : words.zBar.Finite
  /-- The Dutch trace is nonnegative. -/
  zBarLow : 0 ≤ numerical32 words.zBar
  /-- The Dutch trace is at most one. -/
  zBarHigh : numerical32 words.zBar ≤ 1
  /-- The trace is finite. -/
  zFinite : words.z.Finite
  /-- The trace is nonnegative. -/
  zLow : 0 ≤ numerical32 words.z
  /-- The trace is at most the trace bound. -/
  zHigh : numerical32 words.z ≤ numerical32 (traceBound criterion)
  /-- A nonzero trace was laid at the stored step size. -/
  reference : words.z.isZero = false → words.lastAlpha = stepWord
  /-- The pruning reference is positive zero or the stored step size. -/
  referenceLegal : words.lastAlpha = .zero ∨ words.lastAlpha = stepWord


/-- A slot whose nine registers are positive zero, with a zero weight and the initial log step
size, is quiet. -/
theorem slotQuiet_cleared {words : Slot} (weight : words.weight.isZero = true)
    (beta : words.beta = logStepWord) (cleared : words.regs = Vector.replicate 9 .zero) :
    SlotQuiet criterion words := by
  obtain ⟨w, b, regs⟩ := words
  simp only at weight beta cleared
  subst cleared
  have zz : Binary32.zero.isZero = true := by decide
  have zf : Binary32.zero.Finite := by decide
  refine ⟨weight, beta, zz, zz, zz, zz, zz, zf, zf, ?_, ?_, zf, ?_, ?_, ?_, Or.inl rfl⟩
  · change 0 ≤ numerical32 Binary32.zero
    rw [zero_value]
  · change numerical32 Binary32.zero ≤ 1
    rw [zero_value]; norm_num
  · change 0 ≤ numerical32 Binary32.zero
    rw [zero_value]
  · change numerical32 Binary32.zero ≤ _
    rw [zero_value]; exact bound_nonneg criterion
  · intro nonzero
    exact absurd nonzero (by change ¬Binary32.zero.isZero = false; decide)

/-- The trace bound decayed `j` times is small, nonnegative and at most the trace bound. -/
theorem chain_facts (criterion : Criterion) (j : Nat) :
    Small (chain criterion j) ∧ 0 ≤ numerical32 (chain criterion j) ∧
      numerical32 (chain criterion j) ≤ numerical32 (traceBound criterion) := by
  induction j with
  | zero => exact ⟨small_bound criterion, bound_nonneg criterion, le_rfl⟩
  | succ j ih =>
    have product := mul_small ih.1 (small_decay criterion)
    have lower := mul_nonneg' ih.1 (small_decay criterion) ih.2.1 (decay_nonneg criterion)
    have upper := mul_le_self ih.1 (small_decay criterion) ih.2.1 (decay_le_one criterion)
    exact ⟨small_between product.1 small_zero ih.1 (by rw [zero_value]; exact lower) upper,
      lower, le_trans upper ih.2.2⟩

/-- The log step size the first loop writes on a reward-free visit is the stored one. -/
theorem quiet_beta (rails : StepSizeRails (criterion.config .control))
    (sameRails : rails = StepSizeRails.ofConfig (criterion.config .control))
    {zero : Binary32} (hz : zero.isZero = true) :
    (LogStepSize.project rails (logStepWord.add zero)).value = logStepWord := by
  rw [logStep_add_zero hz, sameRails]
  change (StepSizeRails.ofConfig (criterion.config .control)).range.saturate logStepWord = _
  have legal := (StepSizeRails.ofConfig (criterion.config .control)).initial.legal
  rw [rails_initial_value] at legal
  exact Interval32.saturate_identity _ _ legal

/-- **A first-loop visit on a reward-free run.** At zero error and accumulator words, a visit
keeps a quiet slot quiet: it writes a zero weight and the stored log step size, decays the trace
and the Dutch trace, and keeps the pruning reference. -/
theorem quiet_first (current : NumericState (criterion.config .control) dimension)
    (idx : FeatIdx dimension)
    (sameRails : current.rails = StepSizeRails.ofConfig (criterion.config .control))
    {delta vDelta : Binary32} (hd : delta.isZero = true) (hv : vDelta.isZero = true)
    (quiet : SlotQuiet criterion (slotOf current idx)) :
    let result := current.firstLoopElement idx delta vDelta (decayOf criterion)
    (slotOf result.1 idx).weight.isZero = true ∧ (slotOf result.1 idx).beta = logStepWord ∧
      (slotOf result.1 idx).z = (slotOf current idx).z.mul (decayOf criterion) ∧
      (slotOf result.1 idx).zDelta = .zero ∧
      (slotOf result.1 idx).zBar = (slotOf current idx).zBar.mul (decayOf criterion) ∧
      (slotOf result.1 idx).lastAlpha = (slotOf current idx).lastAlpha ∧
      (slotOf result.1 idx).deltaWeight.isZero = true ∧ (slotOf result.1 idx).h.isZero = true ∧
      (slotOf result.1 idx).hOld.isZero = true ∧ (slotOf result.1 idx).hTemp.isZero = true ∧
      (slotOf result.1 idx).p.isZero = true ∧
      result.2 = ((slotOf current idx).z.mul (decayOf criterion)).lessOrEqual
        ((slotOf current idx).lastAlpha.mul (criterion.config .control).epsilon) := by
  obtain ⟨weight, beta, deltaWeight, h, hOld, hTemp, p, zDelta, zBarFinite, _, _, zFinite, _, _,
    _⟩ := quiet
  simp only [slotOf_weight, slotOf_beta, slotOf_z, slotOf_zDelta, slotOf_zBar, slotOf_lastAlpha,
    slotOf_deltaWeight, slotOf_h, slotOf_hOld, slotOf_hTemp, slotOf_p] at *
  have hdw : ((delta.mul (current.transient.z.get idx).value).sub
      ((current.transient.zDelta.get idx).value.mul vDelta)).isZero = true :=
    zeroWord_sub (zeroWord_mul_finite hd zFinite) (finite_mul_zero zDelta hv)
  have hraw := zeroWord_add weight hdw
  have hproj := Inert32.project (Inert32.ofZero hraw) (criterion.config .control).rule
  have heq := zeros_equal hproj hraw
  have alpha : current.stepSize idx = stepWord := by
    rw [NumericState.stepSize_eq]
    exact logStep_alpha _ beta
  simp only [NumericState.firstLoopElement, get_set_vec, ite_true, heq, Bool.not_true,
    Bool.false_eq_true, ite_false, alpha, beta]
  have metaFinite : ((criterion.config .control).metaStep.div stepWord).Finite := by
    cases criterion <;> decide +kernel
  have adapted :=
    zeroWord_mul_finite (finite_mul_zero metaFinite (zeroWord_sub hd hv)) (zero_finite p)
  exact ⟨hproj, quiet_beta current.rails sameRails adapted, trivial, trivial, trivial, trivial, hdw,
    hTemp, h, zeroWord_sub (zeroWord_add hTemp (zeroWord_mul_finite hd zBarFinite))
      (finite_mul_zero zDelta hv), zeroWord_mul_finite p (decay_words criterion).1, trivial⟩

/-- **A second-loop visit without overshoot.** At the stored log step size the trace scale is one,
so the visit lays the stored step size times the trace complement. -/
theorem quiet_second (current : NumericState (criterion.config .control) dimension)
    (idx : FeatIdx dimension) (total vd : Binary32)
    (beta : (slotOf current idx).beta = logStepWord) :
    let result := NumericState.secondLoopElement (criterion.config .control) false
      (criterion.config .control).eta total current vd idx
    let words := slotOf current idx
    let complement := Binary32.one.sub total
    let z := words.z.add (stepWord.mul complement)
    slotOf result.1 idx = ⟨words.weight, words.beta, #v[z, stepWord,
      words.zBar.add (stepWord.mul (complement.sub words.zBar)), stepWord, words.deltaWeight,
      words.h, words.hOld,
      (words.hTemp.sub (words.hOld.mul (z.sub stepWord))).sub (words.h.mul stepWord),
      words.p.add words.h]⟩ ∧
    result.2 = vd.add words.deltaWeight := by
  rw [slotOf_beta] at beta
  have alpha := logStep_alpha _ beta
  have scale := scale_one criterion
  simp only [NumericState.secondLoopElement, NumericState.secondLoopElementAt, alpha, scale,
    slotOf, registers, get_set_vec, ite_true, Bool.false_eq_true, ite_false]
  exact ⟨rfl, rfl⟩

/-- No step among the last `j` of a history laid the slot in the row. -/
def notLaid {actions : Nat} (history : List (Laid dimension actions)) (row : Action actions)
    (slot : FeatIdx dimension) (j : Nat) : Prop :=
  ∀ step ∈ history.drop (history.length - j), ¬step.Lays row slot

/-- One more step of history shifts the count by one. -/
theorem notLaid_snoc {actions : Nat} (history : List (Laid dimension actions))
    (step : Laid dimension actions) (row : Action actions) (slot : FeatIdx dimension) (j : Nat) :
    notLaid (history ++ [step]) row slot (j + 1) ↔
      ¬step.Lays row slot ∧ notLaid history row slot j := by
  unfold notLaid
  rw [List.length_append, List.length_singleton,
    show history.length + 1 - (j + 1) = history.length - j by omega,
    List.drop_append_of_le_length (by omega)]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · intro all
    exact ⟨all step (Or.inr rfl), fun other member => all other (Or.inl member)⟩
  · rintro ⟨last, earlier⟩ other (member | rfl)
    · exact earlier other member
    · exact last

/-- The words of a slot that a reward-free first loop kept eligible. -/
structure Kept {actions : Nat} (criterion : Criterion) (history : List (Laid dimension actions))
    (row : Action actions) (slot : FeatIdx dimension) (words : Slot) : Prop where
  /-- The slot is quiet. -/
  quiet : SlotQuiet criterion words
  /-- The trace is at most the decayed trace bound. -/
  decayed : numerical32 words.z ≤ numerical32 (decayedBound criterion)
  /-- An unlaid gap of `j` steps before this one bounds the trace by `j + 1` decays, and that
  bound is above the pruning threshold. -/
  trace : ∀ j, notLaid history row slot j →
    numerical32 words.z ≤ numerical32 (chain criterion (j + 1)) ∧
      pruneWord.key < (chain criterion (j + 1)).key

/-- The words of a slot that is not eligible after a reward-free first loop. -/
structure Cleared (criterion : Criterion) (words : Slot) : Prop where
  /-- The slot is quiet. -/
  quiet : SlotQuiet criterion words
  /-- The trace is positive zero. -/
  zero : words.z = .zero

/-- **A reward-free first-loop visit.** An eligible quiet slot whose trace lies under the decayed
bounds of its history is either pruned and cleared, or kept under the bounds one step further. -/
theorem quiet_visit {actions : Nat} (history : List (Laid dimension actions)) (row : Action actions)
    {delta vDelta : Binary32} (hd : delta.isZero = true) (hv : vDelta.isZero = true)
    (current : NumericState (criterion.config .control) dimension) (idx : FeatIdx dimension)
    (sameRails : current.rails = StepSizeRails.ofConfig (criterion.config .control))
    (pre : SlotQuiet criterion (slotOf current idx) ∧ ∀ j, notLaid history row idx j →
      numerical32 (slotOf current idx).z ≤ numerical32 (chain criterion j) ∧
        pruneWord.key < (chain criterion j).key) :
    ((current.firstLoopElement idx delta vDelta (decayOf criterion)).2 = true →
      Cleared criterion (slotOf ((current.firstLoopElement idx delta vDelta
        (decayOf criterion)).1.clearFeatureRegisters idx) idx)) ∧
    ((current.firstLoopElement idx delta vDelta (decayOf criterion)).2 = false →
      Kept criterion history row idx (slotOf (current.firstLoopElement idx delta vDelta
        (decayOf criterion)).1 idx)) := by
  obtain ⟨quiet, bounds⟩ := pre
  obtain ⟨weight, beta, z, zDelta, zBar, lastAlpha, deltaWeight, h, hOld, hTemp, p, prune⟩ :=
    quiet_first current idx sameRails hd hv quiet
  constructor
  · intro _
    have knowledge := clear_feature_knowledge
      (current.firstLoopElement idx delta vDelta (decayOf criterion)).1 idx idx
    have registers := clear_feature_self
      (current.firstLoopElement idx delta vDelta (decayOf criterion)).1 idx
    refine ⟨slotQuiet_cleared ?_ ?_ registers, ?_⟩
    · change ((_ : NumericState _ _).weights.get idx).value.isZero = true
      rw [knowledge.1]; exact weight
    · change ((_ : NumericState _ _).beta.get idx).value = _
      rw [knowledge.2]; exact beta
    · exact congrArg (fun words : Vector Binary32 9 => words[0]) registers
  · intro kept
    rw [prune] at kept
    have zSmall : Small (slotOf current idx).z :=
      small_between quiet.zFinite small_zero (small_bound criterion)
        (by rw [zero_value]; exact quiet.zLow) quiet.zHigh
    have zBarSmall : Small (slotOf current idx).zBar :=
      small_between quiet.zBarFinite small_zero small_one
        (by rw [zero_value]; exact quiet.zBarLow) (by rw [one_value]; exact quiet.zBarHigh)
    have decayed := mul_small zSmall (small_decay criterion)
    have decayedLow :=
      mul_nonneg' zSmall (small_decay criterion) quiet.zLow (decay_nonneg criterion)
    have decayedHigh := mul_le_self zSmall (small_decay criterion) quiet.zLow
      (decay_le_one criterion)
    have dutch := mul_small zBarSmall (small_decay criterion)
    have dutchLow := mul_nonneg' zBarSmall (small_decay criterion) quiet.zBarLow
      (decay_nonneg criterion)
    have dutchHigh := mul_le_self zBarSmall (small_decay criterion) quiet.zBarLow
      (decay_le_one criterion)
    have nonzero : ((slotOf current idx).z.mul (decayOf criterion)).isZero = false := by
      apply Bool.eq_false_iff.mpr
      intro zero
      rcases quiet.referenceLegal with reference | reference
      · rw [reference] at kept
        rw [AcornVerif.CurrentLearner.zero_pruned _ _ zero (by cases criterion <;> decide)
          (by cases criterion <;> decide)] at kept
        cases kept
      · rw [reference, prune_eq] at kept
        rw [AcornVerif.CurrentLearner.zero_pruned _ _ zero (by decide) (by decide)] at kept
        cases kept
    have unpruned : (slotOf current idx).lastAlpha = stepWord := by
      apply quiet.reference
      apply Bool.eq_false_iff.mpr
      intro zero
      rw [zeroWord_mul_finite zero (decay_words criterion).1] at nonzero
      cases nonzero
    rw [unpruned, prune_eq, AcornVerif.CurrentLearner.finite_lessOrEqual _ _ decayed.1
      (by decide)] at kept
    have above : numerical32 pruneWord < numerical32 ((slotOf current idx).z.mul
        (decayOf criterion)) := lt_of_not_ge (fun below => by simp [below] at kept)
    refine ⟨⟨weight, beta, deltaWeight, h, hOld, hTemp, p, by rw [zDelta]; decide,
      by rw [zBar]; exact dutch.1, by rw [zBar]; exact dutchLow,
      by rw [zBar]; exact le_trans dutchHigh quiet.zBarHigh, by rw [z]; exact decayed.1,
      by rw [z]; exact decayedLow, by rw [z]; exact le_trans decayedHigh quiet.zHigh,
      fun _ => by rw [lastAlpha]; exact unpruned, by rw [lastAlpha]; exact Or.inr unpruned⟩,
      ?_, ?_⟩
    · rw [z]
      exact mul_mono zSmall (small_decay criterion) (small_bound criterion) (small_decay criterion)
        quiet.zLow (decay_nonneg criterion) quiet.zHigh le_rfl
    · intro j unlaid
      have bound := bounds j unlaid
      have chainFacts := chain_facts criterion j
      have next : numerical32 ((slotOf current idx).z.mul (decayOf criterion)) ≤
          numerical32 (chain criterion (j + 1)) :=
        mul_mono zSmall (small_decay criterion) chainFacts.1 (small_decay criterion) quiet.zLow
          (decay_nonneg criterion) bound.1 le_rfl
      rw [z]
      refine ⟨next, ?_⟩
      have finiteNext := (chain_facts criterion (j + 1)).1.1
      exact (numerical32_strict_order _ _ (by decide) finiteNext).mp (lt_of_lt_of_le above next)

/-- One primitive row on a reward-free run, against the history of what the controller laid:
every slot is quiet, and a slot the row has not laid on the last `j` steps has a trace under the
trace bound decayed `j` times, and is not eligible once that bound is at most the pruning
threshold. -/
structure RowQuiet {actions : Nat} (criterion : Criterion)
    (state : NumericState (criterion.config .control) dimension)
    (history : List (Laid dimension actions)) (row : Action actions) : Prop where
  /-- The rails are the configuration's. -/
  rails : state.rails = StepSizeRails.ofConfig (criterion.config .control)
  /-- Every slot is quiet. -/
  slots : ∀ slot, SlotQuiet criterion (slotOf state slot)
  /-- An unlaid gap of `j` steps bounds the trace by `j` decays and prunes the slot once that
  bound is at most the threshold. -/
  trace : ∀ slot j, notLaid history row slot j →
    numerical32 (slotOf state slot).z ≤ numerical32 (chain criterion j) ∧
      ((chain criterion j).key ≤ pruneWord.key → slot ∉ state.transient.eligible)

/-- **A reward-free first loop on a quiet row.** Every slot left eligible is kept under the bounds
one step further, and every other slot is cleared. -/
theorem quiet_first_loop {actions : Nat}
    (state : NumericState (criterion.config .control) dimension)
    (history : List (Laid dimension actions)) (row : Action actions)
    (quiet : RowQuiet criterion state history row)
    (unique : state.transient.eligible.toList.Nodup)
    (supported : Supported state state.transient.eligible)
    {delta vDelta : Binary32} (hd : delta.isZero = true) (hv : vDelta.isZero = true) :
    let next := state.learnFirstLoop (criterion.config .control) delta vDelta (decayOf criterion)
    next.rails = StepSizeRails.ofConfig (criterion.config .control) ∧
      (∀ slot ∈ next.transient.eligible, Kept criterion history row slot (slotOf next slot)) ∧
      (∀ slot, slot ∉ next.transient.eligible → Cleared criterion (slotOf next slot)) := by
  have result := first_loop_slots
    (fun slot words => SlotQuiet criterion words ∧ ∀ j, notLaid history row slot j →
      numerical32 words.z ≤ numerical32 (chain criterion j) ∧
        pruneWord.key < (chain criterion j).key)
    (Kept criterion history row) (fun _ words => Cleared criterion words)
    delta vDelta (decayOf criterion) (StepSizeRails.ofConfig (criterion.config .control))
    (fun current idx sameRails pre => quiet_visit history row hd hv current idx sameRails pre)
    state quiet.rails unique
    (fun slot member => ⟨quiet.slots slot, fun j unlaid =>
      ⟨(quiet.trace slot j unlaid).1, lt_of_not_ge fun below =>
        (quiet.trace slot j unlaid).2 below member⟩⟩)
    (fun slot absent => ⟨quiet.slots slot, registers_zero_trace state slot (supported slot absent)⟩)
  exact ⟨result.1, result.2.2.1, result.2.2.2⟩

/-- After a reward-free first loop on a quiet row every slot is quiet with its trace under the
decayed bound: a kept slot by `Kept`, every other slot by its zero trace. -/
theorem quiet_first_entry {actions : Nat}
    (state : NumericState (criterion.config .control) dimension)
    (history : List (Laid dimension actions)) (row : Action actions)
    (quiet : RowQuiet criterion state history row)
    (unique : state.transient.eligible.toList.Nodup)
    (supported : Supported state state.transient.eligible)
    {delta vDelta : Binary32} (hd : delta.isZero = true) (hv : vDelta.isZero = true)
    (slot : FeatIdx dimension) :
    SlotQuiet criterion (slotOf (state.learnFirstLoop (criterion.config .control) delta vDelta
      (decayOf criterion)) slot) ∧
    numerical32 (slotOf (state.learnFirstLoop (criterion.config .control) delta vDelta
      (decayOf criterion)) slot).z ≤ numerical32 (decayedBound criterion) := by
  have first := quiet_first_loop state history row quiet unique supported hd hv
  by_cases member : slot ∈ (state.learnFirstLoop (criterion.config .control) delta vDelta
      (decayOf criterion)).transient.eligible
  · exact ⟨(first.2.1 slot member).quiet, (first.2.1 slot member).decayed⟩
  · have out := first.2.2 slot member
    refine ⟨out.quiet, ?_⟩
    rw [out.zero, zero_value]
    exact (chain_facts criterion 1).2.1

/-- The ordered sum of 1999 copies of the trace bound. -/
def totalBound : Criterion → Binary32
  | .discounted => ⟨0x3f6abee9⟩
  | .differential => ⟨0x3f7fe074⟩

/-- Every ordered sum of at most 1999 stored step sizes is at most the step-size budget. -/
theorem rate_check (criterion : Criterion) :
    partialSums stepWord (criterion.config .control).eta .zero 1999 = true := by
  cases criterion <;> decide +kernel

/-- Every ordered sum of at most 1999 trace bounds is at most `totalBound`. -/
theorem total_check (criterion : Criterion) :
    partialSums (traceBound criterion) (totalBound criterion) .zero 1999 = true := by
  cases criterion <;> decide +kernel

/-- The ordered sum of 1900 trace bounds. -/
def partialBound : Criterion → Binary32
  | .discounted => ⟨0x3f5f1eb9⟩
  | .differential => ⟨0x3f733445⟩

/-- Every ordered sum of at most 1900 trace bounds is at most `partialBound`. -/
theorem partial_check (criterion : Criterion) :
    partialSums (traceBound criterion) (partialBound criterion) .zero 1900 = true := by
  cases criterion <;> decide +kernel

/-- **The words a reward-free second loop reads at entry.** On a frame of at most 1999 quiet slots
whose traces are under the decayed bound, the step-size total is at most the budget, so no
overshoot branch is taken, and the trace complement is a small word in `[0, 1]`, at least the
complement of 1900 trace bounds on a frame of at most 1900 slots. -/
theorem quiet_entry (state : NumericState (criterion.config .control) dimension)
    (features : ActiveSet dimension) (fits : features.indices.length ≤ 1999)
    (slots : ∀ slot, SlotQuiet criterion (slotOf state slot) ∧
      numerical32 (slotOf state slot).z ≤ numerical32 (decayedBound criterion)) :
    (criterion.config .control).eta.less (Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.beta.get idx).alpha)) = false ∧
    Small (Binary32.one.sub (Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.transient.z.get idx).value))) ∧
    0 ≤ numerical32 (Binary32.one.sub (Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.transient.z.get idx).value))) ∧
    numerical32 (Binary32.one.sub (Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.transient.z.get idx).value))) ≤ 1 ∧
    (features.indices.length ≤ 1900 →
      numerical32 (Binary32.one.sub (partialBound criterion)) ≤
        numerical32 (Binary32.one.sub (Binary32.sumFrom .zero
          (features.indices.map fun idx => (state.transient.z.get idx).value)))) := by
  have rate : Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.beta.get idx).alpha) =
      repeatSum stepWord features.indices.length := by
    unfold repeatSum
    congr 1
    rw [List.map_congr_left (fun idx _ => logStep_alpha _ (slots idx).1.beta), List.map_const']
  have rateBound := repeatSum_bound stepWord (criterion.config .control).eta 1999
    (rate_check criterion) (by cases criterion <;> decide) features.indices.length fits
  have noOvershoot : (criterion.config .control).eta.less (Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.beta.get idx).alpha)) = false := by
    rw [rate, Binary32.less_eq_key]
    have : ¬(criterion.config .control).eta.key < (repeatSum stepWord
        features.indices.length).key := by omega
    simp [this]
  have zSmall : ∀ slot, Small (slotOf state slot).z := fun slot =>
    small_between (slots slot).1.zFinite small_zero (small_bound criterion)
      (by rw [zero_value]; exact (slots slot).1.zLow) (slots slot).1.zHigh
  have partials := repeatSum_bound (traceBound criterion) (totalBound criterion) 1999
    (total_check criterion) (by cases criterion <;> decide)
  have totalSmall : ∀ k ≤ 1999, Small (repeatSum (traceBound criterion) k) := fun k bound =>
    small_of_key (partials k bound).1 (le_trans (by decide) (partials k bound).2.1)
      (le_trans (partials k bound).2.2 (by cases criterion <;> decide))
  have totalTerms := sumFrom_le_repeat (traceBound criterion) (small_bound criterion)
    (features.indices.map fun idx => (state.transient.z.get idx).value) .zero 0
    (fun k bound => totalSmall k (by simp only [List.length_map] at bound; omega)) small_zero
    (le_of_eq zero_value.symm)
    (le_of_eq (by rw [repeatSum_zero]))
    (fun term member => by
      obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
      exact ⟨zSmall slot, (slots slot).1.zLow, (slots slot).1.zHigh⟩)
  simp only [List.length_map, Nat.zero_add] at totalTerms
  have totalHigh : numerical32 (repeatSum (traceBound criterion) features.indices.length) ≤
      numerical32 (totalBound criterion) :=
    num_le (partials _ fits).1 (by cases criterion <;> decide) (partials _ fits).2.2
  have totalSmallBound : Small (totalBound criterion) := small_named (by cases criterion <;> decide)
  have complement := sub_small small_one totalTerms.1
  have complementHigh : numerical32 (Binary32.one.sub (Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.transient.z.get idx).value))) ≤ 1 := by
    have := sub_mono small_one totalTerms.1 small_one small_zero le_rfl
      (by rw [zero_value]; exact totalTerms.2.1)
    rwa [show Binary32.one.sub Binary32.zero = Binary32.one by decide, one_value] at this
  have complementLow : 0 ≤ numerical32 (Binary32.one.sub (Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.transient.z.get idx).value))) := by
    have below := sub_mono small_one totalSmallBound small_one totalTerms.1 le_rfl
      (le_trans totalTerms.2.2 totalHigh)
    have floor : 0 ≤ numerical32 (Binary32.one.sub (totalBound criterion)) := by
      rw [← zero_value]
      exact num_le (by decide) (by cases criterion <;> decide +kernel)
        (by cases criterion <;> decide +kernel)
    linarith
  have complementSmall : Small (Binary32.one.sub (Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.transient.z.get idx).value))) :=
    ⟨complement.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  refine ⟨noOvershoot, complementSmall, complementLow, complementHigh, fun short => ?_⟩
  have shortPartials := repeatSum_bound (traceBound criterion) (partialBound criterion) 1900
    (partial_check criterion) (by cases criterion <;> decide)
  have shortHigh : numerical32 (repeatSum (traceBound criterion) features.indices.length) ≤
      numerical32 (partialBound criterion) :=
    num_le (shortPartials _ short).1 (by cases criterion <;> decide)
      (shortPartials _ short).2.2
  exact sub_mono small_one (small_named (by cases criterion <;> decide)) small_one totalTerms.1
    le_rfl (le_trans totalTerms.2.2 shortHigh)

/-- **A reward-free second loop on a frame of at most 1999 slots.** From quiet slots whose traces
are under the decayed bound, the second loop takes no overshoot branch, keeps every active slot
quiet with its trace under the trace bound, leaves every other slot's words, and returns a zero
accumulator. -/
theorem quiet_second_loop (state : NumericState (criterion.config .control) dimension)
    (features : ActiveSet dimension) (fits : features.indices.length ≤ 1999)
    (sameRails : state.rails = StepSizeRails.ofConfig (criterion.config .control))
    (slots : ∀ slot, SlotQuiet criterion (slotOf state slot) ∧
      numerical32 (slotOf state slot).z ≤ numerical32 (decayedBound criterion)) :
    let final := state.learnSecondLoop (criterion.config .control) features .zero
    final.1.rails = StepSizeRails.ofConfig (criterion.config .control) ∧
      final.2.isZero = true ∧
      (∀ slot ∈ features.indices, SlotQuiet criterion (slotOf final.1 slot)) ∧
      (∀ slot, slot ∉ features.indices → slotOf final.1 slot = slotOf state slot) := by
  obtain ⟨noOvershoot, complementSmall, complementLow, complementHigh, _⟩ :=
    quiet_entry state features fits slots
  refine second_loop_slots (fun _ words => SlotQuiet criterion words ∧
      numerical32 words.z ≤ numerical32 (decayedBound criterion))
    (fun _ words => SlotQuiet criterion words) (fun word => word.isZero = true)
    (StepSizeRails.ofConfig (criterion.config .control)) state features .zero ?_ sameRails
    (by decide) (fun slot _ => slots slot)
  intro current vd idx _ acc pre
  simp only [noOvershoot, Bool.false_eq_true, ite_false]
  obtain ⟨words, accumulator⟩ := quiet_second current idx _ vd pre.1.beta
  rw [words, accumulator]
  obtain ⟨quiet, decayed⟩ := pre
  have zs : Small (slotOf current idx).z :=
    small_between quiet.zFinite small_zero (small_bound criterion)
      (by rw [zero_value]; exact quiet.zLow) quiet.zHigh
  have trace := laid_trace criterion zs quiet.zLow decayed complementSmall complementLow
    complementHigh
  have dutch := laid_dutch quiet.zBarFinite quiet.zBarLow quiet.zBarHigh complementSmall
    complementLow complementHigh
  have laidSmall : Small ((slotOf current idx).z.add (stepWord.mul (Binary32.one.sub
      (Binary32.sumFrom .zero
        (features.indices.map fun idx => (state.transient.z.get idx).value))))) :=
    small_between trace.1 small_zero (small_bound criterion)
      (by rw [zero_value]; exact le_trans trace.2.1 trace.2.2.1) trace.2.2.2
  have difference := (sub_small laidSmall small_step).1
  refine ⟨⟨quiet.weight, quiet.beta, quiet.deltaWeight, quiet.h, quiet.hOld, ?_, ?_,
    (by decide : stepWord.Finite), dutch.1, dutch.2.1, dutch.2.2, trace.1,
    le_trans trace.2.1 trace.2.2.1, trace.2.2.2, fun _ => rfl, Or.inr rfl⟩,
    zeroWord_add acc quiet.deltaWeight⟩
  · exact zeroWord_sub (zeroWord_sub quiet.hTemp (zeroWord_mul_finite quiet.hOld difference))
      (zeroWord_mul_finite quiet.h (by decide))
  · exact zeroWord_add quiet.p quiet.h

/-- **One more step of history.** After a reward-free first loop, a row whose laid slots are quiet
and whose other slots keep their words and their eligibility is quiet against the longer history. -/
theorem rowQuiet_after {actions : Nat}
    (first final : NumericState (criterion.config .control) dimension)
    (history : List (Laid dimension actions)) (row : Action actions) (step : Laid dimension actions)
    (sameRails : final.rails = StepSizeRails.ofConfig (criterion.config .control))
    (kept : ∀ slot ∈ first.transient.eligible, Kept criterion history row slot (slotOf first slot))
    (cleared : ∀ slot, slot ∉ first.transient.eligible → Cleared criterion (slotOf first slot))
    (laid : ∀ slot, step.Lays row slot → SlotQuiet criterion (slotOf final slot))
    (frame : ∀ slot, ¬step.Lays row slot → slotOf final slot = slotOf first slot ∧
      (slot ∈ final.transient.eligible ↔ slot ∈ first.transient.eligible)) :
    RowQuiet criterion final (history ++ [step]) row := by
  have firstQuiet : ∀ slot, SlotQuiet criterion (slotOf first slot) := fun slot =>
    if member : slot ∈ first.transient.eligible then (kept slot member).quiet
    else (cleared slot member).quiet
  refine ⟨sameRails, fun slot => ?_, fun slot j unlaid => ?_⟩
  · by_cases lays : step.Lays row slot
    · exact laid slot lays
    · rw [(frame slot lays).1]
      exact firstQuiet slot
  · cases j with
    | zero =>
      have quiet : SlotQuiet criterion (slotOf final slot) := by
        by_cases lays : step.Lays row slot
        · exact laid slot lays
        · rw [(frame slot lays).1]
          exact firstQuiet slot
      refine ⟨quiet.zHigh, fun below => absurd below ?_⟩
      have := prune_below criterion
      change ¬(traceBound criterion).key ≤ pruneWord.key
      omega
    | succ j =>
      obtain ⟨lays, earlier⟩ := (notLaid_snoc history step row slot j).mp unlaid
      obtain ⟨same, member⟩ := frame slot lays
      rw [same]
      by_cases eligible : slot ∈ first.transient.eligible
      · have bound := (kept slot eligible).trace j earlier
        refine ⟨bound.1, fun below => absurd below ?_⟩
        omega
      · have zero := (cleared slot eligible).zero
        refine ⟨?_, fun _ => fun inside => eligible (member.mp inside)⟩
        rw [zero, zero_value]
        exact (chain_facts criterion (j + 1)).2.1

end Quiet

section QuietController

open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder
open AcornVerif.CurrentLearner AcornVerif.CurrentPreReward
open SwiftTd (ActiveSet)

variable {criterion : Criterion} {dimension : Dimension} {actions : Nat}

/-! ## The primitive controller while the rewards are zero -/

/-- A primitive controller on a reward-free run, against the history of what it laid: zero shared
lags, no pending restart, and every row quiet. -/
structure CtrlQuiet (criterion : Criterion)
    (controller : Controller (criterion.config .control) dimension actions)
    (history : List (Laid dimension actions)) : Prop where
  /-- The shared previous prediction is a zero word. -/
  vOld : controller.vOld.isZero = true
  /-- The shared weight-change accumulator is a zero word. -/
  vDelta : controller.vDelta.isZero = true
  /-- No restart is pending. -/
  restart : controller.restartPending = false
  /-- Every row is quiet against the history. -/
  rows : ∀ row, RowQuiet criterion (controller.learners.get row).state history row

/-- The fresh controller is quiet against the empty history. -/
theorem ctrlQuiet_initial :
    CtrlQuiet criterion (Controller.initial (criterion.config .control) dimension actions) [] := by
  refine ⟨(by decide : Binary32.zero.isZero = true), (by decide : Binary32.zero.isZero = true), rfl,
    fun row => ?_⟩
  have state : (Controller.initial (criterion.config .control) dimension actions).learners.get row =
      Managed.initial (criterion.config .control) dimension := by
    change (Vector.ofFn fun _ => Managed.initial _ dimension).get row = _
    rw [vec_get, Vector.getElem_ofFn]
  rw [state, show (Managed.initial (criterion.config .control) dimension).state =
    NumericState.initial (criterion.config .control) dimension from rfl]
  have cleared : ∀ slot, registers (NumericState.initial (criterion.config .control) dimension)
      slot = Vector.replicate 9 .zero := fun slot => (initial_core).1 slot (by
        change slot ∉ (TransientState.zero dimension).eligible
        rw [TransientState.zero_def]; simp)
  have quiet : ∀ slot, SlotQuiet criterion
      (slotOf (NumericState.initial (criterion.config .control) dimension) slot) := by
    intro slot
    apply slotQuiet_cleared _ _ (cleared slot)
    · change ((Vector.replicate _ (Weight.project _ .zero)).get slot).value.isZero = true
      rw [get_replicate_vec, Weight.project_zero]
      decide
    · change ((Vector.replicate _ (StepSizeRails.ofConfig _).initial).get slot).value = _
      rw [get_replicate_vec, rails_initial_value]
  refine ⟨rfl, quiet, fun slot j _ => ⟨?_, fun _ inside => ?_⟩⟩
  · rw [slotOf_z, registers_zero_trace _ slot (cleared slot), zero_value]
    exact (chain_facts criterion j).2.1
  · change slot ∈ (TransientState.zero dimension).eligible at inside
    rw [TransientState.zero_def] at inside
    simp at inside

/-- Every row's prediction of a quiet controller is a zero word. -/
theorem ctrlQuiet_predict {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (row : Fin actions) : ((controller.predictAll features).get row).isZero = true := by
  rw [Controller.predictAll_def, get_map_vec, NumericState.linearPrediction_eq_sumFrom,
    Binary32.sumFrom_def]
  apply zeroWord_foldlAdd _ _ (by decide)
  intro value held
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp held
  exact ((quiet.rows row).slots slot).weight

/-- **A reward-free controller step on a frame of at most 1999 slots keeps the controller quiet
against the history extended by that step.** -/
theorem ctrlQuiet_step {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (action : Action actions) {reward : Binary32} (hr : reward.isZero = true)
    (fits : features.indices.length ≤ 1999) :
    CtrlQuiet criterion (controller.step features action reward).1
      (history ++ [⟨features, action⟩]) := by
  rw [step_eq]
  have lag := ctrlQuiet_predict quiet features action
  have gamma : (criterion.config .control).rule.gamma.Finite := by cases criterion <;> decide
  have delta := zeroWord_sub (zeroWord_add hr (finite_mul_zero gamma lag)) quiet.vOld
  generalize ((reward.add ((criterion.config .control).rule.gamma.mul
    ((controller.predictAll features).get action))).sub controller.vOld) = δ at delta ⊢
  generalize (controller.predictAll features).get action = lagWord at lag ⊢
  have decay : (criterion.config .control).rule.gamma.mul (criterion.config .control).lambda =
      decayOf criterion := rfl
  rw [decay]
  have credited : ∀ row, ((controller.learners.get row).credit δ controller.vDelta
      (decayOf criterion) controller.restartPending).val.state =
      (controller.learners.get row).state.learnFirstLoop (criterion.config .control) δ
        controller.vDelta (decayOf criterion) := fun row => by
    rw [credit_state, quiet.restart]
    rfl
  have first := fun row => quiet_first_loop (controller.learners.get row).state history row
    (quiet.rows row) (row_unique controller row) (row_supported controller row) delta quiet.vDelta
  have entry := quiet_first_entry (controller.learners.get action).state history action
    (quiet.rows action) (row_unique controller action) (row_supported controller action) delta
    quiet.vDelta
  have second := quiet_second_loop _ features fits (first action).1 entry
  obtain ⟨vOld, vDelta, restart⟩ := creditStep_lags controller features action lagWord δ
    (decayOf criterion)
  refine ⟨by rw [vOld]; exact lag, by rw [vDelta, credited]; exact second.2.1, restart,
    fun row => ?_⟩
  rw [creditStep_row, credited]
  split
  · rename_i taken
    subst taken
    refine rowQuiet_after _ _ history action ⟨features, action⟩ second.1 (first action).2.1
      (first action).2.2 (fun slot lays => second.2.2.1 slot lays.2) (fun slot lays => ?_)
    have unlisted : slot ∉ features.indices := fun member => lays ⟨rfl, member⟩
    refine ⟨second.2.2.2 slot unlisted, ?_⟩
    rw [← Array.mem_toList_iff, ← Array.mem_toList_iff, second_loop_eligible]
    simp only [List.mem_append, List.mem_filter, unlisted, false_and, or_false]
  · rename_i other
    exact rowQuiet_after _ _ history row ⟨features, action⟩ (first row).1 (first row).2.1
      (first row).2.2 (fun _ lays => absurd lays.1 other) (fun _ _ => ⟨rfl, Iff.rfl⟩)

/-- A retirement keeps every other slot's words. -/
theorem retire_other {cfg : Acorn.Config} (state : NumericState cfg dimension)
    (feature slot : FeatIdx dimension) (different : feature ≠ slot) :
    slotOf (state.retireIndex feature) slot = slotOf state slot := by
  have distinct : feature.val ≠ slot.val := fun equal => different (Fin.ext equal)
  rw [NumericState.retireIndex_def]
  split <;> simp [slotOf, registers, NumericState.removeEligibleAt,
    NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
    NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
    NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
    NumericState.writeLastAlpha, NumericState.writeWeight, NumericState.writeBetaValue,
    vector_get, Vector.getElem_set_ne _ _ distinct]

/-- A retirement keeps the rails. -/
theorem retire_rails {cfg : Acorn.Config} (state : NumericState cfg dimension)
    (feature : FeatIdx dimension) : (state.retireIndex feature).rails = state.rails := by
  rw [NumericState.retireIndex_def]
  split <;> simp [NumericState.removeEligibleAt,
    NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
    NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
    NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
    NumericState.writeLastAlpha, NumericState.writeWeight, NumericState.writeBetaValue]

/-- A retirement admits no slot into the eligible list. -/
theorem retire_eligible {cfg : Acorn.Config} (state : NumericState cfg dimension)
    (feature slot : FeatIdx dimension)
    (member : slot ∈ (state.retireIndex feature).transient.eligible) :
    slot ∈ state.transient.eligible := by
  rw [NumericState.retireIndex_def] at member
  split at member
  · exact swap_remove_subset _ _ _ _ member
  · exact member

/-- **A retirement keeps a quiet row quiet against the same history.** -/
theorem rowQuiet_retire (state : NumericState (criterion.config .control) dimension)
    (history : List (Laid dimension actions)) (row : Action actions)
    (quiet : RowQuiet criterion state history row) (feature : FeatIdx dimension) :
    RowQuiet criterion (state.retireIndex feature) history row := by
  have fresh := retire_registers state feature
  have retiredQuiet : SlotQuiet criterion (slotOf (state.retireIndex feature) feature) := by
    apply slotQuiet_cleared _ _ fresh.1
    · rw [slotOf_weight, fresh.2.1]; decide
    · rw [slotOf_beta, fresh.2.2.1, quiet.rails, rails_initial_value]
  refine ⟨(retire_rails state feature).trans quiet.rails, fun slot => ?_, fun slot j unlaid => ?_⟩
  · by_cases same : feature = slot
    · subst same; exact retiredQuiet
    · rw [retire_other state feature slot same]; exact quiet.slots slot
  · refine ⟨?_, fun below member => (quiet.trace slot j unlaid).2 below
      (retire_eligible state feature slot member)⟩
    by_cases same : feature = slot
    · subst same
      rw [slotOf_z, registers_zero_trace _ feature fresh.1, zero_value]
      exact (chain_facts criterion j).2.1
    · rw [retire_other state feature slot same]
      exact (quiet.trace slot j unlaid).1

/-- A retirement keeps a quiet controller quiet against the same history. -/
theorem ctrlQuiet_retire {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (feature : FeatIdx dimension) :
    CtrlQuiet criterion (controller.retire feature) history := by
  have lags : (controller.retire feature).vOld = controller.vOld ∧
      (controller.retire feature).vDelta = controller.vDelta ∧
      (controller.retire feature).restartPending = controller.restartPending := by
    cases controller
    exact ⟨rfl, rfl, rfl⟩
  refine ⟨lags.1 ▸ quiet.vOld, lags.2.1 ▸ quiet.vDelta, lags.2.2 ▸ quiet.restart, fun row => ?_⟩
  rw [(retire_row controller feature row).1]
  exact rowQuiet_retire _ history row (quiet.rows row) feature

/-- **Credit horizon of a quiet controller.** A slot that a row has not laid on the last
`creditReach` steps of a reward-free run is not eligible in that row and holds a zero weight. -/
theorem ctrlQuiet_dormant {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (row : Action actions)
    (slot : FeatIdx dimension) (unlaid : notLaid history row slot (creditReach criterion)) :
    Dormant controller row slot :=
  ⟨(quiet.rows row).trace slot _ unlaid |>.2 (reach_pruned criterion),
    ((quiet.rows row).slots slot).weight⟩

end QuietController

section Moves

open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds
open AcornVerif.CurrentLearner AcornVerif.CurrentPreReward
open SwiftTd (ActiveSet)

variable {criterion : Criterion} {dimension : Dimension} {actions : Nat}

/-! ## A recently laid slot takes the first reward

On a frame of at most 1900 slots the trace total is at most the ordered sum of 1900 trace bounds,
so a laid trace is at least the stored step size times the complement of that sum (`lowChain`'s
first word). Each later step decays it once, and relaying only adds to it. While the decayed word
stays above the pruning threshold the slot stays eligible, so the first loop at the reward visits
it and writes the trace word itself into the weight. -/

/-- The least trace a laying visit writes on a frame of at most 1900 slots, decayed `i` times. -/
def lowChain (criterion : Criterion) : Nat → Binary32
  | 0 => stepWord.mul (Binary32.one.sub (partialBound criterion))
  | i + 1 => (lowChain criterion i).mul (decayOf criterion)

/-- The least laid trace decayed eighty times is still above the pruning threshold. -/
theorem low_above (criterion : Criterion) : pruneWord.key < (lowChain criterion 80).key := by
  cases criterion <;> decide +kernel

/-- The least laid trace decayed any number of times is small, nonnegative and not above its
undecayed word. -/
theorem lowChain_facts (criterion : Criterion) (i : Nat) :
    Small (lowChain criterion i) ∧ 0 ≤ numerical32 (lowChain criterion i) ∧
      numerical32 (lowChain criterion i) ≤ numerical32 (lowChain criterion 0) := by
  induction i with
  | zero =>
    have small : Small (lowChain criterion 0) := small_named (by cases criterion <;> decide +kernel)
    refine ⟨small, ?_, le_rfl⟩
    rw [← zero_value]
    exact num_le (by decide) small.1 (by cases criterion <;> decide +kernel)
  | succ i ih =>
    have product := mul_small ih.1 (small_decay criterion)
    have lower := mul_nonneg' ih.1 (small_decay criterion) ih.2.1 (decay_nonneg criterion)
    have upper := mul_le_self ih.1 (small_decay criterion) ih.2.1 (decay_le_one criterion)
    exact ⟨small_between product.1 small_zero ih.1 (by rw [zero_value]; exact lower) upper,
      lower, le_trans upper ih.2.2⟩

/-- Decaying more does not raise the least laid trace. -/
theorem lowChain_antitone (criterion : Criterion) (i k : Nat) :
    numerical32 (lowChain criterion (i + k)) ≤ numerical32 (lowChain criterion i) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have facts := lowChain_facts criterion (i + k)
    exact le_trans (mul_le_self facts.1 (small_decay criterion) facts.2.1 (decay_le_one criterion))
      ih

/-- The least laid trace decayed at most eighty times is above the pruning threshold. -/
theorem lowChain_above (criterion : Criterion) (i : Nat) (near : i ≤ 80) :
    numerical32 pruneWord < numerical32 (lowChain criterion i) := by
  have far := lowChain_antitone criterion i (80 - i)
  rw [show i + (80 - i) = 80 by omega] at far
  have above := (numerical32_strict_order _ _ (by decide)
    (lowChain_facts criterion 80).1.1).mpr (low_above criterion)
  exact lt_of_lt_of_le above far

/-- A slot eligible in a row whose trace is at least a word. -/
def Recent (controller : Controller (criterion.config .control) dimension actions)
    (row : Fin actions) (slot : FeatIdx dimension) (lower : Binary32) : Prop :=
  slot ∈ (controller.learners.get row).state.transient.eligible ∧
    numerical32 lower ≤ numerical32 (slotOf (controller.learners.get row).state slot).z

/-- **A reward-free first loop keeps a recent slot eligible.** A quiet eligible slot whose trace
is at least a word whose decay stays above the pruning threshold is visited, kept, and left with a
trace at least that decayed word. -/
theorem recent_first_loop {history : List (Laid dimension actions)} {row : Action actions}
    (state : NumericState (criterion.config .control) dimension)
    (quiet : RowQuiet criterion state history row)
    (unique : state.transient.eligible.toList.Nodup)
    {delta vDelta : Binary32} (hd : delta.isZero = true) (hv : vDelta.isZero = true)
    (slot : FeatIdx dimension) (lower : Binary32) (lowerSmall : Small lower)
    (lowerNonneg : 0 ≤ numerical32 lower)
    (eligible : slot ∈ state.transient.eligible)
    (bound : numerical32 lower ≤ numerical32 (slotOf state slot).z)
    (above : numerical32 pruneWord < numerical32 (lower.mul (decayOf criterion))) :
    let next := state.learnFirstLoop (criterion.config .control) delta vDelta (decayOf criterion)
    slot ∈ next.transient.eligible ∧
      numerical32 (lower.mul (decayOf criterion)) ≤ numerical32 (slotOf next slot).z := by
  have result := first_loop_slots
    (fun idx words => idx = slot →
      SlotQuiet criterion words ∧ numerical32 lower ≤ numerical32 words.z)
    (fun idx words => idx = slot →
      numerical32 (lower.mul (decayOf criterion)) ≤ numerical32 words.z)
    (fun idx _ => idx ≠ slot) delta vDelta (decayOf criterion)
    (StepSizeRails.ofConfig (criterion.config .control)) ?_ state quiet.rails unique
    (fun idx _ same => by subst same; exact ⟨quiet.slots idx, bound⟩)
    (fun idx absent same => absent (same ▸ eligible))
  · exact ⟨by_contra fun absent => result.2.2.2 slot absent rfl, result.2.2.1 slot (by_contra
      fun absent => result.2.2.2 slot absent rfl) rfl⟩
  · intro current idx sameRails pre
    by_cases same : idx = slot
    · subst same
      obtain ⟨words, low⟩ := pre rfl
      obtain ⟨_, _, z, _, _, lastAlpha, _, _, _, _, _, prune⟩ :=
        quiet_first current idx sameRails hd hv words
      have zSmall : Small (slotOf current idx).z :=
        small_between words.zFinite small_zero (small_bound criterion)
          (by rw [zero_value]; exact words.zLow) words.zHigh
      have decayed := mul_mono lowerSmall (small_decay criterion) zSmall (small_decay criterion)
        lowerNonneg (decay_nonneg criterion) low le_rfl
      have nonzero : (slotOf current idx).z.isZero = false := by
        apply Bool.eq_false_iff.mpr
        intro zero
        have zeroRead := zero_reads zero
        have lowered := mul_le_self lowerSmall (small_decay criterion) lowerNonneg
          (decay_le_one criterion)
        have prunePositive : 0 ≤ numerical32 pruneWord := by
          rw [← zero_value]; exact num_le (by decide) (by decide) (by decide)
        linarith
      have threshold := words.reference nonzero
      have keep : (current.firstLoopElement idx delta vDelta (decayOf criterion)).2 = false := by
        rw [prune, threshold, prune_eq, finite_lessOrEqual _ _ (mul_small zSmall
          (small_decay criterion)).1 (by decide)]
        simp only [decide_eq_false_iff_not, not_le]
        linarith
      refine ⟨fun pruned => absurd (keep ▸ pruned) (by decide), fun _ _ => ?_⟩
      rw [z]
      exact decayed
    · exact ⟨fun _ => same, fun _ equal => absurd equal same⟩

/-- **A laying visit on a frame of at most 1900 slots writes at least the least laid trace.** -/
theorem laid_lower (state : NumericState (criterion.config .control) dimension)
    (features : ActiveSet dimension) (fits : features.indices.length ≤ 1900)
    (sameRails : state.rails = StepSizeRails.ofConfig (criterion.config .control))
    (slots : ∀ slot, SlotQuiet criterion (slotOf state slot) ∧
      numerical32 (slotOf state slot).z ≤ numerical32 (decayedBound criterion))
    (slot : FeatIdx dimension) (held : slot ∈ features.indices) :
    numerical32 (lowChain criterion 0) ≤
      numerical32 (slotOf (state.learnSecondLoop (criterion.config .control) features .zero).1
        slot).z := by
  obtain ⟨noOvershoot, complementSmall, complementLow, complementHigh, short⟩ :=
    quiet_entry state features (by omega) slots
  have result := second_loop_slots (fun _ words => SlotQuiet criterion words ∧
      numerical32 words.z ≤ numerical32 (decayedBound criterion))
    (fun idx words => idx = slot → numerical32 (lowChain criterion 0) ≤ numerical32 words.z)
    (fun _ => True) (StepSizeRails.ofConfig (criterion.config .control)) state features .zero ?_
    sameRails trivial (fun idx _ => slots idx)
  · exact result.2.2.1 slot held rfl
  intro current vd idx _ _ pre
  simp only [noOvershoot, Bool.false_eq_true, ite_false]
  obtain ⟨words, _⟩ := quiet_second current idx _ vd pre.1.beta
  rw [words]
  refine ⟨fun _ => ?_, trivial⟩
  obtain ⟨quiet, decayed⟩ := pre
  have zs : Small (slotOf current idx).z :=
    small_between quiet.zFinite small_zero (small_bound criterion)
      (by rw [zero_value]; exact quiet.zLow) quiet.zHigh
  have trace := laid_trace criterion zs quiet.zLow decayed complementSmall complementLow
    complementHigh
  have least := mul_mono_right small_step (small_named (by cases criterion <;> decide +kernel))
    complementSmall step_nonneg (short fits)
  exact le_trans least trace.2.2.1

/-- **The step that lays a slot leaves it recent.** A reward-free step at a row and a frame of at
most 1900 slots that holds the slot leaves the slot eligible in that row with a trace at least the
least laid trace. -/
theorem recent_laid {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (row : Action actions) (fits : features.indices.length ≤ 1900) (slot : FeatIdx dimension)
    (held : slot ∈ features.indices) :
    Recent (controller.step features row .zero).1 row slot (lowChain criterion 0) := by
  unfold Recent
  rw [step_eq]
  have lag := ctrlQuiet_predict quiet features row
  have gamma : (criterion.config .control).rule.gamma.Finite := by cases criterion <;> decide
  have delta := zeroWord_sub (zeroWord_add (by decide : Binary32.zero.isZero = true)
    (finite_mul_zero gamma lag)) quiet.vOld
  generalize ((Binary32.zero.add ((criterion.config .control).rule.gamma.mul
    ((controller.predictAll features).get row))).sub controller.vOld) = δ at delta ⊢
  have decay : (criterion.config .control).rule.gamma.mul (criterion.config .control).lambda =
      decayOf criterion := rfl
  rw [decay, creditStep_row, credit_state, quiet.restart]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have first := quiet_first_loop (controller.learners.get row).state history row (quiet.rows row)
    (row_unique controller row) (row_supported controller row) delta quiet.vDelta
  have entry := quiet_first_entry (controller.learners.get row).state history row
    (quiet.rows row) (row_unique controller row) (row_supported controller row) delta
    quiet.vDelta
  refine ⟨?_, laid_lower _ features fits first.1 entry slot held⟩
  rw [← Array.mem_toList_iff, second_loop_eligible]
  by_cases zero : (((controller.learners.get row).state.learnFirstLoop (criterion.config .control)
      δ controller.vDelta (decayOf criterion)).transient.z.get slot).value.isZero
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨held, zero⟩)
  · apply List.mem_append_left
    rw [Array.mem_toList_iff]
    by_contra absent
    have cleared := (first.2.2 slot absent).zero
    rw [slotOf_z] at cleared
    rw [cleared] at zero
    exact zero (by decide)

/-- The second loop writes no weight. -/
theorem second_loop_weights {cfg : Acorn.Config} (state : NumericState cfg dimension)
    (features : ActiveSet dimension) (vd : Binary32) :
    (state.learnSecondLoop cfg features vd).1.weights = state.weights := by
  rw [NumericState.learnSecondLoop_eq_sumFrom]
  dsimp only
  generalize Binary32.sumFrom .zero (features.indices.map fun idx => (state.beta.get idx).alpha) =
    rate
  generalize Binary32.sumFrom .zero (features.indices.map fun idx =>
    (state.transient.z.get idx).value) = total
  induction features.indices generalizing state vd with
  | nil => rfl
  | cons head rest ih =>
    rw [List.foldl_cons]
    refine (ih _ _).trans ?_
    cases cfg.eta.less rate <;> rfl

/-- **A reward-free step keeps a recent slot recent, one decay lower.** -/
theorem recent_after {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (action : Action actions) (fits : features.indices.length ≤ 1999) (row : Action actions)
    (slot : FeatIdx dimension) (lower : Binary32) (lowerSmall : Small lower)
    (lowerNonneg : 0 ≤ numerical32 lower) (recent : Recent controller row slot lower)
    (above : numerical32 pruneWord < numerical32 (lower.mul (decayOf criterion))) :
    Recent (controller.step features action .zero).1 row slot (lower.mul (decayOf criterion)) := by
  unfold Recent
  rw [step_eq]
  have lag := ctrlQuiet_predict quiet features action
  have gamma : (criterion.config .control).rule.gamma.Finite := by cases criterion <;> decide
  have delta := zeroWord_sub (zeroWord_add (by decide : Binary32.zero.isZero = true)
    (finite_mul_zero gamma lag)) quiet.vOld
  generalize ((Binary32.zero.add ((criterion.config .control).rule.gamma.mul
    ((controller.predictAll features).get action))).sub controller.vOld) = δ at delta ⊢
  have decay : (criterion.config .control).rule.gamma.mul (criterion.config .control).lambda =
      decayOf criterion := rfl
  rw [decay, creditStep_row, credit_state, quiet.restart]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have kept := recent_first_loop (controller.learners.get row).state (quiet.rows row)
    (row_unique controller row) delta quiet.vDelta slot lower lowerSmall lowerNonneg recent.1
    recent.2 above
  split
  · rename_i taken
    subst taken
    have first := quiet_first_loop (controller.learners.get action).state history action
      (quiet.rows action) (row_unique controller action) (row_supported controller action) delta
      quiet.vDelta
    have entry := quiet_first_entry (controller.learners.get action).state history action
      (quiet.rows action) (row_unique controller action) (row_supported controller action) delta
      quiet.vDelta
    refine ⟨?_, ?_⟩
    · rw [← Array.mem_toList_iff, second_loop_eligible]
      exact List.mem_append_left _ (Array.mem_toList_iff.mpr kept.1)
    · obtain ⟨noOvershoot, complementSmall, complementLow, complementHigh, _⟩ :=
        quiet_entry _ features fits entry
      have result := second_loop_slots (fun idx words => (SlotQuiet criterion words ∧
          numerical32 words.z ≤ numerical32 (decayedBound criterion)) ∧
          (idx = slot → numerical32 (lower.mul (decayOf criterion)) ≤ numerical32 words.z))
        (fun idx words => idx = slot →
          numerical32 (lower.mul (decayOf criterion)) ≤ numerical32 words.z)
        (fun _ => True) (StepSizeRails.ofConfig (criterion.config .control)) _ features .zero ?_
        first.1 trivial (fun idx _ => ⟨entry idx, fun same => by subst same; exact kept.2⟩)
      · by_cases held : slot ∈ features.indices
        · exact result.2.2.1 slot held rfl
        · rw [result.2.2.2 slot held]
          exact kept.2
      intro current vd idx _ _ pre
      simp only [noOvershoot, Bool.false_eq_true, ite_false]
      obtain ⟨words, _⟩ := quiet_second current idx _ vd pre.1.1.beta
      rw [words]
      refine ⟨fun same => ?_, trivial⟩
      obtain ⟨⟨quietSlot, decayed⟩, low⟩ := pre
      have zs : Small (slotOf current idx).z :=
        small_between quietSlot.zFinite small_zero (small_bound criterion)
          (by rw [zero_value]; exact quietSlot.zLow) quietSlot.zHigh
      have trace := laid_trace criterion zs quietSlot.zLow decayed complementSmall complementLow
        complementHigh
      have increment : Small (stepWord.mul (Binary32.one.sub (Binary32.sumFrom .zero
          (features.indices.map fun idx => (((controller.learners.get action).state.learnFirstLoop
            (criterion.config .control) δ controller.vDelta
            (decayOf criterion)).transient.z.get idx).value)))) :=
        small_between (mul_small small_step complementSmall).1 small_zero small_step
          (by rw [zero_value]; exact trace.2.1)
          (by
            have := mul_mono_right small_step complementSmall small_one step_nonneg
              (by rw [one_value]; exact complementHigh)
            rwa [show stepWord.mul Binary32.one = stepWord by decide] at this)
      exact le_trans (low same) (le_add_right zs increment trace.2.1)
  · exact kept

/-- The weight a first-loop visit writes. -/
theorem first_element_weight {cfg : Acorn.Config} (state : NumericState cfg dimension)
    (idx : FeatIdx dimension) (delta vDelta decay : Binary32) :
    (slotOf (state.firstLoopElement idx delta vDelta decay).1 idx).weight =
      (Weight.project cfg.rule ((slotOf state idx).weight.add
        ((delta.mul (slotOf state idx).z).sub ((slotOf state idx).zDelta.mul vDelta)))).value := by
  simp only [NumericState.firstLoopElement, slotOf_weight, slotOf_z, slotOf_zDelta, get_set_vec,
    ite_true]

/-- **A reward of one moves a recent weight.** At the trace it reads, a positive trace no larger
than the trace bound is written into the weight word by the first loop at error one. -/
theorem reward_weight (rule : ValueRule) (inside : rule = criterion.rule)
    {weight z zDelta vDelta : Binary32} (hw : weight.isZero = true) (zs : Small z)
    (zh : numerical32 z ≤ numerical32 (traceBound criterion))
    (positive : 0 < numerical32 z) (hd : zDelta.Finite) (hv : vDelta.isZero = true) :
    (Weight.project rule (weight.add ((Binary32.one.mul z).sub (zDelta.mul vDelta)))).value.isZero =
      false := by
  have product := mul_small small_one zs
  have same : numerical32 (Binary32.one.mul z) = numerical32 z :=
    by
      have source := product.2
      rw [one_value, one_mul] at source
      exact rounded_unique source (exact_word zs.1)
  have productSmall : Small (Binary32.one.mul z) := ⟨product.1, by rw [same]; exact zs.2⟩
  have zeroProduct := finite_mul_zero hd hv
  have difference := sub_small productSmall (zero_small zeroProduct)
  have differenceSame : numerical32 ((Binary32.one.mul z).sub (zDelta.mul vDelta)) =
      numerical32 z := by
    rw [← same]
    have source := difference.2
    rw [zero_reads zeroProduct, sub_zero] at source
    exact rounded_unique source (exact_word product.1)
  have differenceSmall : Small ((Binary32.one.mul z).sub (zDelta.mul vDelta)) :=
    ⟨difference.1, by rw [differenceSame]; exact zs.2⟩
  have sum := add_small (zero_small hw) differenceSmall
  have raw : numerical32 (weight.add ((Binary32.one.mul z).sub (zDelta.mul vDelta))) =
      numerical32 z := by
    rw [← differenceSame]
    have source := sum.2
    rw [zero_reads hw, zero_add] at source
    exact rounded_unique source (exact_word difference.1)
  have rawFinite := sum.1
  have contains : rule.domain.range.Contains
      (weight.add ((Binary32.one.mul z).sub (zDelta.mul vDelta))) := by
    refine ⟨rawFinite, ?_, ?_⟩
    · have nonneg :
          (0 : Int) ≤ (weight.add ((Binary32.one.mul z).sub (zDelta.mul vDelta))).key := by
        have := key_le (by decide : Binary32.zero.Finite) rawFinite
          (by rw [zero_value, raw]; exact positive.le)
        have zeroKey : Binary32.zero.key = 0 := by decide
        omega
      have lowerKey : rule.domain.range.lower.key ≤ 0 := by
        subst inside; cases criterion <;> decide +kernel
      omega
    · have upper := key_le rawFinite (small_bound criterion).1 (by rw [raw]; exact zh)
      have boundKey : (traceBound criterion).key ≤ rule.domain.range.upper.key := by
        subst inside; cases criterion <;> decide +kernel
      omega
  rw [Weight.project_eq]
  change (Binary32.project _ rule.domain.range.upper).isZero = false
  rw [rule.domain.symmetric_project_identity _ contains]
  apply Bool.eq_false_iff.mpr
  intro zero
  rw [zero_reads zero] at raw
  linarith

/-- One plus a zero word minus a zero word is one. -/
theorem one_add_sub_zeros {first second : Binary32} (hf : first.isZero = true)
    (hs : second.isZero = true) : (Binary32.one.add first).sub second = Binary32.one := by
  rcases isZero_bits first hf with bf | bf <;> rcases isZero_bits second hs with bs | bs <;>
  · obtain ⟨rf⟩ := first
    obtain ⟨rs⟩ := second
    simp only at bf bs
    subst bf bs
    decide +kernel

/-- **A reward of one moves the weight of a recent slot**, whatever the frame and action of the
reward step. -/
theorem recent_moves {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (action row : Action actions) (slot : FeatIdx dimension) (lower : Binary32)
    (recent : Recent controller row slot lower) (positive : 0 < numerical32 lower) :
    (((controller.step features action .one).1.learners.get row).state.weights.get
      slot).value.isZero = false := by
  rw [step_eq]
  have lag := ctrlQuiet_predict quiet features action
  have gamma : (criterion.config .control).rule.gamma.Finite := by cases criterion <;> decide
  rw [one_add_sub_zeros (finite_mul_zero gamma lag) quiet.vOld, creditStep_row, credit_state,
    quiet.restart]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have moved := first_loop_slots
    (fun idx words => idx = slot → SlotQuiet criterion words ∧
      numerical32 lower ≤ numerical32 words.z)
    (fun idx words => idx = slot → words.weight.isZero = false)
    (fun idx words => idx = slot → words.weight.isZero = false) Binary32.one controller.vDelta
    (decayOf criterion) (StepSizeRails.ofConfig (criterion.config .control)) ?_
    (controller.learners.get row).state (quiet.rows row).rails (row_unique controller row)
    (fun idx _ same => by subst same; exact ⟨(quiet.rows row).slots idx, recent.2⟩)
    (fun idx absent same => absurd (same ▸ recent.1) absent)
  · have weight : (slotOf ((controller.learners.get row).state.learnFirstLoop
        (criterion.config .control) Binary32.one controller.vDelta (decayOf criterion))
        slot).weight.isZero = false := by
      by_cases member : slot ∈ ((controller.learners.get row).state.learnFirstLoop
          (criterion.config .control) Binary32.one controller.vDelta
          (decayOf criterion)).transient.eligible
      · exact moved.2.2.1 slot member rfl
      · exact moved.2.2.2 slot member rfl
    split
    · rw [second_loop_weights]
      exact weight
    · exact weight
  · intro current idx _ pre
    have written : (slotOf (current.firstLoopElement idx Binary32.one controller.vDelta
        (decayOf criterion)).1 idx).weight.isZero = true → idx = slot → False := by
      intro zero same
      subst same
      obtain ⟨words, low⟩ := pre rfl
      have zs : Small (slotOf current idx).z :=
        small_between words.zFinite small_zero (small_bound criterion)
          (by rw [zero_value]; exact words.zLow) words.zHigh
      rw [first_element_weight] at zero
      rw [reward_weight (criterion.config .control).rule rfl words.weight zs words.zHigh
        (lt_of_lt_of_le positive low)
        words.zDelta quiet.vDelta] at zero
      cases zero
    refine ⟨fun _ same => ?_, fun _ same => ?_⟩
    · have knowledge := clear_feature_knowledge
        (current.firstLoopElement idx Binary32.one controller.vDelta (decayOf criterion)).1 idx idx
      rw [slotOf_weight, knowledge.1, ← slotOf_weight]
      exact Bool.eq_false_iff.mpr fun zero => written zero same
    · exact Bool.eq_false_iff.mpr fun zero => written zero same

/-- A cold run's controller is quiet against the steps it took. -/
theorem fold_quiet {cfgCriterion : Criterion} :
    ∀ (steps : List (Laid dimension actions))
      (controller : Controller (cfgCriterion.config .control) dimension actions)
      (history : List (Laid dimension actions)),
      CtrlQuiet cfgCriterion controller history →
      (∀ step ∈ steps, step.features.indices.length ≤ 1999) →
      CtrlQuiet cfgCriterion (steps.foldl (fun controller step =>
        (controller.step step.features step.row .zero).1) controller) (history ++ steps) := by
  intro steps
  induction steps with
  | nil => intro controller history quiet _; simpa using quiet
  | cons step rest ih =>
    intro controller history quiet fits
    rw [List.foldl_cons]
    have next := ctrlQuiet_step quiet step.features step.row
      (by decide : Binary32.zero.isZero = true) (fits step (List.mem_cons_self ..))
    have result := ih _ _ next (fun other member => fits other (List.mem_cons_of_mem _ member))
    simpa [List.append_assoc] using result

/-- Over reward-free steps a recent slot stays recent, decayed once per step, while the decayed
least laid trace stays above the pruning threshold. -/
theorem fold_recent {cfgCriterion : Criterion} (row : Action actions) (slot : FeatIdx dimension) :
    ∀ (steps : List (Laid dimension actions)) (i : Nat)
      (controller : Controller (cfgCriterion.config .control) dimension actions)
      (history : List (Laid dimension actions)),
      CtrlQuiet cfgCriterion controller history →
      Recent controller row slot (lowChain cfgCriterion i) →
      i + steps.length ≤ 80 →
      (∀ step ∈ steps, step.features.indices.length ≤ 1999) →
      Recent (steps.foldl (fun controller step =>
        (controller.step step.features step.row .zero).1) controller) row slot
        (lowChain cfgCriterion (i + steps.length)) := by
  intro steps
  induction steps with
  | nil => intro i controller history _ recent _ _; simpa using recent
  | cons step rest ih =>
    intro i controller history quiet recent near fits
    rw [List.foldl_cons]
    have facts := lowChain_facts cfgCriterion i
    have fitsHere := fits step (List.mem_cons_self ..)
    have next := recent_after quiet step.features step.row fitsHere row slot _ facts.1 facts.2.1
      recent (lowChain_above cfgCriterion (i + 1) (by simp only [List.length_cons] at near; omega))
    have quietNext := ctrlQuiet_step quiet step.features step.row
      (by decide : Binary32.zero.isZero = true) fitsHere
    have result := ih (i + 1) _ _ quietNext next (by simp only [List.length_cons] at near; omega)
      (fun other member => fits other (List.mem_cons_of_mem _ member))
    simpa [Nat.add_assoc, Nat.add_comm 1] using result

end Moves

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- The executed agent over a percept list under a step order, with what each step laid, in
stream order. -/
def traced (order : StepOrder) :
    Agent interface profile config criterion dimension planning → List (Percept interface) →
      Agent interface profile config criterion dimension planning ×
        List (Laid dimension interface.actions.word.toNat)
  | state, [] => (state, [])
  | state, percept :: rest =>
    let chosen := state.choose order percept
    let later := traced order chosen.learn rest
    (later.1, ⟨chosen.features, chosen.decision.action⟩ :: later.2)

/-- The primitive controller of an agent. -/
abbrev controlOf (state : Agent interface profile config criterion dimension planning) :
    Controller (criterion.config .control) dimension interface.actions.word.toNat :=
  state.control.runtime.lifecycle.consumers.control

/-- The steps that can still have credited a slot by the end of `quiet ++ post`: the last
`creditReach criterion` steps of `quiet` and every step of `post`. -/
def window (criterion : Criterion) {actions : Nat} (quiet post : List (Laid dimension actions)) :
    List (Laid dimension actions) :=
  quiet.drop (quiet.length - creditReach criterion) ++ post

/-- The slots of a frame that some step of a list laid, in the frame's order. -/
def sharedWith {actions : Nat} (features : SwiftTd.ActiveSet dimension)
    (steps : List (Laid dimension actions)) : SwiftTd.ActiveSet dimension :=
  ⟨features.indices.filter fun slot =>
      steps.any fun step => decide (slot ∈ step.features.indices),
    features.nodup.filter _⟩

section AgentSteps

open AcornVerif.CurrentPreReward

/-! ## What one agent step writes into the primitive controller

The first part of a step writes neither the primitive controller nor a demon
(`Agent.choose_keeps`), and neither do the owed writes and the deferred planning
(`TemporalControl.deferred_keeps`), the off-policy option learning (`followOptions_eq`) or the
span close (`closeSpan_eq`). The completion boundary credits the controller with one
`Controller.step` at the frame and the executed action under per-step credit, and with nothing
under a frozen profile (`TemporalControl.finish_credit`). The tester then retires slots
(`Lifecycle.test_preserves`), and releasing units writes no primitive row. -/

/-- The temporal state the completion boundary of a chosen step reads. -/
def finishInput (chosen : Chosen interface profile config criterion dimension planning) :
    TemporalControl interface profile config criterion dimension :=
  let deferred := chosen.control.deferred chosen.order planning chosen.features chosen.owed
    chosen.percept.reward chosen.percept.frame.achieved chosen.decision
  (deferred.followOptions (modelOperations criterion dimension) chosen.features
    chosen.percept.frame.declared chosen.percept.reward chosen.percept.frame.achieved
    chosen.decision).closeSpan (deferred.takeoverValue chosen.features
      chosen.percept.frame.declared chosen.percept.frame.achieved chosen.decision)

/-- The first part keeps the percept. -/
theorem choose_percept (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    (state.choose order percept).percept = percept := by
  cases order <;> rfl

/-- Off-policy option learning writes no primitive row. -/
theorem followOptions_control (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (state.followOptions models features declared reward goal
        decision).runtime.lifecycle.consumers.control =
      state.runtime.lifecycle.consumers.control := by
  rw [TemporalControl.followOptions_eq]
  split <;> rfl

/-- The span close writes no primitive row. -/
theorem closeSpan_control (state : TemporalControl interface profile config criterion dimension)
    (continuation : Option Binary32) :
    (state.closeSpan continuation).runtime.lifecycle.consumers.control =
      state.runtime.lifecycle.consumers.control := by
  cases continuation with
  | none => rfl
  | some value =>
    rw [TemporalControl.closeSpan_eq]
    rfl

/-- The completion boundary reads the primitive controller the step started from. -/
theorem finishInput_control (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    (finishInput (state.choose order percept)).runtime.lifecycle.consumers.control =
      controlOf state := by
  let chosen := state.choose order percept
  have deferred := (TemporalControl.deferred_keeps chosen.control chosen.control ⟨rfl, rfl⟩
    chosen.order planning chosen.features chosen.owed chosen.percept.reward
    chosen.percept.frame.achieved chosen.decision).1
  unfold finishInput
  rw [closeSpan_control, followOptions_control, deferred]
  exact (state.choose_keeps order percept).1

/-- The completion boundary credits the controller with one step under per-step credit, and with
nothing under a frozen profile. -/
theorem finish_control (perStep : profile.credit = .perStep)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features obs reward decision).runtime.lifecycle.consumers.control =
      if profile.mode = .frozen then state.runtime.lifecycle.consumers.control
      else (state.runtime.lifecycle.consumers.control.step features decision.action
        (criterion.center reward 1 state.average.rate)).1 := by
  rw [TemporalControl.finish_credit]
  have credit : state.credit = .perStep := by
    have matched := state.creditMatches
    rw [perStep] at matched
    cases h : state.credit <;> simp_all [creditKind]
  unfold PredictionControl.advance PredictionControl.advanceWith
  by_cases frozen : profile.mode = .frozen
  · simp [frozen, PrimitiveControl.finish, TemporalControl.predictionView]
  · simp [frozen, PrimitiveControl.finish, TemporalControl.predictionView,
      PrimitiveControl.creditStep, credit]

/-- The tester writes the primitive controller only by retirements. -/
theorem retire_closed (P : Controller (criterion.config .control) dimension
      interface.actions.word.toNat → Prop)
    (closed : ∀ controller feature, P controller → P (controller.retire feature))
    (agent : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) (holds : P (controlOf agent)) :
    P (controlOf (agent.retire active)) := by
  unfold Agent.retire
  split
  · exact holds
  · have tested := agent.control.runtime.lifecycle.test_preserves
      agent.control.runtime.references.phase.free active (fun ensemble => P ensemble.control)
      (fun ensemble feature held => by
        cases ensemble
        exact closed _ feature held) holds
    change P (((agent.control.runtime.lifecycle.test agent.control.runtime.references.phase.free
      active).1.consumers.releaseAll _).control)
    have released : ∀ (units : List (Fin config.units.count))
        (ensemble : Ensemble interface.actions config criterion dimension interface.layout),
        (ensemble.releaseAll units).control = ensemble.control := by
      intro units
      induction units with
      | nil => intro ensemble; rfl
      | cons unit rest ih =>
        intro ensemble
        exact (ih _).trans rfl
    rw [released]
    exact tested

/-- **A frozen agent step writes no primitive row.** -/
theorem frozen_step (frozen : profile.mode = .frozen) (perStep : profile.credit = .perStep)
    (state : Agent interface profile config criterion dimension planning) (order : StepOrder)
    (percept : Percept interface) :
    controlOf (state.choose order percept).learn = controlOf state := by
  unfold Chosen.learn Agent.retire
  simp only [frozen, beq_self_eq_true, ite_true]
  change ((finishInput (state.choose order percept)).finish _ _ _
    _).runtime.lifecycle.consumers.control = _
  rw [finish_control perStep, finishInput_control]
  simp only [frozen, ↓reduceIte]

/-- **A learning agent step is one controller step, then retirements.** Under per-step credit and
a learning profile, every property of the primitive controller that retirements keep and that the
step at the frame and the executed action reaches holds after the agent step. -/
theorem learning_step (learning : profile.mode ≠ .frozen) (perStep : profile.credit = .perStep)
    (state : Agent interface profile config criterion dimension planning) (order : StepOrder)
    (percept : Percept interface)
    (P : Controller (criterion.config .control) dimension interface.actions.word.toNat → Prop)
    (closed : ∀ controller feature, P controller → P (controller.retire feature))
    (stepped : P ((controlOf state).step (state.choose order percept).features
      (state.choose order percept).decision.action (criterion.center percept.reward 1
        (finishInput (state.choose order percept)).average.rate)).1) :
    P (controlOf (state.choose order percept).learn) := by
  apply retire_closed P closed
  change P ((finishInput (state.choose order percept)).finish _ _ _
    _).runtime.lifecycle.consumers.control
  rw [finish_control perStep, finishInput_control, choose_percept]
  simp only [learning, ↓reduceIte]
  exact stepped

/-- **The completion boundary of a reward-free step reads a zero rate.** From a quiet state and a
zero reward word, the state the completion boundary reads is quiet, so its average-reward rate,
a finite stored word, is a zero word. -/
theorem quiet_rate (state : Agent interface profile config criterion dimension planning)
    (quiet : Quiet state.control) (order : StepOrder) (percept : Percept interface)
    (silent : percept.reward.isZero = true) :
    (finishInput (state.choose order percept)).average.rate.value.isZero = true := by
  obtain ⟨chosen, owed, decision, perceived, _⟩ :=
    quiet.choose order percept (Inert32.ofZero silent)
  have reward : Inert32 (state.choose order percept).percept.reward := by
    rw [perceived]; exact Inert32.ofZero silent
  have deferred := chosen.deferred (state.choose order percept).order planning
    (state.choose order percept).features owed reward
    (state.choose order percept).percept.frame.achieved (state.choose order percept).decision
  have closed : Quiet (finishInput (state.choose order percept)) :=
    (deferred.followOptions (state.choose order percept).features
    (state.choose order percept).percept.frame.declared reward
    (state.choose order percept).percept.frame.achieved decision).closeSpan
    (Quiet.takeoverValue (state := (state.choose order percept).control.deferred
      (state.choose order percept).order planning (state.choose order percept).features
      (state.choose order percept).owed (state.choose order percept).percept.reward
      (state.choose order percept).percept.frame.achieved (state.choose order percept).decision)
      (state.choose order percept).features
      (state.choose order percept).percept.frame.declared
      (state.choose order percept).percept.frame.achieved decision)
  rcases closed.rate with zero | nan
  · exact zero
  · have finite := (finishInput (state.choose order percept)).average.rate.legal.1
    rw [Binary32.finite_not_nan _ finite] at nan
    cases nan

/-- A centered zero reward at a zero rate is a zero word. -/
theorem center_zero {reward : Binary32} (hr : reward.isZero = true) {rate : RewardRate}
    (hg : rate.value.isZero = true) : (criterion.center reward 1 rate).isZero = true := by
  cases criterion
  · exact hr
  · exact zeroWord_sub hr (finite_mul_zero (by decide) hg)

/-- A frozen run writes no primitive row. -/
theorem traced_frozen (frozen : profile.mode = .frozen) (perStep : profile.credit = .perStep)
    (order : StepOrder) :
    ∀ (percepts : List (Percept interface))
      (agent : Agent interface profile config criterion dimension planning),
      controlOf (traced order agent percepts).1 = controlOf agent := by
  intro percepts
  induction percepts with
  | nil => intro agent; rfl
  | cons percept rest ih =>
    intro agent
    exact (ih _).trans (frozen_step frozen perStep agent order percept)

/-- **A learning run over reward-free percepts keeps its primitive controller quiet** against the
history of what it laid, on frames of at most 1999 slots. -/
theorem traced_quiet (learning : profile.mode ≠ .frozen) (perStep : profile.credit = .perStep)
    (order : StepOrder) :
    ∀ (percepts : List (Percept interface))
      (agent : Agent interface profile config criterion dimension planning)
      (history : List (Laid dimension interface.actions.word.toNat)),
      Quiet agent.control → CtrlQuiet criterion (controlOf agent) history →
      (∀ percept ∈ percepts, percept.reward.isZero = true) →
      (∀ step ∈ (traced order agent percepts).2, step.features.indices.length ≤ 1999) →
      CtrlQuiet criterion (controlOf (traced order agent percepts).1)
        (history ++ (traced order agent percepts).2) := by
  intro percepts
  induction percepts with
  | nil =>
    intro agent history _ ctrl _ _
    simp only [traced, List.append_nil]
    exact ctrl
  | cons percept rest ih =>
    intro agent history quiet ctrl silent fits
    have silentHere := silent percept (List.mem_cons_self ..)
    have fitsHere := fits ⟨(agent.choose order percept).features,
      (agent.choose order percept).decision.action⟩ (List.mem_cons_self ..)
    have next := learning_step learning perStep agent order percept
      (fun controller => CtrlQuiet criterion controller
        (history ++ [⟨(agent.choose order percept).features,
          (agent.choose order percept).decision.action⟩]))
      (fun _ feature held => ctrlQuiet_retire held feature)
      (ctrlQuiet_step ctrl _ _ (center_zero silentHere (quiet_rate agent quiet order percept
        silentHere)) fitsHere)
    have quietNext : Quiet (agent.choose order percept).learn.control :=
      quiet.actOrdered order percept (Inert32.ofZero silentHere)
    have result := ih _ _ quietNext next
      (fun other member => silent other (List.mem_cons_of_mem _ member))
      (fun step member => fits step (List.mem_cons_of_mem _ member))
    simpa [traced, List.append_assoc] using result

/-- **A learning run that never lays a dormant slot keeps it dormant**, whatever its rewards and
frames. -/
theorem traced_dormant (learning : profile.mode ≠ .frozen) (perStep : profile.credit = .perStep)
    (order : StepOrder) (row : Action interface.actions.word.toNat) (slot : FeatIdx dimension) :
    ∀ (percepts : List (Percept interface))
      (agent : Agent interface profile config criterion dimension planning),
      Dormant (controlOf agent) row slot →
      (∀ step ∈ (traced order agent percepts).2, ¬step.Lays row slot) →
      Dormant (controlOf (traced order agent percepts).1) row slot := by
  intro percepts
  induction percepts with
  | nil => intro agent dormant _; exact dormant
  | cons percept rest ih =>
    intro agent dormant unlaid
    have here := unlaid ⟨(agent.choose order percept).features,
      (agent.choose order percept).decision.action⟩ (List.mem_cons_self ..)
    have next := learning_step learning perStep agent order percept
      (fun controller => Dormant controller row slot)
      (fun _ feature held => retire_dormant _ feature row slot held)
      (by rw [step_eq]; exact creditStep_dormant _ _ _ _ _ _ row slot dormant here)
    exact ih _ next (fun step member => unlaid step (List.mem_cons_of_mem _ member))


end AgentSteps

/-- **Credit horizon.** From cold initialization, over percepts whose reward words are zero and
whose frames each hold at most 1999 slots, and then any percepts at all, a primitive weight is a
zero word unless its row laid its slot in the window. -/
theorem dormant_weight_rests (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension)
    (planning : PlanningSelection) (order : StepOrder) (perStep : profile.credit = .perStep)
    (quiet post : List (Percept interface))
    (silent : ∀ percept ∈ quiet, percept.reward.isZero = true) :
    let start := Agent.initial interface profile config criterion dimension planning
    let first := traced order start quiet
    let second := traced order first.1 post
    (∀ step ∈ first.2, step.features.indices.length ≤ 1999) →
    ∀ (row : Action interface.actions.word.toNat) (slot : FeatIdx dimension),
      (∀ step ∈ window criterion first.2 second.2, ¬step.Lays row slot) →
      (((controlOf second.1).learners.get row).state.weights.get slot).value.isZero = true := by
  intro start first second fits row slot unlaid
  have cold : CtrlQuiet criterion (controlOf start) [] := ctrlQuiet_initial
  by_cases frozen : profile.mode = .frozen
  · rw [traced_frozen frozen perStep order post first.1,
      traced_frozen frozen perStep order quiet start]
    exact ((cold.rows row).slots slot).weight
  · have reached := traced_quiet frozen perStep order quiet start [] CurrentPreReward.Quiet.initial
      cold silent fits
    rw [List.nil_append] at reached
    have recent : notLaid first.2 row slot (creditReach criterion) := fun step member =>
      unlaid step (List.mem_append_left _ member)
    have rested := traced_dormant frozen perStep order row slot post first.1
      (ctrlQuiet_dormant reached row slot recent)
      (fun step member => unlaid step (List.mem_append_right _ member))
    exact rested.2

/-- **What the greedy choice reads.** Under the same run, at any frame and exploration rate, the
near-maximum candidates of the primitive controller are those of the frame's slots that a step of
the window laid. -/
theorem candidates_read_window (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension)
    (planning : PlanningSelection) (order : StepOrder) (perStep : profile.credit = .perStep)
    (quiet post : List (Percept interface))
    (silent : ∀ percept ∈ quiet, percept.reward.isZero = true)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    let start := Agent.initial interface profile config criterion dimension planning
    let first := traced order start quiet
    let second := traced order first.1 post
    (∀ step ∈ first.2, step.features.indices.length ≤ 1999) →
    ((controlOf second.1).snapshot (count := interface.actions) features epsilon).candidates =
      ((controlOf second.1).snapshot (count := interface.actions)
        (sharedWith features (window criterion first.2 second.2)) epsilon).candidates := by
  intro start first second fits
  apply AcornVerif.CurrentControl.candidates_of_resting
  · change features.indices.filter _ = features.indices.filter fun slot =>
      decide (slot ∈ features.indices.filter _)
    apply List.filter_congr
    intro slot member
    simp only [List.mem_filter, member, true_and]
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, decide_eq_true_eq]
  · intro row slot member absent
    apply dormant_weight_rests interface profile config criterion dimension planning order perStep
      quiet post silent fits row slot
    intro step inside lays
    apply absent
    change slot ∈ features.indices.filter _
    simp only [List.mem_filter, member, true_and, List.any_eq_true, decide_eq_true_eq]
    exact ⟨step, inside, lays.2⟩

/-- A controller's cold run over quiet steps. -/
def quietRun {config : Acorn.Config} {actions : Nat}
    (steps : List (Laid dimension actions)) : Controller config dimension actions :=
  steps.foldl (fun controller step => (controller.step step.features step.row .zero).1)
    (Controller.initial config dimension actions)

/-- **The horizon is not vacuous.** A slot laid at most 81 steps before a first reward of one, over
frames of at most 1900 slots, has a weight that the reward moves, under either criterion. -/
theorem recent_weight_moves (criterion : Criterion) (dimension : Dimension) {actions : Nat}
    (before after : List (Laid dimension actions)) (laid : Laid dimension actions)
    (slot : FeatIdx dimension) (held : slot ∈ laid.features.indices)
    (near : after.length + 1 ≤ 81)
    (fits : ∀ step ∈ before ++ laid :: after, step.features.indices.length ≤ 1900)
    (next : Laid dimension actions) :
    let quiet : Controller (criterion.config .control) dimension actions :=
      quietRun (before ++ laid :: after)
    (((quiet.step next.features next.row .one).1.learners.get laid.row).state.weights.get
      slot).value.isZero = false := by
  intro quiet
  have fitsAll : ∀ step ∈ before ++ laid :: after, step.features.indices.length ≤ 1999 :=
    fun step member => le_trans (fits step member) (by omega)
  have split : quiet = after.foldl (fun controller step =>
      (controller.step step.features step.row .zero).1)
      ((before.foldl (fun controller step => (controller.step step.features step.row .zero).1)
        (Controller.initial (criterion.config .control) dimension actions)).step laid.features
        laid.row .zero).1 := by
    simp only [quiet, quietRun, List.foldl_append, List.foldl_cons]
  have early := fold_quiet before (Controller.initial (criterion.config .control) dimension actions)
    [] ctrlQuiet_initial (fun step member => fitsAll step (List.mem_append_left _ member))
  have laidRecent := recent_laid early laid.features laid.row
    (fits laid (List.mem_append_right _ (List.mem_cons_self ..))) slot held
  have laidQuiet := ctrlQuiet_step early laid.features laid.row
    (by decide : Binary32.zero.isZero = true)
    (fitsAll laid (List.mem_append_right _ (List.mem_cons_self ..)))
  have afterFits : ∀ step ∈ after, step.features.indices.length ≤ 1999 := fun step member =>
    fitsAll step (List.mem_append_right _ (List.mem_cons_of_mem _ member))
  have lateRecent := fold_recent laid.row slot after 0 _ _ laidQuiet laidRecent (by omega) afterFits
  have lateQuiet := fold_quiet after _ _ laidQuiet afterFits
  rw [Nat.zero_add] at lateRecent
  rw [split]
  have prunePositive : 0 ≤ AcornVerif.CurrentArithmetic.numerical32 pruneWord := by
    rw [← zero_value]; exact num_le (by decide) (by decide) (by decide)
  exact recent_moves lateQuiet next.features next.row laid.row slot _ lateRecent
    (lt_of_le_of_lt prunePositive (lowChain_above criterion after.length (by omega)))

end AcornVerif.CurrentCreditHorizon
