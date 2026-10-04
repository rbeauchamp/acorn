/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.Interface
import Acorn.Provenance

/-!
# D5 reward question and D1 prediction feedback, for every world

Two declared parts of the composed agent read no world type. The reward question
asks whether the delivered reward is positive; it heads the agent's prediction
layout before the signals a world supplies (D5). The previous step's predictions
return to the coder as bucketed words on their own channels (D1).

The feedback channels are the ones an interface reserves (`Interface.reserved`), and
a frame carries no word on a reserved channel (`Frame.clear`), so no word of a world
is on the channel of a feedback word (`feedbackWords_reserved`). This separates
channels, not features: the coder hashes each word into a slot, and two words on
different channels can still collide there, as any two hashed words can.
-/
namespace Acorn.Handcrafted
open Features

/-- Boolean predicates become the exact binary32 indicator words. -/
def indicator (value : Bool) : Binary32 := if value then .one else .zero

/-- The agent's reward question: whether the delivered reward word is positive. -/
def rewardSignal (reward : Binary32) : Binary32 := indicator (Binary32.zero.less reward)

/-- One cumulant per question of the agent's layout, evaluated once per frame: the
reward question, then the world's signals in their declared order. -/
def signalValues {interface : Interface} (frame : Frame interface) (reward : Binary32) :
    Cumulants interface.layout :=
  .cons (some .cumulants) (rewardSignal reward) frame.signals

/-- The exact division, saturation, multiply, floor and byte-cast recipe.
Standard native float operations, including floor and cast, retain their
explicit runtime trust boundary; the output bound does not assume their accuracy. -/
def predictionBucket (value horizon : Binary32) : Fin Acorn.FeatureConstants.predictionBuckets :=
  let frac := (value.div horizon).saturate .zero ⟨0x3f800000⟩
  let scaled := frac.mul (Binary32.ofUInt64 Acorn.FeatureConstants.predictionBuckets.toUInt64)
  let idx := (Float32.ofBits scaled.bits).floor.toUInt8.toNat
  ⟨min idx (Acorn.FeatureConstants.predictionBuckets - 1), by
    have : 0 < Acorn.FeatureConstants.predictionBuckets := by decide
    have := Nat.min_le_right idx (Acorn.FeatureConstants.predictionBuckets - 1)
    omega⟩

/-- Prediction feedback words in layout order, one per stored prediction, numbered
from `index`: the channel is `base` plus the position and the value is the
prediction's bucket at its own horizon. -/
def feedbackWords (base : UInt64) : List Discount → List Binary32 → Nat → List SensorWord
  | discount :: discounts, value :: values, index =>
    ⟨base + index.toUInt64, (predictionBucket value discount.horizon).val.toUInt64⟩ ::
      feedbackWords base discounts values (index + 1)
  | [], _, _ => []
  | _ :: _, [], _ => []

/-- Feedback has one word per question that has a stored prediction. -/
theorem feedbackWords_length (base : UInt64) (discounts : List Discount) (values : List Binary32)
    (index : Nat) :
    (feedbackWords base discounts values index).length = min discounts.length values.length := by
  induction discounts generalizing values index with
  | nil => simp [feedbackWords]
  | cons discount rest ih =>
    cases values with
    | nil => simp [feedbackWords]
    | cons value others => simp [feedbackWords, ih, Nat.succ_min_succ]

/-- The word at each position names that position's channel and buckets that position's
prediction at that position's horizon. -/
theorem feedbackWords_getElem (base : UInt64) (discounts : List Discount) (values : List Binary32)
    (index position : Nat) (inside : position < (feedbackWords base discounts values index).length)
    (horizon : position < discounts.length) (stored : position < values.length) :
    (feedbackWords base discounts values index)[position] =
      ⟨base + (index + position).toUInt64,
        (predictionBucket values[position] discounts[position].horizon).val.toUInt64⟩ := by
  induction discounts generalizing values index position with
  | nil => simp at horizon
  | cons discount rest ih =>
    cases values with
    | nil => simp at stored
    | cons value others =>
      cases position with
      | zero => simp [feedbackWords]
      | succ position =>
        simp only [feedbackWords, List.getElem_cons_succ]
        rw [ih others (index + 1) position (by simpa [feedbackWords] using inside)
          (by simpa using horizon) (by simpa using stored)]
        simp [Nat.add_assoc, Nat.add_comm 1 position]

/-- A channel offset by a position lies at most that position past its base, in
wrapping word arithmetic. -/
theorem channel_offset (base : UInt64) (position : Nat) :
    (base + position.toUInt64 - base).toNat ≤ position := by
  have bounded := base.toNat_lt
  have reduced := Nat.mod_le position (2 ^ 64)
  simp only [UInt64.toNat_sub, UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat']
  omega

/-- Every feedback word of the agent's layout is on a channel the interface reserves,
so it differs from the channel of every word a frame can carry. -/
theorem feedbackWords_reserved {interface : Interface} (values : List Binary32) :
    ∀ word ∈ feedbackWords interface.feedback interface.layout values 0,
      interface.reserved word.channel = true := by
  intro word member
  obtain ⟨position, inside, same⟩ := List.mem_iff_getElem.mp member
  have counted := feedbackWords_length interface.feedback interface.layout values 0
  have horizon : position < interface.layout.length := by omega
  have stored : position < values.length := by omega
  rw [feedbackWords_getElem interface.feedback interface.layout values 0 position inside horizon
    stored] at same
  subst same
  have offset := channel_offset interface.feedback (0 + position)
  simp only [Interface.reserved, decide_eq_true_eq]
  omega

end Acorn.Handcrafted
