import Acorn.FeatureConstants
import Acorn.Interface
import Acorn.Provenance

namespace Acorn.Handcrafted
open Features

def indicator (value : Bool) : Binary32 := if value then .one else .zero

def rewardSignal (reward : Binary32) : Binary32 := indicator (Binary32.zero.less reward)

def signalValues {interface : Interface} (frame : Frame interface) (reward : Binary32) :
    Cumulants interface.layout :=
  .cons (some .cumulants) (rewardSignal reward) frame.signals

def predictionBucket (value horizon : Binary32) : Fin Acorn.FeatureConstants.predictionBuckets :=
  let frac := (value.div horizon).saturate .zero ⟨0x3f800000⟩
  let scaled := frac.mul (Binary32.ofUInt64 Acorn.FeatureConstants.predictionBuckets.toUInt64)
  let idx := (Float32.ofBits scaled.bits).floor.toUInt8.toNat
  ⟨min idx (Acorn.FeatureConstants.predictionBuckets - 1), by
    have : 0 < Acorn.FeatureConstants.predictionBuckets := by decide
    have := Nat.min_le_right idx (Acorn.FeatureConstants.predictionBuckets - 1)
    omega⟩

def feedbackWordsCosted (base : UInt64) :
    List Discount → List Binary32 → Nat → Costed (List SensorWord)
  | discount :: discounts, value :: values, index =>
    let word : SensorWord :=
      ⟨base + index.toUInt64, (predictionBucket value discount.horizon).val.toUInt64⟩
    Costed.charge .feedbackWord do
      let tail ← feedbackWordsCosted base discounts values (index + 1)
      Costed.op .visit (word :: tail)
  | [], _, _ => Costed.op .visit []
  | _ :: _, [], _ => Costed.op .visit []

def feedbackWords (base : UInt64) (discounts : List Discount) (values : List Binary32)
    (index : Nat) : List SensorWord :=
  (feedbackWordsCosted base discounts values index).val

theorem feedbackWords_cons_cons (base : UInt64) (discount : Discount) (discounts : List Discount)
    (value : Binary32) (values : List Binary32) (index : Nat) :
    feedbackWords base (discount :: discounts) (value :: values) index =
      ⟨base + index.toUInt64, (predictionBucket value discount.horizon).val.toUInt64⟩ ::
        feedbackWords base discounts values (index + 1) := rfl

theorem feedbackWords_nil (base : UInt64) (values : List Binary32) (index : Nat) :
    feedbackWords base [] values index = [] := by
  cases values <;> rfl

theorem feedbackWords_cons_nil (base : UInt64) (discount : Discount) (discounts : List Discount)
    (index : Nat) : feedbackWords base (discount :: discounts) [] index = [] := rfl

theorem feedbackWords_length (base : UInt64) (discounts : List Discount) (values : List Binary32)
    (index : Nat) :
    (feedbackWords base discounts values index).length = min discounts.length values.length := by
  induction discounts generalizing values index with
  | nil => simp [feedbackWords_nil]
  | cons discount rest ih =>
    cases values with
    | nil => simp [feedbackWords_cons_nil]
    | cons value others => simp [feedbackWords_cons_cons, ih, Nat.succ_min_succ]

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
      | zero => simp [feedbackWords_cons_cons]
      | succ position =>
        simp only [feedbackWords_cons_cons, List.getElem_cons_succ]
        rw [ih others (index + 1) position (by simpa [feedbackWords_cons_cons] using inside)
          (by simpa using horizon) (by simpa using stored)]
        simp [Nat.add_assoc, Nat.add_comm 1 position]

theorem channel_offset (base : UInt64) (position : Nat) :
    (base + position.toUInt64 - base).toNat ≤ position := by
  have bounded := base.toNat_lt
  have reduced := Nat.mod_le position (2 ^ 64)
  simp only [UInt64.toNat_sub, UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat']
  omega

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
