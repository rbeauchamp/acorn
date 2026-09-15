/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentPortable
import Acorn.State
/-!
# Closed configuration and derived-rate contracts

The complete discount and role domains supply their own numeric premises.
Storage legality and immutable rail identities then connect the public
exponential bound to the actual recovered step size. Raw transient registers
receive no bound from these projected-state contracts.
-/
open Acorn
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentPortable
namespace AcornVerif.CurrentState

/-- Every current discount is a strict positive contraction with a finite horizon greater than
one. The entire closed domain supplies the raw ordering premises. -/
theorem discount_numeric_contract (discount : Discount) :
    discount.gamma.Finite ∧ 0 < numerical32 discount.gamma ∧
      numerical32 discount.gamma < 1 ∧ discount.horizon.Finite ∧
      1 < numerical32 discount.horizon := by
  have raw : discount.gamma.Finite ∧ 0 < discount.gamma.key ∧
      discount.gamma.key < 0x3f800000 ∧ discount.horizon.Finite ∧
      0x3f800000 < discount.horizon.key := by cases discount <;> decide
  let unit : Binary32 := ⟨0x3f800000⟩
  have unitFinite : unit.Finite := by decide
  have zeroFinite : Binary32.zero.Finite := by decide
  have unitKey : unit.key = (0x3f800000:Int) := by dsimp only [unit]; rfl
  have zeroKey : Binary32.zero.key = 0 := rfl
  have unitValue : numerical32 unit = 1 := by
    dsimp only [unit]
    change (1:ℚ)*8388608*(2:ℚ)^(-23:Int) = _
    norm_num
  have zeroValue : numerical32 .zero = 0 := rfl
  have positive := (numerical32_strict_order .zero discount.gamma zeroFinite raw.1).mpr
    (by rw [zeroKey]; exact raw.2.1)
  have contraction := (numerical32_strict_order discount.gamma unit raw.1 unitFinite).mpr
    (by rw [unitKey]; exact raw.2.2.1)
  have horizon := (numerical32_strict_order unit discount.horizon unitFinite raw.2.2.2.1).mpr
    (by rw [unitKey]; exact raw.2.2.2.2)
  rw [zeroValue] at positive
  rw [unitValue] at contraction horizon
  exact ⟨raw.1,positive,contraction,raw.2.2.2.1,horizon⟩

set_option maxRecDepth 8192 in
/-- The actual upper logarithmic rail is nonpositive throughout the closed role domain. -/
theorem config_log_rail_nonpositive (config : Config) : (Portable.ln config.eta).key ≤ 0 := by
  rcases config with ⟨role,rule⟩
  cases role <;> simp only [Config.eta] <;> decide

/-- Every legally stored log step recovers a finite positive-sign value at most one through the
actual public exponential, including saturation. -/
theorem log_step_alpha_unit (config : Config) (rails : StepSizeRails config)
    (stored : LogStepSize rails) :
    stored.alpha.Finite ∧ stored.alpha.bits.toNat ≤ 0x3f800000 := by
  have upper := stored.legal.2.2
  rw [rails.upperIdentity] at upper
  have key : stored.value.key ≤ 0 := le_trans upper (config_log_rail_nonpositive config)
  have zeroKey : Binary32.zero.key = 0 := rfl
  have zeroValue : numerical32 .zero = 0 := rfl
  have nonpositive := (numerical32_order stored.value .zero stored.legal.1 (by decide)).mpr
    (by rw [zeroKey]; exact key)
  rw [zeroValue] at nonpositive
  have word := exp_nonpositive_unit stored.value stored.legal.1 nonpositive
  refine ⟨?_,word⟩
  change (Portable.exp stored.value).bits.toNat &&& (2^31-1) < 0x7f800000
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by omega)

end AcornVerif.CurrentState
