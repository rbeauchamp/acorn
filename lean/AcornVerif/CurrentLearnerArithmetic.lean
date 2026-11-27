import AcornVerif.CurrentState
import AcornVerif.CurrentPrediction

open Acorn
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder AcornVerif.CurrentDivision AcornVerif.CurrentPrediction

namespace AcornVerif.CurrentLearnerArithmetic

theorem mul32_decoded (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (normal : ModelNormalized Format.binary32
      (UnpackedFloat.mul Format.binary32 (decoded32 left) (decoded32 right)))
    (fits : ModelFits Format.binary32
      (UnpackedFloat.mul Format.binary32 (decoded32 left) (decoded32 right))) :
    decoded32 (left.mul right) =
      UnpackedFloat.mul Format.binary32 (decoded32 left) (decoded32 right) := by
  change unpack Format.binary32 (pack Format.binary32
    (UnpackedFloat.mul Format.binary32 (Float32.Model.ofBits left.bits).unpack
      (Float32.Model.ofBits right.bits).unpack)) = _
  rw [model_ofBits32_decoded left hl, model_ofBits32_decoded right hr]
  exact model_unpack_pack_normalized _ _ normal fits

theorem div32_decoded (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (normal : ModelNormalized Format.binary32
      (UnpackedFloat.div Format.binary32 (decoded32 left) (decoded32 right)))
    (fits : ModelFits Format.binary32
      (UnpackedFloat.div Format.binary32 (decoded32 left) (decoded32 right))) :
    decoded32 (left.div right) =
      UnpackedFloat.div Format.binary32 (decoded32 left) (decoded32 right) := by
  change unpack Format.binary32 (pack Format.binary32
    (UnpackedFloat.div Format.binary32 (Float32.Model.ofBits left.bits).unpack
      (Float32.Model.ofBits right.bits).unpack)) = _
  rw [model_ofBits32_decoded left hl, model_ofBits32_decoded right hr]
  exact model_unpack_pack_normalized _ _ normal fits

theorem local32_fits (value : UnpackedFloat) (exactValue : ℚ)
    (normal : ModelNormalized Format.binary32 value) (bound : |exactValue| ≤ 4)
    (error : |unpackedValue value - exactValue| ≤ 1) : ModelFits Format.binary32 value := by
  apply model_fits_of_value_bound Format.binary32 value
    (model_normalized_finite _ _ normal) 3 (by decide)
  have triangle := abs_add_le (unpackedValue value - exactValue) exactValue
  rw [sub_add_cancel] at triangle
  norm_num
  linarith only [triangle, bound, error]

theorem round_nonnegative (spec : Format) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) :
    0 ≤ unpackedValue (roundWithAccuracy spec .positive mantissa exponent accuracy) := by
  rw [model_round_accuracy_value]
  simp only [signCoefficient, one_mul]
  positivity

theorem finite_nonnegative_sign (sign : Sign) (mantissa : Nat) (exponent : Int)
    (positive : 0 < mantissa)
    (nonnegative : 0 ≤ unpackedValue (.finite sign mantissa exponent positive)) :
    sign = .positive := by
  cases sign with
  | positive => rfl
  | negative =>
    have magnitude : (0:ℚ) < mantissa * (2:ℚ)^exponent := by positivity
    simp only [unpackedValue, signCoefficient, neg_one_mul] at nonnegative
    nlinarith only [magnitude, nonnegative]

theorem model_mul_nonnegative (spec : Format) (left right : UnpackedFloat)
    (hl : ModelNormalized spec left) (hr : ModelNormalized spec right)
    (pl : 0 ≤ unpackedValue left) (pr : 0 ≤ unpackedValue right) :
    0 ≤ unpackedValue (UnpackedFloat.mul spec left right) := by
  cases left with
  | notANumber => contradiction
  | infinity s => contradiction
  | zero s => cases right <;> simp_all [ModelNormalized, UnpackedFloat.mul, unpackedValue]
  | finite sl ml el lp =>
    cases right with
    | notANumber => contradiction
    | infinity s => contradiction
    | zero s => exact le_refl 0
    | finite sr mr er rp =>
      have ls := finite_nonnegative_sign sl ml el lp pl
      have rs := finite_nonnegative_sign sr mr er rp pr
      subst sl
      subst sr
      exact round_nonnegative spec _ _ _

theorem model_div_nonnegative (spec : Format) (left right : UnpackedFloat)
    (hl : ModelNormalized spec left) (hr : ModelNormalized spec right)
    (pl : 0 ≤ unpackedValue left) (pr : 0 < unpackedValue right) :
    0 ≤ unpackedValue (UnpackedFloat.div spec left right) := by
  cases right with
  | notANumber => contradiction
  | infinity s => contradiction
  | zero s => exact False.elim ((lt_irrefl 0) pr)
  | finite sr mr er rp =>
    cases left with
    | notANumber => contradiction
    | infinity s => contradiction
    | zero s => exact le_refl 0
    | finite sl ml el lp =>
      have ls := finite_nonnegative_sign sl ml el lp pl
      have rs := finite_nonnegative_sign sr mr er rp pr.le
      subst sl
      subst sr
      exact round_nonnegative spec _ _ _

theorem mul32_nonnegative_bound (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (pl : 0 ≤ numerical32 left) (pr : 0 ≤ numerical32 right)
    (bound : numerical32 left * numerical32 right ≤ 4) :
    (left.mul right).Finite ∧ 0 ≤ numerical32 (left.mul right) ∧
      numerical32 (left.mul right) ≤ 5 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have magnitude : |numerical32 left * numerical32 right| ≤ 4 := by
    simpa only [abs_of_nonneg (mul_nonneg pl pr)] using bound
  have operation := model_mul_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 2 (by norm_num [numerical32] at magnitude ⊢; exact magnitude)
  have error : |unpackedValue (UnpackedFloat.mul Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left * numerical32 right| ≤ 1 := by
    apply le_trans operation.2
    norm_num [Format.mantissaBits, Format.minExponent]
  have decoded := mul32_decoded left right hl hr operation.1
    (local32_fits _ _ operation.1 magnitude error)
  refine ⟨?_, ?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · change 0 ≤ unpackedValue (decoded32 (left.mul right))
    rw [decoded]
    exact model_mul_nonnegative _ _ _ ln rn pl pr
  · have upper := (abs_le.mp error).2
    change unpackedValue (decoded32 (left.mul right)) ≤ 5
    rw [decoded]
    linarith only [upper, bound]

theorem div32_nonnegative_bound (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (pl : 0 < numerical32 left) (order : numerical32 left ≤ numerical32 right) :
    (left.div right).Finite ∧ 0 ≤ numerical32 (left.div right) ∧
      numerical32 (left.div right) ≤ 2 := by
  have pr := lt_of_lt_of_le pl order
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have bound : |numerical32 left / numerical32 right| ≤ 1 := by
    rw [abs_of_pos (div_pos pl pr)]
    exact (div_le_one pr).mpr order
  have operation := model_div_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn (ne_of_gt pr) 0 (by simpa only [numerical32, zpow_zero] using bound)
  have error : |unpackedValue (UnpackedFloat.div Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left / numerical32 right| ≤ 1 := by
    apply le_trans operation.2
    norm_num [Format.mantissaBits, Format.minExponent]
  have decoded := div32_decoded left right hl hr operation.1
    (local32_fits _ _ operation.1 (le_trans bound (by norm_num)) error)
  refine ⟨?_, ?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · change 0 ≤ unpackedValue (decoded32 (left.div right))
    rw [decoded]
    exact model_div_nonnegative _ _ _ ln rn pl.le pr
  · have upper := (abs_le.mp error).2
    have quotient := (abs_le.mp bound).2
    change unpackedValue (decoded32 (left.div right)) ≤ 2
    rw [decoded]
    linarith only [upper, quotient]

theorem word_unit_interval (word : Binary32) (finite : word.Finite)
    (bound : word.bits.toNat ≤ 0x3f800000) :
    0 ≤ numerical32 word ∧ numerical32 word ≤ 1 := by
  have sign : word.bits &&& 0x80000000 = 0 := by
    apply UInt32.toNat.inj
    rw [word32_sign_exact, Nat.div_eq_of_lt (by omega), Nat.zero_mul]
    rfl
  have magnitude : word.magnitude ≤ 0x3f800000 := by
    exact le_trans Nat.and_le_left bound
  have key : word.key = (word.magnitude : Int) := by
    simp [Binary32.key_eq_negative, Binary32.negative, sign]
  let unit : Binary32 := ⟨0x3f800000⟩
  have unitValue : numerical32 unit = 1 := by
    dsimp only [unit]
    change (1:ℚ) * 8388608 * (2:ℚ)^(-23:Int) = 1
    norm_num
  have lower := (numerical32_order .zero word (by decide) finite).mpr
    (by rw [key]; change (0:Int) ≤ _; omega)
  have upper := (numerical32_order word unit finite (by decide)).mpr
    (by rw [key]; dsimp only [unit]; change (word.magnitude:Int) ≤ 0x3f800000; omega)
  exact ⟨lower, by rwa [unitValue] at upper⟩

theorem alpha_numeric {config : Config} {rails : StepSizeRails config}
    (beta : LogStepSize rails) :
    beta.alpha.Finite ∧ 0 ≤ numerical32 beta.alpha ∧ numerical32 beta.alpha ≤ 1 := by
  have contract := CurrentState.log_step_alpha_unit config rails beta
  exact ⟨contract.1, word_unit_interval beta.alpha contract.1 contract.2⟩

theorem alpha_sum_finite {config : Config} {rails : StepSizeRails config}
    (betas : List (LogStepSize rails)) :
    (Binary32.sumFrom .zero (betas.map (·.alpha))).Finite := by
  apply (prediction_sumFrom_bound 0 .zero (betas.map (·.alpha)) (by decide)
    (by change |(0:ℚ)| ≤ (0:ℚ)*256; norm_num) ?_).1
  intro word member
  obtain ⟨beta, _, rfl⟩ := List.mem_map.mp member
  have contract := alpha_numeric beta
  exact ⟨contract.1, by rw [abs_of_nonneg contract.2.1]; linarith only [contract.2.2]⟩

theorem eta_numeric (config : Config) : config.eta.Finite ∧ 0 < numerical32 config.eta := by
  have raw : config.eta.Finite ∧ 0 < config.eta.key := by
    rcases config with ⟨role, rule⟩
    cases role <;> simp only [Config.eta] <;> decide
  have order := (numerical32_strict_order .zero config.eta (by decide) raw.1).mpr raw.2
  exact ⟨raw.1, order⟩

set_option maxRecDepth 32768 in
theorem word_half_interval (word : Binary32) (finite : word.Finite)
    (lowerKey : 0 ≤ word.key) (upperKey : word.key ≤ 0x3f000000) :
    0 ≤ numerical32 word ∧ numerical32 word ≤ 1/2 := by
  let half : Binary32 := ⟨0x3f000000⟩
  have halfValue : numerical32 half = 1/2 := by
    dsimp only [half]
    change (1:ℚ)*8388608*(2:ℚ)^(-24:Int) = 1/2
    norm_num
  have lower := (numerical32_order .zero word (by decide) finite).mpr lowerKey
  have halfKey : half.key = (0x3f000000:Int) := by dsimp only [half]; rfl
  have halfFinite : half.Finite := by decide
  have upper := (numerical32_order word half finite halfFinite).mpr
    (by rw [halfKey]; exact upperKey)
  exact ⟨lower, by rwa [halfValue] at upper⟩

theorem epsilon_numeric (config : Config) :
    config.epsilon.Finite ∧ 0 ≤ numerical32 config.epsilon ∧
      numerical32 config.epsilon ≤ 1/2 := by
  have raw : config.epsilon.Finite ∧ 0 ≤ config.epsilon.key ∧
      config.epsilon.key ≤ 0x3f000000 := by
    simp only [Config.epsilon]
    decide
  exact ⟨raw.1, word_half_interval config.epsilon raw.1 raw.2.1 raw.2.2⟩

theorem denominator_numeric (config : Config) (rate : Binary32) (finite : rate.Finite) :
    let denominator := if config.eta.less rate then rate else config.eta
    denominator.Finite ∧ numerical32 config.eta ≤ numerical32 denominator := by
  dsimp only
  have eta := eta_numeric config
  split
  · rename_i overshoot
    have order := numerical32_less config.eta rate eta.1 finite
    rw [order] at overshoot
    exact ⟨finite, (of_decide_eq_true overshoot).le⟩
  · rename_i noOvershoot
    exact ⟨eta.1, le_refl _⟩

theorem trace_increment_numeric {config : Config} {rails : StepSizeRails config}
    (beta : LogStepSize rails) (rate : Binary32) (finite : rate.Finite) :
    let denominator := if config.eta.less rate then rate else config.eta
    let increment := (config.eta.div denominator).mul beta.alpha
    increment.Finite ∧ 0 ≤ numerical32 increment ∧ numerical32 increment ≤ 5 := by
  have eta := eta_numeric config
  have denominator := denominator_numeric config rate finite
  have scale := div32_nonnegative_bound config.eta _ eta.1 denominator.1 eta.2 denominator.2
  have alpha := alpha_numeric beta
  apply mul32_nonnegative_bound _ _ scale.1 alpha.1 scale.2.1 alpha.2.1
  nlinarith only [scale.2.1, scale.2.2, alpha.2.1, alpha.2.2]

theorem mul32_zero (word : Binary32) (finite : word.Finite) : (word.mul .zero).key = 0 := by
  have zeroFinite : (Binary32.zero).Finite := by decide
  have zeroDecoded : decoded32 .zero = .zero .positive := rfl
  have normal := (model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)).1
  have product : ∃ sign, UnpackedFloat.mul Format.binary32 (decoded32 word) (decoded32 .zero) =
      .zero sign := by
    rw [zeroDecoded]
    change ModelNormalized Format.binary32 (decoded32 word) at normal
    cases decoded : decoded32 word with
    | notANumber => rw [decoded] at normal; contradiction
    | infinity sign => rw [decoded] at normal; contradiction
    | zero sign => exact ⟨_, rfl⟩
    | finite sign mantissa exponent positive => exact ⟨_, rfl⟩
  obtain ⟨sign, product⟩ := product
  have decoded := mul32_decoded word .zero finite zeroFinite (by rw [product]; trivial)
    (by rw [product]; trivial)
  rw [product] at decoded
  have resultFinite : (word.mul .zero).Finite :=
    (model_decoded32_finite _).mp (by rw [decoded]; rfl)
  have value : numerical32 (word.mul .zero) = numerical32 .zero := by
    simp only [numerical32, decoded, zeroDecoded, unpackedValue]
  have below := (numerical32_order _ _ resultFinite zeroFinite).mp (le_of_eq value)
  have above := (numerical32_order _ _ zeroFinite resultFinite).mp (le_of_eq value.symm)
  have zeroKey : (Binary32.zero).key = 0 := by decide
  omega

theorem pruning_threshold_numeric (config : Config) (reference : Binary32)
    (finite : reference.Finite) (nonnegative : 0 ≤ numerical32 reference)
    (bound : numerical32 reference ≤ 5) :
    (reference.mul config.epsilon).Finite ∧ 0 ≤ (reference.mul config.epsilon).key := by
  have epsilon := epsilon_numeric config
  have product := mul32_nonnegative_bound reference config.epsilon finite epsilon.1
    nonnegative epsilon.2.1 (by nlinarith only [bound, nonnegative, epsilon.2.1, epsilon.2.2])
  exact ⟨product.1, (numerical32_order .zero _ (by decide) product.1).mp product.2.1⟩

end AcornVerif.CurrentLearnerArithmetic
