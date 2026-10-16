import Kalman.Proofs.UncertaintyIntervalArithmetic

/-! Native variance inflation, square root, radius and outward endpoints.
All arithmetic/finite guards are proved from original bounded Float arguments. -/

namespace Kalman.Proofs.FloatUncertaintyIntervals

open Kalman.Definitions Kalman.Implementation.UncertaintyIntervals
  Kalman.Implementation.Correctness.UncertaintyIntervals
  Kalman.Definitions.Theorems.UncertaintyBounds
  Kalman.Proofs.UncertaintyIntervalArithmetic
  Flare.Binary64.Value

set_option maxHeartbeats 1800000

/-- Actual executable interval endpoints enclose every covered ideal value.
No square root or endpoint remains an unimplemented Real operation. -/
theorem bounds_enclose (mean variance covarianceError meanError multiplier : Float)
    (d : Domain mean variance covarianceError meanError multiplier)
    (referenceMean referenceVariance : ℝ)
    (meanAccuracy : |value mean - referenceMean| ≤ value meanError)
    (varianceAccuracy : referenceVariance ≤ value variance + value covarianceError)
    : Enclosure mean variance covarianceError meanError multiplier referenceMean
        referenceVariance := by
  have varianceBound : |value variance| ≤ 2 := by
    rw [abs_of_nonneg d.variance_lower]
    exact d.variance_upper
  have covarianceBound : |value covarianceError| ≤ 1 := by
    rw [abs_of_nonneg d.covariance_error_lower]
    exact d.covariance_error_upper
  have meanErrorBound : |value meanError| ≤ 2 := by
    rw [abs_of_nonneg d.mean_error_lower]
    exact d.mean_error_upper
  have multiplierBound : |value multiplier| ≤ 8 := by
    rw [abs_of_nonneg d.multiplier_lower]
    exact d.multiplier_upper
  have padBound : |value padding| ≤ 1 := by rw [padding_value]; norm_num
  let v1 := variance+covarianceError
  let inflated := v1+padding
  let root := inflated.sqrt
  let scaled := multiplier*root
  let r0 := scaled+meanError
  let radius := r0+padding
  let lower0 := mean-radius
  let upper0 := mean+radius
  let lower := lower0-padding
  let upper := upper0+padding
  have h1 := add_round variance covarianceError 2 1 d.variance_finite d.covariance_error_finite
    varianceBound covarianceBound (by norm_num)
  have sumBound : |value variance+value covarianceError| ≤ 3 :=
    (abs_add_le _ _).trans (by linarith)
  have v1Bound : |value v1| ≤ 4 :=
    (bound_from_error v1 _ 3 h1.2 sumBound).trans (by norm_num [roundingRadius])
  have h2 := add_round v1 padding 4 1 h1.1 padding_finite v1Bound padBound (by norm_num)
  have inflation : value variance+value covarianceError ≤ value inflated := by
    have a := (abs_le.mp h1.2).1
    have b := (abs_le.mp h2.2).1
    rw [padding_value] at b
    dsimp only [roundingRadius] at a b
    linarith
  have inflatedNonnegative : 0 ≤ value inflated := by
    linarith [d.variance_lower, d.covariance_error_lower]
  have inflatedUpper : value inflated ≤ 4 := by
    have a := (abs_le.mp h1.2).2
    have b := (abs_le.mp h2.2).2
    rw [padding_value] at b
    dsimp only [roundingRadius] at a b
    linarith [d.variance_upper, d.covariance_error_upper]
  have sqrtUpper : Real.sqrt (value inflated) ≤ 2 := by
    calc
      _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt inflatedUpper
      _ = 2 := by norm_num
  have sqrtResult := Flare.Binary64.Sqrt.sqrt_error_nearest inflated h2.1 inflatedNonnegative
  have rootError : |value root-Real.sqrt (value inflated)| ≤ roundingRadius := by
    apply sqrtResult.2.trans
    exact (mul_le_mul_of_nonneg_left sqrtUpper (by positivity)).trans (by norm_num [roundingRadius])
  have rootBound : |value root| ≤ 3 :=
    (bound_from_error root _ 2 rootError (by rwa [abs_of_nonneg (Real.sqrt_nonneg _)])).trans
      (by norm_num [roundingRadius])
  have h3 := mul_round multiplier root 8 3 d.multiplier_finite sqrtResult.1
    multiplierBound rootBound (by norm_num)
  have productBound : |value multiplier*value root| ≤ 24 := by
    rw [abs_mul]
    exact (mul_le_mul multiplierBound rootBound (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have scaledBound : |value scaled| ≤ 25 :=
    (bound_from_error scaled _ 24 h3.2 productBound).trans (by norm_num [roundingRadius])
  have h4 := add_round scaled meanError 25 2 h3.1 d.mean_error_finite
    scaledBound meanErrorBound (by norm_num)
  have sumRadiusBound : |value scaled+value meanError| ≤ 27 :=
    (abs_add_le _ _).trans (by linarith)
  have r0Bound : |value r0| ≤ 28 :=
    (bound_from_error r0 _ 27 h4.2 sumRadiusBound).trans (by norm_num [roundingRadius])
  have h5 := add_round r0 padding 28 1 h4.1 padding_finite r0Bound padBound (by norm_num)
  have radiusSumBound : |value r0+value padding| ≤ 29 :=
    (abs_add_le _ _).trans (by linarith)
  have radiusBound : |value radius| ≤ 30 :=
    (bound_from_error radius _ 29 h5.2 radiusSumBound).trans (by norm_num [roundingRadius])
  have multipliedRoot : value multiplier*Real.sqrt (value inflated)-8*roundingRadius
      ≤ value multiplier*value root := by
    have a := (abs_le.mp rootError).1
    have b := mul_le_mul_of_nonneg_left a d.multiplier_lower
    have c := mul_le_mul_of_nonneg_right d.multiplier_upper (by norm_num [roundingRadius] : (0 : ℝ) ≤ roundingRadius)
    dsimp only [roundingRadius] at a b c ⊢
    nlinarith
  have radiusLower : value multiplier*Real.sqrt (value inflated)+value meanError ≤ value radius := by
    have a := (abs_le.mp h3.2).1
    have b := (abs_le.mp h4.2).1
    have c := (abs_le.mp h5.2).1
    rw [padding_value] at c
    dsimp only [roundingRadius] at a b c multipliedRoot
    linarith
  have h6 := sub_round mean radius 1 30 d.mean_finite h5.1
    d.mean_bound radiusBound (by norm_num)
  have h7 := add_round mean radius 1 30 d.mean_finite h5.1
    d.mean_bound radiusBound (by norm_num)
  have lowExactBound : |value mean-value radius| ≤ 31 :=
    (abs_sub _ _).trans (by linarith [d.mean_bound])
  have upExactBound : |value mean+value radius| ≤ 31 :=
    (abs_add_le _ _).trans (by linarith [d.mean_bound])
  have low0Bound : |value lower0| ≤ 32 :=
    (bound_from_error lower0 _ 31 h6.2 lowExactBound).trans (by norm_num [roundingRadius])
  have up0Bound : |value upper0| ≤ 32 :=
    (bound_from_error upper0 _ 31 h7.2 upExactBound).trans (by norm_num [roundingRadius])
  have h8 := sub_round lower0 padding 32 1 h6.1 padding_finite low0Bound padBound (by norm_num)
  have h9 := add_round upper0 padding 32 1 h7.1 padding_finite up0Bound padBound (by norm_num)
  have lowerOutward : value lower ≤ value mean-value radius := by
    have a := (abs_le.mp h6.2).2
    have b := (abs_le.mp h8.2).2
    rw [padding_value] at b
    dsimp only [roundingRadius] at a b
    linarith
  have upperOutward : value mean+value radius ≤ value upper := by
    have a := (abs_le.mp h7.2).1
    have b := (abs_le.mp h9.2).1
    rw [padding_value] at b
    dsimp only [roundingRadius] at a b
    linarith
  let output : Interval := ⟨inflated, radius, lower, upper⟩
  have run : Kalman.Implementation.UncertaintyIntervals.bounds mean variance covarianceError
      meanError multiplier = .ok output := by
    simp only [Kalman.Implementation.UncertaintyIntervals.bounds,
      FloatDenseError.finite_ok _ h1.1, FloatDenseError.finite_ok _ h2.1,
      FloatDenseError.finite_ok _ sqrtResult.1, FloatDenseError.finite_ok _ h3.1,
      FloatDenseError.finite_ok _ h4.1, FloatDenseError.finite_ok _ h5.1,
      FloatDenseError.finite_ok _ h6.1, FloatDenseError.finite_ok _ h7.1,
      FloatDenseError.finite_ok _ h8.1, FloatDenseError.finite_ok _ h9.1,
      bind, Except.bind, pure, Except.pure, output, v1, inflated, root,
      scaled, r0, radius, lower0, upper0, lower, upper]
  refine ⟨output, run, h2.1, h5.1, h8.1, h9.1, varianceAccuracy.trans inflation,
    radiusLower, lowerOutward, upperOutward, ?_⟩
  intro truth covered
  have refRadius : value multiplier*Real.sqrt referenceVariance+value meanError ≤ value radius := by
    exact (add_le_add (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (varianceAccuracy.trans inflation)) d.multiplier_lower) (le_refl _)).trans radiusLower
  have truthRadius : |truth-value mean| ≤ value radius := by
    have hm : |referenceMean-value mean| ≤ value meanError := by
      simpa only [abs_sub_comm] using meanAccuracy
    exact (abs_sub_le truth referenceMean (value mean)).trans
      ((add_le_add covered hm).trans refRadius)
  have sides := abs_le.mp truthRadius
  exact ⟨by change value lower ≤ truth; linarith, by change truth ≤ value upper; linarith⟩

end Kalman.Proofs.FloatUncertaintyIntervals
