import Kalman.Proofs.FloatUniformTracking
import Kalman.Proofs.FloatUncertaintyIntervals
import Kalman.Implementation.Correctness.TrackingIntervals

namespace Kalman.Proofs.FloatTrackingIntervals

open Kalman.Definitions Kalman.Implementation.UncertaintyIntervals
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.ConstantVelocityTracking
  Kalman.Implementation.Correctness.TrackingIntervals
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Flare.Binary64.Value

set_option maxHeartbeats 1000000

theorem allowance_value : value trackingMeanAllowance = (2 : ℝ) ^ (-29 : Int) := by
  change (4503599627370496 : ℝ)*(2 : ℝ)^(-81 : Int) = _
  norm_num

/-- Actual native interval endpoints follow from the proved original-input
tracking accuracy, including mean error and every endpoint operation. -/
theorem horizon_intervals : HorizonIntervals := by
  intro measurements initial horizon d t ht
  obtain ⟨output, run, invariant, _⟩ :=
    FloatConstantVelocityHorizon.weighted_horizon measurements initial horizon d t ht
  obtain ⟨accurate, runAccurate, error⟩ :=
    FloatUniformTracking.horizon_accuracy measurements initial horizon d t ht
  have same : accurate = output := Except.ok.inj (runAccurate.symm.trans run)
  rw [same] at error
  have radiusCap := FloatConstantVelocityTracking.envelope_bound t (ht.trans d.horizon_bound)
  have meanCap (i : Fin 2) : |value (output.mean.getD i.val 0.0)| ≤ 1 := by
    have hx := invariant.mean_envelope.2.1
    have hv := invariant.mean_envelope.2.2
    simp only [Pi.zero_apply, sub_zero] at hx hv
    fin_cases i
    · change |(state 2 output).mean 0| ≤ 1
      linarith
    · change |(state 2 output).mean 1| ≤ 1
      linarith
  have varianceCap (i : Fin 2) :
      0 ≤ value (output.covariance.getD (i.val*2+i.val) 0.0) ∧
      value (output.covariance.getD (i.val*2+i.val) 0.0) ≤ 2 := by
    change 0 ≤ matrix 2 2 output.covariance i i ∧ matrix 2 2 output.covariance i i ≤ 2
    rw [invariant.covariance_words, FloatConstantVelocityStorage.posterior_decode]
    fin_cases i <;> norm_num [posteriorCovariance]
  have covarianceFinite : output.covariance.all Float.isFinite = true := by
    rw [invariant.covariance_words]
    exact FloatConstantVelocityStorage.posterior_finite
  refine ⟨output, run, ?_⟩
  intro i multiplier finite nonnegative cap
  apply FloatUncertaintyIntervals.bounds_enclose
  · exact ⟨Flare.Matrix.Storage.getD_finite _ _ invariant.mean_finite,
      Flare.Matrix.Storage.getD_finite _ _ covarianceFinite,
      by decide +kernel, by decide +kernel, finite, meanCap i,
      (varianceCap i).1, (varianceCap i).2,
      by norm_num [Flare.Binary64.Arithmetic.zero_value],
      by norm_num [Flare.Binary64.Arithmetic.zero_value],
      by rw [allowance_value]; positivity, by rw [allowance_value]; norm_num,
      nonnegative, cap⟩
  · simpa only [allowance_value, state, vector] using error.2.2 i
  · have h := (abs_le.mp (error.1.2 i i)).1
    change _ ≤ value (output.covariance.getD (i.val*2+i.val) 0.0)+value (0.0 : Float)
    rw [Flare.Binary64.Arithmetic.zero_value]
    simp only [neg_zero] at h
    change _ ≤ (state 2 output).covariance i i + 0
    linarith

end Kalman.Proofs.FloatTrackingIntervals
