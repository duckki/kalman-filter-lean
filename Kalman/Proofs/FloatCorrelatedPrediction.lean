import Kalman.Proofs.TrackingCovarianceTube
import Kalman.Implementation.Correctness.CorrelatedTracking

/-! Original-word prediction domains and the reached correction domain for a
nonstationary covariance neighborhood with bounded model variation. -/

namespace Kalman.Proofs.FloatCorrelatedPrediction

open Matrix hiding transpose
open Kalman.Definitions Kalman.Implementation.LinearAlgebra
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.CorrelatedTracking
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.TrackingCovarianceTube
  Kalman.Definitions.Theorems.RecursionSensitivity
  Kalman.Proofs.TrackingCovarianceTube Kalman.Proofs.ErrorPropagation
  Kalman.Proofs.FloatJosephPositionArithmetic
  Flare.Binary64.Value

set_option maxHeartbeats 1800000

/-- Validator guards follow from original finite shaped state storage. -/
theorem state_valid (r : ℝ) (s : Input.State) (d : StateDomain r s)
    : s.validate 2 = .ok () := by
  have shape : (s.mean.size == 2 && s.covariance.size == 2*2) = true := by
    simp [d.mean_size, d.covariance_size]
  have finite : (s.mean.all Float.isFinite && s.covariance.all Float.isFinite) = true := by
    simp only [d.mean_finite, d.covariance_finite, Bool.true_and]
  simp [Input.State.validate, shape, finite, pure, Except.pure]

theorem covariance_cap (r : ℝ) (s : Input.State) (d : StateDomain r s)
    : ∀ i j, |matrix 2 2 s.covariance i j| ≤ 2 :=
  near_bound _ _ _ 1 2
    (tube_entries _ d.covariance_tube)
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [posteriorCovariance])
    (by norm_num [radius])

theorem process_cap (input : Input.Model) (dt : Float) (d : ModelDomain input dt)
    : ∀ i j, |matrix 2 2 input.processNoise i j| ≤ 2 :=
  near_bound _ _ _ 1 2 d.process_close
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [trackingModel])
    (by norm_num [parameterRadius])

/-- Full original-input prediction conditions, including positive covariance,
are consequences of the neighborhood and model envelope. -/
theorem prediction_domain (input : Input.Model) (dt : Float) (s : Input.State) (r : ℝ)
    (d : ModelDomain input dt) (hs : StateDomain r s) (hr : r ≤ 3 / 16)
    : Kalman.Implementation.Correctness.ConstantVelocityPrediction.Domain input s dt := by
  refine ⟨d.state_dimension, d.measurement_dimension, d.input_valid,
    state_valid r s hs, d.transition_words, d.dt_finite, d.dt_bound,
    hs.covariance_finite, hs.mean_finite, d.process_finite,
    covariance_cap r s hs, ?_, process_cap input dt d, ?_, d.process_psd⟩
  · intro i j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    have hx := hs.mean_envelope.2.1
    have hv := hs.mean_envelope.2.2
    simp only [Pi.zero_apply, sub_zero] at hx hv
    fin_cases i
    · change |(state 2 s).mean 0| ≤ 1
      linarith
    · change |(state 2 s).mean 1| ≤ 1
      linarith
  · exact (Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ (1/8)
      (by norm_num) (tube_floor _ hs.covariance_tube)).posSemidef

/-- Parameter perturbations change the exact prediction by at most `18*theta`.
The native prediction error is added, not silently absorbed into the model. -/
theorem nominal_prediction_accuracy (input : Input.Model) (dt : Float)
    (s prior : Input.State) (r : ℝ) (d : ModelDomain input dt) (hs : StateDomain r s)
    (hr : r ≤ 3 / 16)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          input s prior)
    : EntrywiseWithin ((2 : ℝ) ^ (-36 : Int) + 18 * parameterRadius)
        (matrix 2 2 prior.covariance)
        (trackingModel.transition * matrix 2 2 s.covariance
            * trackingModel.transition.transpose
          + trackingModel.processNoise) := by
  have pd := prediction_domain input dt s r d hs hr
  have fdecode := FloatConstantVelocityPrediction.transition_decode input s dt pd
  have fb : ∀ i j, |matrix 2 2 input.transition i j| ≤ 1 := by
    rw [fdecode]
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Kalman.Definitions.Theorems.ConstantVelocity.transition, d.dt_bound]
  have f0 : ∀ i j, |trackingModel.transition i j| ≤ 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [trackingModel]
  have pc := covariance_cap r s hs
  have fp := within_mul_right d.transition_close (matrix 2 2 s.covariance)
    (by norm_num : (0 : ℝ) ≤ 2) pc
  have first := within_mul_right fp (matrix 2 2 input.transition).transpose
    (by norm_num : (0 : ℝ) ≤ 1) (fun i j => fb j i)
  have second := within_mul_left (trackingModel.transition * matrix 2 2 s.covariance)
    (within_transpose d.transition_close) (by norm_num : (0 : ℝ) ≤ 4)
    (by intro i j; exact (product_magnitude _ _ 1 2 f0 pc i j).trans (by norm_num))
  have changed := within_add (within_trans first second) d.process_close
  have native := hp.2.2.2.2.2.1.1
  change EntrywiseWithin ((2 : ℝ)^(-36 : Int)) (matrix 2 2 prior.covariance)
    (matrix 2 2 input.transition * matrix 2 2 s.covariance *
      (matrix 2 2 input.transition).transpose + matrix 2 2 input.processNoise) at native
  have total := within_trans native changed
  refine ⟨by norm_num [parameterRadius], ?_⟩
  intro i j
  exact (total.2 i j).trans (by norm_num [parameterRadius])

/-- Total reached-prior distance from the nominal prior. The first term
comes from a covariance neighborhood, not from exact stored covariance words. -/
theorem prior_accuracy (input : Input.Model) (dt : Float) (s prior : Input.State) (r : ℝ)
    (d : ModelDomain input dt) (hs : StateDomain r s) (hr : r ≤ 3 / 16)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          input s prior)
    : EntrywiseWithin (6 * radius + (2 : ℝ) ^ (-36 : Int) + 18 * parameterRadius)
        (matrix 2 2 prior.covariance) priorCovariance := by
  have h := within_trans (nominal_prediction_accuracy input dt s prior r d hs hr hp)
    (predicted_tube_entries _ hs.covariance_tube)
  convert h using 1
  ring

/-- Prediction derives every premise of the existing checked Joseph
correction theorem, including the prior floor and mean cap. -/
theorem correction_domain (input : Input.Model) (dt : Float) (s prior : Input.State)
    (r : ℝ) (d : ModelDomain input dt) (hs : StateDomain r s) (hr : r ≤ 3 / 16)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          input s prior)
    : Kalman.Implementation.Correctness.JosephPositionCorrection.Domain input prior := by
  have error := prior_accuracy input dt s prior r d hs hr hp
  have lower := Flare.Analysis.EntrywiseError.lower_bound_of_error _ _ (17/32)
    _ nominal_prior_floor hp.2.2.2.2.2.2 error
  have floor : (matrix 2 2 prior.covariance - (1/2 : ℝ) • 1).PosSemidef := by
    have extra := (PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num [radius, parameterRadius] : (0 : ℝ) ≤ 17/32 -
        2*(6*radius+(2 : ℝ)^(-36 : Int)+18*parameterRadius) - 1/2)
    convert lower.add extra using 1
    norm_num
    module
  have cap := near_bound prior.covariance _ _ (9/8) 2 error
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [priorCovariance])
    (by norm_num [radius, parameterRadius])
  have noiseError : |value (input.measurementNoise.getD 0 0.0)-1| ≤ parameterRadius := by
    have h := d.noise_close.2 0 0
    change |value (input.measurementNoise.getD 0 0.0)-1| ≤ parameterRadius at h
    exact h

  have noiseUpper : value (input.measurementNoise.getD 0 0.0) ≤ 3/2 := by
    have h := (abs_le.mp noiseError).2
    calc
      _ ≤ 1 + parameterRadius := by linarith
      _ ≤ 3 / 2 := by norm_num [parameterRadius]
  have meanCap : ∀ i, i < 2 → |value (prior.mean.getD i 0.0)| ≤ 1 := by
    have pd := prediction_domain input dt s r d hs hr
    have fd := FloatConstantVelocityPrediction.transition_decode input s dt pd
    have meanError (i : Fin 2) : |(state 2 prior).mean i -
        (Kalman.Definitions.Theorems.ConstantVelocity.transition (value dt) *ᵥ (state 2 s).mean) i|
        ≤ (2 : ℝ)^(-41 : Int) := by
      have he := hp.2.2.2.2.2.1.2.2 i
      change |(state 2 prior).mean i - (matrix 2 2 input.transition *ᵥ (state 2 s).mean) i| ≤ _ at he
      rw [fd] at he
      exact he
    have hx := hs.mean_envelope.2.1
    have hv := hs.mean_envelope.2.2
    simp only [Pi.zero_apply, sub_zero] at hx hv
    have m0 : (Kalman.Definitions.Theorems.ConstantVelocity.transition (value dt) *ᵥ
        (state 2 s).mean) 0 = (state 2 s).mean 0 + value dt*(state 2 s).mean 1 := by
      simp [Kalman.Definitions.Theorems.ConstantVelocity.transition, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two]
    have m1 : (Kalman.Definitions.Theorems.ConstantVelocity.transition (value dt) *ᵥ
        (state 2 s).mean) 1 = (state 2 s).mean 1 := by
      simp [Kalman.Definitions.Theorems.ConstantVelocity.transition, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two]
    intro i hi
    interval_cases i
    · have he := meanError 0
      rw [m0] at he
      have hm : |value dt*(state 2 s).mean 1| ≤ 4*r := by
        rw [abs_mul]
        have h := mul_le_mul d.dt_bound hv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using h
      have ht := abs_add_le ((state 2 s).mean 0) (value dt*(state 2 s).mean 1)
      have out := abs_sub_le ((state 2 prior).mean 0)
        ((state 2 s).mean 0+value dt*(state 2 s).mean 1) 0
      simp only [sub_zero] at out
      change |(state 2 prior).mean 0| ≤ 1
      have bound : (2 : ℝ)^(-41 : Int)+5*r ≤ 1 := by norm_num; linarith only [hr]
      linarith
    · have he := meanError 1
      rw [m1] at he
      have out := abs_sub_le ((state 2 prior).mean 1) ((state 2 s).mean 1) 0
      simp only [sub_zero] at out
      change |(state 2 prior).mean 1| ≤ 1
      have bound : (2 : ℝ)^(-41 : Int)+4*r ≤ 1 := by norm_num; linarith only [hr]
      linarith
  exact ⟨
    d.state_dimension,
    d.measurement_dimension,
    d.input_valid,
    d.observation_words,
    hp.2.2.1,
    hp.2.1,
    d.noise_size,
    d.measurement_size,
    hp.2.2.2.2.1,
    hp.2.2.2.1,
    d.noise_finite,
    d.measurement_finite,
    floor,
    cap,
    d.noise_lower,
    noiseUpper,
    meanCap,
    d.measurement_bound.trans (by norm_num)
  ⟩

end Kalman.Proofs.FloatCorrelatedPrediction
