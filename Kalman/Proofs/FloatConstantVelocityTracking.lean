import Kalman.Proofs.FloatConstantVelocityStorage

/-! Complete checked prediction/correction and operating-domain preservation
for a correlated steady-covariance family with varying stored measurements. -/

namespace Kalman.Proofs.FloatConstantVelocityTracking

open Matrix hiding transpose
open Kalman.Definitions Kalman.Implementation.LinearAlgebra
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.ConstantVelocityTracking
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.RecursionSensitivity
  Kalman.Proofs.FloatConstantVelocityStorage
  Kalman.Proofs.ConstantVelocityTracking
  Flare.Binary64.Value

set_option maxHeartbeats 1600000

/-- A sufficient growing envelope, including both measurement drive and rounding. -/
noncomputable def envelope (t : Nat) : ℝ :=
  1 / 8 + t * ((2 : ℝ) ^ (-25 : Int) + (2 : ℝ) ^ (-36 : Int))

theorem envelope_bound (t : Nat) (ht : t ≤ 1048576) : envelope t ≤ 3 / 16 := by
  have h : (t : ℝ) ≤ 1048576 := by exact_mod_cast ht
  unfold envelope
  norm_num

  linarith

/-- Original bounded native state supplies the entire local prediction domain. -/
theorem prediction_domain (z : Float) (s : Input.State) (r : ℝ)
    (hz : z.isFinite = true) (hs : TrackingState r s) (hr : r ≤ 3 / 16)
    : Kalman.Implementation.Correctness.ConstantVelocityPrediction.Domain
        (trackingInput z) s 0.25 := by
  have hq := congrArg LinearModel.Model.processNoise (model_decode z)
  change matrix 2 2 (trackingInput z).processNoise = trackingModel.processNoise at hq
  refine ⟨
    rfl,
    rfl,
    input_valid z hz,
    state_valid s hs.mean_size hs.mean_finite hs.covariance_words,
    rfl,
    by decide +kernel,
    ?_,
    ?_,
    hs.mean_finite,
    by dsimp only [trackingInput]; decide +kernel,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_
  ⟩
  · change |(4503599627370496 : ℝ)*(2 : ℝ)^(-54 : Int)| ≤ 1
    norm_num
  · rw [hs.covariance_words]
    exact posterior_finite
  · rw [hs.covariance_words, posterior_decode]
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [posteriorCovariance]
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
  · rw [hq]
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [trackingModel]
  · rw [hs.covariance_words, posterior_decode]
    exact posterior_psd
  · rw [hq]
    exact process_psd

/-- The covariance part of actual repaired prediction is exactly stationary;
mean success still comes from the complete arithmetic theorem. -/
theorem prediction_covariance (z : Float) (s output : Input.State) (r : ℝ)
    (hz : z.isFinite = true) (hs : TrackingState r s)
    (run
      : Kalman.Implementation.SymmetricJosephFilter.predict (trackingInput z) s
        = .ok output)
    : output.covariance = priorWords := by
  have valid := state_valid s hs.mean_size hs.mean_finite hs.covariance_words
  cases hm : multiply 2 2 1 (trackingInput z).transition s.mean with
  | error e =>
      simp only [Kalman.Implementation.SymmetricJosephFilter.predict,
        Kalman.Implementation.CovarianceFilter.predict,
        Kalman.Implementation.CovarianceFilter.predictUnchecked,
        input_valid z hz, show (trackingInput z).stateDimension = 2 from rfl,
        valid, hm, bind, Except.bind] at run
      cases run
  | ok mean =>
      have computed
          : Kalman.Implementation.SymmetricJosephFilter.predict (trackingInput z) s
            = .ok ⟨mean, priorWords⟩ := by
        simp only [Kalman.Implementation.SymmetricJosephFilter.predict,
          Kalman.Implementation.CovarianceFilter.predict,
          Kalman.Implementation.CovarianceFilter.predictUnchecked, input_valid z hz,
          show (trackingInput z).stateDimension = 2 from rfl, valid, hm,
          hs.covariance_words, predict_first, predict_second, predict_sum,
          Kalman.Implementation.SymmetricJosephFilter.mirrorCovariance,
          mirror_prior, bind, Except.bind, pure, Except.pure]
      exact congrArg Input.State.covariance (Except.ok.inj (run.symm.trans computed))

/-- The prediction mean comparator has the fixed physical transition, with
explicit state dimension; all original input words are retained. -/
theorem prediction_mean_accuracy (z : Float) (s prior : Input.State)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          (trackingInput z) s prior)
    : ∀ i : Fin 2,
        |(state 2 prior).mean i - (trackingModel.transition *ᵥ (state 2 s).mean) i|
        ≤ (2 : ℝ) ^ (-41 : Int) := by
  have hf := congrArg LinearModel.Model.transition (model_decode z)
  change matrix 2 2 (trackingInput z).transition = trackingModel.transition at hf
  intro i
  have he := hp.2.2.2.2.2.1.2.2 i
  change |(state 2 prior).mean i -
    (matrix 2 2 (trackingInput z).transition *ᵥ (state 2 s).mean) i| ≤ _ at he
  rw [hf] at he
  exact he

/-- Predicted original words satisfy every premise of the correlated correction
certificate; no reached-state domain is assumed by the caller. -/
theorem correction_domain (z : Float) (s prior : Input.State) (r : ℝ)
    (hz : z.isFinite = true) (hb : |value z| ≤ (2 : ℝ) ^ (-24 : Int))
    (hs : TrackingState r s) (hr : r ≤ 3 / 16)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          (trackingInput z) s prior)
    : Kalman.Implementation.Correctness.JosephPositionCorrection.Domain
        (trackingInput z) prior := by
  have cov := prediction_covariance z s prior r hz hs hp.1
  have meanError := prediction_mean_accuracy z s prior hp
  have meanCap : ∀ i, i < 2 → |value (prior.mean.getD i 0.0)| ≤ 1 := by
    intro i hi
    have hx := hs.mean_envelope.2.1
    have hv := hs.mean_envelope.2.2
    simp only [Pi.zero_apply, sub_zero] at hx hv
    have pred0 : (trackingModel.transition *ᵥ (state 2 s).mean) (0 : Fin 2) = (state 2 s).mean 0 + (state 2 s).mean 1/4 := by
      simp [trackingModel, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      ring
    have pred1 : (trackingModel.transition *ᵥ (state 2 s).mean) (1 : Fin 2) = (state 2 s).mean 1 := by
      simp [trackingModel, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
    interval_cases i
    · have he := meanError 0
      rw [pred0] at he
      have exactCap : |(state 2 s).mean 0 + (state 2 s).mean 1/4| ≤ 2*r := by
        have ht := abs_add_le ((state 2 s).mean 0) ((state 2 s).mean 1/4)
        norm_num only [abs_div, show |(4 : ℝ)| = 4 by norm_num] at ht
        linarith
      have ht := (abs_sub_le ((state 2 prior).mean 0)
        ((state 2 s).mean 0 + (state 2 s).mean 1/4) 0)
      simp only [sub_zero] at ht
      change |(state 2 prior).mean 0| ≤ 1
      linarith
    · have he := meanError 1
      rw [pred1] at he
      have ht := abs_sub_le ((state 2 prior).mean 1) ((state 2 s).mean 1) 0
      simp only [sub_zero] at ht
      change |(state 2 prior).mean 1| ≤ 1
      calc
        _ ≤ |(state 2 prior).mean 1 - (state 2 s).mean 1| + |(state 2 s).mean 1| := ht
        _ ≤ (2 : ℝ) ^ (-41 : Int) + 4 * r := add_le_add he hv
        _ ≤ 1 := by
          norm_num
          linarith only [hr]
  refine ⟨
    rfl,
    rfl,
    input_valid z hz,
    rfl,
    hp.2.2.1,
    hp.2.1,
    rfl,
    rfl,
    hp.2.2.2.2.1,
    hp.2.2.2.1,
    by dsimp only [trackingInput]; decide +kernel,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    meanCap,
    ?_
  ⟩
  · simpa [trackingInput] using hz
  · rw [cov, prior_decode]
    exact prior_floor
  · rw [cov, prior_decode]
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [priorCovariance]
  · norm_num [trackingInput, Flare.Binary64.Arithmetic.one_value]
  · norm_num [trackingInput, Flare.Binary64.Arithmetic.one_value]
  · exact hb.trans (by norm_num)

/-- The entire checked correction uses the actual scalar LDL gain; its
covariance words are exact while mean arithmetic is separately enclosed. -/
theorem correction_accuracy (z : Float) (prior : Input.State)
    (d
      : Kalman.Implementation.Correctness.JosephPositionCorrection.Domain
          (trackingInput z) prior) (hc : prior.covariance = priorWords)
    : ∃ output,
        Kalman.Implementation.SymmetricJosephFilter.update (trackingInput z) prior
          = .ok output
        ∧ output.mean.size = 2
        ∧ output.mean.all Float.isFinite = true
        ∧ output.covariance = posteriorWords
        ∧ WeightedWithin ((2 : ℝ) ^ (-38 : Int)) (state 2 output).mean
            (correctedMean (state 2 prior).mean (value z)) := by
  have kf : (#[0.5, 0.25] : Array Float).all Float.isFinite = true := by decide +kernel
  have kb : ∀ i j, |matrix 2 1 #[0.5, 0.25] i j| ≤ 2 := by
    rw [gain_decode]
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  obtain ⟨u⟩ := FloatJosephPositionMean.mean_stages (trackingInput z) prior d
    #[0.5, 0.25] kf kb
  have correction : Kalman.Implementation.CovarianceFilter.correctionUnchecked
      (trackingInput z) prior = .ok ⟨#[0.5, 0.25], #[2.0], u.residual⟩ := by
    simp only [Kalman.Implementation.CovarianceFilter.correctionUnchecked,
      d.state_dimension, d.measurement_dimension, hc, gain_hp, gain_hph, gain_sum,
      gain_pht, gain_solve, gain_transpose, u.computeProjected, u.computeResidual,
      bind, Except.bind, pure, Except.pure]
  have kernel : Kalman.Implementation.CovarianceFilter.covarianceUnchecked .joseph
      (trackingInput z) prior #[0.5, 0.25] = .ok posteriorWords := by
    simpa only [Kalman.Implementation.CovarianceFilter.covarianceUnchecked, hc]
      using covariance_cycle z prior.mean
  have shape : (prior.mean.size == 2 && prior.covariance.size == 2*2) = true := by
    simp [d.mean_size, d.prior_size]
  have finite : (prior.mean.all Float.isFinite && prior.covariance.all Float.isFinite) = true := by
    simp only [d.mean_finite, d.prior_finite, Bool.true_and]
  have pv : prior.validate 2 = .ok () := by
    simp [Input.State.validate, shape, finite, pure, Except.pure]
  let output : Input.State := ⟨u.mean, posteriorWords⟩
  have run : Kalman.Implementation.SymmetricJosephFilter.update (trackingInput z) prior = .ok output := by
    simp only [Kalman.Implementation.SymmetricJosephFilter.update,
      Kalman.Implementation.CovarianceFilter.update,
      Kalman.Implementation.CovarianceFilter.updateUnchecked,
      d.input_valid, d.state_dimension, d.measurement_dimension, pv, correction,
      u.computeIncrement, u.computeMean, kernel,
      Kalman.Implementation.SymmetricJosephFilter.mirrorCovariance,
      mirror_posterior, output, bind, Except.bind, pure, Except.pure]
  have decodedH := congrArg LinearModel.Model.observation (model_decode z)
  change matrix 1 2 (trackingInput z).observation = !![(1 : ℝ), 0] at decodedH
  have meanReference (i : Fin 2) :
      (matrix 2 1 prior.mean + matrix 2 1 #[0.5, 0.25] *
        (matrix 1 1 (trackingInput z).measurement -
          matrix 1 2 (trackingInput z).observation * matrix 2 1 prior.mean)) i 0
      = correctedMean (state 2 prior).mean (value z) i := by
    rw [gain_decode, decodedH]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply,
      Fin.sum_univ_two, Fin.sum_univ_one]
    fin_cases i <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, correctedMean, trackingInput,
        matrix, Flare.Matrix.Value.matrix, state, vector] <;> ring
  have meanError (i : Fin 2) : |(state 2 output).mean i -
      correctedMean (state 2 prior).mean (value z) i| ≤ (2 : ℝ)^(-38 : Int) := by
    have he := u.accuracy.2 i 0
    rw [meanReference] at he
    simpa only [output, state, vector, matrix, Flare.Matrix.Value.matrix,
      Fin.val_zero, Nat.mul_one, Nat.add_zero] using he
  refine ⟨
    output,
    run,
    u.mean_size,
    u.mean_finite,
    rfl,
    by positivity,
    meanError 0,
    (meanError 1).trans ?_
  ⟩
  norm_num

/-- A complete native step is locally accurate relative to the original
decoded posterior, with no covariance error in this stationary family. -/
theorem step_accuracy (z : Float) (s : Input.State) (r : ℝ)
    (hz : z.isFinite = true) (hb : |value z| ≤ (2 : ℝ) ^ (-24 : Int))
    (hs : TrackingState r s) (hr : r ≤ 3 / 16)
    : ∃ output, StepAccuracy z s output := by
  obtain ⟨prior, hp⟩ := FloatConstantVelocityPrediction.predict_accuracy
    (trackingInput z) s 0.25 (prediction_domain z s r hz hs hr)
  have cov := prediction_covariance z s prior r hz hs hp.1
  have domain := correction_domain z s prior r hz hb hs hr hp
  obtain ⟨output, run, size, finite, words, error⟩ := correction_accuracy z prior domain cov
  have predictionError := prediction_mean_accuracy z s prior hp
  have propagated := corrected_perturbation _ _ (value z) ((2 : ℝ)^(-41 : Int))
    (by positivity) predictionError
  rw [corrected_predict_mean] at propagated
  have total := weighted_trans error propagated
  refine ⟨output, ?_, size, finite, words, weighted_mono total (by norm_num)⟩
  simp [Kalman.Implementation.SymmetricJosephFilter.step, hp.1, run,
    bind, Except.bind]

/-- Original envelopes remain valid after prediction and correction. The
caller supplies neither a successful execution nor a reached-state domain. -/
theorem domain_preservation (z : Float) (s : Input.State) (t : Nat)
    (ht : t < 1048576) (hz : z.isFinite = true)
    (hb : |value z| ≤ (2 : ℝ) ^ (-24 : Int)) (hs : TrackingState (envelope t) s)
    : ∃ output,
        Kalman.Implementation.SymmetricJosephFilter.step (trackingInput z) s = .ok output
        ∧ TrackingState (envelope (t + 1)) output
        ∧ WeightedWithin ((2 : ℝ) ^ (-36 : Int)) (state 2 output).mean
            (trackingMean (state 2 s).mean (value z)) := by
  obtain ⟨output, run, size, finite, words, error⟩ := step_accuracy z s (envelope t)
    hz hb hs (envelope_bound t (by omega))
  have drive := mean_envelope (state 2 s).mean (value z) (envelope t) hs.mean_envelope
  have total := weighted_trans error drive
  have radius : (2 : ℝ)^(-36 : Int) + (envelope t + |value z|/2) ≤ envelope (t+1) := by
    unfold envelope
    push_cast
    norm_num at hb ⊢
    linarith
  exact ⟨output, run, ⟨size, finite, words, weighted_mono total radius⟩, error⟩

/-- Every state in the retained family has a strictly positive stored
covariance, with a certified `1/4` floor. -/
theorem state_posDef (r : ℝ) (s : Input.State) (hs : TrackingState r s)
    : (matrix 2 2 s.covariance).PosDef := by
  rw [hs.covariance_words, posterior_decode]
  exact Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ (1 / 4)
    (by norm_num) posterior_floor

/-- The original state envelope is inhabited and is genuinely correlated. -/
theorem domain_nonempty
    : ∃ s, TrackingState (1 / 8) s ∧ matrix 2 2 s.covariance 0 1 = (1 : ℝ) / 4 := by
  let s : Input.State := ⟨#[0.0, 0.0], posteriorWords⟩
  refine ⟨s, ⟨rfl, by decide +kernel, rfl, ?_⟩, ?_⟩
  · norm_num [WeightedWithin, s, state, vector, Flare.Binary64.Arithmetic.zero_value]
  · change matrix 2 2 posteriorWords 0 1 = _
    rw [posterior_decode]
    norm_num [posteriorCovariance]

end Kalman.Proofs.FloatConstantVelocityTracking
