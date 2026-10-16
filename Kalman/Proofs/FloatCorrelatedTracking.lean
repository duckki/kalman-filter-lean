import Kalman.Proofs.FloatCorrelatedCorrection

/-! Complete checked nonstationary tracking envelope. Covariance evolution
and all native stages are derived from original state and model conditions. -/

namespace Kalman.Proofs.FloatCorrelatedTracking

open Matrix Kalman.Definitions
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.CorrelatedTracking
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.TrackingCovarianceTube
  Kalman.Definitions.Theorems.RecursionSensitivity
  Kalman.Proofs.TrackingCovarianceTube Kalman.Proofs.ConstantVelocityTracking
  Kalman.Proofs.FloatCorrelatedPrediction Kalman.Proofs.FloatCorrelatedCorrection
  Kalman.Proofs.ErrorPropagation
  Flare.Binary64.Value

set_option maxHeartbeats 2000000

/-- The mean envelope pays for varying gain and parameters as well as native
arithmetic. It compares with the nominal affine map, not a substituted gain in
the independent original-input source trajectory. -/
theorem mean_envelope_accuracy (input : Input.Model) (dt : Float)
    (s prior output : Input.State) (r : ℝ) (d : ModelDomain input dt)
    (hs : StateDomain r s) (hr : r ≤ 3 / 16)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          input s prior)
    (hu
      : Kalman.Implementation.Correctness.SymmetricJosephCorrection.CorrectionAccuracy
          input prior output)
    : WeightedWithin ((2 : ℝ) ^ (-8 : Int)) (state 2 output).mean
        (trackingMean (state 2 s).mean (value (input.measurement.getD 0 0.0))) := by
  let m : LinearModel.Model 2 1 := model (atDimensions 2 1 input)
  let p : LinearModel.State 2 := state 2 prior
  let z := value (input.measurement.getD 0 0.0)
  let residual : Matrix (Fin 1) (Fin 1) ℝ :=
    matrix 1 1 input.measurement - matrix 1 2 input.observation * matrix 2 1 prior.mean
  have dc := correction_domain input dt s prior r d hs hr hp
  have gainError := gain_closeness input dt s prior r d hs hr hp
  change EntrywiseWithin (7*radius) (CovarianceRecursion.gain m p) steadyGain at gainError
  have propagatedGain := within_add (within_refl (matrix 2 1 prior.mean))
    (within_mul_right gainError residual (by norm_num : (0 : ℝ) ≤ 2)
      (FloatJosephPositionMean.residual_bound input prior dc))
  have actualMean (i : Fin 2) :
      (matrix 2 1 prior.mean + CovarianceRecursion.gain m p * residual) i 0 =
      (CovarianceRecursion.update .joseph m p (vector 1 input.measurement)).mean i := by
    simp [CovarianceRecursion.update, CovarianceRecursion.innovation, residual,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, m, p, model, state, atDimensions,
      vector, matrix, Flare.Matrix.Value.matrix]
  have steadyMean (i : Fin 2) :
      (matrix 2 1 prior.mean + steadyGain * residual) i 0 = correctedMean p.mean z i := by
    have obs := observation_decode input dt d
    dsimp only [residual]
    rw [obs]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_one, Fin.sum_univ_two]
    fin_cases i <;> norm_num [steadyGain, trackingModel, correctedMean,
      p, state, vector, matrix, Flare.Matrix.Value.matrix, z] <;> ring
  have meanError (i : Fin 2) : |(state 2 output).mean i - correctedMean p.mean z i|
      ≤ (2 : ℝ)^(-28 : Int)+14*radius := by
    have eg := propagatedGain.2 i 0
    rw [actualMean, steadyMean] at eg
    have en := hu.2.2.2.2.2.1.2.2 i
    exact (abs_sub_le _ _ _).trans ((add_le_add en eg).trans (by norm_num [radius]))
  have localMean : WeightedWithin ((2 : ℝ)^(-28 : Int)+14*radius)
      (state 2 output).mean (correctedMean p.mean z) := by
    refine ⟨by norm_num [radius], meanError 0, (meanError 1).trans ?_⟩
    norm_num [radius]
  have pd := prediction_domain input dt s r d hs hr
  have meanCap := pd.mean_bound
  have changedMean := within_mul_right d.transition_close (matrix 2 1 s.mean)
    (by norm_num : (0 : ℝ) ≤ 1) meanCap
  have priorMean (i : Fin 2) : |p.mean i - (trackingModel.transition *ᵥ (state 2 s).mean) i|
      ≤ (2 : ℝ)^(-41 : Int)+2*parameterRadius := by
    have native := hp.2.2.2.2.2.1.2.2 i
    change |p.mean i - (matrix 2 2 input.transition *ᵥ (state 2 s).mean) i| ≤ _ at native
    have changed : |(matrix 2 2 input.transition *ᵥ (state 2 s).mean) i -
        (trackingModel.transition *ᵥ (state 2 s).mean) i| ≤ 2*parameterRadius := by
      have he := changedMean.2 i 0
      norm_num only [Nat.cast_ofNat, mul_one] at he
      simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, state, vector,
        matrix, Flare.Matrix.Value.matrix, Fin.val_zero, Nat.mul_one, Nat.add_zero] using he
    exact (abs_sub_le _ _ _).trans (add_le_add native changed)
  have propagated := corrected_perturbation p.mean _ z
    ((2 : ℝ)^(-41 : Int)+2*parameterRadius) (by norm_num [parameterRadius]) priorMean
  rw [corrected_predict_mean] at propagated
  exact weighted_mono (weighted_trans localMean propagated)
    (by norm_num [radius, parameterRadius])

/-- Original neighborhood and model bounds suffice for the complete checked
step. Actual output covariance is permitted to evolve and round. -/
theorem step_envelope (input : Input.Model) (dt : Float) (s : Input.State) (r : ℝ)
    (d : ModelDomain input dt) (hs : StateDomain r s) (hr : r ≤ 3 / 16)
    : ∃ output, StepEnvelope input s output := by
  obtain ⟨prior, hp⟩ := FloatConstantVelocityPrediction.predict_accuracy input s dt
    (prediction_domain input dt s r d hs hr)
  have dc := correction_domain input dt s prior r d hs hr hp
  obtain ⟨output, hu⟩ := FloatSymmetricJosephCorrection.update_accuracy input prior dc
  have tube := correction_tube input dt s prior output r d hs hr hp hu
  have meanError := mean_envelope_accuracy input dt s prior output r d hs hr hp hu
  refine ⟨output, ?_, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1, tube, meanError⟩
  simp [Kalman.Implementation.SymmetricJosephFilter.step, hp.1, hu.1, bind, Except.bind]

/-- Every covariance in the native neighborhood has a certified positive floor. -/
theorem state_posDef (s : Input.State) (r : ℝ) (hs : StateDomain r s)
    : (matrix 2 2 s.covariance).PosDef :=
  Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ (1 / 8) (by norm_num)
    (tube_floor _ hs.covariance_tube)

/-- The original state and models determine every reached native prefix.
No constant covariance or reached-domain hypothesis is used. -/
theorem horizon_preservation (inputs : Nat → Input.Model) (increments : Nat → Float)
    (initial : Input.State) (horizon : Nat)
    (d : HorizonDomain inputs increments initial horizon)
    : ∀ t, t ≤ horizon → ∃ output, HorizonPreserved inputs initial t output := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨initial, rfl, ?_⟩
      simpa only [Nat.cast_zero, zero_mul, add_zero] using d.initial_state
  | succ t ih =>
      intro ht
      obtain ⟨s, run, hs⟩ := ih (by omega)
      have hr
          : (1 / 8 : ℝ) + t * ((2 : ℝ) ^ (-25 : Int) + (2 : ℝ) ^ (-8 : Int))
            ≤ 3 / 16 := by
        have h : (t : ℝ) ≤ 15 := by
          have := d.horizon_bound; exact_mod_cast (show t ≤ 15 by omega)
        norm_num
        linarith
      have modelDomain := d.input_domain t (by omega)
      obtain ⟨output, step, ms, cs, mf, cf, tube, localError⟩ := step_envelope
        (inputs t) (increments t) s _ modelDomain hs hr
      have drive := mean_envelope (state 2 s).mean
        (value ((inputs t).measurement.getD 0 0.0)) _ hs.mean_envelope
      have total := weighted_trans localError drive
      have radiusBound : (2 : ℝ)^(-8 : Int) +
          (1/8 + t*((2 : ℝ)^(-25 : Int)+(2 : ℝ)^(-8 : Int)) +
            |value ((inputs t).measurement.getD 0 0.0)|/2)
          ≤ 1/8 + ((t+1 : Nat) : ℝ)*((2 : ℝ)^(-25 : Int)+(2 : ℝ)^(-8 : Int)) := by
        have hb := modelDomain.measurement_bound
        push_cast
        norm_num at hb ⊢
        linarith
      refine ⟨output, ?_, ms, cs, mf, cf, tube, weighted_mono total radiusBound⟩
      simp [Kalman.Implementation.SymmetricJosephFilter.run, run, step, bind, Except.bind]

end Kalman.Proofs.FloatCorrelatedTracking
