import Kalman.Proofs.FloatCorrelatedPrediction

/-! Gain geometry and native covariance-neighborhood preservation. The
intermediate bounds here are derived from original model/state conditions. -/

namespace Kalman.Proofs.FloatCorrelatedCorrection

open Matrix Kalman.Definitions
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.CorrelatedTracking
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.TrackingCovarianceTube
  Kalman.Definitions.Theorems.RecursionSensitivity
  Kalman.Proofs.TrackingCovarianceTube Kalman.Proofs.FloatCorrelatedPrediction
  Kalman.Proofs.ErrorPropagation
  Flare.Binary64.Value

set_option maxHeartbeats 1800000

theorem noise_posDef (input : Input.Model) (dt : Float) (d : ModelDomain input dt)
    : (matrix 1 1 input.measurementNoise).PosDef := by
  have eq : matrix 1 1 input.measurementNoise =
      diagonal (fun _ : Fin 1 => value (input.measurementNoise.getD 0 0.0)) := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [eq]
  exact PosDef.diagonal (fun _ => by linarith [d.noise_lower])

theorem observation_decode (input : Input.Model) (dt : Float) (d : ModelDomain input dt)
    : matrix 1 2 input.observation = trackingModel.observation := by
  rw [d.observation_words]
  ext i j
  fin_cases i
  fin_cases j <;> norm_num [matrix, Flare.Matrix.Value.matrix, trackingModel,
    Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]

/-- Nearby original covariances and model parameters give a quantified change
in the exact optimal gain, through its actual scalar innovation denominator. -/
theorem gain_closeness (input : Input.Model) (dt : Float) (s prior : Input.State) (r : ℝ)
    (d : ModelDomain input dt) (hs : StateDomain r s) (hr : r ≤ 3 / 16)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          input s prior)
    : EntrywiseWithin (7 * radius)
        (CovarianceRecursion.gain (model (atDimensions 2 1 input)) (state 2 prior))
        steadyGain := by
  let m : LinearModel.Model 2 1 := model (atDimensions 2 1 input)
  let p : LinearModel.State 2 := state 2 prior
  have dc := correction_domain input dt s prior r d hs hr hp
  have he := prior_accuracy input dt s prior r d hs hr hp
  have hh := FloatJosephPositionGain.observation_decode input prior dc
  have re : |m.measurementNoise 0 0 - 1| ≤ parameterRadius := by
    have h := d.noise_close.2 0 0
    change |m.measurementNoise 0 0-1| ≤ parameterRadius at h
    exact h
  have lower : (3/2 : ℝ) ≤ p.covariance 0 0 + m.measurementNoise 0 0 := by
    have h := FloatJosephPositionGain.observed_floor input prior dc
    change (1/2 : ℝ) ≤ p.covariance 0 0 at h
    have hn := d.noise_lower
    change 1 ≤ m.measurementNoise 0 0 at hn
    linarith
  change EntrywiseWithin (7*radius) (CovarianceRecursion.gain m p) steadyGain
  refine ⟨by norm_num [radius], ?_⟩
  intro i j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  rw [JosephPositionCorrection.gain_entry m p hh i]
  have station : priorCovariance i 0 = 2*steadyGain i 0 := by
    fin_cases i <;> norm_num [priorCovariance, steadyGain]
  have kb : |steadyGain i 0| ≤ (1/2 : ℝ) := by
    fin_cases i <;> norm_num [steadyGain]
  have diag : |p.covariance 0 0-1| ≤ 6*radius+(2 : ℝ)^(-36 : Int)+18*parameterRadius := by
    have h := he.2 0 0
    change |p.covariance 0 0-1| ≤ _ at h
    exact h
  have bound := quotient_gain_bound (p.covariance i 0) (priorCovariance i 0)
    (p.covariance 0 0) (m.measurementNoise 0 0) (steadyGain i 0)
    (6*radius+(2 : ℝ)^(-36 : Int)+18*parameterRadius) parameterRadius
    (by norm_num [radius, parameterRadius]) (by norm_num [parameterRadius])
    lower (he.2 i 0) diag re kb station
  exact bound.trans (by norm_num [radius, parameterRadius])

/-- Fixed-gain error accounts for rounded prediction and every model parameter
change. Optimal-gain error is charged separately by completion of the square. -/
theorem fixed_gain_accuracy (input : Input.Model) (dt : Float) (s prior : Input.State)
    (r : ℝ) (d : ModelDomain input dt) (hs : StateDomain r s) (hr : r ≤ 3 / 16)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          input s prior)
    : EntrywiseWithin (4 * (2 : ℝ) ^ (-36 : Int) + 73 * parameterRadius)
        (CovarianceRecursion.joseph (model (atDimensions 2 1 input)) (state 2 prior)
          steadyGain)
        (fixedCovariance (matrix 2 2 s.covariance)) := by
  let m : LinearModel.Model 2 1 := model (atDimensions 2 1 input)
  let p : LinearModel.State 2 := state 2 prior
  let w : LinearModel.Square 2 := 1-steadyGain*trackingModel.observation
  have obs : m.observation = trackingModel.observation := observation_decode input dt d
  have wb : ∀ i j, |w i j| ≤ 1 := by
    intro i j
    simp only [w, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one]
    fin_cases i <;> fin_cases j <;> norm_num [steadyGain, trackingModel, Matrix.one_apply]
  have kb : ∀ i j, |steadyGain i j| ≤ 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [steadyGain]
  have ep := nominal_prediction_accuracy input dt s prior r d hs hr hp
  have first := within_mul_right
    (within_mul_left w ep (by norm_num : (0 : ℝ) ≤ 1) wb) w.transpose
    (by norm_num : (0 : ℝ) ≤ 1) (fun i j => wb j i)
  have second := within_mul_right
    (within_mul_left steadyGain d.noise_close (by norm_num : (0 : ℝ) ≤ 1) kb)
    steadyGain.transpose (by norm_num : (0 : ℝ) ≤ 1) (fun i j => kb j i)
  have total := within_add first second
  change EntrywiseWithin _ (CovarianceRecursion.joseph m p steadyGain) _
  rw [CovarianceRecursion.joseph, obs]
  refine ⟨by norm_num [parameterRadius], ?_⟩
  intro i j
  exact (total.2 i j).trans (by norm_num [parameterRadius])

/-- Full native covariance-neighborhood preservation, including both rounded
prediction and the checked optimal-gain Joseph correction. -/
theorem correction_tube (input : Input.Model) (dt : Float)
    (s prior output : Input.State) (r : ℝ)
    (d : ModelDomain input dt) (hs : StateDomain r s) (hr : r ≤ 3 / 16)
    (hp
      : Kalman.Implementation.Correctness.ConstantVelocityPrediction.PredictionAccuracy
          input s prior)
    (hu
      : Kalman.Implementation.Correctness.SymmetricJosephCorrection.CorrectionAccuracy
          input prior output)
    : Tube (matrix 2 2 output.covariance) := by
  let m : LinearModel.Model 2 1 := model (atDimensions 2 1 input)
  let p : LinearModel.State 2 := state 2 prior
  have dc := correction_domain input dt s prior r d hs hr hp
  have pp : p.covariance.PosSemidef :=
    (Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ (1/2) (by norm_num) dc.prior_floor).posSemidef
  have rr : m.measurementNoise.PosDef := noise_posDef input dt d
  have hh := FloatJosephPositionGain.observation_decode input prior dc
  have sb : ∀ i j, |CovarianceRecursion.innovationCovariance m p i j| ≤ 7/2 := by
    rw [JosephPositionCorrection.innovation_diagonal m p hh]
    intro i j
    have hj : j = i := Subsingleton.elim _ _
    subst j
    simp only [Matrix.diagonal_apply_eq]
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have lo := FloatJosephPositionGain.observed_floor input prior dc
    have upper := (le_abs_self _).trans (dc.prior_bound 0 0)
    change |matrix 2 2 prior.covariance 0 0 + value (input.measurementNoise.getD 0 0.0)| ≤ 7/2
    rw [abs_of_pos (by linarith [d.noise_lower])]
    linarith [dc.noise_upper]
  have jpsd := CovarianceStructure.joseph_posSemidef m p steadyGain pp rr.posSemidef
  have opsd := CovarianceStructure.joseph_posSemidef m p (CovarianceRecursion.gain m p)
    pp rr.posSemidef
  have gainError := JosephGainSensitivity.quadratic_accuracy m p pp rr steadyGain
    (7*radius) (7/2) (within_sym (gain_closeness input dt s prior r d hs hr hp))
    (by norm_num) sb
  have optimal := JosephGainSensitivity.optimal_overbound m p pp rr steadyGain
  have rounding := hu.2.2.2.2.2.1.1
  change EntrywiseWithin ((2 : ℝ)^(-28 : Int)) (matrix 2 2 output.covariance)
    (CovarianceRecursion.joseph m p (CovarianceRecursion.gain m p)) at rounding
  apply tube_transfer (matrix 2 2 s.covariance)
    (CovarianceRecursion.joseph m p steadyGain)
    (CovarianceRecursion.joseph m p (CovarianceRecursion.gain m p))
    (matrix 2 2 output.covariance) hs.covariance_tube
    jpsd.isHermitian opsd.isHermitian hu.2.2.2.2.2.2.1
    (fixed_gain_accuracy input dt s prior r d hs hr hp) optimal ?_ rounding
  simpa only [Nat.cast_one, one_pow, one_mul] using gainError

end Kalman.Proofs.FloatCorrelatedCorrection
