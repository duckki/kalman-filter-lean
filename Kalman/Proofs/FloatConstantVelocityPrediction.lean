import Kalman.Proofs.FloatSymmetricJosephCorrection
import Kalman.Implementation.Correctness.ConstantVelocityPrediction

/-! Complete native prediction stages with the unchanged dense product order.
Lower-triangle copying is charged by its separate storage theorem. -/

namespace Kalman.Proofs.FloatConstantVelocityPrediction

open Matrix hiding transpose
open Kalman.Definitions Kalman.Implementation.LinearAlgebra
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.ConstantVelocityPrediction
  Kalman.Definitions.Theorems.RecursionSensitivity
  Kalman.Proofs.FloatJosephPositionArithmetic
  Kalman.Proofs.ErrorPropagation

set_option maxHeartbeats 1200000

/-- The native transition words denote precisely the chosen physical coupling. -/
theorem transition_decode (input : Input.Model) (posterior : Input.State) (dt : Float)
    (d : Domain input posterior dt)
    : matrix 2 2 input.transition
      = Kalman.Definitions.Theorems.ConstantVelocity.transition
          (Flare.Binary64.Value.value dt) := by
  rw [d.transition_words]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Kalman.Definitions.Theorems.ConstantVelocity.transition,
      matrix, Flare.Matrix.Value.matrix, Flare.Binary64.Arithmetic.one_value,
      Flare.Binary64.Arithmetic.zero_value]

/-- Every rounded prediction stage succeeds from the original operand caps. -/
theorem prediction_stages (input : Input.Model) (posterior : Input.State) (dt : Float)
    (d : Domain input posterior dt)
    : ∃ raw,
        Kalman.Implementation.CovarianceFilter.predict input posterior = .ok raw
        ∧ raw.mean.size = 2
        ∧ raw.covariance.size = 4
        ∧ raw.mean.all Float.isFinite = true
        ∧ raw.covariance.all Float.isFinite = true
        ∧ StateWithin ((2 : ℝ) ^ (-36 : Int)) ((2 : ℝ) ^ (-41 : Int)) (state 2 raw)
            (CovarianceRecursion.predict (model (atDimensions 2 1 input))
              (state 2 posterior)) := by
  have ff : input.transition.all Float.isFinite = true := by
    rw [d.transition_words]
    have oneFinite : (1.0 : Float).isFinite = true := by decide +kernel
    simp [oneFinite, d.dt_finite]
  have fb : ∀ i j, |matrix 2 2 input.transition i j| ≤ 1 := by
    rw [transition_decode input posterior dt d]
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Kalman.Definitions.Theorems.ConstantVelocity.transition, d.dt_bound]
  obtain ⟨mean, _, hm, ms, mf, em⟩ := product 2 2 1 input.transition posterior.mean 1 1
    (by decide) ff d.mean_finite (by norm_num) (by norm_num) (by norm_num) fb d.mean_bound
  obtain ⟨fp, _, hfp, _, fpf, efp⟩ := product 2 2 2 input.transition posterior.covariance 1 2
    (by decide) ff d.covariance_finite (by norm_num) (by norm_num) (by norm_num)
    fb d.covariance_bound
  have fpb := near_bound fp _ _ 4 5 efp
    (fun i j => (product_magnitude _ _ 1 2 fb d.covariance_bound i j).trans (by norm_num))
    (by norm_num)
  have ft := transpose_bound 2 2 input.transition 1 ff fb
  have ftm := Flare.Matrix.Multiplication.transpose_matrix 2 2 input.transition ff
  change matrix 2 2 (transpose 2 2 input.transition) =
    (matrix 2 2 input.transition).transpose at ftm
  obtain ⟨propagated, _, hp, ps, pf, ep⟩ := product 2 2 2 fp (transpose 2 2 input.transition) 5 1
    (by decide) fpf ft.1 (by norm_num) (by norm_num) (by norm_num) fpb ft.2
  have pb := near_bound propagated _ _ 10 11 ep
    (fun i j => (product_magnitude _ _ 5 1 fpb ft.2 i j).trans (by norm_num))
    (by norm_num)
  have prof := sum_profile 2 2 propagated input.processNoise 11 2 4 false
    (by decide) ps pf d.process_finite (by norm_num) (by norm_num) (by norm_num)
    pb d.process_bound
  obtain ⟨cov, hc, cs, cf, _⟩ := FloatDenseError.add_accuracy propagated input.processNoise 4
    prof.exponent_lower prof.exponent_upper pf d.process_finite
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using prof.magnitude)
  have ec := FloatJosephError.add_within (n := 2) (m := 2) prof ps hc
  have propagatedError := within_trans ep (within_mul_right efp _ (by norm_num : (0 : ℝ) ≤ 1) ft.2)
  rw [ftm] at propagatedError
  have total := within_trans ec (within_add propagatedError (within_refl (matrix 2 2 input.processNoise)))
  let raw : Input.State := ⟨mean, cov⟩
  refine ⟨raw, ?_, ms, cs.trans ps, mf, cf, ?_, by positivity, ?_⟩
  · simp [Kalman.Implementation.CovarianceFilter.predict,
      Kalman.Implementation.CovarianceFilter.predictUnchecked,
      d.input_valid, d.state_dimension, d.state_valid, hm, hfp, hp, hc,
      raw, bind, Except.bind, pure, Except.pure]
  · refine ⟨by positivity, ?_⟩
    intro i j
    exact (total.2 i j).trans (by norm_num [ArithmeticProfiles.sumRadius])
  · intro i
    have he := em.2 i 0
    simpa [state, vector, matrix, Flare.Matrix.Value.matrix, CovarianceRecursion.predict,
      model, atDimensions, Matrix.mul_apply, Matrix.mulVec, dotProduct] using he

/-- Full local checked prediction and storage repair from bounded original
words, compared with the exact original-word constant-velocity prediction. -/
theorem predict_accuracy (input : Input.Model) (posterior : Input.State) (dt : Float)
    (d : Domain input posterior dt)
    : ∃ output, PredictionAccuracy input posterior output := by
  obtain ⟨raw, run, ms, cs, mf, cf, error⟩ := prediction_stages input posterior dt d
  have exactPSD : (CovarianceRecursion.predict (model (atDimensions 2 1 input))
      (state 2 posterior)).covariance.PosSemidef := by
    have hp := d.covariance_psd.mul_mul_conjTranspose_same (matrix 2 2 input.transition)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
    exact hp.add d.process_psd
  obtain ⟨size, finite, hermitian, accuracy⟩ :=
    FloatSymmetricJosephCorrection.mirror_accuracy raw _ _ _ cs cf exactPSD.isHermitian error
  refine ⟨Kalman.Implementation.SymmetricJosephFilter.mirrorCovariance 2 raw,
    ?_, ms, size, mf, finite, accuracy, hermitian⟩
  simp [Kalman.Implementation.SymmetricJosephFilter.predict, run, d.state_dimension,
    bind, Except.bind, pure, Except.pure]

end Kalman.Proofs.FloatConstantVelocityPrediction
