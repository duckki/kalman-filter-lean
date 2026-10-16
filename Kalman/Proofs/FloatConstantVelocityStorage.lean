import Kalman.Proofs.FloatConstantVelocityPrediction
import Kalman.Proofs.ConstantVelocityTracking
import Kalman.Implementation.Correctness.ConstantVelocityTracking

/-! Exact native covariance cycle and original-word decoding for a coupled
steady-covariance tracking family. All computational equalities use kernel
reduction; no native_decide axiom or empirical execution premise is used. -/

namespace Kalman.Proofs.FloatConstantVelocityStorage

open Matrix hiding transpose
open Kalman.Definitions Kalman.Implementation.LinearAlgebra
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.ConstantVelocityTracking
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Flare.Binary64.Value

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

deriving instance DecidableEq for Except

private theorem half_value : value (0.5 : Float) = (1 : ℝ) / 2 := by
  change (4503599627370496 : ℝ)*(2 : ℝ)^(-53 : Int) = _
  norm_num

private theorem quarter_value : value (0.25 : Float) = (1 : ℝ) / 4 := by
  change (4503599627370496 : ℝ)*(2 : ℝ)^(-54 : Int) = _
  norm_num

private theorem eighth_value : value (0.125 : Float) = (1 : ℝ) / 8 := by
  change (4503599627370496 : ℝ)*(2 : ℝ)^(-55 : Int) = _
  norm_num

private theorem process_value : value (0.3125 : Float) = (5 : ℝ) / 16 := by
  change (5629499534213120 : ℝ)*(2 : ℝ)^(-54 : Int) = _
  norm_num

private theorem prior_value : value (1.125 : Float) = (9 : ℝ) / 8 := by
  change (5066549580791808 : ℝ)*(2 : ℝ)^(-52 : Int) = _
  norm_num

attribute [local simp] half_value quarter_value eighth_value process_value prior_value
  Flare.Binary64.Arithmetic.zero_value Flare.Binary64.Arithmetic.one_value

theorem posterior_decode : matrix 2 2 posteriorWords = posteriorCovariance := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Flare.Matrix.Value.matrix, posteriorWords, posteriorCovariance]

theorem prior_decode : matrix 2 2 priorWords = priorCovariance := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Flare.Matrix.Value.matrix, priorWords, priorCovariance]

theorem model_decode (z : Float)
    : model (atDimensions 2 1 (trackingInput z)) = trackingModel := by
  have hF : matrix 2 2 (trackingInput z).transition = !![(1 : ℝ), 1/4; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [trackingInput, matrix, Flare.Matrix.Value.matrix]
  have hH : matrix 1 2 (trackingInput z).observation = !![(1 : ℝ), 0] := by
    ext i j
    fin_cases i
    fin_cases j <;>
      norm_num [trackingInput, matrix, Flare.Matrix.Value.matrix]
  have hQ : matrix 2 2 (trackingInput z).processNoise = !![(5 : ℝ)/16, 0; 0, 1/8] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [trackingInput, matrix, Flare.Matrix.Value.matrix]
  have hR : matrix 1 1 (trackingInput z).measurementNoise = !![(1 : ℝ)] := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [trackingInput, matrix, Flare.Matrix.Value.matrix]
  change (⟨matrix 2 2 (trackingInput z).transition,
    matrix 1 2 (trackingInput z).observation, matrix 2 2 (trackingInput z).processNoise,
    matrix 1 1 (trackingInput z).measurementNoise⟩ : LinearModel.Model 2 1) = _
  rw [hF, hH, hQ, hR]
  rfl

theorem gain_decode : matrix 2 1 #[0.5, 0.25] = !![1 / 2; 1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Flare.Matrix.Value.matrix]

theorem posterior_finite : posteriorWords.all Float.isFinite = true := by decide +kernel
theorem prior_finite : priorWords.all Float.isFinite = true := by decide +kernel

theorem input_valid (z : Float) (hz : z.isFinite = true)
    : (trackingInput z).validate = .ok () := by
  have oneFinite : (1.0 : Float).isFinite = true := by decide +kernel
  have quarterFinite : (0.25 : Float).isFinite = true := by decide +kernel
  have processFinite : (0.3125 : Float).isFinite = true := by decide +kernel
  have eighthFinite : (0.125 : Float).isFinite = true := by decide +kernel
  have qs : Input.symmetric 2 #[0.3125, 0.0, 0.0, 0.125] = true := by decide +kernel
  have rs : Input.symmetric 1 #[1.0] = true := by decide +kernel
  simp [Input.Model.validate, trackingInput, oneFinite, quarterFinite, processFinite,
    eighthFinite, hz, qs, rs, pure, Except.pure]

theorem state_valid (s : Input.State) (hs : s.mean.size = 2)
    (hf : s.mean.all Float.isFinite = true) (hc : s.covariance = posteriorWords)
    : s.validate 2 = .ok () := by
  have shape : (s.mean.size == 2 && s.covariance.size == 2*2) = true := by
    simp [hs, hc, posteriorWords]
  have finite : (s.mean.all Float.isFinite && s.covariance.all Float.isFinite) = true := by
    simp only [hf, hc, posterior_finite, Bool.true_and]
  simp [Input.State.validate, shape, finite, pure, Except.pure]

theorem posterior_psd : posteriorCovariance.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [posteriorCovariance]
  · intro x
    simp [posteriorCovariance, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0+x 1), sq_nonneg (x 0), sq_nonneg (x 1)]

theorem posterior_floor : (posteriorCovariance - (1 / 4 : ℝ) • 1).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [posteriorCovariance, Matrix.one_apply]
  · intro x
    simp [posteriorCovariance, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
    nlinarith [sq_nonneg (x 0+x 1), sq_nonneg (x 1)]

theorem prior_floor : (priorCovariance - (1 / 2 : ℝ) • 1).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [priorCovariance, Matrix.one_apply]
  · intro x
    simp [priorCovariance, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
    nlinarith [sq_nonneg (x 0+x 1), sq_nonneg (x 1)]

theorem process_psd : trackingModel.processNoise.PosSemidef := by
  have h : trackingModel.processNoise = diagonal ![(5 : ℝ)/16, 1/8] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [trackingModel, Matrix.diagonal_apply]
  rw [h]
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

/-! ## Exact native covariance and gain operations -/

theorem predict_first (z : Float)
    : multiply 2 2 2 (trackingInput z).transition posteriorWords
      = .ok #[0.5625, 0.5, 0.25, 1.0] := by
  dsimp only [trackingInput]
  decide +kernel

theorem predict_second (z : Float)
    : multiply 2 2 2 #[0.5625, 0.5, 0.25, 1.0]
        (transpose 2 2 (trackingInput z).transition)
      = .ok #[0.6875, 0.5, 0.5, 1.0] := by
  dsimp only [trackingInput]
  decide +kernel

theorem predict_sum (z : Float)
    : add #[0.6875, 0.5, 0.5, 1.0] (trackingInput z).processNoise = .ok priorWords := by
  dsimp only [trackingInput]
  decide +kernel

theorem mirror_prior : Flare.Matrix.Dense.mirrorLower 2 priorWords = priorWords := by
  decide +kernel

theorem mirror_posterior
    : Flare.Matrix.Dense.mirrorLower 2 posteriorWords = posteriorWords := by
  decide +kernel

theorem gain_hp (z : Float)
    : multiply 1 2 2 (trackingInput z).observation priorWords = .ok #[1.0, 0.5] := by
  dsimp only [trackingInput]
  decide +kernel

theorem gain_hph (z : Float)
    : multiply 1 2 1 #[1.0, 0.5] (transpose 1 2 (trackingInput z).observation)
      = .ok #[1.0] := by
  dsimp only [trackingInput]
  decide +kernel

theorem gain_sum (z : Float)
    : add #[1.0] (trackingInput z).measurementNoise = .ok #[2.0] := by
  dsimp only [trackingInput]
  decide +kernel

theorem gain_pht (z : Float)
    : multiply 2 2 1 priorWords (transpose 1 2 (trackingInput z).observation)
      = .ok #[1.0, 0.5] := by
  dsimp only [trackingInput]
  decide +kernel

theorem gain_solve
    : solveSPD 1 2 #[2.0] (transpose 2 1 #[1.0, 0.5]) = .ok #[0.5, 0.25] := by
  decide +kernel

theorem gain_transpose : transpose 1 2 #[0.5, 0.25] = #[0.5, 0.25] := by
  decide +kernel

theorem covariance_cycle (z : Float) (x : Array Float)
    : Kalman.Implementation.CovarianceFilter.covarianceUnchecked .joseph
        (trackingInput z) ⟨x, priorWords⟩ #[0.5, 0.25]
      = .ok posteriorWords := by
  dsimp only [trackingInput, Kalman.Implementation.CovarianceFilter.covarianceUnchecked]
  decide +kernel

end Kalman.Proofs.FloatConstantVelocityStorage
