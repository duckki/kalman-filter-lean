import Kalman.Proofs.FloatJosephPositionMean
import Kalman.Proofs.FloatJosephPositionKernel
import Kalman.Proofs.JosephGainSensitivity

/-! Complete checked Joseph correction with coupled covariance and one position
observation. Every native stage is derived from the original bounded domain.
No exact stored symmetry is inferred from the exact Joseph identity. -/

namespace Kalman.Proofs.FloatJosephPositionCorrection

open Matrix hiding transpose
open Kalman.Definitions Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.JosephPositionCorrection
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Definitions.Theorems.JosephPositionCorrection
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1600000

/-- Original stored prior and model conditions suffice for the entire checked
native correction, optimal-reference accuracy, and a symmetric-part floor. -/
theorem update_accuracy (input : Input.Model) (prior : Input.State)
    (d : Domain input prior)
    : ∃ output, CorrectionAccuracy input prior output := by
  let m : LinearModel.Model 2 1 := model (atDimensions 2 1 input)
  let p : LinearModel.State 2 := state 2 prior
  obtain ⟨g⟩ := FloatJosephPositionGain.gain_stages input prior d
  let k := transpose 1 2 g.solution
  obtain ⟨u⟩ := FloatJosephPositionMean.mean_stages input prior d k g.gain_finite g.gain_bound
  have hh := FloatJosephPositionGain.observation_decode input prior d
  have hf : input.observation.all Float.isFinite = true := by rw [d.observation]; decide +kernel
  have hb : ∀ i j, |matrix 1 2 input.observation i j| ≤ 1 := by
    rw [hh]
    intro i j
    fin_cases i
    fin_cases j <;> norm_num [positionRow]
  have rb : ∀ i j, |matrix 1 1 input.measurementNoise i j| ≤ 3/2 := by
    intro i j
    fin_cases i
    fin_cases j
    change |value (input.measurementNoise.getD 0 0.0)| ≤ 3/2
    rw [abs_of_pos (by linarith [d.noise_lower])]
    exact d.noise_upper
  obtain ⟨cov, cs, cf, hc, ec⟩ := FloatJosephPositionKernel.covariance_accuracy input prior k
    d.state_dimension d.measurement_dimension d.prior_finite hf d.noise_finite g.gain_finite
    d.prior_bound hb rb g.gain_bound
  have hp : p.covariance.PosSemidef :=
    (Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ (1/2) (by norm_num) d.prior_floor).posSemidef
  have hr : m.measurementNoise.PosDef := by
    have he : m.measurementNoise = diagonal (fun _ : Fin 1 => value (input.measurementNoise.getD 0 0.0)) := by
      ext i j
      fin_cases i
      fin_cases j
      rfl
    rw [he]
    exact PosDef.diagonal (fun _ => by
      change 0 < value (input.measurementNoise.getD 0 0.0)
      linarith [d.noise_lower])
  have sb : ∀ i j, |CovarianceRecursion.innovationCovariance m p i j| ≤ 7/2 := by
    rw [JosephPositionCorrection.innovation_diagonal m p hh]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [Matrix.diagonal_apply_eq]
    change |matrix 2 2 prior.covariance 0 0 + value (input.measurementNoise.getD 0 0.0)| ≤ 7/2
    have hlo := FloatJosephPositionGain.observed_floor input prior d
    have hhi := (le_abs_self _).trans (d.prior_bound 0 0)
    rw [abs_of_pos (by linarith [d.noise_lower])]
    linarith [d.noise_upper]
  have eg := JosephGainSensitivity.quadratic_accuracy m p hp hr (matrix 2 1 k)
    ((2 : ℝ)^(-36 : Int)) (7/2) g.gain_error (by norm_num) sb
  have covarianceError : EntrywiseWithin ((2 : ℝ)^(-28 : Int)) (matrix 2 2 cov)
      (CovarianceRecursion.joseph m p (CovarianceRecursion.gain m p)) := by
    refine ⟨by positivity, ?_⟩
    intro i j
    exact ((within_trans ec eg).2 i j).trans (by norm_num)
  let residual : Matrix (Fin 1) (Fin 1) ℝ :=
    matrix 1 1 input.measurement - matrix 1 2 input.observation * matrix 2 1 prior.mean
  have meanGainError := within_add (within_refl (matrix 2 1 prior.mean))
    (within_mul_right g.gain_error residual (by norm_num : (0 : ℝ) ≤ 2)
      (FloatJosephPositionMean.residual_bound input prior d))
  have meanTotal := within_trans u.accuracy meanGainError
  let reference : LinearModel.State 2 := CovarianceRecursion.update .joseph m p (vector 1 input.measurement)
  have meanReference (i : Fin 2) :
      (matrix 2 1 prior.mean + CovarianceRecursion.gain m p * residual) i 0 = reference.mean i := by
    simp [reference, CovarianceRecursion.update, CovarianceRecursion.innovation,
      residual, Matrix.mul_apply, Matrix.mulVec, dotProduct, m, p, model, state, atDimensions,
      vector, matrix, Flare.Matrix.Value.matrix]
  have exactSym : (CovarianceRecursion.joseph m p (CovarianceRecursion.gain m p)).IsHermitian :=
    (CovarianceStructure.joseph_posSemidef m p (CovarianceRecursion.gain m p) hp hr.posSemidef).isHermitian
  have asymmetry := JosephPositionCorrection.asymmetry_bound _ _ _ exactSym covarianceError
  have exactFloor := JosephPositionCorrection.covariance_floor m p d.prior_floor hh d.noise_lower
    (CovarianceRecursion.gain m p)
  have symmetricError := JosephPositionCorrection.symmetric_part_error _ _ _ exactSym covarianceError
  have floor := Flare.Analysis.EntrywiseError.lower_bound_of_error _ _ (1/4) ((2 : ℝ)^(-28 : Int))
    exactFloor (JosephPositionCorrection.symmetric_part_hermitian _) symmetricError
  have remaining : (symmetricPart (matrix 2 2 cov) - (1/8 : ℝ) • 1).PosSemidef := by
    have extra := (PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : (0 : ℝ) ≤ (1/4 : ℝ) - 2*(2 : ℝ)^(-28 : Int) - 1/8)
    convert floor.add extra using 1
    norm_num
    module
  let output : Input.State := ⟨u.mean, cov⟩
  have correction : Kalman.Implementation.CovarianceFilter.correctionUnchecked input prior
      = .ok ⟨k, g.innovation, u.residual⟩ := by
    simp [Kalman.Implementation.CovarianceFilter.correctionUnchecked,
      d.state_dimension, d.measurement_dimension, g.computeHP, g.computeHPH,
      g.computeInnovation, g.computePHT, g.computeSolution, u.computeProjected, u.computeResidual, k,
      bind, Except.bind, pure, Except.pure]
  have unchecked : Kalman.Implementation.CovarianceFilter.updateUnchecked .joseph input prior = .ok output := by
    simp [Kalman.Implementation.CovarianceFilter.updateUnchecked, correction,
      d.state_dimension, d.measurement_dimension, u.computeIncrement, u.computeMean, hc, output, bind, Except.bind, pure, Except.pure]
  have shape : (prior.mean.size == 2 && prior.covariance.size == 2*2) = true := by
    simp [d.mean_size, d.prior_size]
  have finiteBool : (prior.mean.all Float.isFinite && prior.covariance.all Float.isFinite) = true := by
    simp only [d.mean_finite, d.prior_finite, Bool.true_and]
  have pv : prior.validate 2 = .ok () := by
    simp [Input.State.validate, shape, finiteBool, pure, Except.pure]
  refine ⟨output, ?_, u.mean_size, cs, u.mean_finite, cf, ?_, ?_, remaining⟩
  · simpa only [Kalman.Implementation.CovarianceFilter.update, d.input_valid,
      d.state_dimension, pv, bind, Except.bind, pure, Except.pure] using unchecked
  · change StateWithin ((2 : ℝ)^(-28 : Int)) ((2 : ℝ)^(-28 : Int)) (state 2 output) reference
    refine ⟨covarianceError, by positivity, ?_⟩
    intro i
    have he := meanTotal.2 i 0
    rw [meanReference] at he
    have small : (2 : ℝ)^(-38 : Int) + (0 + ((1 : Nat) : ℝ) * (2 : ℝ)^(-36 : Int) * 2)
        ≤ (2 : ℝ)^(-28 : Int) := by norm_num
    have finalBound := he.trans small
    simpa only [output, state, vector, matrix, Flare.Matrix.Value.matrix, Fin.val_zero,
      Nat.mul_one, Nat.add_zero] using finalBound
  · intro i j
    exact (asymmetry i j).trans (by norm_num)

/-- The original-input envelope contains a genuinely correlated prior. -/
theorem domain_nonempty
    : ∃ input prior,
        Domain input prior ∧ matrix 2 2 prior.covariance 0 1 = (1 : ℝ) / 8 := by
  let input : Input.Model := ⟨2, 1, identity 2, #[1.0, 0.0], identity 2, #[1.0], #[0.5]⟩
  let prior : Input.State := ⟨#[0.0, 0.0], #[1.0, 0.125, 0.125, 1.0]⟩
  have hb : value (0.125 : Float) = (1 : ℝ)/8 := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-55 : Int) = _
    norm_num
  have hz : value (0.5 : Float) = (1 : ℝ)/2 := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-53 : Int) = _
    norm_num
  have floor : (matrix 2 2 prior.covariance - (1/2 : ℝ) • 1).PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [prior, matrix, Flare.Matrix.Value.matrix, hb, Matrix.one_apply,
          Flare.Binary64.Arithmetic.one_value]
    · intro x
      simp [prior, matrix, Flare.Matrix.Value.matrix, hb, Matrix.one_apply,
        Flare.Binary64.Arithmetic.one_value, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]
  refine ⟨input, prior, ?_, ?_⟩
  · refine ⟨rfl, rfl, by decide +kernel, rfl, by decide, by decide, by decide,
      by decide, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, floor, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [prior, matrix, Flare.Matrix.Value.matrix, hb, Flare.Binary64.Arithmetic.one_value]
    · norm_num [input, Flare.Binary64.Arithmetic.one_value]
    · norm_num [input, Flare.Binary64.Arithmetic.one_value]
    · intro i hi
      interval_cases i <;> norm_num [prior, Flare.Binary64.Arithmetic.zero_value]
    · norm_num [input, hz]
  · norm_num [prior, matrix, Flare.Matrix.Value.matrix, hb]

end Kalman.Proofs.FloatJosephPositionCorrection
