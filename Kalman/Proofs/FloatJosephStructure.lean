import Kalman.Proofs.FloatJosephDomain
import Kalman.Proofs.FloatDiagonalStorage

/-! Diagonal structure of the actual direct Joseph covariance kernel.
Every product and both rounded sums are covered, including signed zeros. -/

namespace Kalman.Proofs.FloatJosephStructure

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.JosephCovarianceEvaluation
open Kalman.Proofs.ArithmeticProfiles
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-- All five products and both sums preserve decoded diagonal storage. The
profile is an intermediate arithmetic contract, not an input-domain theorem. -/
theorem covariance_diagonal (input : Input.Model) (prior : Input.State)
    (k output : Array Float) (hn : input.stateDimension = 2)
    (hm : input.measurementDimension = 2) (p : JosephProfile input prior k output)
    (hw : p.exponentW = 2) (dp : DecodedDiagonal 2 prior.covariance)
    (dh : DecodedDiagonal 2 input.observation)
    (dr : DecodedDiagonal 2 input.measurementNoise) (dk : DecodedDiagonal 2 k)
    : DecodedDiagonal 2 output := by
  have kh := FloatDiagonalStorage.multiply_diagonal_two k input.observation p.kh
    p.profileKH.finite_left p.profileKH.finite_right dk dh
    (by simpa only [hn, hm] using p.computeKH)
  have di : DecodedDiagonal 2 (identity 2) := by
    intro i j hi hj hij
    change matrix 2 2 (identity 2) ⟨i, hi⟩ ⟨j, hj⟩ = 0
    rw [FloatJosephError.identity_matrix]
    exact Matrix.one_apply_ne (fun h => hij (Fin.val_eq_of_eq h))
  have dw := FloatDiagonalStorage.sub_diagonal_two (identity 2) p.kh p.w
    (by simpa only [hn, hw] using p.profileW)
    (by simp [identity, Flare.Matrix.Dense.identity]) di kh (by simpa only [hn] using p.computeW)
  have dwp := FloatDiagonalStorage.multiply_diagonal_two p.w prior.covariance p.wp
    p.profileWP.finite_left p.profileWP.finite_right dw dp
    (by simpa only [hn] using p.computeWP)
  have dwt := FloatDiagonalStorage.transpose_diagonal 2 p.w p.profileWP.finite_left dw
  have df := FloatDiagonalStorage.multiply_diagonal_two p.wp (transpose 2 2 p.w) p.first
    p.profileFirst.finite_left (by simpa only [hn] using p.profileFirst.finite_right) dwp dwt
    (by simpa only [hn] using p.computeFirst)
  have dkr := FloatDiagonalStorage.multiply_diagonal_two k input.measurementNoise p.kr
    p.profileKR.finite_left p.profileKR.finite_right dk dr
    (by simpa only [hn, hm] using p.computeKR)
  have dkt := FloatDiagonalStorage.transpose_diagonal 2 k p.profileKH.finite_left dk
  have ds := FloatDiagonalStorage.multiply_diagonal_two p.kr (transpose 2 2 k) p.second
    p.profileSecond.finite_left (by simpa only [hn, hm] using p.profileSecond.finite_right) dkr dkt
    (by simpa only [hn, hm] using p.computeSecond)
  have fs := (FloatJosephError.product_within p.profileFirst p.computeFirst).1
  apply FloatDiagonalStorage.add_diagonal_two p.first p.second output p.exponentSum
    p.profileSum (by simpa only [hn] using fs) df ds p.computeSum

/-- Stored-input success and accuracy now include exact diagonal preservation;
no successful intermediate computation is assumed by this result. -/
theorem stored_input_diagonal_accuracy (input : Input.Model) (prior : Input.State)
    (k : Array Float) (d : TwoStateDomain input prior k)
    (dp : DecodedDiagonal 2 prior.covariance) (dh : DecodedDiagonal 2 input.observation)
    (dr : DecodedDiagonal 2 input.measurementNoise) (dk : DecodedDiagonal 2 k)
    : ∃ output,
        output.size = 4
        ∧ output.all Float.isFinite = true
        ∧ JosephCovarianceAccuracy ((2 : ℝ) ^ (-34 : Int)) input prior k output
        ∧ DecodedDiagonal 2 output := by
  obtain ⟨output, os, of, he⟩ := FloatJosephDomain.stored_input_accuracy input prior k d
  obtain ⟨other, p, _, _, _, _, _, _, _, hw, _⟩ := FloatJosephDomain.covariance_stages input prior k d
  have run : Kalman.Implementation.CovarianceFilter.covarianceUnchecked .joseph input prior k = .ok other := by
    simp [Kalman.Implementation.CovarianceFilter.covarianceUnchecked, p.computeKH, p.computeW,
      p.computeWP, p.computeFirst, p.computeKR, p.computeSecond, p.computeSum,
      bind, Except.bind]
  have eq := Except.ok.inj (run.symm.trans he.1)
  subst other
  exact ⟨output, os, of, he, covariance_diagonal input prior k output
    d.state_dimension d.measurement_dimension p hw dp dh dr dk⟩

/-- For fully observed diagonal inputs with prior/noise variances at least
one half, the actual rounded dense covariance has a strict floor. The supplied
gain need not be optimal. This remains a local covariance-kernel guarantee. -/
theorem stored_input_positive : StoredDiagonalPositive := by
  intro input prior k d dp hH dr dk hp hr
  have dh : DecodedDiagonal 2 input.observation := by
    intro i j hi hj hij
    change matrix 2 2 input.observation ⟨i, hi⟩ ⟨j, hj⟩ = 0
    rw [hH]
    exact Matrix.one_apply_ne (fun h => hij (Fin.val_eq_of_eq h))
  obtain ⟨output, os, of, he, dout⟩ := stored_input_diagonal_accuracy input prior k d dp dh dr dk
  have err := he.2
  simp only [CovarianceRecursion.joseph, model, state] at err
  rw [d.state_dimension, d.measurement_dimension] at err
  rw [hH, Matrix.mul_one] at err
  have jd : (1 - matrix 2 2 k) * matrix 2 2 prior.covariance * (1 - matrix 2 2 k).transpose
      + matrix 2 2 k * matrix 2 2 input.measurementNoise * (matrix 2 2 k).transpose
      = diagonal (fun i => (1 - matrix 2 2 k i i)^2 * matrix 2 2 prior.covariance i i
        + (matrix 2 2 k i i)^2 * matrix 2 2 input.measurementNoise i i) := by
    rw [FloatDiagonalStorage.matrix_diagonal 2 k dk,
      FloatDiagonalStorage.matrix_diagonal 2 prior.covariance dp,
      FloatDiagonalStorage.matrix_diagonal 2 input.measurementNoise dr,
      ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1
    funext i
    simp only [Matrix.diagonal_apply_eq]
    ring
  rw [jd] at err
  have floor : ∀ i, (1 : ℝ) / 8 ≤ matrix 2 2 output i i := by
    intro i
    have h := (abs_le.mp (err.2 i i)).1
    simp only [Matrix.diagonal_apply_eq] at h
    have ha := hp i
    have hb := hr i
    have h1 := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (1 - matrix 2 2 k i i))
    have h2 := mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg (matrix 2 2 k i i))
    have h3 := sq_nonneg (matrix 2 2 k i i - 1 / 2)
    norm_num only at h
    nlinarith
  refine ⟨output, os, of, he, dout, floor, ?_⟩
  rw [FloatDiagonalStorage.matrix_diagonal 2 output dout, Matrix.posDef_diagonal_iff]
  intro i
  linarith [floor i]

end Kalman.Proofs.FloatJosephStructure
