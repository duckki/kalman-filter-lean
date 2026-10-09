import Kalman.Definitions.Theorems.RecursionSensitivity
import Kalman.Proofs.RealRecursion

/-! The scalar fully observed diagonal specialization agrees with the existing
matrix Kalman prediction, optimal gain, mean correction and every covariance
formulation. All innovation inverses used here have nonzero diagonal entries. -/

namespace Kalman.Proofs.RealDiagonalObservation

open Matrix
open Kalman.Definitions
open Kalman.Definitions.LinearModel
open Kalman.Definitions.DiagonalObservation

theorem predict_eq {n : Nat} (f q r x p : Vector n)
    : CovarianceRecursion.predict (model f q r) (state x p)
      = state (fun i => f i * x i) (fun i => priorVariance (f i) (q i) (p i)) := by
  simp only [CovarianceRecursion.predict, model, state, State.mk.injEq]
  constructor
  · funext i
    exact Matrix.mulVec_diagonal f x i
  · simp only [diagonal_transpose, diagonal_mul_diagonal]
    rw [diagonal_add]
    apply congrArg Matrix.diagonal
    funext i
    dsimp [priorVariance]
    ring

theorem innovation_covariance_eq {n : Nat} (f q r x p : Vector n)
    : CovarianceRecursion.innovationCovariance (model f q r) (state x p)
      = diagonal (fun i => p i + r i) := by
  simp [CovarianceRecursion.innovationCovariance, model, state, ← diagonal_add]

theorem diagonal_inverse {n : Nat} (a : Vector n) (ha : ∀ i, a i ≠ 0)
    : (diagonal a)⁻¹ = diagonal (fun i => (a i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [diagonal_mul_diagonal]
  simp [ha]

theorem gain_eq {n : Nat} (f q r x p : Vector n) (h : ∀ i, p i + r i ≠ 0)
    : CovarianceRecursion.gain (model f q r) (state x p)
      = diagonal (fun i => optimalGain (p i) (r i)) := by
  rw [CovarianceRecursion.gain, innovation_covariance_eq, diagonal_inverse _ h]
  simp [model, state, optimalGain, diagonal_mul_diagonal, div_eq_mul_inv]

theorem update_eq {n : Nat} (form : CovarianceRecursion.Form) (f q r z x p : Vector n)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < r i)
    : CovarianceRecursion.update form (model f q r) (state x p) z
      = state (fun i => posteriorMean (p i) (r i) (x i) (z i))
          (fun i => posteriorVariance (p i) (r i)) := by
  have h : ∀ i, p i + r i ≠ 0 := fun i => (add_pos_of_nonneg_of_pos (hp i) (hr i)).ne'
  have hk := gain_eq f q r x p h
  apply congrArg₂ State.mk
  · change x + CovarianceRecursion.gain (model f q r) (state x p) *ᵥ
        CovarianceRecursion.innovation (model f q r) (state x p) z = _
    rw [hk]
    funext i
    simp only [CovarianceRecursion.innovation, model, state, one_mulVec,
      Pi.add_apply, Pi.sub_apply, Matrix.mulVec_diagonal]
    dsimp [posteriorMean, optimalGain]
    field_simp [h i]
    ring
  · have hj : CovarianceRecursion.joseph (model f q r) (state x p)
        (CovarianceRecursion.gain (model f q r) (state x p)) =
        CovarianceRecursion.compact (model f q r) (state x p)
          (CovarianceRecursion.gain (model f q r) (state x p)) :=
      RealRecursion.joseph_eq_compact _ _ (Matrix.PosSemidef.diagonal hp) (Matrix.PosDef.diagonal hr)
    change CovarianceRecursion.correctedCovariance form (model f q r) (state x p)
      (CovarianceRecursion.gain (model f q r) (state x p)) = _
    have hc : CovarianceRecursion.correctedCovariance form (model f q r) (state x p)
        (CovarianceRecursion.gain (model f q r) (state x p)) =
        CovarianceRecursion.compact (model f q r) (state x p)
          (CovarianceRecursion.gain (model f q r) (state x p)) := by
      cases form with
      | compact => rfl
      | subtractive => exact (RealRecursion.compact_eq_subtractive _ _ _).symm
      | joseph => exact hj
    rw [hc, CovarianceRecursion.compact, hk]
    simp only [model, state, mul_one]
    rw [← diagonal_one]
    rw [diagonal_sub, diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    dsimp [posteriorVariance, optimalGain]
    field_simp [h i]
    ring

/-- Every exact covariance formulation specializes to the same componentwise
full step. Positivity of Q and R justifies the correction denominator. -/
theorem step_eq {n : Nat} (form : CovarianceRecursion.Form) (f q r z x p : Vector n)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 < r i)
    : CovarianceRecursion.step form (model f q r) (state x p) z = step f q r z x p := by
  rw [CovarianceRecursion.step, predict_eq, update_eq form]
  · rfl
  · intro i
    exact add_nonneg (mul_nonneg (sq_nonneg _) (hp i)) (hq i)
  · exact hr

theorem state_eq_of_diagonal {n : Nat} (reference : State n)
    (h : reference.covariance = diagonal (fun i => reference.covariance i i))
    : reference = state reference.mean (fun i => reference.covariance i i) := by
  cases reference with
  | mk x p => exact congrArg (State.mk x) h

end Kalman.Proofs.RealDiagonalObservation
