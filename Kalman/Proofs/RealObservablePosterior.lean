import Kalman.Proofs.RealDiagonalObservation

/-! Exact Joseph gain perturbation for fully observed diagonal covariance.
The quadratic identity includes the whole remainder, and supplies posterior
energy and rank margins for the unchanged native factor algorithm. -/

namespace Kalman.Proofs.RealObservablePosterior

open Matrix
open Kalman.Definitions
open Kalman.Definitions.DiagonalObservation

/-- Optimal gain cancels the linear term exactly. -/
theorem joseph_gain_difference (p r k : ℝ) (h : p + r ≠ 0)
    : josephVariance p r k
      = posteriorVariance p r + (p + r) * (k - optimalGain p r) ^ 2 := by
  unfold josephVariance posteriorVariance optimalGain
  field_simp [h]
  ring

theorem posterior_variance_mono (a b r : ℝ) (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r)
    : posteriorVariance a r ≤ posteriorVariance b r := by
  unfold posteriorVariance
  apply (div_le_div_iff₀ (by linarith : 0 < a + r) (by linarith : 0 < b + r)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg r)]

theorem posterior_variance_bounds (p r : ℝ) (hp : 15 / 16 ≤ p) (hP : p ≤ 13 / 4)
    (hr : 1 ≤ r) (hR : r ≤ 3 / 2)
    : 15 / 31 ≤ posteriorVariance p r ∧ posteriorVariance p r ≤ 39 / 38 := by
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by linarith
  have hs (a b : ℝ) : posteriorVariance a b = posteriorVariance b a := by
    simp [posteriorVariance, mul_comm, add_comm]
  constructor
  · calc
      _ = posteriorVariance (15 / 16) 1 := by norm_num [posteriorVariance]
      _ ≤ posteriorVariance (15 / 16) r := by
        rw [hs (15 / 16) 1, hs (15 / 16) r]
        exact posterior_variance_mono 1 r (15 / 16) (by norm_num) hr (by norm_num)
      _ ≤ _ := posterior_variance_mono (15 / 16) p r (by norm_num) hp hr0
  · calc
      _ ≤ posteriorVariance (13 / 4) r := posterior_variance_mono p (13 / 4) r hp0 hP hr0
      _ ≤ posteriorVariance (13 / 4) (3 / 2) := by
        rw [hs (13 / 4) r, hs (13 / 4) (3 / 2)]
        exact posterior_variance_mono r (3 / 2) (13 / 4) hr0 hR (by norm_num)
      _ = _ := by norm_num [posteriorVariance]

/-- A gain error of 2^-27 changes exact scalar Joseph covariance by at most
2^-50 on the reached prior/noise domain. -/
theorem joseph_gain_accuracy (p r k : ℝ) (hp : 15 / 16 ≤ p) (hP : p ≤ 13 / 4)
    (hr : 1 ≤ r) (hR : r ≤ 3 / 2) (hk : |k - optimalGain p r| ≤ (2 : ℝ) ^ (-27 : Int))
    : |josephVariance p r k - posteriorVariance p r| ≤ (2 : ℝ) ^ (-50 : Int) := by
  rw [joseph_gain_difference p r k (by linarith), add_sub_cancel_left,
    abs_mul, abs_of_nonneg (by linarith : 0 ≤ p + r), abs_of_nonneg (sq_nonneg _)]
  have hsq : (k - optimalGain p r)^2 ≤ ((2 : ℝ)^(-27 : Int))^2 := by
    nlinarith [(abs_le.mp hk).1, (abs_le.mp hk).2]
  exact (mul_le_mul (by linarith : p + r ≤ 19 / 4) hsq (sq_nonneg _)
          (by norm_num : (0 : ℝ) ≤ 19 / 4)).trans
    (by norm_num)

/-- Matrix Joseph specialization at any supplied diagonal gain. -/
theorem joseph_diagonal {n : Nat} (p r k : Fin n → ℝ)
    : (1 - diagonal k) * diagonal p * (1 - diagonal k).transpose
        + diagonal k * diagonal r * (diagonal k).transpose
      = diagonal (fun i => josephVariance (p i) (r i) (k i)) := by
  rw [← diagonal_one, diagonal_sub]
  simp only [diagonal_transpose, diagonal_mul_diagonal]
  rw [diagonal_add]
  apply congrArg diagonal
  funext i
  dsimp [josephVariance]
  ring

end Kalman.Proofs.RealObservablePosterior
