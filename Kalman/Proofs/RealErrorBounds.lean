import Kalman.Proofs.ErrorPropagation
import Kalman.Proofs.RealRecursion

/-! Exact matrix perturbation tools for composing the native filter stages.
These lemmas infer errors from proved residuals; no native arithmetic is idealized. -/

namespace Kalman.Proofs.RealErrorBounds

open Matrix
open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ErrorPropagation

/-! Reusable right-system residual bound, proved in FLARE. -/

alias gain_residual_accuracy := Flare.Analysis.EntrywiseError.right_residual_accuracy

/-- Gain error propagates through the two terms of the exact Joseph formula. -/
theorem joseph_gain_accuracy {n m : Nat} (input : LinearModel.Model n m)
    (prior : LinearModel.State n) (k k₀ : Matrix (Fin n) (Fin m) ℝ)
    (ε P R H K : ℝ) (he : EntrywiseWithin ε k k₀)
    (hP : 0 ≤ P) (hR : 0 ≤ R) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hp : ∀ i j, |prior.covariance i j| ≤ P)
    (hr : ∀ i j, |input.measurementNoise i j| ≤ R)
    (hh : ∀ i j, |input.observation i j| ≤ H)
    (hk : ∀ i j, |k₀ i j| ≤ K)
    : EntrywiseWithin
        (n ^ 2 * P * (2 * (m * ε * H) * (1 + m * K * H) + (m * ε * H) ^ 2)
          + m ^ 2 * R * (2 * ε * K + ε ^ 2))
        (CovarianceRecursion.joseph input prior k)
        (CovarianceRecursion.joseph input prior k₀) := by
  let w := (1 : LinearModel.Square n) - k * input.observation
  let w₀ := (1 : LinearModel.Square n) - k₀ * input.observation
  have ew := within_sub (within_refl (1 : LinearModel.Square n)) (within_mul_right he _ hH hh)
  simp only [zero_add] at ew
  have hw : ∀ i j, |w₀ i j| ≤ 1 + m * K * H := by
    intro i j
    have hm := product_magnitude k₀ input.observation K H hk hh i j
    have hi : |(1 : LinearModel.Square n) i j| ≤ 1 := by simp [Matrix.one_apply]; split_ifs <;> norm_num
    exact (abs_sub _ _).trans (add_le_add hi hm)
  have ewp := within_mul ew (within_refl prior.covariance) (by positivity) hP hw hp
  have efirst := within_mul ewp (within_transpose ew) (by positivity) (by positivity)
    (product_magnitude w₀ prior.covariance _ _ hw hp) (fun i j => hw j i)
  have ekr := within_mul he (within_refl input.measurementNoise) hK hR hk hr
  have esecond := within_mul ekr (within_transpose he) (by positivity) hK
    (product_magnitude k₀ input.measurementNoise _ _ hk hr) (fun i j => hk j i)
  convert within_add efirst esecond using 1 <;> first | ring | rfl

end Kalman.Proofs.RealErrorBounds
