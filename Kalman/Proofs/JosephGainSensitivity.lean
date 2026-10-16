import Kalman.Definitions.Theorems.JosephGainSensitivity
import Kalman.Proofs.RealRecursion
import Kalman.Proofs.RealErrorBounds

namespace Kalman.Proofs.JosephGainSensitivity

open Matrix Kalman.Definitions.LinearModel Kalman.Definitions.CovarianceRecursion
open Kalman.Proofs.CovarianceStructure
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ErrorPropagation

/-- Expanded form grouped around the innovation covariance. -/
theorem joseph_expansion {n m : Nat} (input : Model n m) (prior : State n)
    (k : Matrix (Fin n) (Fin m) ℝ)
    : joseph input prior k
      = prior.covariance
        - k * (input.observation * prior.covariance)
        - (prior.covariance * input.observation.transpose) * k.transpose
        + k * innovationCovariance input prior * k.transpose := by
  simp only [joseph, innovationCovariance, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- Completion of the square at the exact optimal gain. -/
theorem gain_difference {n m : Nat} (input : Model n m) (prior : State n)
    (hp : prior.covariance.PosSemidef) (hr : input.measurementNoise.PosDef)
    (k : Matrix (Fin n) (Fin m) ℝ)
    : joseph input prior k - joseph input prior (gain input prior)
      = (k - gain input prior) * innovationCovariance input prior
        * (k - gain input prior).transpose := by
  have hs := innovation_posDef input prior hp hr
  have hstation := RealRecursion.gain_innovation input prior hp hr
  have hpt : prior.covariance.transpose = prior.covariance := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hp.isHermitian
  have hst : (innovationCovariance input prior).transpose = innovationCovariance input prior := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hs.isHermitian
  have hleft : innovationCovariance input prior * (gain input prior).transpose
      = input.observation * prior.covariance := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hpt, hst]
      using congrArg Matrix.transpose hstation
  rw [joseph_expansion, joseph_expansion, ← hstation, ← hleft]
  simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- Gain error alone can only increase the exact Joseph covariance. -/
theorem optimal_overbound {n m : Nat} (input : Model n m) (prior : State n)
    (hp : prior.covariance.PosSemidef) (hr : input.measurementNoise.PosDef)
    (k : Matrix (Fin n) (Fin m) ℝ)
    : (joseph input prior k - joseph input prior (gain input prior)).PosSemidef := by
  rw [gain_difference input prior hp hr]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
    using (innovation_posDef input prior hp hr).posSemidef.mul_mul_conjTranspose_same
      (k - gain input prior)

/-- A sharp entrywise quadratic bound, with no linear gain-error term. -/
theorem quadratic_accuracy {n m : Nat} (input : Model n m) (prior : State n)
    (hp : prior.covariance.PosSemidef) (hr : input.measurementNoise.PosDef)
    (k : Matrix (Fin n) (Fin m) ℝ) (ε S : ℝ)
    (he : EntrywiseWithin ε k (gain input prior)) (hS : 0 ≤ S)
    (hs : ∀ i j, |innovationCovariance input prior i j| ≤ S)
    : EntrywiseWithin (m ^ 2 * S * ε ^ 2)
        (joseph input prior k) (joseph input prior (gain input prior)) := by
  refine ⟨by have := he.1; positivity, ?_⟩
  intro i j
  change |(joseph input prior k - joseph input prior (gain input prior)) i j| ≤ _
  rw [gain_difference input prior hp hr k]
  have he' : ∀ i j, |(k - gain input prior) i j| ≤ ε := he.2
  have hb := product_magnitude (k - gain input prior) (innovationCovariance input prior)
    ε S he' hs
  have hc := product_magnitude ((k - gain input prior) * innovationCovariance input prior)
    (k - gain input prior).transpose (m * ε * S) ε hb (fun i j => he' j i) i j
  convert hc using 1
  ring

/-- Public exact matrix identity, with its positivity premises discharged. -/
theorem gainDifference
    : Kalman.Definitions.Theorems.JosephGainSensitivity.GainDifference := by
  intro n m input prior hp hr k
  exact gain_difference input prior hp hr k

/-- Public semidefinite-order consequence. -/
theorem optimalOverbound
    : Kalman.Definitions.Theorems.JosephGainSensitivity.OptimalOverbound := by
  intro n m input prior hp hr k
  exact optimal_overbound input prior hp hr k

end Kalman.Proofs.JosephGainSensitivity
