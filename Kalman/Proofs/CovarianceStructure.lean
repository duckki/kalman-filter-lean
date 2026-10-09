import Kalman.Definitions.FactorRecursion
import Mathlib.Algebra.Order.Star.Real

/-!
# Exact covariance structure

Small Mathlib consequences for the source definitions. These prove prediction,
innovation, Joseph PSD, and factor interpretation properties. The remaining
exact identities are in RealRecursion/FactorStructure; native results have their
own proof modules.
-/

namespace Kalman.Proofs.CovarianceStructure

open Matrix
open Kalman.Definitions.LinearModel
open Kalman.Definitions.CovarianceRecursion
open Kalman.Definitions.FactorRecursion

theorem prediction_posDef {n m : Nat} (model : Model n m) (state : State n)
    (hp : state.covariance.PosSemidef) (hq : model.processNoise.PosDef)
    : (predict model state).covariance.PosDef := by
  have hf := hp.mul_mul_conjTranspose_same model.transition
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hf
  exact Matrix.PosDef.posSemidef_add hf hq

theorem innovation_posDef {n m : Nat} (model : Model n m) (prior : State n)
    (hp : prior.covariance.PosSemidef) (hr : model.measurementNoise.PosDef)
    : (innovationCovariance model prior).PosDef := by
  have hh := hp.mul_mul_conjTranspose_same model.observation
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  exact Matrix.PosDef.posSemidef_add hh hr

theorem joseph_posSemidef {n m : Nat} (model : Model n m) (prior : State n)
    (k : Matrix (Fin n) (Fin m) ℝ)
    (hp : prior.covariance.PosSemidef) (hr : model.measurementNoise.PosSemidef)
    : (joseph model prior k).PosSemidef := by
  have hw := hp.mul_mul_conjTranspose_same (1 - k * model.observation)
  have hk := hr.mul_mul_conjTranspose_same k
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hw hk
  exact hw.add hk

theorem gram_posSemidef {n : Nat} {ι : Type} [Fintype ι] (l : Matrix (Fin n) ι ℝ)
    : (gram l).PosSemidef := by
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial]
    using Matrix.posSemidef_self_mul_conjTranspose l

theorem gram_posDef_of_isUnit {n : Nat} (l : Square n) (hl : IsUnit l)
    : (gram l).PosDef := by
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial]
    using Matrix.PosDef.mul_conjTranspose_self l (Matrix.vecMul_injective_of_isUnit hl)

end Kalman.Proofs.CovarianceStructure
