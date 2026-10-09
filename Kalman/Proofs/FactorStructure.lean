import Kalman.Proofs.CovarianceStructure
import Kalman.Definitions.Theorems.FormulationEquivalence
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-! Exact factor representations and orthogonal prearray transformations. -/

namespace Kalman.Proofs.FactorStructure

open Matrix
open Kalman.Definitions.LinearModel
open Kalman.Definitions.CovarianceRecursion
open Kalman.Definitions.FactorRecursion
open Kalman.Proofs.CovarianceStructure

theorem lowerPositive_isUnit {n : Nat} (l : Square n) (hl : LowerPositive l)
    : IsUnit l := by
  apply (Matrix.isUnit_iff_isUnit_det l).2
  apply isUnit_iff_ne_zero.mpr
  have ht : l.IsLowerTriangular := fun _ _ hij => hl.1 _ _ hij
  rw [Matrix.det_of_isLowerTriangular l ht]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (hl.2 i)

theorem lowerPositive_gram_posDef {n : Nat} (l : Square n) (hl : LowerPositive l)
    : (gram l).PosDef :=
  gram_posDef_of_isUnit l (lowerPositive_isUnit l hl)

theorem covarianceFactor_posDef {n : Nat} (p l : Square n) (hl : CovarianceFactor p l)
    : p.PosDef :=
  hl.2 ▸ lowerPositive_gram_posDef l hl.1

theorem udFactor_posDef {n : Nat} (p u : Square n) (d : Vector n) (h : UDFactor p u d)
    : p.PosDef := by
  have hu : IsUnit u := by
    apply (Matrix.isUnit_iff_isUnit_det u).2
    have ht : u.IsUpperTriangular := fun _ _ hij => h.1 _ _ hij
    rw [Matrix.det_of_isUpperTriangular ht]
    simp [h.2.1]
  have hd : (Matrix.diagonal d).PosDef := Matrix.posDef_diagonal_iff.mpr h.2.2.1
  have hp := hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hu)
  simpa only [h.2.2.2, Matrix.conjTranspose_eq_transpose_of_trivial] using hp

theorem gram_mul {n m : Nat} {ι : Type} [Fintype ι]
    (a : Matrix (Fin n) (Fin m) ℝ) (l : Matrix (Fin m) ι ℝ)
    : gram (a * l) = a * gram l * a.transpose := by
  simp [gram, Matrix.transpose_mul, Matrix.mul_assoc]

theorem gram_fromCols {n : Nat} {ι κ : Type} [Fintype ι] [Fintype κ]
    (a : Matrix (Fin n) ι ℝ) (b : Matrix (Fin n) κ ℝ)
    : gram (Matrix.fromCols a b) = gram a + gram b := by
  simp [gram, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]

theorem qrGramFactor_gram {n p : Nat}
    (a : Matrix (Fin n) (Fin n ⊕ Fin p) ℝ) (l : Square n) (h : QRGramFactor a l)
    : gram l = gram a := by
  obtain ⟨u, hu, hau⟩ := h.2
  have heq : gram (a * u) = gram a := by
    simp [gram, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc u, hu]
  rw [hau, gram_fromCols] at heq
  simpa [gram] using heq

theorem squareRootStagesAgree
    : Kalman.Definitions.Theorems.FormulationEquivalence.SquareRootStagesAgree := by
  intro n m model prior l tq predicted posterior tr innovationFactor k hl h
  obtain ⟨hq, hr, hpred, hs, hk, hpost⟩ := h
  have hp : gram predicted = (predict model prior).covariance := by
    rw [qrGramFactor_gram _ _ hpred, predictionPrearray, gram_fromCols, gram_mul, hl.2, hq.2]
    rfl
  have hi : gram innovationFactor = innovationCovariance model (predict model prior) := by
    rw [qrGramFactor_gram _ _ hs, innovationPrearray, gram_fromCols, gram_mul, hr.2, hp]
    exact add_comm _ _
  have hgain : k = gain model (predict model prior) := by
    rw [hk, hp, hi]
    rfl
  refine ⟨hp, ?_⟩
  rw [qrGramFactor_gram _ _ hpost, posteriorPrearray, gram_fromCols, gram_mul, gram_mul,
    hp, hr.2, hgain]
  rfl

end Kalman.Proofs.FactorStructure
