import Kalman.Proofs.FloatJosephError
import Kalman.Proofs.FactorStructure
import Kalman.Proofs.FloatQRInitialDomain

/-! Exact native horizontal assembly and rounded-prearray Gram propagation.
Assembly copies stored entries; all product and factorization error remains explicit. -/

namespace Kalman.Proofs.FloatPrearray

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Definitions.FactorRecursion
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

theorem fromCols_size (rows left right : Nat) (a b : Array Float)
    : (fromCols rows left right a b).size = rows * (left + right) := by
  simp [fromCols]

theorem fromCols_finite (rows left right : Nat) (a b : Array Float)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    : (fromCols rows left right a b).all Float.isFinite = true := by
  rw [Array.all_eq_true]
  intro k hk
  simp only [fromCols, Array.getElem_map, Array.getElem_range]
  split <;> exact Flare.Matrix.Storage.getD_finite _ _ (by assumption)

theorem fromCols_entry (rows left right : Nat) (a b : Array Float)
    (i : Fin rows) (j : Fin (left + right))
    : entry (left + right) (fromCols rows left right a b) i.val j.val
      = if j.val < left then
          entry left a i.val j.val
        else
          entry right b i.val (j.val - left) := by
  have hi : i.val * (left + right) + j.val < rows * (left + right) := by
    have h := Nat.mul_le_mul_right (left + right) i.isLt
    rw [Nat.succ_mul] at h
    omega
  have hd : (i.val * (left + right) + j.val) / (left + right) = i.val := by
    rw [Nat.mul_comm i.val, Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt),
      Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hm : (i.val * (left + right) + j.val) % (left + right) = j.val := by
    exact Nat.mul_add_mod_of_lt j.isLt
  simp [entry, Flare.Matrix.Dense.entry, fromCols, hi, hd, hm]

/-- The exact Real Gram of copied native blocks is the sum of their exact Grams.
No dense product or rounded addition is performed by this assembly. -/
theorem fromCols_gram (rows left right : Nat) (a b : Array Float)
    : gram (matrix rows (left + right) (fromCols rows left right a b))
      = gram (matrix rows left a) + gram (matrix rows right b) := by
  ext i j
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    change value (entry (left + right) _ i.val _) * value (entry (left + right) _ j.val _) = _
    rw [fromCols_entry, fromCols_entry]
    simp [Fin.castAdd, k.isLt, matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry,
      Array.getD_eq_getD_getElem?]
  · apply Finset.sum_congr rfl
    intro k _
    change value (entry (left + right) _ i.val _) * value (entry (left + right) _ j.val _) = _
    rw [fromCols_entry, fromCols_entry]
    simp [Fin.natAdd, matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry,
      Array.getD_eq_getD_getElem?]

/-- Converting a rectangular entry enclosure to its exact Gram enclosure. -/
theorem gram_within {rows columns : Nat} {a b : Matrix (Fin rows) (Fin columns) ℝ}
    {ε B : ℝ} (he : EntrywiseWithin ε a b) (hB : 0 ≤ B)
    (hb : ∀ i j, |b i j| ≤ B)
    : EntrywiseWithin (columns * (2 * ε * B + ε ^ 2)) (gram a) (gram b) := by
  convert within_mul he (within_transpose he) hB hB hb (fun i j => hb j i) using 1 <;>
    first | ring | rfl

end Kalman.Proofs.FloatPrearray
