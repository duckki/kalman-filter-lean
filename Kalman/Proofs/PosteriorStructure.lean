import Kalman.Proofs.FactorStructure
import Kalman.Proofs.ErrorPropagation

/-! Quantitative exact stored-factor posterior prearray margins. These use
the computed gain's magnitude; optimality of that gain is not assumed. -/

namespace Kalman.Proofs.PosteriorStructure

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ErrorPropagation

set_option maxHeartbeats 800000

/-- Covariance entry bounds control a congruence diagonal by row absolute mass. -/
theorem congruence_diagonal_bound {n m : Nat} (w : Matrix (Fin m) (Fin n) ℝ)
    (p : Matrix (Fin n) (Fin n) ℝ) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hp : ∀ i j, |p i j| ≤ C) (hw : ∀ i, ∑ j, |w i j| ≤ B)
    : ∀ i, (w * p * w.transpose) i i ≤ C * B ^ 2 := by
  intro i
  have he : |(w * p * w.transpose) i i| ≤ C * (∑ j, |w i j|)^2 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    calc
      _ ≤ ∑ j, ∑ k, |w i k * p k j * w i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ j, ∑ k, |w i k| * C * |w i j| := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp k j) (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by
        simp only [pow_two, Finset.mul_sum, mul_left_comm, mul_comm]
  have hs0 : 0 ≤ ∑ j, |w i j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : (∑ j, |w i j|)^2 ≤ B^2 := by nlinarith [hw i]
  exact (le_abs_self _).trans (he.trans (mul_le_mul_of_nonneg_left hs hC))

/-- The exact Joseph first term remains close enough to the incoming covariance
to preserve a spectral margin when KH is small. -/
theorem first_term_within (h k p : Matrix (Fin 2) (Fin 2) ℝ)
    (hh : ∀ i j, |h i j| ≤ 1 / 64) (hk : ∀ i j, |k i j| ≤ 1 / 6)
    (hp : ∀ i j, |p i j| ≤ 7 / 4)
    : EntrywiseWithin (1 / 13) ((1 - k * h) * p * (1 - k * h).transpose) p := by
  have hm := product_magnitude k h (1 / 6) (1 / 64) hk hh
  have ew : EntrywiseWithin (1 / 192) (1 - k * h) (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine ⟨by norm_num, fun i j => ?_⟩
    calc
      _ = |(k * h) i j| := by simp [Matrix.sub_apply, sub_sub_cancel_left, abs_neg]
      _ ≤ 1 / 192 := (hm i j).trans (by norm_num)
  have hi : ∀ i j : Fin 2, |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
    intro i j
    simp [Matrix.one_apply]
    split_ifs <;> norm_num
  have ep := within_mul_right ew p (by norm_num : (0 : ℝ) ≤ 7 / 4) hp
  rw [Matrix.one_mul] at ep
  have ept := within_mul ep (within_transpose ew) (by norm_num : (0 : ℝ) ≤ 7 / 4)
    (by norm_num : (0 : ℝ) ≤ 1) hp (fun i j => hi j i)
  rw [Matrix.transpose_one, Matrix.mul_one] at ept
  refine ⟨by norm_num, fun i j => (ept.2 i j).trans ?_⟩
  norm_num

/-- Computed-gain cap 1/6 suffices for strict posterior prearray headroom.
No optimal-gain identity or statistical interpretation is required here. -/
theorem prearray_reference_bounds (h k l tr : Matrix (Fin 2) (Fin 2) ℝ)
    (hh : ∀ i j, |h i j| ≤ 1 / 64) (hk : ∀ i j, |k i j| ≤ 1 / 6)
    (hp : ∀ i j, |FactorRecursion.gram l i j| ≤ 7 / 4)
    (hf : (FactorRecursion.gram l - (2 / 3 : ℝ) • 1).PosSemidef)
    (ht : ∀ i j, |FactorRecursion.gram tr i j| ≤ 25 / 16)
    : (FactorRecursion.gram (((1 : Matrix (Fin 2) (Fin 2) ℝ) - k * h) * l)
        + FactorRecursion.gram (k * tr)
        - (20 / 39 : ℝ) • 1).PosSemidef
      ∧ (∀ i,
          (FactorRecursion.gram (((1 : Matrix (Fin 2) (Fin 2) ℝ) - k * h) * l)
            + FactorRecursion.gram (k * tr))
            i i
          ≤ 251 / 128) := by
  let w : Matrix (Fin 2) (Fin 2) ℝ := 1 - k * h
  have he := first_term_within h k (FactorRecursion.gram l) hh hk hp
  rw [← FactorStructure.gram_mul] at he
  have hfloor := lower_bound_of_error _ _ (2 / 3) (1 / 13) hf
    (CovarianceStructure.gram_posSemidef (w * l)).isHermitian he
  have hg := hfloor.add (CovarianceStructure.gram_posSemidef (k * tr))
  have hkm := product_magnitude k h (1 / 6) (1 / 64) hk hh
  have hw : ∀ i, ∑ j, |w i j| ≤ 97 / 96 := by
    intro i
    calc
      _ ≤ ∑ j, (|(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| + |(k * h) i j|) :=
        Finset.sum_le_sum (fun j _ => abs_sub _ _)
      _ = 1 + ∑ j, |(k * h) i j| := by
        rw [Finset.sum_add_distrib]
        congr 1
        fin_cases i <;> norm_num [Matrix.one_apply, Fin.sum_univ_two]
      _ ≤ 1 + ∑ _j : Fin 2, (1 / 192 : ℝ) := by
        apply add_le_add (le_refl (1 : ℝ))
        apply Finset.sum_le_sum
        intro j _
        exact (hkm i j).trans (by norm_num)
      _ = _ := by norm_num
  have hkr : ∀ i, ∑ j, |k i j| ≤ (1 / 3 : ℝ) := by
    intro i
    exact (Finset.sum_le_sum (fun j _ => hk i j)).trans (by norm_num)
  have hdw := congruence_diagonal_bound w (FactorRecursion.gram l) (7 / 4) (97 / 96)
    (by norm_num) (by norm_num) hp hw
  have hdk := congruence_diagonal_bound k (FactorRecursion.gram tr) (25 / 16) (1 / 3)
    (by norm_num) (by norm_num) ht hkr
  refine ⟨?_, ?_⟩
  · convert hg using 1
    dsimp only [w]
    norm_num
    module
  · intro i
    rw [Matrix.add_apply, FactorStructure.gram_mul, FactorStructure.gram_mul]
    exact (add_le_add (hdw i) (hdk i)).trans (by norm_num)

end Kalman.Proofs.PosteriorStructure
