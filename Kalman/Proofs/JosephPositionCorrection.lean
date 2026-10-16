import Kalman.Definitions.Theorems.JosephPositionCorrection
import Kalman.Proofs.RealRecursion
import Flare.Analysis.NumericalBounds

namespace Kalman.Proofs.JosephPositionCorrection

open Matrix Kalman.Definitions.LinearModel Kalman.Definitions.CovarianceRecursion
open Kalman.Proofs.CovarianceStructure
open Kalman.Definitions.Theorems.JosephPositionCorrection

theorem covariance_floor (input : Model 2 1) (prior : State 2)
    (hp : (prior.covariance - (1 / 2 : ℝ) • 1).PosSemidef)
    (hh : input.observation = positionRow) (hr : 1 ≤ input.measurementNoise 0 0)
    (k : Matrix (Fin 2) (Fin 1) ℝ)
    : (joseph input prior k - (1 / 4 : ℝ) • 1).PosSemidef := by
  have hp' := (Flare.Analysis.NumericalBounds.posDef_of_lower_bound
    prior.covariance (1/2) (by norm_num) hp).posSemidef
  have hr' : input.measurementNoise.PosSemidef := by
    have he : input.measurementNoise = diagonal (fun _ : Fin 1 => input.measurementNoise 0 0) := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [he]
    exact PosSemidef.diagonal (fun _ => by change (0 : ℝ) ≤ input.measurementNoise 0 0; linarith)
  have hj := joseph_posSemidef input prior k hp' hr'
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    (hj.isHermitian.sub
      ((PosSemidef.one (n := Fin 2) (R := ℝ)).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 4)).isHermitian)
  intro x
  let y := (1 - k * input.observation).transpose *ᵥ x
  let u := k 0 0 * x 0 + k 1 0 * x 1
  have hy : y = ![x 0 - u, x 1] := by
    ext i
    fin_cases i <;> simp [y, u, hh, positionRow, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    <;> simp [Matrix.mul_apply]
    ring
  have hu : k.transpose *ᵥ x = ![u] := by
    ext i
    fin_cases i
    simp [u, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hl := Flare.Analysis.NumericalBounds.quadratic_lower_bound
    prior.covariance (1/2) hp y
  have hl' : (1/2 : ℝ) * ((x 0-u)^2 + (x 1)^2) ≤ y ⬝ᵥ prior.covariance.mulVec y := by
    simpa only [hy, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
      using hl
  have hc : (1/4 : ℝ) * ((x 0)^2 + (x 1)^2)
      ≤ y ⬝ᵥ prior.covariance.mulVec y + input.measurementNoise 0 0 * u^2 := by
    nlinarith [sq_nonneg (x 0 - 2*u), sq_nonneg u, sq_nonneg (x 1)]
  have hjx : x ⬝ᵥ (joseph input prior k).mulVec x
      = y ⬝ᵥ prior.covariance.mulVec y + input.measurementNoise 0 0 * u^2 := by
    simp only [joseph, Matrix.add_mulVec, dotProduct_add, RealRecursion.quadratic_congruence]
    change y ⬝ᵥ prior.covariance.mulVec y + _ = _
    rw [hu]
    simp [Matrix.mulVec, dotProduct]
    ring
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hjx]
  have hx : x ⬝ᵥ x = (x 0)^2 + (x 1)^2 := by simp [dotProduct, Fin.sum_univ_two, pow_two]
  rw [hx]
  linarith

theorem innovation_diagonal (input : Model 2 1) (prior : State 2)
    (hh : input.observation = positionRow)
    : innovationCovariance input prior
      = diagonal
          (fun _ : Fin 1 => prior.covariance 0 0 + input.measurementNoise 0 0) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [innovationCovariance, hh, positionRow, Matrix.mul_apply]

theorem gain_entry (input : Model 2 1) (prior : State 2)
    (hh : input.observation = positionRow) (i : Fin 2)
    : gain input prior i 0
      = prior.covariance i 0 / (prior.covariance 0 0 + input.measurementNoise 0 0) := by
  unfold gain
  rw [innovation_diagonal input prior hh, Matrix.inv_subsingleton]
  fin_cases i <;>
    simp [hh, positionRow, Matrix.mul_apply, div_eq_mul_inv, Ring.inverse_eq_inv]

/-- Public exact lower bound for position-only Joseph correction. -/
theorem covarianceFloor
    : Kalman.Definitions.Theorems.JosephPositionCorrection.CovarianceFloor := by
  intro input prior hp hh hr k
  exact covariance_floor input prior hp hh hr k

/-- An entrywise enclosure also controls loss of stored symmetry. -/
theorem asymmetry_bound {n : Nat} (actual reference : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hs : reference.IsHermitian)
    (he
      : Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin ε actual
          reference)
    : ∀ i j, |actual i j - actual j i| ≤ 2 * ε := by
  have ht : reference.transpose = reference := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hs.eq
  intro i j
  have hij : reference j i = reference i j := congrFun (congrFun ht i) j
  have hb := he.2 j i
  rw [hij] at hb
  have h := abs_sub_le (actual i j) (reference i j) (actual j i)
  rw [abs_sub_comm (reference i j) (actual j i)] at h
  exact h.trans ((add_le_add (he.2 i j) hb).trans (by linarith))

/-- Taking the exact symmetric part spends no additional entrywise allowance. -/
theorem symmetric_part_error {n : Nat} (actual reference : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hs : reference.IsHermitian)
    (he
      : Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin ε actual
          reference)
    : Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin ε
        (symmetricPart actual) reference := by
  have ht : reference.transpose = reference := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hs.eq
  refine ⟨he.1, ?_⟩
  intro i j
  have hij : reference j i = reference i j := congrFun (congrFun ht i) j
  have ha := abs_le.mp (he.2 i j)
  have hb := abs_le.mp (he.2 j i)
  rw [hij] at hb
  simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- The symmetric interpretation is Hermitian even if the stored output is not. -/
theorem symmetric_part_hermitian {n : Nat} (a : Matrix (Fin n) (Fin n) ℝ)
    : (symmetricPart a).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, symmetricPart, add_comm]

end Kalman.Proofs.JosephPositionCorrection
