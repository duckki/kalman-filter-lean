import Kalman.Proofs.FloatJosephUpdate
import Kalman.Proofs.FloatMeanDomain
import Kalman.Proofs.RealObservableCorrection
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy

/-! Dense native prediction from original model/state bounds, with every
product and sum charged against the same decoded covariance and mean. -/

namespace Kalman.Proofs.FloatJosephPrediction

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy (ModelDomain)
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1800000

/-! ----------------------------------------------------------------------
## Storage bounds and exact diagonal products
-------------------------------------------------------------------------- -/

private theorem vector_entry (a : Array Float) (i : Fin 2)
    : matrix 2 1 a i 0 = value (a.getD i.val 0.0) := by
  simp [matrix, Flare.Matrix.Value.matrix]

private theorem array_bound (a : Array Float) (A : ℝ)
    (h : ∀ i j, |matrix 2 2 a i j| ≤ A) (t : Nat) (ht : t < 4)
    : |value (a.getD t 0.0)| ≤ A := by
  have hi : t / 2 < 2 := by omega
  have hj : t % 2 < 2 := by omega
  have hm := h ⟨t / 2, hi⟩ ⟨t % 2, hj⟩
  have he : t / 2 * 2 + t % 2 = t := by omega
  change |value (a.getD (t / 2 * 2 + t % 2) 0.0)| ≤ A at hm
  simpa only [he] using hm

private theorem diagonal_product_bound (a b : Matrix (Fin 2) (Fin 2) ℝ) (A B : ℝ)
    (ha : a = diagonal (fun i => a i i)) (hb : b = diagonal (fun i => b i i))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ab : ∀ i j, |a i j| ≤ A) (bb : ∀ i j, |b i j| ≤ B)
    : ∀ i j, |(a * b) i j| ≤ A * B := by
  intro i j
  rw [ha, hb, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, abs_mul]
    exact mul_le_mul (ab i i) (bb i i) (abs_nonneg _) hA
  · rw [Matrix.diagonal_apply_ne _ hij, abs_zero]
    exact mul_nonneg hA hB

private theorem near_bound (a reference : Matrix (Fin 2) (Fin 2) ℝ) (e cap target : ℝ)
    (he : EntrywiseWithin e a reference) (hb : ∀ i j, |reference i j| ≤ cap)
    (hc : cap + e ≤ target)
    : ∀ i j, |a i j| ≤ target := by
  intro i j
  have ht := abs_sub_le (a i j) (reference i j) 0
  simp only [sub_zero] at ht
  linarith [he.2 i j, hb i j]

/-! ----------------------------------------------------------------------
## Prediction and reached correction domain
-------------------------------------------------------------------------- -/

/-- Exact prediction of the incoming stored state has covariance floor one
and mean magnitude at most 9/8, including unit and sign-reversing dynamics. -/
theorem exact_prediction_bounds (input : Input.Model) (current : Input.State)
    (p : ModelDomain input) (s : StateInvariant current)
    : let prior : LinearModel.State 2 :=
        CovarianceRecursion.predict (model (atDimensions 2 2 input)) (state 2 current)
      prior.covariance = diagonal (fun i => prior.covariance i i)
      ∧ (∀ i, 1 ≤ prior.covariance i i)
      ∧ (∀ i, |prior.mean i| ≤ 9 / 8) := by
  let m : LinearModel.Model 2 2 := model (atDimensions 2 2 input)
  change let prior : LinearModel.State 2 := CovarianceRecursion.predict m (state 2 current)
    prior.covariance = diagonal (fun i => prior.covariance i i)
      ∧ (∀ i, 1 ≤ prior.covariance i i) ∧ (∀ i, |prior.mean i| ≤ 9 / 8)
  have hF := FloatDiagonalStorage.matrix_diagonal 2 input.transition p.transition_diagonal
  have hQ := FloatDiagonalStorage.matrix_diagonal 2 input.processNoise p.process_noise.diagonal
  have hP := FloatDiagonalStorage.matrix_diagonal 2 current.covariance s.diagonal
  have he := RealObservableCorrection.predict_eq_diagonal m
    (state 2 current) _ _ _ hF hQ hP
  dsimp only
  rw [he]
  refine ⟨by simp only [DiagonalObservation.state, Matrix.diagonal_apply_eq], ?_, ?_⟩
  · intro i
    simp only [DiagonalObservation.state, Matrix.diagonal_apply_eq, DiagonalObservation.priorVariance]
    have hp : 0 ≤ matrix 2 2 current.covariance i i :=
      (by norm_num : (0 : ℝ) ≤ 7 / 16).trans (s.covariance_floor i)
    have hq := p.process_noise.covariance.diagonal_lower i.val i.isLt
    change 1 ≤ matrix 2 2 input.processNoise i i at hq
    linarith [mul_nonneg (sq_nonneg (matrix 2 2 input.transition i i)) hp]
  · intro i
    change |matrix 2 2 input.transition i i * value (current.mean.getD i.val 0.0)| ≤ 9 / 8
    rw [abs_mul]
    exact (mul_le_mul (p.transition_bound i.val i.val i.isLt i.isLt)
      (s.mean_bound i.val i.isLt) (abs_nonneg _) (by norm_num)).trans (by norm_num)

/-- Native dense prediction succeeds, has covariance/mean errors 2^-42/2^-46,
and derives the original-input domain of the complete correction theorem. -/
theorem prediction_accuracy (input : Input.Model) (current : Input.State)
    (p : ModelDomain input) (s : StateInvariant current)
    : ∃ prior,
        Kalman.Implementation.CovarianceFilter.predictUnchecked input current = .ok prior
        ∧ StateWithin ((2 : ℝ) ^ (-42 : Int)) ((2 : ℝ) ^ (-46 : Int)) (state 2 prior)
            (CovarianceRecursion.predict (model (atDimensions 2 2 input))
              (state 2 current))
        ∧ FloatJosephUpdate.UpdateDomain input prior := by
  have fb : ∀ i j, |matrix 2 2 input.transition i j| ≤ 1 :=
    fun i j => p.transition_bound i.val j.val i.isLt j.isLt
  have pb := FloatDiagonalStorage.diagonal_magnitude 2 current.covariance (13 / 8) s.diagonal
    (fun i => (by norm_num : (0 : ℝ) ≤ 7 / 16).trans (s.covariance_floor i)) s.covariance_cap (by norm_num)
  have qb := FloatDiagonalStorage.diagonal_magnitude 2 input.processNoise (3 / 2) p.process_noise.diagonal
    (fun i => (by norm_num : (0 : ℝ) ≤ 1).trans (p.process_noise.covariance.diagonal_lower i.val i.isLt))
    (fun i => p.process_noise.diagonal_cap i.val i.isLt) (by norm_num)
  have hF := FloatDiagonalStorage.matrix_diagonal 2 input.transition p.transition_diagonal
  have hP := FloatDiagonalStorage.matrix_diagonal 2 current.covariance s.diagonal
  have tf := Flare.Matrix.Multiplication.transpose_storage 2 2 input.transition p.transition_finite
  have tm : matrix 2 2 (transpose 2 2 input.transition) = (matrix 2 2 input.transition).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 input.transition p.transition_finite
  have tb : ∀ i j, |matrix 2 2 (transpose 2 2 input.transition) i j| ≤ 1 := by
    intro i j
    rw [tm]
    exact fb j i
  have tdiag : (matrix 2 2 input.transition).transpose
      = diagonal (fun i => (matrix 2 2 input.transition).transpose i i) := by
    rw [hF, Matrix.diagonal_transpose]
    simp only [Matrix.diagonal_apply_eq]
  have ib0 := diagonal_product_bound (matrix 2 2 input.transition) (matrix 2 2 current.covariance)
    1 (13 / 8) hF hP (by norm_num) (by norm_num) fb pb
  have ib : ∀ i j, |(matrix 2 2 input.transition * matrix 2 2 current.covariance) i j| ≤ 13 / 8 := by
    simpa only [one_mul] using ib0
  have idiag : matrix 2 2 input.transition * matrix 2 2 current.covariance
      = diagonal (fun i => (matrix 2 2 input.transition * matrix 2 2 current.covariance) i i) := by
    rw [hF, hP, Matrix.diagonal_mul_diagonal]
    simp only [Matrix.diagonal_apply_eq]
  have ipb0 := diagonal_product_bound (matrix 2 2 input.transition * matrix 2 2 current.covariance)
    (matrix 2 2 input.transition).transpose (13 / 8) 1 idiag tdiag (by norm_num) (by norm_num) ib
    (fun i j => fb j i)
  have ipb : ∀ i j, |((matrix 2 2 input.transition * matrix 2 2 current.covariance)
      * (matrix 2 2 input.transition).transpose) i j| ≤ 13 / 8 := by
    simpa only [mul_one] using ipb0
  have pp := FloatGainDomain.product_profile_two input.transition current.covariance 1 (13 / 8)
    p.transition_finite s.covariance_finite (by norm_num) (by norm_num) (by norm_num)
    p.transition_bound (fun i j hi hj => pb ⟨i, hi⟩ ⟨j, hj⟩)
  obtain ⟨fp, hfp, fps, fpf, efp0⟩ := FloatDenseError.multiply_entrywise_accuracy 2 2 2 input.transition current.covariance
    (fun _ _ => (8 : ℝ)) pp.inner_le pp.finite_left pp.finite_right
    (fun _ _ _ _ => pp.upper) (fun _ _ _ _ => pp.lower) pp.mass
  have efp : EntrywiseWithin (productRadius 2 8) (matrix 2 2 fp)
      (matrix 2 2 input.transition * matrix 2 2 current.covariance) := ⟨by norm_num [productRadius], efp0⟩
  have fpb := near_bound _ _ _ (13 / 8) (7 / 4) efp ib (by norm_num [productRadius])
  have fpd := FloatDiagonalStorage.multiply_diagonal_two input.transition current.covariance fp
    p.transition_finite s.covariance_finite p.transition_diagonal s.diagonal hfp
  have pprop := FloatGainDomain.product_profile_two fp (transpose 2 2 input.transition) (7 / 4) 1
    fpf tf.2.1 (by norm_num) (by norm_num) (by norm_num)
    (fun i j hi hj => fpb ⟨i, hi⟩ ⟨j, hj⟩) (fun i j hi hj => tb ⟨i, hi⟩ ⟨j, hj⟩)
  obtain ⟨propagated, hprop, props, propf, ep0⟩ := FloatDenseError.multiply_entrywise_accuracy
    2 2 2 fp (transpose 2 2 input.transition) (fun _ _ => (8 : ℝ)) pprop.inner_le pprop.finite_left pprop.finite_right
    (fun _ _ _ _ => pprop.upper) (fun _ _ _ _ => pprop.lower) pprop.mass
  have ep : EntrywiseWithin (productRadius 2 8) (matrix 2 2 propagated)
      (matrix 2 2 fp * matrix 2 2 (transpose 2 2 input.transition)) := ⟨by norm_num [productRadius], ep0⟩
  have eprop := within_trans ep (within_mul_right efp (matrix 2 2 (transpose 2 2 input.transition)) (by norm_num : (0 : ℝ) ≤ 1) tb)
  rw [tm] at eprop
  have propb := near_bound _ _ _ (13 / 8) (7 / 4) eprop ipb (by norm_num [productRadius])
  have td := FloatDiagonalStorage.transpose_diagonal 2 input.transition p.transition_finite p.transition_diagonal
  have propd := FloatDiagonalStorage.multiply_diagonal_two fp (transpose 2 2 input.transition) propagated fpf tf.2.1 fpd td hprop
  have ps : SumProfile propagated input.processNoise 2 false := by
    refine ⟨by norm_num, by norm_num, propf, p.process_noise.covariance.finite, ?_⟩
    intro t ht
    have ha := array_bound propagated (7 / 4) propb t (by omega)
    have hb := array_bound input.processNoise (3 / 2) qb t (by omega)
    simpa only [Bool.false_eq_true, ↓reduceIte, show (2 : ℝ)^(2 : Int) = 4 by norm_num]
      using (abs_add_le _ _).trans ((add_le_add ha hb).trans (by norm_num))
  obtain ⟨cov, hc, cs, cf, _⟩ := FloatDenseError.add_accuracy propagated input.processNoise 2
    ps.exponent_lower ps.exponent_upper ps.finite_left ps.finite_right
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using ps.magnitude)
  have eadd := FloatJosephError.add_within (n := 2) (m := 2) ps props hc
  have ec := within_trans eadd (within_add eprop (within_refl (matrix 2 2 input.processNoise)))
  have cd := FloatDiagonalStorage.add_diagonal_two propagated input.processNoise cov 2 ps props propd p.process_noise.diagonal hc
  let ideal : LinearModel.State 2 := CovarianceRecursion.predict (model (atDimensions 2 2 input)) (state 2 current)
  have ecov : EntrywiseWithin ((2 : ℝ)^(-42 : Int)) (matrix 2 2 cov) ideal.covariance := by
    refine ⟨by positivity, fun i j => (ec.2 i j).trans ?_⟩
    norm_num [productRadius, sumRadius]
  have idealb := exact_prediction_bounds input current p s
  change ideal.covariance = diagonal (fun i => ideal.covariance i i)
    ∧ (∀ i, 1 ≤ ideal.covariance i i) ∧ (∀ i, |ideal.mean i| ≤ 9 / 8) at idealb
  have cfloor : ∀ i, (15 : ℝ) / 16 ≤ matrix 2 2 cov i i := by
    intro i
    have he := (abs_le.mp (ecov.2 i i)).1
    have hb := idealb.2.1 i
    norm_num only at he
    linarith
  have ccap : ∀ i, matrix 2 2 cov i i ≤ (13 : ℝ) / 4 := by
    intro i
    have hi : ideal.covariance i i ≤ (25 : ℝ) / 8 := by
      change ((matrix 2 2 input.transition * matrix 2 2 current.covariance)
        * (matrix 2 2 input.transition).transpose + matrix 2 2 input.processNoise) i i ≤ _
      rw [Matrix.add_apply]
      have hp' := (abs_le.mp (ipb i i)).2
      have hq := p.process_noise.diagonal_cap i.val i.isLt
      change matrix 2 2 input.processNoise i i ≤ (3 : ℝ) / 2 at hq
      linarith
    have he := (abs_le.mp (ecov.2 i i)).2
    norm_num only at he
    linarith
  obtain ⟨mean, _, hm, ms, mf, em, _⟩ := FloatMeanDomain.vector_product input.transition current.mean 1 (9 / 8)
    p.transition_finite s.mean_finite (by norm_num) (by norm_num) p.transition_bound s.mean_bound
  have emean : ∀ i : Fin 2, |value (mean.getD i.val 0.0) - ideal.mean i| ≤ (2 : ℝ)^(-46 : Int) := by
    intro i
    have he := em.2 i 0
    rw [hF, Matrix.diagonal_mul] at he
    simp only [vector_entry] at he
    change |value (mean.getD i.val 0.0) - (matrix 2 2 input.transition *ᵥ vector 2 current.mean) i| ≤ _
    rw [hF, Matrix.mulVec_diagonal]
    simpa only [vector, show productRadius 2 8 = (2 : ℝ)^(-46 : Int) by norm_num [productRadius]] using he
  have mb : ∀ i, i < 2 → |value (mean.getD i 0.0)| ≤ (19 : ℝ) / 16 := by
    intro i hi
    have he := emean ⟨i, hi⟩
    have hb := idealb.2.2 ⟨i, hi⟩
    have hh := abs_sub_le (value (mean.getD i 0.0)) (ideal.mean ⟨i, hi⟩) 0
    simp only [sub_zero] at hh
    norm_num only at he
    linarith
  let prior : Input.State := ⟨mean, cov⟩
  refine ⟨prior, ?_, ⟨ecov, by positivity, emean⟩, ?_⟩
  · simp [Kalman.Implementation.CovarianceFilter.predictUnchecked, p.state_dimension,
      hm, hfp, hprop, hc, prior, bind, Except.bind, pure, Except.pure]
  · exact ⟨p.state_dimension, p.measurement_dimension, cs.trans props, p.observation_size,
      p.noise.covariance.size,
      ⟨cf, p.observation_finite, p.noise.covariance.finite, cd, p.noise.diagonal,
        p.observation_identity, cfloor, ccap,
        fun i => p.noise.covariance.diagonal_lower i.val i.isLt,
        fun i => p.noise.diagonal_cap i.val i.isLt⟩,
      ⟨ms, p.measurement_size, mf, p.measurement_finite, mb, p.measurement_bound⟩⟩

end Kalman.Proofs.FloatJosephPrediction
