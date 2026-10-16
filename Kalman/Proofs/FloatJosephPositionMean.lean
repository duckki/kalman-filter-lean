import Kalman.Proofs.FloatJosephPositionGain

/-! Native residual and mean evaluation at a stored scalar-observation gain.
The complete correction derives the gain's finiteness and cap separately. -/

namespace Kalman.Proofs.FloatJosephPositionMean

open Matrix hiding transpose
open Kalman.Definitions Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.JosephPositionCorrection
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Definitions.Theorems.JosephPositionCorrection
open Kalman.Proofs.ArithmeticProfiles Kalman.Proofs.ErrorPropagation
open Kalman.Proofs.FloatJosephPositionArithmetic
open Flare.Binary64.Value

structure MeanStages (input : Input.Model) (prior : Input.State)
    (k : Array Float) where
  (projected residual increment mean : Array Float)
  computeProjected : multiply 1 2 1 input.observation prior.mean = .ok projected
  computeResidual : sub input.measurement projected = .ok residual
  computeIncrement : multiply 2 1 1 k residual = .ok increment
  computeMean : add prior.mean increment = .ok mean
  mean_size : mean.size = 2
  mean_finite : mean.all Float.isFinite = true
  accuracy
    : EntrywiseWithin ((2 : ℝ) ^ (-38 : Int)) (matrix 2 1 mean)
        (matrix 2 1 prior.mean
          + matrix 2 1 k
            * (matrix 1 1 input.measurement
                - matrix 1 2 input.observation * matrix 2 1 prior.mean))

/-- Exact scalar residual has magnitude at most two on the original domain. -/
theorem residual_bound (input : Input.Model) (prior : Input.State)
    (d : Domain input prior)
    : ∀ i j,
        |(matrix 1 1 input.measurement
          - matrix 1 2 input.observation * matrix 2 1 prior.mean)
          i j|
        ≤ 2 := by
  intro i j
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  subst j
  have hx := d.mean_bound 0 (by decide)
  have hz := d.measurement_bound
  have hh := FloatJosephPositionGain.observation_decode input prior d
  have hp : (matrix 1 2 input.observation * matrix 2 1 prior.mean) 0 0 = value (prior.mean.getD 0 0.0) := by
    simp [hh, positionRow, Matrix.mul_apply, matrix, Flare.Matrix.Value.matrix]
  rw [Matrix.sub_apply, hp]
  exact (abs_sub _ _).trans ((add_le_add hz hx).trans (by norm_num))

theorem mean_stages (input : Input.Model) (prior : Input.State) (d : Domain input prior)
    (k : Array Float) (kf : k.all Float.isFinite = true)
    (kb : ∀ i j, |matrix 2 1 k i j| ≤ 2)
    : Nonempty (MeanStages input prior k) := by
  have hh := FloatJosephPositionGain.observation_decode input prior d
  have hf : input.observation.all Float.isFinite = true := by rw [d.observation]; decide +kernel
  have hb : ∀ i j, |matrix 1 2 input.observation i j| ≤ 1 := by
    rw [hh]
    intro i j
    fin_cases i
    fin_cases j <;> norm_num [positionRow]
  have xb : ∀ i j, |matrix 2 1 prior.mean i j| ≤ 1 := by
    intro i j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simpa only [matrix, Flare.Matrix.Value.matrix, Fin.val_zero, Nat.mul_one,
      Nat.add_zero]
      using d.mean_bound i.val i.isLt
  have zb : ∀ i j, |matrix 1 1 input.measurement i j| ≤ 1 := by
    intro i j
    fin_cases i
    fin_cases j
    exact d.measurement_bound
  have projectedIdeal : ∀ i j, |(matrix 1 2 input.observation * matrix 2 1 prior.mean) i j| ≤ 1 := by
    intro i j
    fin_cases i
    fin_cases j
    simpa [hh, positionRow, Matrix.mul_apply] using xb 0 0
  obtain ⟨projected, _, hp, _, hpf, ep⟩ := product 1 2 1 input.observation prior.mean 1 1
    (by decide) hf d.mean_finite (by norm_num) (by norm_num) (by norm_num) hb xb
  have projectedBound := near_bound projected _ _ 1 2 ep projectedIdeal (by norm_num)
  have pr := sum_profile 1 1 input.measurement projected 1 2 2 true (by decide)
    d.measurement_size d.measurement_finite hpf (by norm_num) (by norm_num) (by norm_num) zb projectedBound
  obtain ⟨residual, hr, _, rf, _⟩ := FloatDenseError.sub_accuracy input.measurement projected 2
    pr.exponent_lower pr.exponent_upper d.measurement_finite hpf
    (by simpa only [↓reduceIte, ← sub_eq_add_neg] using pr.magnitude)
  have er := FloatJosephError.subtract_within (n := 1) (m := 1) pr d.measurement_size hr
  have erOriginal := within_trans er (within_sub (within_refl (matrix 1 1 input.measurement)) ep)
  have rb := near_bound residual _ _ 2 3 erOriginal (residual_bound input prior d) (by norm_num [sumRadius])
  obtain ⟨increment, _, hi, _, hif, ei⟩ := product 2 1 1 k residual 2 3
    (by decide) kf rf (by norm_num) (by norm_num) (by norm_num) kb rb
  have ib := near_bound increment _ _ 6 7 ei
    (by intro i j; exact (product_magnitude (matrix 2 1 k) (matrix 1 1 residual) 2 3 kb rb i j).trans (by norm_num))
    (by norm_num)
  have pm := sum_profile 2 1 prior.mean increment 1 7 4 false (by decide) d.mean_size d.mean_finite hif
    (by norm_num) (by norm_num) (by norm_num) xb ib
  obtain ⟨mean, hm, ms, mf, _⟩ := FloatDenseError.add_accuracy prior.mean increment 4
    pm.exponent_lower pm.exponent_upper d.mean_finite hif
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using pm.magnitude)
  have em := FloatJosephError.add_within (n := 2) (m := 1) pm d.mean_size hm
  have incError := within_trans ei (within_mul_left (matrix 2 1 k) erOriginal (by norm_num : (0 : ℝ) ≤ 2) kb)
  have total := within_trans em (within_add (within_refl (matrix 2 1 prior.mean)) incError)
  refine ⟨⟨
            projected,
            residual,
            increment,
            mean,
            hp,
            hr,
            hi,
            hm,
            ms.trans d.mean_size,
            mf,
            by positivity,
            ?_
          ⟩⟩
  intro i j
  exact (total.2 i j).trans (by norm_num [sumRadius])

end Kalman.Proofs.FloatJosephPositionMean
