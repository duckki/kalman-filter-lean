import Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
import Kalman.Proofs.FloatJosephGain
import Kalman.Proofs.FloatJosephStructure
import Kalman.Proofs.FloatObservableMean
import Kalman.Proofs.RealObservablePosterior
import Kalman.Proofs.RealObservableCorrection

namespace Kalman.Proofs.FloatJosephUpdate

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1600000

/-! ----------------------------------------------------------------------
## Original correction inputs
-------------------------------------------------------------------------- -/

structure UpdateDomain (input : Input.Model) (prior : Input.State) : Prop where
  state_dimension : input.stateDimension = 2
  measurement_dimension : input.measurementDimension = 2
  prior_size : prior.covariance.size = 4
  observation_size : input.observation.size = 4
  noise_size : input.measurementNoise.size = 4
  gain
    : FloatJosephGain.GainDomain prior.covariance input.observation input.measurementNoise
  vectors : DiagonalStages.Mean.VectorDomain prior.mean input.measurement

/-! ----------------------------------------------------------------------
## Exact scalar/diagonal bridges
-------------------------------------------------------------------------- -/

private theorem vector_entry (a : Array Float) (i : Fin 2)
    : matrix 2 1 a i 0 = value (a.getD i.val 0.0) := by
  simp [matrix, Flare.Matrix.Value.matrix]

private theorem posterior_mean_affine (p r x z : ℝ) (ht : p + r ≠ 0)
    : DiagonalObservation.posteriorMean p r x z
      = x + DiagonalObservation.optimalGain p r * (z - x) := by
  unfold DiagonalObservation.posteriorMean DiagonalObservation.optimalGain
  field_simp
  ring

private theorem joseph_diagonal_arrays (p r k : Array Float)
    (pd : DecodedDiagonal 2 p) (rd : DecodedDiagonal 2 r) (kd : DecodedDiagonal 2 k)
    : (1 - matrix 2 2 k) * matrix 2 2 p * (1 - matrix 2 2 k).transpose
        + matrix 2 2 k * matrix 2 2 r * (matrix 2 2 k).transpose
      = diagonal
          (fun i =>
            DiagonalObservation.josephVariance
              (matrix 2 2 p i i) (matrix 2 2 r i i) (matrix 2 2 k i i)) := by
  conv_lhs =>
    rw [FloatDiagonalStorage.matrix_diagonal 2 p pd,
      FloatDiagonalStorage.matrix_diagonal 2 r rd,
      FloatDiagonalStorage.matrix_diagonal 2 k kd, RealObservablePosterior.joseph_diagonal]

/-! ----------------------------------------------------------------------
## Complete native correction
-------------------------------------------------------------------------- -/

/-- The propagated dense-state floor and exact diagonal structure imply
strict positivity of the actual stored covariance. -/
theorem invariant_positive (current : Input.State) (d : StateInvariant current)
    : (matrix 2 2 current.covariance).PosDef := by
  rw [FloatDiagonalStorage.matrix_diagonal 2 current.covariance d.diagonal,
    Matrix.posDef_diagonal_iff]
  intro i
  linarith [d.covariance_floor i]

/-- A complete native direct-Joseph correction, including computed gain and
mean, succeeds and restores the dense-state invariant. Original stored inputs
alone establish local covariance and mean error at most 2^-33. -/
theorem update_accuracy (input : Input.Model) (prior : Input.State)
    (d : UpdateDomain input prior)
    : ∃ output, CorrectionAccuracy input prior output := by
  obtain ⟨g⟩ := FloatJosephGain.gain_stages prior.covariance input.observation input.measurementNoise d.gain
  let k := transpose 2 2 g.solution
  have kb := FloatDiagonalStorage.diagonal_magnitude 2 k 1 g.gain_diagonal
    (fun i => (by norm_num : (0 : ℝ) ≤ 3 / 8).trans (g.gain_floor i))
    (fun i => (g.gain_cap i).trans (by norm_num)) (by norm_num)
  have pb := FloatDiagonalStorage.diagonal_magnitude 2 prior.covariance 4 d.gain.prior_diagonal
    (fun i => (by norm_num : (0 : ℝ) ≤ 15 / 16).trans (d.gain.prior_floor i))
    (fun i => (d.gain.prior_cap i).trans (by norm_num)) (by norm_num)
  have rb := FloatDiagonalStorage.diagonal_magnitude 2 input.measurementNoise (3 / 2) d.gain.noise_diagonal
    (fun i => (by norm_num : (0 : ℝ) ≤ 1).trans (d.gain.noise_floor i)) d.gain.noise_cap (by norm_num)
  have hb : ∀ i j, |matrix 2 2 input.observation i j| ≤ 1 := by
    rw [d.gain.observation_identity]
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hd : DecodedDiagonal 2 input.observation := by
    intro i j hi hj hij
    change matrix 2 2 input.observation ⟨i, hi⟩ ⟨j, hj⟩ = 0
    rw [d.gain.observation_identity]
    exact Matrix.one_apply_ne (fun he => hij (Fin.val_eq_of_eq he))
  have cd : Kalman.Implementation.Correctness.JosephCovarianceEvaluation.TwoStateDomain input prior k :=
    ⟨d.state_dimension, d.measurement_dimension, d.prior_size, d.observation_size, d.noise_size,
      g.gain_size, d.gain.prior_finite, d.gain.observation_finite, d.gain.noise_finite, g.gain_finite,
      pb, hb, rb, kb⟩
  obtain ⟨cov, cs, cf, ce, cz⟩ := FloatJosephStructure.stored_input_diagonal_accuracy input prior k cd
    d.gain.prior_diagonal hd d.gain.noise_diagonal g.gain_diagonal
  have ec := ce.2
  simp only [CovarianceRecursion.joseph, model, state] at ec
  rw [d.state_dimension, d.measurement_dimension, d.gain.observation_identity, Matrix.mul_one,
    joseph_diagonal_arrays _ _ _ d.gain.prior_diagonal d.gain.noise_diagonal g.gain_diagonal] at ec
  have eg : EntrywiseWithin ((2 : ℝ)^(-50 : Int))
      (diagonal (fun i => DiagonalObservation.josephVariance
        (matrix 2 2 prior.covariance i i) (matrix 2 2 input.measurementNoise i i) (matrix 2 2 k i i)))
      (diagonal (fun i => DiagonalObservation.posteriorVariance
        (matrix 2 2 prior.covariance i i) (matrix 2 2 input.measurementNoise i i))) := by
    refine ⟨by positivity, ?_⟩
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      apply RealObservablePosterior.joseph_gain_accuracy _ _ _ (d.gain.prior_floor i) (d.gain.prior_cap i)
        (d.gain.noise_floor i) (d.gain.noise_cap i)
      exact (g.gain_pointwise i).trans (by norm_num)
    · simp [Matrix.diagonal_apply_ne _ hij]
  have ecov : EntrywiseWithin ((2 : ℝ)^(-33 : Int)) (matrix 2 2 cov)
      (diagonal (fun i => DiagonalObservation.posteriorVariance
        (matrix 2 2 prior.covariance i i) (matrix 2 2 input.measurementNoise i i))) := by
    refine ⟨by positivity, fun i j => ((within_trans ec eg).2 i j).trans ?_⟩
    norm_num
  have cfloor : ∀ i, (7 : ℝ) / 16 ≤ matrix 2 2 cov i i := by
    intro i
    have he := (abs_le.mp (ecov.2 i i)).1
    simp only [Matrix.diagonal_apply_eq] at he
    have hb' := (RealObservablePosterior.posterior_variance_bounds _ _ (d.gain.prior_floor i)
      (d.gain.prior_cap i) (d.gain.noise_floor i) (d.gain.noise_cap i)).1
    norm_num only at he
    linarith
  have ccap : ∀ i, matrix 2 2 cov i i ≤ (13 : ℝ) / 8 := by
    intro i
    have he := (abs_le.mp (ecov.2 i i)).2
    simp only [Matrix.diagonal_apply_eq] at he
    have hb' := (RealObservablePosterior.posterior_variance_bounds _ _ (d.gain.prior_floor i)
      (d.gain.prior_cap i) (d.gain.noise_floor i) (d.gain.noise_cap i)).2
    norm_num only at he
    linarith
  obtain ⟨projected, residual, increment, mean, _, hp, _, hr, _, hi, _, hm, ms, mf, mb, me⟩ :=
    FloatObservableMean.mean_stages input.observation prior.mean input.measurement k d.vectors
      d.gain.observation_finite g.gain_finite d.gain.observation_identity g.gain_diagonal
      (fun i hi => ⟨g.gain_floor ⟨i, hi⟩, g.gain_cap ⟨i, hi⟩⟩)
  have emean : ∀ i, |value (mean.getD i.val 0.0)
      - DiagonalObservation.posteriorMean (matrix 2 2 prior.covariance i i)
          (matrix 2 2 input.measurementNoise i i) (value (prior.mean.getD i.val 0.0))
          (value (input.measurement.getD i.val 0.0))| ≤ (2 : ℝ)^(-33 : Int) := by
    intro i
    have he := me.2 i 0
    rw [FloatDiagonalStorage.matrix_diagonal 2 k g.gain_diagonal] at he
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.sub_apply, vector_entry] at he
    have hg := g.gain_pointwise i
    have ht : matrix 2 2 prior.covariance i i + matrix 2 2 input.measurementNoise i i ≠ 0 := by
      linarith [d.gain.prior_floor i, d.gain.noise_floor i]
    rw [posterior_mean_affine _ _ _ _ ht]
    have hres : |value (input.measurement.getD i.val 0.0) - value (prior.mean.getD i.val 0.0)| ≤ 3 :=
      (abs_sub _ _).trans ((add_le_add (d.vectors.measurement_bound i.val i.isLt)
        (d.vectors.mean_bound i.val i.isLt)).trans (by norm_num))
    have hmul := mul_le_mul hg hres (abs_nonneg _) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(-36 : Int))
    have eq : value (mean.getD i.val 0.0)
        - (value (prior.mean.getD i.val 0.0)
          + DiagonalObservation.optimalGain (matrix 2 2 prior.covariance i i)
              (matrix 2 2 input.measurementNoise i i)
            * (value (input.measurement.getD i.val 0.0) - value (prior.mean.getD i.val 0.0)))
        = (value (mean.getD i.val 0.0) - (value (prior.mean.getD i.val 0.0)
            + matrix 2 2 k i i * (value (input.measurement.getD i.val 0.0) - value (prior.mean.getD i.val 0.0))))
          + (matrix 2 2 k i i - DiagonalObservation.optimalGain (matrix 2 2 prior.covariance i i)
              (matrix 2 2 input.measurementNoise i i))
            * (value (input.measurement.getD i.val 0.0) - value (prior.mean.getD i.val 0.0)) := by ring
    rw [eq]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have hh := add_le_add he hmul
    apply hh.trans
    norm_num
  let output : Input.State := ⟨mean, cov⟩
  have correction : Kalman.Implementation.CovarianceFilter.correctionUnchecked input prior
      = .ok ⟨k, g.innovation, residual⟩ := by
    simp [Kalman.Implementation.CovarianceFilter.correctionUnchecked, d.state_dimension,
      d.measurement_dimension, g.computeHP, g.computeHPH, g.computeInnovation, g.computePHT,
      g.computeSolution, hp, hr, k, bind, Except.bind, pure, Except.pure]
  have run : Kalman.Implementation.CovarianceFilter.updateUnchecked .joseph input prior = .ok output := by
    simp [Kalman.Implementation.CovarianceFilter.updateUnchecked, correction,
      d.state_dimension, d.measurement_dimension, hi, hm, ce.1, output,
      bind, Except.bind, pure, Except.pure]
  have ideal := RealObservableCorrection.update_eq_full_observation .joseph
    (model (atDimensions 2 2 input)) (state 2 prior) (vector 2 input.measurement)
    (fun i => matrix 2 2 prior.covariance i i) (fun i => matrix 2 2 input.measurementNoise i i)
    d.gain.observation_identity
    (FloatDiagonalStorage.matrix_diagonal 2 prior.covariance d.gain.prior_diagonal)
    (FloatDiagonalStorage.matrix_diagonal 2 input.measurementNoise d.gain.noise_diagonal)
    (fun i => (by norm_num : (0 : ℝ) ≤ 15 / 16).trans (d.gain.prior_floor i))
    (fun i => (by norm_num : (0 : ℝ) < 1).trans_le (d.gain.noise_floor i))
  refine ⟨output, run, ⟨ms, cs, mf, cf, cz, cfloor, ccap, mb⟩, ?_⟩
  apply (congrArg (fun reference => StateWithin ((2 : ℝ)^(-33 : Int))
    ((2 : ℝ)^(-33 : Int)) (state 2 output) reference) ideal).mpr
  exact ⟨ecov, by positivity, emean⟩

end Kalman.Proofs.FloatJosephUpdate
