import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.FloatFilterInputDomain
import Kalman.Proofs.FilterComposition

/-! Independent exact Kalman trajectory bounds from original stored inputs.
Optimal covariance decrease closes the reference invariant; no native error
or reached numerical profile is used in these exact-recursion bounds. -/

namespace Kalman.Proofs.RealFilterInvariant

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
open Kalman.Proofs.CorrelatedStages
open Kalman.Proofs.FilterComposition.Horizon
open Kalman.Proofs.FilterComposition
open Kalman.Proofs.ErrorPropagation

set_option maxHeartbeats 1000000

/-- Exact optimal correction removes a PSD covariance term. This does not
apply to a rounded computed gain or a separately rounded dense posterior. -/
theorem update_covariance_decrease {n m : Nat} (input : LinearModel.Model n m)
    (prior : LinearModel.State n) (measurement : LinearModel.Vector m)
    (hp : prior.covariance.PosSemidef) (hr : input.measurementNoise.PosDef)
    : (prior.covariance
        - (CovarianceRecursion.update .joseph input prior
            measurement).covariance).PosSemidef := by
  have hs := CovarianceStructure.innovation_posDef input prior hp hr
  have hk := RealRecursion.gain_innovation input prior hp hr
  have hpT : prior.covariance.transpose = prior.covariance := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hp.isHermitian.eq
  have hsT : (CovarianceRecursion.innovationCovariance input prior).transpose
      = CovarianceRecursion.innovationCovariance input prior := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hs.isHermitian.eq
  have hkt := congrArg Matrix.transpose hk
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hpT, hsT] at hkt
  have hd := hs.posSemidef.mul_mul_conjTranspose_same (CovarianceRecursion.gain input prior)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hd
  change (prior.covariance - CovarianceRecursion.joseph input prior (CovarianceRecursion.gain input prior)).PosSemidef
  rw [RealRecursion.joseph_eq_compact input prior hp hr,
    RealRecursion.compact_eq_subtractive, CovarianceRecursion.subtractive, sub_sub_cancel]
  simpa only [Matrix.mul_assoc, hkt] using hd

/-- The independently decoded original dense state meets the ideal invariant. -/
theorem initial_invariant (initial : Input.State) (d : InitializationDomain initial)
    : ReferenceInvariant (state 2 initial) := by
  refine ⟨FloatCholeskyDomain.input_positive _ d.covariance, ?_, ?_⟩
  · intro i j
    exact (FloatFilterInputDomain.noise_magnitude _ d.covariance d.diagonal_cap i j).trans (by norm_num [atDimensions])
  · intro i
    exact d.mean_bound i.val i.isLt

/-- Exact prediction and ideal gain/residual headroom from original model
words and an independent reference-state invariant. -/
theorem prediction_bounds (input : Input.Model) (p : ModelDomain input)
    (reference : LinearModel.State 2) (s : ReferenceInvariant reference)
    : let ideal := model (atDimensions 2 2 input)
      let prior := CovarianceRecursion.predict ideal reference
      prior.covariance.PosDef
      ∧ (∀ i j, |prior.covariance i j| ≤ 7 / 4)
      ∧ (∀ i, |prior.mean i| ≤ 1 / 4)
      ∧ (∀ i,
          |CovarianceRecursion.innovation ideal prior (vector 2 input.measurement) i| ≤ 2)
      ∧ (∀ i j, |CovarianceRecursion.gain ideal prior i j| ≤ 7 / 48) := by
  let ideal := model (atDimensions 2 2 input)
  let prior := CovarianceRecursion.predict ideal reference
  have hF : ∀ i j, |ideal.transition i j| ≤ 1 / 8 :=
    fun i j => p.transition_bound i.val j.val i.isLt j.isLt
  have hH : ∀ i j, |ideal.observation i j| ≤ 1 / 64 :=
    fun i j => p.observation_bound i.val j.val i.isLt j.isLt
  have hQ : ∀ i j, |ideal.processNoise i j| ≤ 3 / 2 :=
    FloatFilterInputDomain.noise_magnitude _ p.process_noise p.process_diagonal_cap
  have hq : ideal.processNoise.PosDef := FloatCholeskyDomain.input_positive _ p.process_noise
  have hr : (ideal.measurementNoise - (3 / 4 : ℝ) • 1).PosSemidef :=
    FloatCholeskyDomain.input_lower_bound _ p.noise
  have hprior : prior.covariance.PosDef := CovarianceStructure.prediction_posDef ideal reference s.covariance_positive.posSemidef hq
  have hcongruence := product_magnitude _ _ _ (1 / 8)
    (product_magnitude ideal.transition reference.covariance (1 / 8) 2 hF s.covariance_bound)
    (fun i j => hF j i)
  have hp : ∀ i j, |prior.covariance i j| ≤ 7 / 4 := by
    intro i j
    exact (abs_add_le _ _).trans ((add_le_add (hcongruence i j) (hQ i j)).trans (by norm_num [atDimensions]))
  have hμ := product_magnitude ideal.transition (fun i (_ : Fin 1) => reference.mean i)
    (1 / 8) 1 hF (fun i _ => s.mean_bound i)
  have hm : ∀ i, |prior.mean i| ≤ 1 / 4 := by
    intro i
    exact (hμ i 0).trans (by norm_num [atDimensions])
  have hhμ := product_magnitude ideal.observation (fun i (_ : Fin 1) => prior.mean i)
    (1 / 64) (1 / 4) hH (fun i _ => hm i)
  have hz : ∀ i, |CovarianceRecursion.innovation ideal prior (vector 2 input.measurement) i| ≤ 2 := by
    intro i
    exact (abs_sub _ _).trans ((add_le_add (p.measurement_bound i.val i.isLt) (hhμ i 0)).trans (by norm_num [atDimensions]))
  have hg := RecursionSensitivity.gain_magnitude ideal prior (3 / 4) (7 / 4) (1 / 64)
    (by norm_num [atDimensions]) (by norm_num [atDimensions]) (by norm_num [atDimensions]) hprior.posSemidef hr hp hH
  exact ⟨
    hprior,
    hp,
    hm,
    hz,
    fun i j =>
      (hg i j).trans
        (by
          norm_num [Kalman.Definitions.Theorems.RecursionSensitivity.gainMagnitude, atDimensions])
  ⟩

/-- Ideal correction preserves the reference-state invariant. Its covariance
bound uses exact optimal covariance decrease, independent of native roundoff. -/
theorem step_invariant (input : Input.Model) (p : ModelDomain input)
    (reference : LinearModel.State 2) (s : ReferenceInvariant reference)
    : ReferenceInvariant
        (CovarianceRecursion.step .joseph (model (atDimensions 2 2 input)) reference
          (vector 2 input.measurement)) := by
  let ideal := model (atDimensions 2 2 input)
  let prior := CovarianceRecursion.predict ideal reference
  let output := CovarianceRecursion.update .joseph ideal prior (vector 2 input.measurement)
  obtain ⟨hp, hc, hm, hz, hk⟩ := prediction_bounds input p reference s
  have hr : ideal.measurementNoise.PosDef := FloatCholeskyDomain.input_positive _ p.noise
  have ho : output.covariance.PosDef := RealRecursion.update_posDef .joseph ideal prior _ hp hr
  have hd := update_covariance_decrease ideal prior (vector 2 input.measurement) hp.posSemidef hr
  have hdiag : ∀ i, output.covariance i i ≤ 7 / 4 := by
    intro i
    have hh := hd.diag_nonneg (i := i)
    simp only [Matrix.sub_apply] at hh
    exact (le_of_sub_nonneg hh).trans ((le_abs_self _).trans (hc i i))
  have hcap : ∀ i j, |output.covariance i j| ≤ 7 / 4 := by
    intro i j
    have hs := Flare.Analysis.NumericalBounds.entry_sq_le_diagonal_product _ ho.posSemidef i j
    have hp2 : output.covariance i i * output.covariance j j ≤ (7 / 4 : ℝ)^2 := by
      nlinarith [hdiag i, hdiag j, ho.posSemidef.diag_nonneg (i := i), ho.posSemidef.diag_nonneg (i := j)]
    nlinarith [sq_abs (output.covariance i j), abs_nonneg (output.covariance i j)]
  have hinc := product_magnitude (CovarianceRecursion.gain ideal prior)
    (fun i (_ : Fin 1) => CovarianceRecursion.innovation ideal prior (vector 2 input.measurement) i)
    (7 / 48) 2 hk (fun i _ => hz i)
  refine ⟨ho, fun i j => (hcap i j).trans (by norm_num [atDimensions]), ?_⟩
  intro i
  exact (abs_add_le _ _).trans
    ((add_le_add (hm i) (hinc i 0)).trans (by norm_num [atDimensions]))

/-- Every ideal prefix, initialized from the original dense input, stays
within explicit covariance/mean bounds and remains strictly PD. -/
theorem run_invariant (inputs : Nat → Input.Model) (initial : Input.State) (horizon : Nat)
    (p : ∀ t, t < horizon → ModelDomain (inputs t)) (d : InitializationDomain initial)
    : ∀ t,
        t ≤ horizon → ReferenceInvariant (exactRun 2 2 inputs (state 2 initial) t) := by
  intro t ht
  induction t with
  | zero => exact initial_invariant initial d
  | succ t ih => exact step_invariant (inputs t) (p t (by omega)) _ (ih (by omega))

/-- Conditioning and magnitudes for the independently propagated exact
trajectory are conclusions of the original input domain at every prefix. -/
theorem reference_environment (input : Input.Model) (p : ModelDomain input)
    (reference : LinearModel.State 2) (s : ReferenceInvariant reference)
    : ∃ d : StepEnvironment (atDimensions 2 2 input) reference,
        d.noiseFloor = 3 / 4
        ∧ d.covarianceBound = 7 / 4
        ∧ d.noiseBound = 3 / 2
        ∧ d.innovationBound = 2 := by
  obtain ⟨_, hc, _, hz, _⟩ := prediction_bounds input p reference s
  exact ⟨
    ⟨
      3 / 4,
      7 / 4,
      3 / 2,
      2,
      by norm_num,
      by norm_num,
      by norm_num,
      by norm_num,
      (FloatCholeskyDomain.input_positive _ p.process_noise).posSemidef,
      FloatCholeskyDomain.input_lower_bound _ p.noise,
      hc,
      FloatFilterInputDomain.noise_magnitude _ p.noise p.noise_diagonal_cap,
      hz
    ⟩,
    rfl,
    rfl,
    rfl,
    rfl
  ⟩

end Kalman.Proofs.RealFilterInvariant
