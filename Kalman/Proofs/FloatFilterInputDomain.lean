import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Implementation.SquareRootFilter
import Kalman.Proofs.FloatPosteriorDomain
import Kalman.Proofs.FloatFullFilter

/-! All full-step profiles and successful checked execution follow from an
original two-state operating domain. Its stored-state bounds are invariant. -/

namespace Kalman.Proofs.FloatFilterInputDomain

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
open Kalman.Proofs.CorrelatedStages
open Kalman.Proofs.FilterComposition
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1400000

/-- Recover original storage checks from the factor's input representation. -/
theorem factor_storage (current : Input.FactorState) (p : StateInvariant current)
    : current.mean.size = 2
      ∧ current.lower.size = 4
      ∧ current.mean.all Float.isFinite = true
      ∧ current.lower.all Float.isFinite = true := by
  have hv := p.valid.1
  cases hs : (current.mean.size == 2 && current.lower.size == 2 * 2) with
  | false => simp [Input.FactorState.validate, hs] at hv
  | true =>
      cases hf
            : (current.mean.all Float.isFinite && current.lower.all Float.isFinite) with
      | false => simp [Input.FactorState.validate, hs, hf] at hv
      | true =>
          obtain ⟨hm, hl⟩ := Bool.and_eq_true_iff.mp hs
          obtain ⟨hmf, hlf⟩ := Bool.and_eq_true_iff.mp hf
          exact ⟨of_decide_eq_true hm, of_decide_eq_true hl, hmf, hlf⟩

/-- Static original inputs derive every executable model validation check. -/
theorem input_validate (input : Input.Model) (p : ModelDomain input)
    : input.validate = .ok () := by
  have hq := FloatCholeskyDomain.input_symmetric input.processNoise p.process_noise
  have hr := FloatCholeskyDomain.input_symmetric input.measurementNoise p.noise
  have hd : (0 < input.stateDimension && input.stateDimension ≤ 32
      && 0 < input.measurementDimension && input.measurementDimension ≤ 32) = true := by
    simp [p.state_dimension, p.measurement_dimension]
  have hs : (input.transition.size == input.stateDimension * input.stateDimension
      && input.observation.size == input.measurementDimension * input.stateDimension
      && input.processNoise.size == input.stateDimension * input.stateDimension
      && input.measurementNoise.size == input.measurementDimension * input.measurementDimension
      && input.measurement.size == input.measurementDimension) = true := by
    simp [p.state_dimension, p.measurement_dimension, p.transition_size, p.observation_size,
      p.process_noise.size, p.noise.size, p.measurement_size]
  have hsym : (Input.symmetric input.stateDimension input.processNoise
      && Input.symmetric input.measurementDimension input.measurementNoise) = true := by
    simp [p.state_dimension, p.measurement_dimension, hq, hr]
  have hf : #[input.transition, input.observation, input.processNoise,
      input.measurementNoise, input.measurement].all (fun a => a.all Float.isFinite) = true := by
    rw [Array.all_eq_true]
    intro i hi
    change i < 5 at hi
    interval_cases i
    · exact p.transition_finite
    · exact p.observation_finite
    · exact p.process_noise.finite
    · exact p.noise.finite
    · exact p.measurement_finite
  simp only [Input.Model.validate, hd, hs, hf, hsym, ↓reduceIte, pure, Except.pure]

/-- The stored-state invariant and static inputs establish prediction's whole
input domain. No previous-step profile or accuracy is needed. -/
theorem prediction_domain (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : Kalman.Proofs.CorrelatedStages.Prediction.TwoStateDomain input initial := by
  obtain ⟨hm, hl, hmf, hlf⟩ := factor_storage initial s
  exact ⟨p.state_dimension,
    ⟨p.transition_size, hl, p.transition_finite, hlf, p.transition_bound,
      s.factor_bound, s.covariance_bound⟩,
    p.process_noise, p.process_diagonal_cap, hm, hmf, s.mean_bound⟩

/-- Every complete-filter profile and its constants are derived from original
model bounds and the incoming stored-state representation/bounds. -/
theorem step_profile (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : ∃ profile : StepProfile input initial, StepParameters profile := by
  have d := prediction_domain input initial p s
  obtain ⟨prediction, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := FloatPredictionDomain.prediction_profile input initial d
  have dq : GramFactorInputDomain 2 4 (fromCols 2 2 2 prediction.fl prediction.tq) 2 := by
    simpa only [p.state_dimension, h6] using prediction.qr
  obtain ⟨l, hl, _, _, _, _, _, _⟩ := FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 4 _ 2 dq
  have hln : Kalman.Implementation.OrthogonalFactorization.gramFactor input.stateDimension
      (input.stateDimension + input.stateDimension)
      (fromCols input.stateDimension input.stateDimension input.stateDimension prediction.fl prediction.tq) = .ok l := by
    simpa only [p.state_dimension] using hl
  have hrun : Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok ⟨prediction.mean, l⟩ := by
    simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, prediction.noise.execution,
      prediction.computeProduct, hln, prediction.computeMean, bind, Except.bind, pure, Except.pure]
  obtain ⟨prior, hr, dp⟩ := FloatPosteriorDomain.prediction_posterior_domain input initial d p.toCorrectionInputs
  have eq : prior = ⟨prediction.mean, l⟩ := Except.ok.inj (hr.symm.trans hrun)
  subst prior
  obtain ⟨innovation, gain, g, mean, hm1, hm2, hm3, hm4, _, posterior, q, _⟩ :=
    FloatPosteriorDomain.correction_profiles input ⟨prediction.mean, l⟩ dp
  let profile : StepProfile input initial := ⟨prediction, l, hln, innovation, gain, mean, posterior⟩
  exact ⟨profile, h1, h2, h3, h4, h5, h6, h7, h8, g, hm1, hm2, hm3, hm4, q⟩

/-- Original covariance entry cap from its PD Cholesky input domain and
diagonal headroom, including correlations. -/
theorem noise_magnitude (a : Array Float)
    (p : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain a)
    (hd : ∀ i, i < 2 → value (entry 2 a i i) ≤ 3 / 2)
    : ∀ i j, |matrix 2 2 a i j| ≤ 3 / 2 := by
  have hp := (FloatCholeskyDomain.input_positive a p).posSemidef
  intro i j
  have hs := Flare.Analysis.NumericalBounds.entry_sq_le_diagonal_product _ hp i j
  have hi := hd i.val i.isLt
  have hj := hd j.val j.isLt
  change matrix 2 2 a i i ≤ _ at hi
  change matrix 2 2 a j j ≤ _ at hj
  have hm : matrix 2 2 a i i * matrix 2 2 a j j ≤ (3 / 2 : ℝ)^2 := by
    nlinarith [hi, hj, hp.diag_nonneg (i := i), hp.diag_nonneg (i := j)]
  nlinarith [sq_abs (matrix 2 2 a i j), abs_nonneg (matrix 2 2 a i j)]

/-- Original dense initialization derives the retained-state invariant and
covariance error 2^-42, without a validation, Cholesky run or output-bound premise. -/
theorem initialize_invariant (input : Input.Model) (initial : Input.State)
    (p : ModelDomain input) (d : InitializationDomain initial)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.fromCovariance input initial = .ok output
        ∧ StateInvariant output
        ∧ FactorAccuracy ((2 : ℝ) ^ (-42 : Int)) 0 2 output (state 2 initial)
        ∧ (state 2 initial).covariance.PosDef := by
  obtain ⟨l, hls, hl, hlf, hlp, hpd, _, _, he⟩ := FloatCholeskyDomain.cholesky_accuracy initial.covariance d.covariance
  have hv := FloatFactorValidity.factor_validate_complete 2 ⟨initial.mean, l⟩
    d.mean_size hls d.mean_finite hlf hlp
  have hs : initial.validate 2 = .ok () := by
    have hshape : (initial.mean.size == 2 && initial.covariance.size == 2 * 2) = true := by
      simp [d.mean_size, d.covariance.size]
    have hfinite : (initial.mean.all Float.isFinite && initial.covariance.all Float.isFinite) = true := by
      simp only [d.mean_finite, d.covariance.finite, Bool.and_self]
    simp [Input.State.validate, hshape, hfinite, pure, Except.pure]
  have hs' : initial.validate input.stateDimension = .ok () := by
    simpa only [p.state_dimension] using hs
  have hsym := FloatCholeskyDomain.input_symmetric initial.covariance d.covariance
  have hln : cholesky input.stateDimension initial.covariance = .ok l := by
    simpa only [p.state_dimension] using hl
  have hsymn : Input.symmetric input.stateDimension initial.covariance = true := by
    simpa only [p.state_dimension] using hsym
  have hrun : Kalman.Implementation.SquareRootFilter.fromCovariance input initial = .ok ⟨initial.mean, l⟩ := by
    simp [Kalman.Implementation.SquareRootFilter.fromCovariance, input_validate input p,
      hs', hsymn, hln, bind, Except.bind, pure, Except.pure]
  have hd := FloatCholeskySolveDomain.factor_domain_of_cholesky initial.covariance l d.covariance hl
  have hcap := noise_magnitude initial.covariance d.covariance d.diagonal_cap
  have hc : ∀ i j, |FactorRecursion.gram (matrix 2 2 l) i j| ≤ 2 := by
    intro i j
    have hab := abs_sub_le (FactorRecursion.gram (matrix 2 2 l) i j) (matrix 2 2 initial.covariance i j) 0
    simp only [sub_zero] at hab
    exact hab.trans ((add_le_add (he.2 i j) (hcap i j)).trans (by norm_num))
  have ha : FactorAccuracy ((2 : ℝ)^(-42 : Int)) 0 2 ⟨initial.mean, l⟩ (state 2 initial) := by
    refine ⟨hv, he, le_rfl, ?_⟩
    intro i
    simp [state]
  exact ⟨_, hrun, ⟨hv, d.mean_bound, hd.entry_bound, hc⟩, ha, hpd⟩

/-- The ideal full-step reference environment follows from the same original
model/state bounds. It predicts the incoming stored state exactly, independently
of rounded prediction. -/
theorem step_environment (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : ∃ d : StepEnvironment input (factorState input.stateDimension initial),
        d.noiseFloor = 3 / 4
        ∧ d.covarianceBound = 7 / 4
        ∧ d.noiseBound = 3 / 2
        ∧ d.innovationBound = 2 := by
  have hq : ∀ n : Nat, n = 2 → (matrix n n input.processNoise).PosSemidef := by
    intro n hn
    subst n
    exact (FloatCholeskyDomain.input_positive _ p.process_noise).posSemidef
  have hr : ∀ m : Nat, m = 2 → (matrix m m input.measurementNoise - (3 / 4 : ℝ) • 1).PosSemidef := by
    intro m hm
    subst m
    exact FloatCholeskyDomain.input_lower_bound _ p.noise
  have hn : ∀ m : Nat, m = 2 → ∀ i j, |matrix m m input.measurementNoise i j| ≤ 3 / 2 := by
    intro m hm
    subst m
    exact noise_magnitude _ p.noise p.noise_diagonal_cap
  have hQ : ∀ n : Nat, n = 2 → ∀ i j, |matrix n n input.processNoise i j| ≤ 3 / 2 := by
    intro n hn
    subst n
    exact noise_magnitude _ p.process_noise p.process_diagonal_cap
  have hP : ∀ n : Nat, n = 2 → ∀ i j, |(factorState n initial).covariance i j| ≤ 2 := by
    intro n hn
    subst n
    exact s.covariance_bound
  have hF : ∀ i j, |(model input).transition i j| ≤ 1 / 8 := by
    have hFn : ∀ i j : Nat, i < input.stateDimension → j < input.stateDimension →
        |value (entry input.stateDimension input.transition i j)| ≤ 1 / 8 := by
      simpa only [p.state_dimension] using p.transition_bound
    exact fun i j => hFn i.val j.val i.isLt j.isLt
  have hH : ∀ i j, |(model input).observation i j| ≤ 1 / 64 := by
    have hHn : ∀ i j : Nat, i < input.measurementDimension → j < input.stateDimension →
        |value (entry input.stateDimension input.observation i j)| ≤ 1 / 64 := by
      simpa only [p.state_dimension, p.measurement_dimension] using p.observation_bound
    exact fun i j => hHn i.val j.val i.isLt j.isLt
  have hmu : ∀ (i : Fin input.stateDimension) (j : Fin 1),
      |matrix input.stateDimension 1 initial.mean i j| ≤ 1 := by
    intro i j
    fin_cases j
    simpa [matrix, Flare.Matrix.Value.matrix]
      using s.mean_bound i.val (by simpa only [p.state_dimension] using i.isLt)
  have hcov := product_magnitude _ _ _ (1 / 8)
    (product_magnitude (model input).transition (factorState input.stateDimension initial).covariance
      (1 / 8) 2 hF (hP _ p.state_dimension)) (fun i j => hF j i)
  have hmean := product_magnitude (model input).transition (matrix input.stateDimension 1 initial.mean)
    (1 / 8) 1 hF hmu
  have hpmean : ∀ (i : Fin input.stateDimension) (j : Fin 1),
      |(fun i (_ : Fin 1) => (CovarianceRecursion.predict (model input)
        (factorState input.stateDimension initial)).mean i) i j| ≤ 1 / 4 := by
    intro i j
    have hh := hmean i j
    fin_cases j
    change |Matrix.mulVec (model input).transition (vector input.stateDimension initial.mean) i| ≤ _
    have hh' : |((model input).transition * matrix input.stateDimension 1 initial.mean) i 0| ≤ 1 / 4 :=
      hh.trans (by norm_num [p.state_dimension])
    convert hh' using 1
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, vector, matrix, Flare.Matrix.Value.matrix]
  have hpH := product_magnitude (model input).observation
    (fun i (_ : Fin 1) => (CovarianceRecursion.predict (model input)
      (factorState input.stateDimension initial)).mean i) (1 / 64) (1 / 4) hH hpmean
  refine ⟨
    ⟨
      3 / 4,
      7 / 4,
      3 / 2,
      2,
      by norm_num,
      by norm_num,
      by norm_num,
      by norm_num,
      hq _ p.state_dimension,
      hr _ p.measurement_dimension,
      ?_,
      hn _ p.measurement_dimension,
      ?_
    ⟩,
    rfl,
    rfl,
    rfl,
    rfl
  ⟩
  · intro i j
    exact (abs_add_le _ _).trans ((add_le_add (hcov i j) (hQ _ p.state_dimension i j)).trans
      (by norm_num [p.state_dimension]))
  · intro i
    have hz := p.measurement_bound i.val (by simpa only [p.measurement_dimension] using i.isLt)
    have hproj := hpH i 0
    change |Matrix.mulVec (model input).observation
      (CovarianceRecursion.predict (model input) (factorState input.stateDimension initial)).mean i| ≤ _ at hproj
    exact (abs_sub _ _).trans ((add_le_add hz hproj).trans (by norm_num [p.state_dimension]))

/-- A full checked step succeeds and preserves the original stored-state
operating domain, including strictly PD exact covariance. Both Q and R may be
correlated within the original domain. -/
theorem step_invariant (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.step input initial = .ok output
        ∧ StateInvariant output
        ∧ (factorState 2 output).covariance.PosDef := by
  obtain ⟨prior, hp, dp⟩ := FloatPosteriorDomain.prediction_posterior_domain input initial
    (prediction_domain input initial p s) p.toCorrectionInputs
  obtain ⟨output, hu, ha, _, hm, hl, hc⟩ := FloatPosteriorDomain.correction_accuracy_and_bounds input prior dp
  have hv : Kalman.Implementation.Correctness.SquareRootFilterProperties.ValidFactor 2 output := by
    simpa only [p.state_dimension] using ha.1
  have hvn : initial.validate input.stateDimension = .ok () := by
    simpa only [p.state_dimension] using s.valid.1
  have hvo : output.validate input.stateDimension = .ok () := ha.1.1
  refine ⟨
    output,
    ?_,
    ⟨hv, hm, hl, hc⟩,
    FloatFactorValidity.validFactor_posDef 2 output hv
  ⟩
  simp [Kalman.Implementation.SquareRootFilter.step, input_validate input p,
    hvn, hp, hu, hvo, bind, Except.bind, pure, Except.pure]

/-- Every finite prefix succeeds and retains the same bounded PD state from
only original model conditions and the initial stored-state invariant.
This theorem makes no trajectory accuracy claim. -/
theorem run_invariant (inputs : Nat → Input.Model) (initial : Input.FactorState)
    (horizon : Nat) (p : ∀ t, t < horizon → ModelDomain (inputs t))
    (s : StateInvariant initial)
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            Kalman.Implementation.SquareRootFilter.run inputs initial t = .ok output
            ∧ StateInvariant output
            ∧ (factorState 2 output).covariance.PosDef := by
  intro t ht
  induction t with
  | zero =>
      exact ⟨initial, rfl, s, FloatFactorValidity.validFactor_posDef 2 initial s.valid⟩
  | succ t ih =>
      obtain ⟨current, hr, hs, _⟩ := ih (by omega)
      obtain ⟨output, ho, so, hp⟩ := step_invariant (inputs t) current (p t (by omega)) hs
      exact ⟨
        output,
        by simp [Kalman.Implementation.SquareRootFilter.run, hr, ho,
          bind, Except.bind],
        so,
        hp
      ⟩

/-- Checked dense initialization followed by every finite prefix succeeds and
preserves bounded positive-definite retained covariance. All premises constrain
the original words; accumulated ideal-trajectory error is a later theorem. -/
theorem initialized_run_invariant (initializationInput : Input.Model)
    (initial : Input.State) (inputs : Nat → Input.Model) (horizon : Nat)
    (p : ModelDomain initializationInput) (d : InitializationDomain initial)
    (q : ∀ t, t < horizon → ModelDomain (inputs t))
    : ∃ retained,
        Kalman.Implementation.SquareRootFilter.fromCovariance initializationInput initial
          = .ok retained
        ∧ FactorAccuracy ((2 : ℝ) ^ (-42 : Int)) 0 2 retained (state 2 initial)
        ∧ (∀ t,
            t ≤ horizon
            → ∃ output,
                Kalman.Implementation.SquareRootFilter.run inputs retained t = .ok output
                ∧ StateInvariant output
                ∧ (factorState 2 output).covariance.PosDef) := by
  obtain ⟨retained, hr, hs, ha, _⟩ := initialize_invariant initializationInput initial p d
  exact ⟨retained, hr, ha, run_invariant inputs retained horizon q hs⟩

/-- Full-step roundoff, including rounded prediction's effect on the ideal
correction, fits the existing refined tolerance on this original local domain. -/
theorem step_radius_caps (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (profile : StepProfile input initial)
    (c : StepParameters profile)
    (d : StepEnvironment input (factorState input.stateDimension initial))
    (h1 : d.noiseFloor = 3 / 4) (h2 : d.covarianceBound = 7 / 4)
    (h3 : d.noiseBound = 3 / 2) (h4 : d.innovationBound = 2)
    : stepCovarianceRadius profile d 0 ≤ (2 : ℝ) ^ (-25 : Int)
      ∧ stepMeanRadius profile d 0 0 ≤ (2 : ℝ) ^ (-25 : Int) := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hη : (2 : ℝ)^(-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  have hη3 := pow_le_one₀ hη0 hη1 (n := 3)
  have hη4 := pow_le_one₀ hη0 hη1 (n := 4)
  constructor <;> simp only [stepCovarianceRadius, stepMeanRadius, predictedCovarianceRadius,
    predictedMeanRadius, predictionCovarianceRadius, predictionMeanRadius,
    posteriorRadius, posteriorEvaluationRadius, meanRadius, gainRadius, gainResidualRadius,
    innovationRadius, gainMagnitude, correctionCovarianceRadius, correctionMeanRadius,
    correctionGainRadius, p.state_dimension, p.measurement_dimension,
    c.prediction_noise_mass, c.prediction_noise_floor, c.prediction_noise_bound,
    c.prediction_product_mass, c.prediction_mean_mass, c.prediction_qr_budget,
    c.transition_bound, c.factor_bound, c.gain.noise_mass, c.gain.noise_floor, c.gain.noise_bound,
    c.gain.innovation_product_mass, c.gain.innovation_qr_budget, c.gain.observation_bound,
    c.gain.factor_bound, c.gain.gain_product_mass, c.gain.solve_mass, c.gain.solve_floor,
    c.gain.solve_bound, c.gain.gain_bound, c.mean_projected_mass, c.mean_increment_mass,
    c.mean_residual_exponent, c.mean_exponent, c.posterior.kh_mass, c.posterior.wl_mass,
    c.posterior.ktr_mass, c.posterior.qr_budget, c.posterior.noise_factor_bound,
    c.posterior.w_exponent, h1, h2, h3, h4,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius,
    columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius,
    Finset.sum_range_succ, Finset.sum_range_zero, productRadius, diagonalRadius, divisionRadius,
    residualRadius, sumRadius, hη] <;> norm_num <;> ring_nf <;> linarith

/-- Complete checked-step accuracy against an independently exact prediction
and Joseph correction of the incoming stored state, with every arithmetic
profile, validation check and reference magnitude derived from original inputs.
The returned invariant also holds; accumulated trajectory error is separate. -/
theorem step_accuracy_and_invariant (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.step input initial = .ok output
        ∧ FactorAccuracy ((2 : ℝ) ^ (-25 : Int)) ((2 : ℝ) ^ (-25 : Int))
            input.stateDimension output
            (CovarianceRecursion.step .joseph (model input)
              (factorState input.stateDimension initial)
              (vector input.measurementDimension input.measurement))
        ∧ StateInvariant output
        ∧ (factorState 2 output).covariance.PosDef := by
  obtain ⟨profile, c⟩ := step_profile input initial p s
  obtain ⟨d, h1, h2, h3, h4⟩ := step_environment input initial p s
  have hv : Kalman.Implementation.Correctness.SquareRootFilterProperties.ValidFactor input.stateDimension initial := by
    have hvalid : ∀ n : Nat, n = 2 → Kalman.Implementation.Correctness.SquareRootFilterProperties.ValidFactor n initial := by
      intro n hn
      subst n
      exact s.valid
    exact hvalid _ p.state_dimension
  obtain ⟨output, hr, ha⟩ := FloatFullFilter.step_accuracy input initial _ profile d 0 0
    (input_validate input p) hv (CovarianceStructure.gram_posSemidef _)
    ⟨within_refl _, le_rfl, fun i => by simp⟩
  obtain ⟨hp, hm⟩ := step_radius_caps input initial p profile c d h1 h2 h3 h4
  obtain ⟨out', hr', hs, hd⟩ := step_invariant input initial p s
  have eq : out' = output := Except.ok.inj (hr'.symm.trans hr)
  subst out'
  exact ⟨
    output,
    hr,
    ⟨
      ha.1,
      ⟨by positivity, fun i j => (ha.2.1.2 i j).trans hp⟩,
      by positivity,
      fun i => (ha.2.2.2 i).trans hm
    ⟩,
    hs,
    hd
  ⟩

/-- An explicit correlated covariance in the initialization/noise headroom. -/
theorem correlated_noise_domain
    : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain
        #[1.0, 0.25, 0.25, 1.5]
      ∧ (∀ i, i < 2 → value (entry 2 #[1.0, 0.25, 0.25, 1.5] i i) ≤ 3 / 2) := by
  have hq : value (0.25 : Float) = (1 : ℝ) / 4 := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-54 : Int) = _
    norm_num
  have ht : value (1.5 : Float) = (3 : ℝ) / 2 := by
    change (6755399441055744 : ℝ) * (2 : ℝ)^(-52 : Int) = _
    norm_num
  constructor
  · refine ⟨by decide, by decide +kernel, rfl, ?_, ?_, ?_⟩
    · intro i hi
      interval_cases i <;> norm_num [entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.one_value, ht]
    · intro i hi
      interval_cases i <;> norm_num [entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.one_value, ht]
    · norm_num [entry, Flare.Matrix.Dense.entry, hq]
  · intro i hi
    interval_cases i <;> norm_num [entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.one_value, ht]

/-- Nonzero transition and correlated process/initial covariance witness the
original dense-input family. Initialization and all finite native prefixes can
therefore be derived for a nontrivial model. -/
theorem input_domain_nonempty
    : ∃ input : Input.Model,
      ∃ initial : Input.State,
        ModelDomain input
        ∧ InitializationDomain initial
        ∧ input.transition = #[0.015625, 0.0, 0.0, 0.015625]
        ∧ input.processNoise = #[1.0, 0.25, 0.25, 1.5]
        ∧ initial.mean = #[1.0, -1.0]
        ∧ initial.covariance = #[1.0, 0.25, 0.25, 1.5] := by
  obtain ⟨input, current, p, q, hF, hmu, _⟩ := FloatPredictionDomain.input_domain_nonempty
  let input' := {input with processNoise := #[1.0, 0.25, 0.25, 1.5]}
  let initial : Input.State := ⟨current.mean, #[1.0, 0.25, 0.25, 1.5]⟩
  obtain ⟨hn, hd⟩ := correlated_noise_domain
  have q' : Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.CorrectionInputs input' :=
    ⟨q.measurement_dimension, q.observation_size, q.observation_finite, q.observation_bound,
      q.noise, q.noise_diagonal_cap, q.measurement_size, q.measurement_finite, q.measurement_bound⟩
  have hmodel : ModelDomain input' :=
    ⟨q', p.state_dimension, p.transition_inputs.transition_size,
      p.transition_inputs.transition_finite, p.transition_inputs.transition_bound, hn, hd⟩
  have hinit : InitializationDomain initial := ⟨hn, hd, p.mean_size, p.mean_finite, p.mean_bound⟩
  exact ⟨input', initial, hmodel, hinit, hF, rfl, hmu, rfl⟩

end Kalman.Proofs.FloatFilterInputDomain
