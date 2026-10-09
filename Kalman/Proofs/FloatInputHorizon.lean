import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.RealFilterInvariant
import Kalman.Proofs.FloatFilterHorizon

/-! Accumulated native covariance/mean error against one independently
initialized exact trajectory, with every condition derived from original inputs.
Correlated Q and R are included; no reached numerical profile is assumed. -/

namespace Kalman.Proofs.FloatInputHorizon

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
open Flare.Binary64.Value

set_option maxHeartbeats 1800000

/-- The independently derived correlated-noise environment and fixed native
profile constants close the same refined budget after incoming accumulated error.
Higher-order and normal/subnormal terms remain in the checked expressions. -/
theorem propagated_radius_caps (input : Input.Model) (initial : Input.FactorState)
    (reference : LinearModel.State input.stateDimension) (p : ModelDomain input)
    (profile : StepProfile input initial) (c : StepParameters profile)
    (d : StepEnvironment input reference)
    (h1 : d.noiseFloor = 3 / 4) (h2 : d.covarianceBound = 7 / 4)
    (h3 : d.noiseBound = 3 / 2) (h4 : d.innovationBound = 2)
    : stepCovarianceRadius profile d uniformBudget ≤ uniformBudget
      ∧ stepMeanRadius profile d uniformBudget uniformBudget ≤ uniformBudget := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hη : (2 : ℝ)^(-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  have hη3 := pow_le_one₀ hη0 hη1 (n := 3)
  have hη4 := pow_le_one₀ hη0 hη1 (n := 4)
  constructor <;> simp only [uniformBudget, stepCovarianceRadius, stepMeanRadius,
    predictedCovarianceRadius, predictedMeanRadius, predictionCovarianceRadius, predictionMeanRadius,
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

/-- Every reached native profile is derived from original models and the
preserved stored-state invariant. Fixing metadata preserves all input words. -/
theorem reached_profile (inputs : Nat → Input.Model) (initial : Input.FactorState)
    (horizon : Nat) (p : ∀ t, t < horizon → ModelDomain (inputs t))
    (s : StateInvariant initial) (t : Nat) (ht : t < horizon)
    (current : Input.FactorState) (hrun : nativeRun inputs initial t = .ok current)
    : ∃ profile : StepProfile (atDimensions 2 2 (inputs t)) current,
        StepParameters profile := by
  obtain ⟨out, hr, hs, _⟩ := FloatFilterInputDomain.run_invariant inputs initial horizon p s t (by omega)
  have eq : out = current := Except.ok.inj (hr.symm.trans hrun)
  subst out
  have hd := FloatFilterHorizon.atDimensions_eq 2 2 (inputs t) (p t ht).state_dimension (p t ht).measurement_dimension
  have dp : ModelDomain (atDimensions 2 2 (inputs t)) := hd.symm ▸ p t ht
  exact FloatFilterInputDomain.step_profile _ current dp hs

/-- Build the general horizon theorem's entire operand and budget domain from
original input conditions, the derived initializer accuracy and invariant.
This proof helper's initial representation/error are provided by initialization. -/
noncomputable def horizon_domain (initializationInput : Input.Model)
    (initial : Input.State) (inputs : Nat → Input.Model) (horizon : Nat)
    (d : HorizonDomain initializationInput initial inputs horizon)
    (retained : Input.FactorState) (s : StateInvariant retained)
    (ha : FactorAccuracy uniformBudget uniformBudget 2 retained (state 2 initial))
    : FilterComposition.Horizon.HorizonDomain 2 2 horizon inputs retained
        (state 2 initial) (fun _ => uniformBudget) (fun _ => uniformBudget) := by
  classical
  have env : ∀ t, t < horizon → ∃ e : StepEnvironment (atDimensions 2 2 (inputs t))
      (exactRun 2 2 inputs (state 2 initial) t),
      e.noiseFloor = 3 / 4 ∧ e.covarianceBound = 7 / 4 ∧ e.noiseBound = 3 / 2 ∧ e.innovationBound = 2 := by
    intro t ht
    exact RealFilterInvariant.reference_environment _ (d.models t ht) _
      (RealFilterInvariant.run_invariant inputs initial horizon d.models d.initial_state t (by omega))
  choose environment h1 h2 h3 h4 using env
  have profiles : ∀ t (ht : t < horizon) current (hrun : nativeRun inputs retained t = .ok current),
      ∃ profile : StepProfile (atDimensions 2 2 (inputs t)) current, StepParameters profile :=
    reached_profile inputs retained horizon d.models s
  choose profile parameters using profiles
  refine {
    initial_positive :=
      (RealFilterInvariant.initial_invariant initial d.initial_state).covariance_positive
    dimensions :=
      fun t ht => ⟨(d.models t ht).state_dimension, (d.models t ht).measurement_dimension⟩
    input_valid := fun t ht => FloatFilterInputDomain.input_validate _ (d.models t ht)
    process_positive :=
      fun t ht => FloatCholeskyDomain.input_positive _ (d.models t ht).process_noise
    environment := environment
    profile := profile
    initial_accuracy := ha
    covariance_cap := ?_
    mean_cap := ?_
  }
  · intro t ht current hrun
    have hd := FloatFilterHorizon.atDimensions_eq 2 2 (inputs t) (d.models t ht).state_dimension (d.models t ht).measurement_dimension
    exact (propagated_radius_caps _ current _ (hd.symm ▸ d.models t ht)
      (profile t ht current hrun) (parameters t ht current hrun) (environment t ht)
      (h1 t ht) (h2 t ht) (h3 t ht) (h4 t ht)).1
  · intro t ht current hrun
    have hd := FloatFilterHorizon.atDimensions_eq 2 2 (inputs t) (d.models t ht).state_dimension (d.models t ht).measurement_dimension
    exact (propagated_radius_caps _ current _ (hd.symm ▸ d.models t ht)
      (profile t ht current hrun) (parameters t ht current hrun) (environment t ht)
      (h1 t ht) (h2 t ht) (h3 t ht) (h4 t ht)).2

/-- Original dense initialization and original time-varying model bounds alone
give successful execution and accumulated covariance/mean errors at most 2^-25
against the independent ideal trajectory at every finite prefix. Both native
factor covariance and exact reference covariance remain PD; stored caps persist. -/
theorem initialized_horizon_accuracy (initializationInput : Input.Model)
    (initial : Input.State) (inputs : Nat → Input.Model) (horizon : Nat)
    (d : HorizonDomain initializationInput initial inputs horizon)
    : ∃ retained,
        Kalman.Implementation.SquareRootFilter.fromCovariance initializationInput initial
          = .ok retained
        ∧ (∀ t,
            t ≤ horizon
            → ∃ output,
                nativeRun inputs retained t = .ok output
                ∧ FactorAccuracy uniformBudget uniformBudget 2 output
                    (exactRun 2 2 inputs (state 2 initial) t)
                ∧ StateInvariant output
                ∧ (factorState 2 output).covariance.PosDef
                ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef) := by
  obtain ⟨retained, hr, hs, ha, _⟩ := FloatFilterInputDomain.initialize_invariant initializationInput initial
    d.initialization_model d.initial_state
  have ha' : FactorAccuracy uniformBudget uniformBudget 2 retained (state 2 initial) :=
    FloatFilterHorizon.factorAccuracy_mono ha (by norm_num [uniformBudget]) (by norm_num [uniformBudget])
  let hd := horizon_domain initializationInput initial inputs horizon d retained hs ha'
  refine ⟨retained, hr, ?_⟩
  intro t ht
  obtain ⟨output, ho, he, hp, hq⟩ := FloatFilterHorizon.finite_horizon_accuracy 2 2 horizon inputs retained
    (state 2 initial) (fun _ => uniformBudget) (fun _ => uniformBudget) hd t ht
  obtain ⟨out, hout, hstate, _⟩ := FloatFilterInputDomain.run_invariant inputs retained horizon d.models hs t ht
  have eq : out = output := Except.ok.inj (hout.symm.trans ho)
  subst out
  exact ⟨output, ho, he, hstate, hp, hq⟩

/-- A nonzero transition and correlated original process/measurement/initial covariance
inhabit the fully derived accuracy domain for every finite horizon. -/
theorem domain_nonempty (horizon : Nat)
    : ∃ input : Input.Model,
      ∃ initial : Input.State,
        HorizonDomain input initial (fun _ => input) horizon
        ∧ input.transition = #[0.015625, 0.0, 0.0, 0.015625]
        ∧ input.processNoise = #[1.0, 0.25, 0.25, 1.5]
        ∧ input.measurementNoise = #[1.0, 0.25, 0.25, 1.5]
        ∧ initial.covariance = #[1.0, 0.25, 0.25, 1.5] := by
  obtain ⟨input, initial, p, q, hF, hQ, _, hP⟩ := FloatFilterInputDomain.input_domain_nonempty
  let input' := {input with measurementNoise := #[1.0, 0.25, 0.25, 1.5]}
  obtain ⟨hn, hd⟩ := FloatFilterInputDomain.correlated_noise_domain
  have pq : Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.CorrectionInputs input' :=
    ⟨p.measurement_dimension, p.observation_size, p.observation_finite, p.observation_bound,
      hn, hd, p.measurement_size, p.measurement_finite, p.measurement_bound⟩
  have p' : ModelDomain input' :=
    ⟨pq, p.state_dimension, p.transition_size, p.transition_finite, p.transition_bound,
      p.process_noise, p.process_diagonal_cap⟩
  exact ⟨input', initial, ⟨p', q, fun _ _ => p'⟩, hF, hQ, rfl, hP⟩

/-- The widened domain reaches both signs of the transition cap, with
correlated original Q/R and initial covariance, at every finite horizon. -/
theorem boundary_domain_nonempty (horizon : Nat)
    : ∃ input : Input.Model,
      ∃ initial : Input.State,
        HorizonDomain input initial (fun _ => input) horizon
        ∧ input.transition = #[0.125, 0.125, -0.125, 0.125]
        ∧ input.processNoise = #[1.0, 0.25, 0.25, 1.5]
        ∧ input.measurementNoise = #[1.0, 0.25, 0.25, 1.5]
        ∧ initial.covariance = #[1.0, 0.25, 0.25, 1.5] := by
  obtain ⟨input, initial, d, _, hQ, hR, hP⟩ := domain_nonempty horizon
  let input' := {input with transition := #[0.125, 0.125, -0.125, 0.125]}
  have he : value (0.125 : Float) = (1 : ℝ) / 8 := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-55 : Int) = _
    norm_num
  have hn := (Flare.Binary64.Order.neg_value (0.125 : Float) (by decide +kernel)).2
  have p := d.initialization_model
  have pc : Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.CorrectionInputs input' :=
    ⟨p.measurement_dimension, p.observation_size, p.observation_finite, p.observation_bound,
      p.noise, p.noise_diagonal_cap, p.measurement_size, p.measurement_finite, p.measurement_bound⟩
  have p' : ModelDomain input' := by
    refine ⟨pc, p.state_dimension,
      by change (#[0.125, 0.125, -0.125, 0.125] : Array Float).size = 4; decide,
      by change (#[0.125, 0.125, -0.125, 0.125] : Array Float).all Float.isFinite = true; decide +kernel,
      ?_, p.process_noise, p.process_diagonal_cap⟩
    intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      norm_num [input', entry, Flare.Matrix.Dense.entry, hn, he]
  exact ⟨input', initial, ⟨p', d.initial_state, fun _ _ => p'⟩, rfl, hQ, hR, hP⟩

/-- Proof witness for the result catalogue statement. -/
theorem initializedHorizonAccuracy
    : Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.InitializedHorizonAccuracy :=
  initialized_horizon_accuracy

end Kalman.Proofs.FloatInputHorizon
