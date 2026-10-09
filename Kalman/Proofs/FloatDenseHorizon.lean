import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.FloatInputHorizon
import Kalman.Proofs.FloatMaterialization

/-! Checked dense covariance accuracy and positivity at every finite prefix.
All profiles, execution and spectral margins follow from the original input
horizon domain. The native materialization algorithm is unchanged. -/

namespace Kalman.Proofs.FloatDenseHorizon

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
open Kalman.Proofs.CorrelatedStages
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.QRProfiles
open Flare.Binary64.Value

set_option maxHeartbeats 1400000

/-- Original dense initialization gives at least the uniform quarter floor.
The Cholesky theorem supplies the stronger half floor before padding. -/
theorem initialization_covariance_floor (input : Input.Model) (initial : Input.State)
    (retained : Input.FactorState) (p : ModelDomain input)
    (d : InitializationDomain initial)
    (hr
      : Kalman.Implementation.SquareRootFilter.fromCovariance input initial
        = .ok retained)
    : ((factorState 2 retained).covariance - retainedFloor • 1).PosSemidef := by
  obtain ⟨l, _, hl, _, _, _, _, hf, _⟩ := FloatCholeskyDomain.cholesky_accuracy initial.covariance d.covariance
  have hln : cholesky input.stateDimension initial.covariance = .ok l := by
    simpa only [p.state_dimension] using hl
  have hsym : Input.symmetric input.stateDimension initial.covariance = true := by
    simpa only [p.state_dimension]
      using FloatCholeskyDomain.input_symmetric initial.covariance d.covariance
  cases hs : initial.validate input.stateDimension with
  | error e =>
      simp [Kalman.Implementation.SquareRootFilter.fromCovariance,
        FloatFilterInputDomain.input_validate input p, hs, bind, Except.bind] at hr
  | ok x =>
      have he : retained = ⟨initial.mean, l⟩ := by
        have h : (Except.ok (⟨initial.mean, l⟩ : Input.FactorState) : Except Input.Error Input.FactorState)
            = .ok retained := by
          simpa [Kalman.Implementation.SquareRootFilter.fromCovariance,
            FloatFilterInputDomain.input_validate input p, hs, hsym, hln, bind,
            Except.bind, pure, Except.pure]
            using hr
        exact (Except.ok.inj h).symm
      rw [he]
      change (matrix 2 2 l * (matrix 2 2 l).transpose - retainedFloor • 1).PosSemidef
      convert hf.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 4)) using 1
      unfold retainedFloor
      module

private theorem correction_covariance_floor (input : Input.Model)
    (prior output : Input.FactorState)
    (p : Kalman.Proofs.CorrelatedStages.Posterior.TwoStateDomain input prior)
    (hu : Kalman.Implementation.SquareRootFilter.updateUnchecked input prior = .ok output)
    : ((factorState 2 output).covariance - retainedFloor • 1).PosSemidef := by
  obtain ⟨innovation, gain, g, mean, _, _, _, _, _, posterior, q, _⟩ :=
    FloatPosteriorDomain.correction_profiles input prior p
  have d : GramFactorInputDomain 2 4 (fromCols 2 2 2 posterior.wl posterior.ktr) 2 := by
    simpa only [p.state_dimension, p.measurement_dimension, q.qr_budget]
      using posterior.qr
  obtain ⟨l, hl2, _, _, _, _, hf, _⟩ := FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 4 _ 2 d
  have hl : Kalman.Implementation.OrthogonalFactorization.gramFactor input.stateDimension
      (input.stateDimension + input.measurementDimension)
      (fromCols input.stateDimension input.stateDimension input.measurementDimension posterior.wl posterior.ktr)
      = .ok l := by
    simpa only [p.state_dimension, p.measurement_dimension] using hl2
  have hnoise := (FloatMeanDomain.ideal_mean_operand_bounds input prior p.toMeanDomain).1
  have hgain := (FloatSquareRootUpdate.gain_accuracy input prior innovation gain (3 / 4) (by norm_num) hnoise).1
  have hinc : multiply input.stateDimension input.measurementDimension 1
      (transpose input.measurementDimension input.stateDimension gain.solution) mean.residual = .ok mean.increment := mean.computeIncrement
  have hkh : multiply input.stateDimension input.measurementDimension input.stateDimension
      (transpose input.measurementDimension input.stateDimension gain.solution) input.observation = .ok posterior.kh := posterior.computeKH
  have hktr : multiply input.stateDimension input.measurementDimension input.measurementDimension
      (transpose input.measurementDimension input.stateDimension gain.solution) innovation.tr = .ok posterior.ktr := posterior.computeKTR
  have hrun : Kalman.Implementation.SquareRootFilter.updateUnchecked input prior = .ok ⟨mean.mean, l⟩ := by
    simp [Kalman.Implementation.SquareRootFilter.updateUnchecked, innovation.noise.execution,
      innovation.computeProduct, innovation.computeQR, gain.computeProduct, hgain,
      mean.computeProjected, mean.computeResidual, hinc, mean.computeMean, hkh,
      posterior.computeW, posterior.computeWL, hktr, hl, bind, Except.bind, pure, Except.pure]
  have he : output = ⟨mean.mean, l⟩ := Except.ok.inj (hu.symm.trans hrun)
  rw [he]
  simpa only [factorState, retainedFloor, show (2 : ℝ)^2 / 16 = 1 / 4 by norm_num]
    using hf

/-- The original full-step domain derives a fresh quarter covariance floor
from posterior QR, independently of any incoming spectral floor premise. -/
theorem step_covariance_floor (input : Input.Model) (initial output : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    (hr : Kalman.Implementation.SquareRootFilter.step input initial = .ok output)
    : ((factorState 2 output).covariance - retainedFloor • 1).PosSemidef := by
  obtain ⟨prior, hp, dp⟩ := FloatPosteriorDomain.prediction_posterior_domain input initial
    (FloatFilterInputDomain.prediction_domain input initial p s) p.toCorrectionInputs
  obtain ⟨out, hu, ha, _, _, _, _⟩ := FloatPosteriorDomain.correction_accuracy_and_bounds input prior dp
  have hvn : initial.validate input.stateDimension = .ok () := by
    simpa only [p.state_dimension] using s.valid.1
  have hrun : Kalman.Implementation.SquareRootFilter.step input initial = .ok out := by
    simp [Kalman.Implementation.SquareRootFilter.step, FloatFilterInputDomain.input_validate input p,
      hvn, hp, hu, ha.1.1, bind, Except.bind, pure, Except.pure]
  have he : out = output := Except.ok.inj (hrun.symm.trans hr)
  subst out
  exact correction_covariance_floor input prior output dp hu

/-- Every successful finite prefix has the quarter floor. Initialization
supplies the zero-prefix floor, and each subsequent step derives it afresh. -/
theorem run_covariance_floor (inputs : Nat → Input.Model) (initial : Input.FactorState)
    (horizon : Nat) (p : ∀ t, t < horizon → ModelDomain (inputs t))
    (s : StateInvariant initial)
    (hf : ((factorState 2 initial).covariance - retainedFloor • 1).PosSemidef)
    (t : Nat) (ht : t ≤ horizon) (output : Input.FactorState)
    (hr : nativeRun inputs initial t = .ok output)
    : ((factorState 2 output).covariance - retainedFloor • 1).PosSemidef := by
  cases t with
  | zero =>
      have he : initial = output := Except.ok.inj hr
      subst output
      exact hf
  | succ t =>
      obtain ⟨current, hc, sc, _⟩ := FloatFilterInputDomain.run_invariant inputs initial horizon p s t (by omega)
      obtain ⟨out, ho, _, _⟩ := FloatFilterInputDomain.step_invariant (inputs t) current (p t (by omega)) sc
      have hrun : nativeRun inputs initial (t + 1) = .ok out := by
        simp [nativeRun, Kalman.Implementation.SquareRootFilter.run, hc, ho, bind, Except.bind]
      have he : out = output := Except.ok.inj (hrun.symm.trans hr)
      subst out
      exact step_covariance_floor (inputs t) current output (p t (by omega)) sc ho

theorem denseFloor_positive : 0 < denseFloor := by
  norm_num [denseFloor, retainedFloor, materializationRadius]

/-- A simpler public floor is available without rounding away the exact margin. -/
theorem denseFloor_ge_eighth : (1 : ℝ) / 8 ≤ denseFloor := by
  norm_num [denseFloor, retainedFloor, materializationRadius]

/-- The separately rounded dense matrix preserves the explicit spectral floor
quarter minus 2^-47, hence is strictly PD. All symmetry/error premises are
conclusions of the stored invariant and actual native conversion. -/
theorem materialization_positive (factor : Input.FactorState) (s : StateInvariant factor)
    (hf : ((factorState 2 factor).covariance - retainedFloor • 1).PosSemidef)
    : ∃ output,
        DenseMaterializationWithin factor output
        ∧ ((state 2 output).covariance - denseFloor • 1).PosSemidef
        ∧ (state 2 output).covariance.PosDef := by
  obtain ⟨output, hm⟩ := FloatMaterialization.two_state_accuracy factor s
  have he := ErrorPropagation.lower_bound_of_error _ _ retainedFloor materializationRadius hf hm.2.2.2 hm.1.2.2.2
  have hfloor : ((state 2 output).covariance - denseFloor • 1).PosSemidef := by
    simpa only [denseFloor, Nat.cast_ofNat] using he
  exact ⟨
    output,
    hm,
    hfloor,
    Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ denseFloor denseFloor_positive
      hfloor
  ⟩

/-- Original dense initialization and time-varying original model bounds
alone derive successful rounded dense output at every finite prefix, exact
symmetry, spectral floor quarter minus 2^-47 and accumulated covariance/mean
errors at most 2^-25 + 2^-48 and 2^-25 against one independent ideal trajectory. -/
theorem initialized_dense_horizon_accuracy (initializationInput : Input.Model)
    (initial : Input.State) (inputs : Nat → Input.Model) (horizon : Nat)
    (d : HorizonDomain initializationInput initial inputs horizon)
    : ∃ retained,
        Kalman.Implementation.SquareRootFilter.fromCovariance initializationInput initial
          = .ok retained
        ∧ ∀ t,
            t ≤ horizon
            → ∃ factor output,
                nativeRun inputs retained t = .ok factor
                ∧ StateInvariant factor
                ∧ FactorAccuracy uniformBudget uniformBudget 2 factor
                    (exactRun 2 2 inputs (state 2 initial) t)
                ∧ ((factorState 2 factor).covariance - retainedFloor • 1).PosSemidef
                ∧ DenseMaterializationWithin factor output
                ∧ DenseHorizonAccuracy output (exactRun 2 2 inputs (state 2 initial) t)
                ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef := by
  obtain ⟨retained, hr, prefixes⟩ := FloatInputHorizon.initialized_horizon_accuracy initializationInput initial inputs horizon d
  obtain ⟨retained', hr', s, _, _⟩ := FloatFilterInputDomain.initialize_invariant initializationInput initial
    d.initialization_model d.initial_state
  have hret : retained' = retained := Except.ok.inj (hr'.symm.trans hr)
  subst retained'
  have hinit := initialization_covariance_floor initializationInput initial retained d.initialization_model d.initial_state hr
  refine ⟨retained, hr, ?_⟩
  intro t ht
  obtain ⟨factor, hrun, ha, hs, _, hp⟩ := prefixes t ht
  have hf := run_covariance_floor inputs retained horizon d.models s hinit t ht factor hrun
  obtain ⟨output, hm, hfloor, hpd⟩ := materialization_positive factor hs hf
  have hcov : EntrywiseWithin (uniformBudget + materializationRadius)
      (state 2 output).covariance (exactRun 2 2 inputs (state 2 initial) t).covariance := by
    simpa only [add_comm materializationRadius uniformBudget]
      using ErrorPropagation.within_trans hm.1.2.2.2 ha.2.1
  have hmean : ∀ i, |(state 2 output).mean i - (exactRun 2 2 inputs (state 2 initial) t).mean i| ≤ uniformBudget := by
    simpa only [state, hm.2.1] using ha.2.2.2
  exact ⟨factor, output, hrun, hs, ha, hf, hm,
    ⟨hm.1.2.2.1, ⟨hcov, ha.2.2.1, hmean⟩, hm.2.2.2, hfloor, hpd⟩, hp⟩

/-- Proof witness for the result catalogue statement. -/
theorem initializedDenseHorizonAccuracy
    : Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.InitializedDenseHorizonAccuracy :=
  initialized_dense_horizon_accuracy

end Kalman.Proofs.FloatDenseHorizon
