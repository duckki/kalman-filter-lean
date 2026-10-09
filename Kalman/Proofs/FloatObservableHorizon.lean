import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Proofs.RealObservableHorizon

/-! Accumulated native accuracy against one independent Real trajectory from
original dense initialization and time-varying original model bounds alone.
The sharper covariance contraction closes separate covariance and mean budgets. -/

namespace Kalman.Proofs.FloatObservableHorizon

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.DiagonalStages
open Kalman.Proofs.DiagonalStages.Horizon
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Definitions.Theorems.RecursionSensitivity

/-- Complete numeric expressions close without discarding gain changes or
cross terms. Initialization's covariance error fits the same uniform budget. -/
theorem uniform_budget_caps
    : 3 * (2 : ℝ) ^ (-30 : Int) + 9 / 25 * covarianceBudget ≤ covarianceBudget
      ∧ localJointRadius + 3 / 5 * meanBudget + 1 / 2 * covarianceBudget ≤ meanBudget
      ∧ (2 : ℝ) ^ (-42 : Int) ≤ covarianceBudget := by
  norm_num [covarianceBudget, meanBudget, localJointRadius]

/-- One actual checked step includes incoming covariance/mean discrepancy
against an independent exact reference, and preserves the native invariant. -/
theorem step_accumulated_accuracy (input : Input.Model) (current : Input.FactorState)
    (reference : LinearModel.State 2) (p : ModelDomain input) (s : StateInvariant current)
    (r
      : Kalman.Definitions.Theorems.RecursionSensitivity.DiagonalStateInvariant reference)
    (he : FactorAccuracy covarianceBudget meanBudget 2 current reference)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.step input current = .ok output
        ∧ StateInvariant output
        ∧ FactorAccuracy covarianceBudget meanBudget 2 output
            (CovarianceRecursion.step .joseph (model (atDimensions 2 2 input)) reference
              (vector 2 input.measurement))
        ∧ (factorState 2 output).covariance.PosDef := by
  obtain ⟨output, hr, so, hlocal, hp, _⟩ := FloatObservableFilter.step_accuracy_and_invariant input current p s
  have da : (factorState 2 current).covariance = diagonal (fun i => (factorState 2 current).covariance i i) := by
    change FactorRecursion.gram (matrix 2 2 current.lower) = diagonal (fun i => FactorRecursion.gram (matrix 2 2 current.lower) i i)
    rw [FloatDiagonalStorage.gram_diagonal 2 current.lower s.diagonal]
    simp only [diagonal_apply_eq]
  have ep : ∀ i, 0 ≤ (factorState 2 current).covariance i i :=
    fun i => (CovarianceStructure.gram_posSemidef _).diag_nonneg
  have propagated := RealObservableSensitivity.step_sensitivity .joseph
    (transition input) (processVariance input) (measurementVariance input) (vector 2 input.measurement)
    (factorState 2 current) reference covarianceBudget meanBudget
    (RealObservableHorizon.model_domain input p) da ep r
    (FloatFullFilter.factorAccuracy_stateWithin he)
  rw [← RealObservableHorizon.model_diagonal input p] at propagated
  have joined := FloatFullFilter.stateWithin_trans (FloatFullFilter.factorAccuracy_stateWithin hlocal) propagated
  have acc : FactorAccuracy covarianceBudget meanBudget 2 output
      (CovarianceRecursion.step .joseph (model (atDimensions 2 2 input)) reference
        (vector 2 input.measurement)) := by
    refine ⟨hlocal.1, ⟨by unfold covarianceBudget; positivity, ?_⟩, by unfold meanBudget; positivity, ?_⟩
    · intro i j
      exact (joined.1.2 i j).trans uniform_budget_caps.1
    · intro i
      exact (joined.2.2 i).trans (by simpa only [add_assoc] using uniform_budget_caps.2.1)
  exact ⟨output, hr, so, acc, hp⟩

/-- Original dense initialization and time-varying models derive successful
execution and uniform accumulated covariance/mean errors 5·2^-30 / 2^-24
at every finite prefix, even with identity transition. The reference starts
from the original covariance and mean words, not a rounded factor Gram. -/
theorem initialized_horizon_accuracy (initializationInput : Input.Model)
    (initial : Input.State) (inputs : Nat → Input.Model) (horizon : Nat)
    (d : HorizonDomain initializationInput initial inputs horizon)
    : ∃ retained,
        Kalman.Implementation.SquareRootFilter.fromCovariance initializationInput initial
          = .ok retained
        ∧ ∀ t,
            t ≤ horizon
            → ∃ output,
                nativeRun inputs retained t = .ok output
                ∧ StateInvariant output
                ∧ FactorAccuracy covarianceBudget meanBudget 2 output
                    (exactRun 2 2 inputs (state 2 initial) t)
                ∧ (factorState 2 output).covariance.PosDef
                ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef := by
  obtain ⟨retained, hr, sr, ar, _⟩ := FloatObservableInitialization.initialize_invariant initializationInput initial
    d.initialization_model d.initial_state
  refine ⟨retained, hr, ?_⟩
  intro t ht
  induction t with
  | zero =>
      refine ⟨
        retained,
        rfl,
        sr,
        ?_,
        FactorStructure.lowerPositive_gram_posDef _ sr.lower_positive,
        ?_
      ⟩
      · exact FloatFilterHorizon.factorAccuracy_mono ar uniform_budget_caps.2.2 (by unfold meanBudget; positivity)
      · exact RealObservableInvariant.covariance_positive _
          (RealObservableHorizon.run_invariant initializationInput initial inputs horizon d 0 (by omega))
  | succ t ih =>
      obtain ⟨current, hc, sc, ac, _, _⟩ := ih (by omega)
      have rc := RealObservableHorizon.run_invariant initializationInput initial inputs horizon d t (by omega)
      obtain ⟨output, ho, so, ao, hp⟩ := step_accumulated_accuracy (inputs t) current _
        (d.models t (by omega)) sc rc ac
      refine ⟨output, ?_, so, ao, hp, ?_⟩
      · simp [nativeRun, Kalman.Implementation.SquareRootFilter.run, hc, ho, bind, Except.bind]
      · exact RealObservableInvariant.covariance_positive _
          (RealObservableHorizon.run_invariant initializationInput initial inputs horizon d (t+1) ht)

/-- Identity dynamics and signed nonzero means/measurements inhabit every
finite original-input accuracy domain, including dense initialization. -/
theorem identity_domain_nonempty (horizon : Nat)
    : ∃ input : Input.Model,
      ∃ initial : Input.State,
        HorizonDomain input initial (fun _ => input) horizon
        ∧ input.transition = identity 2
        ∧ initial.covariance = identity 2
        ∧ initial.mean = #[1.0, -1.0] := by
  obtain ⟨input, _, p, _, hF, _, _⟩ := FloatObservableFilter.identity_domain_nonempty
  exact ⟨input, ⟨#[1.0, -1.0], identity 2⟩,
    ⟨p, FloatObservableInitialization.identity_domain_nonempty, fun _ _ => p⟩, hF, rfl, rfl⟩

/-- Near-identity and sign-reversing native dynamics inhabit the original-input
accuracy domain. The words decode exactly to 1023/1024 and minus one. -/
theorem near_identity_domain_nonempty (horizon : Nat)
    : ∃ input : Input.Model,
      ∃ initial : Input.State,
        HorizonDomain input initial (fun _ => input) horizon
        ∧ input.transition = #[0.9990234375, -0.0, 0.0, -1.0]
        ∧ initial.covariance = identity 2
        ∧ initial.mean = #[1.0, -1.0] := by
  obtain ⟨input, initial, d, _, hP, hx⟩ := identity_domain_nonempty horizon
  let input' := {input with transition := #[0.9990234375, -0.0, 0.0, -1.0]}
  have hf : Flare.Binary64.Value.value (0.9990234375 : Float) = (1023 : ℝ) / 1024 := by
    change (8998403161718784 : ℝ) * (2 : ℝ)^(-53 : Int) = _
    norm_num
  have hn := (Flare.Binary64.Order.neg_value (1.0 : Float) (by decide +kernel)).2
  have hd : Kalman.Implementation.Correctness.InputInterpretation.DecodedDiagonal 2 input'.transition := by
    intro i j hi hj hij
    interval_cases i <;> interval_cases j <;>
      simp_all [input', entry, Flare.Matrix.Dense.entry,
        show Flare.Binary64.Value.value (-0.0 : Float) = 0 from rfl,
        Flare.Binary64.Arithmetic.zero_value]
  have p := d.initialization_model
  have p' : ModelDomain input' := by
    refine ⟨⟨p.measurement_dimension, p.observation_size, p.observation_finite,
      p.observation_identity, p.noise⟩, p.state_dimension,
      by change (#[0.9990234375, -0.0, 0.0, -1.0] : Array Float).size = 4; decide,
      by change (#[0.9990234375, -0.0, 0.0, -1.0] : Array Float).all Float.isFinite = true; decide +kernel,
      hd, ?_, p.process_noise, p.measurement_size, p.measurement_finite, p.measurement_bound⟩
    intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      norm_num [input', entry, Flare.Matrix.Dense.entry, hf, hn,
        show Flare.Binary64.Value.value (-0.0 : Float) = 0 from rfl,
        Flare.Binary64.Arithmetic.zero_value, Flare.Binary64.Arithmetic.one_value]
  exact ⟨input', initial, ⟨p', d.initial_state, fun _ _ => p'⟩, rfl, hP, hx⟩

/-- Proof witness for the result catalogue statement. -/
theorem initializedHorizonAccuracy
    : Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.InitializedHorizonAccuracy :=
  initialized_horizon_accuracy

end Kalman.Proofs.FloatObservableHorizon
