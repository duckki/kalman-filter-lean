import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Proofs.FloatObservableHorizon
import Kalman.Proofs.FloatMaterialization

/-! Rounded dense output inherits its own spectral and accuracy guarantees
from original inputs, without assuming the unknown dense error or positivity.
The operation order, symmetry behavior and mean words are unchanged. -/

namespace Kalman.Proofs.FloatObservableDenseOutput

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.DiagonalStages
open Kalman.Proofs.DiagonalStages.Horizon
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties

/-- The exact dense margin is positive and admits a simpler public floor. -/
theorem denseFloor_ge_three_eighths : (3 : ℝ) / 8 ≤ denseFloor := by
  norm_num [denseFloor, materializationRadius,
    Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.materializationRadius]

theorem denseFloor_positive : 0 < denseFloor :=
  (by norm_num : (0 : ℝ) < 3 / 8).trans_le denseFloor_ge_three_eighths

/-- Stored validation and covariance cap derive materialization. Its error is
charged against the retained Gram before using the independent ideal comparator. -/
theorem materialization_positive (factor : Input.FactorState) (s : StateInvariant factor)
    : ∃ output,
        DenseMaterializationWithin factor output
        ∧ ((state 2 output).covariance - denseFloor • 1).PosSemidef
        ∧ (state 2 output).covariance.PosDef := by
  have hv : Kalman.Implementation.Correctness.SquareRootFilterProperties.ValidFactor 2 factor :=
    ⟨FloatObservableFilter.factor_validate factor s, s.lower_positive⟩
  obtain ⟨output, hm⟩ := FloatMaterialization.two_state_accuracy_of_diagonal_cap factor hv
    (fun i => (s.covariance_diagonal_cap i).trans (by norm_num))
  have hf := ErrorPropagation.lower_bound_of_error _ _ (7 / 16)
    materializationRadius s.covariance_floor hm.2.2.2 hm.1.2.2.2
  have hfloor : ((state 2 output).covariance - denseFloor • 1).PosSemidef := by
    simpa only [denseFloor, Nat.cast_ofNat] using hf
  exact ⟨
    output,
    hm,
    hfloor,
    Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ denseFloor denseFloor_positive
      hfloor
  ⟩

/-- Complete initialized native filtering and separately rounded dense output
at every finite prefix, from original input bounds alone. Covariance/mean errors
are at most 5·2^-30 + 2^-48 / 2^-24 against one independent ideal trajectory;
dense covariance is symmetric and strictly PD with floor 7/16 - 2^-47. -/
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
                ∧ FactorAccuracy covarianceBudget meanBudget 2 factor
                    (exactRun 2 2 inputs (state 2 initial) t)
                ∧ DenseMaterializationWithin factor output
                ∧ DenseHorizonAccuracy output (exactRun 2 2 inputs (state 2 initial) t)
                ∧ (factorState 2 factor).covariance.PosDef
                ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef := by
  obtain ⟨retained, hr, prefixes⟩ := FloatObservableHorizon.initialized_horizon_accuracy
    initializationInput initial inputs horizon d
  refine ⟨retained, hr, ?_⟩
  intro t ht
  obtain ⟨factor, hrun, sf, af, pf, pr⟩ := prefixes t ht
  obtain ⟨output, hm, hf, pd⟩ := materialization_positive factor sf
  have hc : EntrywiseWithin (covarianceBudget + materializationRadius)
      (state 2 output).covariance (exactRun 2 2 inputs (state 2 initial) t).covariance := by
    simpa only [materializationRadius, add_comm]
      using ErrorPropagation.within_trans hm.1.2.2.2 af.2.1
  have hx : ∀ i, |(state 2 output).mean i - (exactRun 2 2 inputs (state 2 initial) t).mean i| ≤ meanBudget := by
    simpa only [state, hm.2.1] using af.2.2.2
  exact ⟨factor, output, hrun, sf, af, hm,
    ⟨hm.1.2.2.1, ⟨hc, af.2.2.1, hx⟩, hm.2.2.2, hf, pd⟩, pf, pr⟩

/-- Proof witness for the result catalogue statement. -/
theorem initializedDenseHorizonAccuracy
    : Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.InitializedDenseHorizonAccuracy :=
  initialized_dense_horizon_accuracy

end Kalman.Proofs.FloatObservableDenseOutput
