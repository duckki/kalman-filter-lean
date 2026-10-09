import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy

/-!
# Fully observed diagonal filter accuracy

Original-input domains, uniform budgets, and completed retained/dense horizon
guarantees for diagonal dynamics. Proof-witness references accompany the results.
-/

namespace Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy

open Kalman.Definitions Kalman.Implementation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Flare.Binary64.Value

noncomputable section

/-! ----------------------------------------------------------------------
## Original diagonal noise and observation inputs
-------------------------------------------------------------------------- -/

structure NoiseDomain (a : Array Float) : Prop where
  covariance : TwoStateCovarianceDomain a
  diagonal : DecodedDiagonal 2 a
  diagonal_cap : ∀ i, i < 2 → value (entry 2 a i i) ≤ 3 / 2

structure ObservationInputs (input : Input.Model) : Prop where
  measurement_dimension : input.measurementDimension = 2
  observation_size : input.observation.size = 4
  observation_finite : input.observation.all Float.isFinite = true
  observation_identity : matrix 2 2 input.observation = 1
  noise : NoiseDomain input.measurementNoise

/-! ----------------------------------------------------------------------
## Original model and retained-state invariants
-------------------------------------------------------------------------- -/

/-! Original model/storage domain and retained state invariant for fully
observed diagonal two-state filtering. No intermediate run, operand profile or
desired error is a domain field. Fixed-dimension interpretation preserves all
original words and uses the authoritative Input.Model format. -/

structure ModelDomain (input : Input.Model) : Prop extends ObservationInputs input where
  state_dimension : input.stateDimension = 2
  transition_size : input.transition.size = 4
  transition_finite : input.transition.all Float.isFinite = true
  transition_diagonal : DecodedDiagonal 2 input.transition
  transition_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 input.transition i j)| ≤ 1
  process_noise : NoiseDomain input.processNoise
  measurement_size : input.measurement.size = 2
  measurement_finite : input.measurement.all Float.isFinite = true
  measurement_bound : ∀ i, i < 2 → |value (input.measurement.getD i 0.0)| ≤ 1

structure StateInvariant (current : Input.FactorState) : Prop where
  mean_size : current.mean.size = 2
  factor_size : current.lower.size = 4
  mean_finite : current.mean.all Float.isFinite = true
  factor_finite : current.lower.all Float.isFinite = true
  lower_positive : FactorRecursion.LowerPositive (matrix 2 2 current.lower)
  diagonal : DecodedDiagonal 2 current.lower
  factor_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 current.lower i j)| ≤ 2
  covariance_floor
    : (FactorRecursion.gram (matrix 2 2 current.lower) - (7 / 16 : ℝ) • 1).PosSemidef
  covariance_diagonal_cap
    : ∀ i, FactorRecursion.gram (matrix 2 2 current.lower) i i ≤ 13 / 8
  mean_bound : ∀ i, i < 2 → |value (current.mean.getD i 0.0)| ≤ 9 / 8

/-! ----------------------------------------------------------------------
## Original dense initialization
-------------------------------------------------------------------------- -/

/-! Original dense initialization for the fully observed diagonal native family.
The covariance words are authoritative; initialization is not specified by a
pre-existing factor or by its eventual rounded Gram. -/

/-- Initial diagonal variances in [1,3/2] and means of magnitude at most one.
This is a sufficient native subset of the wider independent Real initial domain. -/
structure InitializationDomain (initial : Input.State) : Prop where
  covariance : NoiseDomain initial.covariance
  mean_size : initial.mean.size = 2
  mean_finite : initial.mean.all Float.isFinite = true
  mean_bound : ∀ i, i < 2 → |value (initial.mean.getD i 0.0)| ≤ 1

/-! ----------------------------------------------------------------------
## Original-input accumulated accuracy
-------------------------------------------------------------------------- -/

/-! Original-input finite horizons and uniform componentwise error budgets.
The independent Real trace starts from the original dense covariance/mean words.
No reached profile, successful run or unknown output accuracy is assumed. -/

def covarianceBudget : ℝ := 5 * (2 : ℝ) ^ (-30 : Int)
def meanBudget : ℝ := (2 : ℝ) ^ (-24 : Int)

structure HorizonDomain (initializationInput : Input.Model) (initial : Input.State)
    (inputs : Nat → Input.Model) (horizon : Nat)
    : Prop where
  initialization_model : ModelDomain initializationInput
  initial_state : InitializationDomain initial
  models : ∀ t, t < horizon → ModelDomain (inputs t)

/-! ----------------------------------------------------------------------
## Rounded dense output guarantees
-------------------------------------------------------------------------- -/

/-! Accuracy and positivity contracts for separately rounded dense covariance
in the fully observed diagonal original-input family. The native factor Gram
and the rounded materialization are different matrix values. -/

/-- The existing checked two-state multiplication allowance. -/
def materializationRadius : ℝ :=
  Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.materializationRadius

def denseFloor : ℝ := 7 / 16 - 2 * materializationRadius

abbrev DenseMaterializationWithin :=
  Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.DenseMaterializationWithin

def DenseHorizonAccuracy (output : Input.State) (reference : LinearModel.State 2)
    : Prop :=
  output.validate 2 = .ok ()
  ∧ StateWithin (covarianceBudget + materializationRadius) meanBudget (state 2 output)
      reference
  ∧ (state 2 output).covariance.IsHermitian
  ∧ ((state 2 output).covariance - denseFloor • 1).PosSemidef
  ∧ (state 2 output).covariance.PosDef

/-! Main FullyObservedDiagonalFilterAccuracy guarantees, with proof-witness references.
Supporting domains and budgets live in `Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy`. -/

/-! ----------------------------------------------------------------------
## Retained-factor horizon accuracy
-------------------------------------------------------------------------- -/

/-- Fully observed diagonal original inputs give success at every finite prefix,
uniform covariance error 5·2⁻³⁰, mean error 2⁻²⁴, and positive covariances.
Proof witness: `Kalman.Proofs.FloatObservableHorizon.initializedHorizonAccuracy`
(the existing `FloatObservableHorizon.initialized_horizon_accuracy` proof). -/
def InitializedHorizonAccuracy : Prop :=
  ∀ (initializationInput : Input.Model) (initial : Input.State)
    (inputs : Nat → Input.Model) (horizon : Nat)
    (_ : HorizonDomain initializationInput initial inputs horizon),
    ∃ retained,
      SquareRootFilter.fromCovariance initializationInput initial = .ok retained
      ∧ ∀ t,
          t ≤ horizon
          → ∃ output,
              nativeRun inputs retained t = .ok output
              ∧ StateInvariant output
              ∧ FactorAccuracy covarianceBudget meanBudget 2 output
                  (exactRun 2 2 inputs (state 2 initial) t)
              ∧ (factorState 2 output).covariance.PosDef
              ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef

/-! ----------------------------------------------------------------------
## Rounded dense horizon accuracy
-------------------------------------------------------------------------- -/

/-- The diagonal family also has symmetric rounded dense output, covariance error
5·2⁻³⁰ + 2⁻⁴⁸, mean error 2⁻²⁴, and dense covariance floor at least 3/8.
Proof witness: `Kalman.Proofs.FloatObservableDenseOutput.initializedDenseHorizonAccuracy`
(the existing `FloatObservableDenseOutput.initialized_dense_horizon_accuracy` proof). -/
def InitializedDenseHorizonAccuracy : Prop :=
  ∀ (initializationInput : Input.Model)
    (initial : Input.State) (inputs : Nat → Input.Model) (horizon : Nat)
    (_ : HorizonDomain initializationInput initial inputs horizon),
    ∃ retained,
      SquareRootFilter.fromCovariance initializationInput initial = .ok retained
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
              ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef

end
end Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
