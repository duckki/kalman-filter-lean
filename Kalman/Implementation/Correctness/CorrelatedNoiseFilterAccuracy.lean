import Kalman.Implementation.Correctness.SquareRootFilterProperties

/-!
# Correlated original-input filter accuracy

Operating domains, comparison relations, and completed retained/dense horizon
guarantees. Proof-witness references accompany the result statements.
-/

namespace Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy

open Kalman.Definitions Kalman.Implementation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Flare.Binary64.Value

noncomputable section

/-! ----------------------------------------------------------------------
## Original observation and measurement inputs
-------------------------------------------------------------------------- -/

/-- Static measurement-stage inputs needed to transfer a prediction result to
the already proved local correction domain. These do not constrain its output. -/
structure CorrectionInputs (input : Input.Model) : Prop where
  measurement_dimension : input.measurementDimension = 2
  observation_size : input.observation.size = 4
  observation_finite : input.observation.all Float.isFinite = true
  observation_bound
    : ∀ i j, i < 2 → j < 2 → |value (entry 2 input.observation i j)| ≤ 1 / 64
  noise : TwoStateCovarianceDomain input.measurementNoise
  noise_diagonal_cap : ∀ i, i < 2 → value (entry 2 input.measurementNoise i i) ≤ 3 / 2
  measurement_size : input.measurement.size = 2
  measurement_finite : input.measurement.all Float.isFinite = true
  measurement_bound : ∀ i, i < 2 → |value (input.measurement.getD i 0.0)| ≤ 1

/-! ----------------------------------------------------------------------
## Original model and retained-state invariants
-------------------------------------------------------------------------- -/

/-! Original model bounds and a preserved stored-state operating domain.
These propositions contain no execution, profile or error conclusion as an
assumption. ValidFactor specifies the input factor's working representation. -/

/-- Time-varying two-state models: small finite transition/observation,
bounded measurement, and symmetric PD original process/measurement noise.
Both noise inputs may be correlated. -/
structure ModelDomain (input : Input.Model) : Prop
    extends CorrectionInputs input where
  state_dimension : input.stateDimension = 2
  transition_size : input.transition.size = 4
  transition_finite : input.transition.all Float.isFinite = true
  transition_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 input.transition i j)| ≤ 1 / 8
  process_noise : TwoStateCovarianceDomain input.processNoise
  process_diagonal_cap : ∀ i, i < 2 → value (entry 2 input.processNoise i i) ≤ 3 / 2

/-- Bounds on retained words, independent of an ideal trajectory's error.
Covariance denotes the exact Real Gram of the finite stored lower factor. -/
structure StateInvariant (current : Input.FactorState) : Prop where
  valid : SquareRootFilterProperties.ValidFactor 2 current
  mean_bound : ∀ i, i < 2 → |value (current.mean.getD i 0.0)| ≤ 1
  factor_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 current.lower i j)| ≤ 2
  covariance_bound : ∀ i j, |FactorRecursion.gram (matrix 2 2 current.lower) i j| ≤ 2

/-- Original dense covariance initialization with headroom inside the retained
state's covariance cap. The mean is interpreted exactly from the same words. -/
structure InitializationDomain (initial : Input.State) : Prop where
  covariance : TwoStateCovarianceDomain initial.covariance
  diagonal_cap : ∀ i, i < 2 → value (entry 2 initial.covariance i i) ≤ 3 / 2
  mean_size : initial.mean.size = 2
  mean_finite : initial.mean.all Float.isFinite = true
  mean_bound : ∀ i, i < 2 → |value (initial.mean.getD i 0.0)| ≤ 1

/-! ----------------------------------------------------------------------
## Original-input accumulated accuracy
-------------------------------------------------------------------------- -/

/-! Original input conditions and the uniform accumulated roundoff budget.
This domain contains no reached profile, native run, reference-state bound or
output accuracy premise. Proof witnesses live in Proofs/FloatInputHorizon. -/

def uniformBudget : ℝ := (2 : ℝ) ^ (-25 : Int)

/-- Dense initialization and a finite sequence of original operating inputs.
The initializer's model may differ from the time-varying subsequent models. -/
structure HorizonDomain (initializationInput : Input.Model) (initial : Input.State)
    (inputs : Nat → Input.Model) (horizon : Nat)
    : Prop where
  initialization_model : ModelDomain initializationInput
  initial_state : InitializationDomain initial
  models : ∀ t, t < horizon → ModelDomain (inputs t)

/-! ----------------------------------------------------------------------
## Rounded dense output guarantees
-------------------------------------------------------------------------- -/

/-! Public relations for the optionally materialized native covariance.
The rounded dense matrix has its own error and spectral guarantee, separate
from the exact Gram denoted by the retained factor. Definitions are contracts. -/

/-- Two-state dense multiplication allowance from retained covariance cap two. -/
def materializationRadius : ℝ := (2 : ℝ) ^ (-48 : Int)

/-- Uniform retained covariance floor obtained from initialization and QR. -/
def retainedFloor : ℝ := 1 / 4

/-- Spectral floor after the two-state entrywise materialization perturbation. -/
def denseFloor : ℝ := retainedFloor - 2 * materializationRadius

def DenseMaterializationWithin (factor : Input.FactorState) (output : Input.State)
    : Prop :=
  SquareRootFilterProperties.MaterializationWithin materializationRadius 2 factor output
  ∧ output.mean = factor.mean
  ∧ Implementation.LinearAlgebra.entry 2 output.covariance 0 1
    = Implementation.LinearAlgebra.entry 2 output.covariance 1 0
  ∧ (state 2 output).covariance.IsHermitian

/-- Checked dense output accuracy against the independently initialized ideal
trajectory, with unchanged mean words and the additional dense conversion error. -/
def DenseHorizonAccuracy (output : Input.State) (reference : LinearModel.State 2)
    : Prop :=
  output.validate 2 = .ok ()
  ∧ StateWithin (uniformBudget + materializationRadius) uniformBudget (state 2 output)
      reference
  ∧ (state 2 output).covariance.IsHermitian
  ∧ ((state 2 output).covariance - denseFloor • 1).PosSemidef
  ∧ (state 2 output).covariance.PosDef

/-! Main CorrelatedNoiseFilterAccuracy guarantees, with proof-witness references.
Supporting domains and budgets live in `Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy`. -/

/-! ----------------------------------------------------------------------
## Retained-factor horizon accuracy
-------------------------------------------------------------------------- -/

/-- Original-input initialization and every finite prefix succeed, with uniform
covariance and mean error at most 2⁻²⁵ and both covariances positive-definite.
Proof witness: `Kalman.Proofs.FloatInputHorizon.initializedHorizonAccuracy`
(the existing `FloatInputHorizon.initialized_horizon_accuracy` proof). -/
def InitializedHorizonAccuracy : Prop :=
  ∀ (initializationInput : Input.Model) (initial : Input.State)
    (inputs : Nat → Input.Model) (horizon : Nat)
    (_ : HorizonDomain initializationInput initial inputs horizon),
    ∃ retained,
      SquareRootFilter.fromCovariance initializationInput initial = .ok retained
      ∧ (∀ t,
          t ≤ horizon
          → ∃ output,
              nativeRun inputs retained t = .ok output
              ∧ FactorAccuracy uniformBudget uniformBudget 2 output
                  (exactRun 2 2 inputs (state 2 initial) t)
              ∧ StateInvariant output
              ∧ (factorState 2 output).covariance.PosDef
              ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef)

/-! ----------------------------------------------------------------------
## Rounded dense horizon accuracy
-------------------------------------------------------------------------- -/

/-- The correlated family also has finite symmetric rounded dense output,
covariance error 2⁻²⁵ + 2⁻⁴⁸, mean error 2⁻²⁵, and strict covariance positivity.
Proof witness: `Kalman.Proofs.FloatDenseHorizon.initializedDenseHorizonAccuracy`
(the existing `FloatDenseHorizon.initialized_dense_horizon_accuracy` proof). -/
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
              ∧ FactorAccuracy uniformBudget uniformBudget 2 factor
                  (exactRun 2 2 inputs (state 2 initial) t)
              ∧ ((factorState 2 factor).covariance - retainedFloor • 1).PosSemidef
              ∧ DenseMaterializationWithin factor output
              ∧ DenseHorizonAccuracy output (exactRun 2 2 inputs (state 2 initial) t)
              ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef

end
end Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
