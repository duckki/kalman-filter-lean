import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Definitions.Theorems.RecursionSensitivity

/-!
# Fully observed diagonal filter operating domains

Related interpretation relations, operand domains, and error contracts are
grouped below. These definitions state propositions; proof witnesses
live in `Kalman/Proofs/`.
-/

/-! ----------------------------------------------------------------------
## Diagonal prediction and innovation domains
-------------------------------------------------------------------------- -/

/-! Local native prediction/innovation domains for the larger diagonal-transition
family. These constrain the existing decoded input and retained working state;
no native run, arithmetic profile or desired accuracy is a premise. The slack
around the Real invariant accommodates later accumulated-roundoff arguments.
FloatObservableDiagonal adds returned diagonality for diagonal incoming factors;
The complete-step native invariant is stated in the main namespace below. -/

namespace Kalman.Proofs.DiagonalStages.Prediction

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Flare.Binary64.Value

noncomputable section

structure TwoStateDomain (input : Input.Model) (initial : Input.FactorState) : Prop where
  state_dimension : input.stateDimension = 2
  transition_size : input.transition.size = 4
  transition_finite : input.transition.all Float.isFinite = true
  transition_diagonal : DecodedDiagonal 2 input.transition
  transition_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 input.transition i j)| ≤ 1
  factor_size : initial.lower.size = 4
  factor_finite : initial.lower.all Float.isFinite = true
  factor_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 initial.lower i j)| ≤ 2
  covariance_diagonal_cap
    : ∀ i, FactorRecursion.gram (matrix 2 2 initial.lower) i i ≤ 13 / 8
  noise : NoiseDomain input.processNoise
  mean_size : initial.mean.size = 2
  mean_finite : initial.mean.all Float.isFinite = true
  mean_bound : ∀ i, i < 2 → |value (initial.mean.getD i 0.0)| ≤ 9 / 8

structure InnovationDomain (input : Input.Model) (prior : Input.FactorState) : Prop where
  observation : ObservationInputs input
  factor_size : prior.lower.size = 4
  factor_finite : prior.lower.all Float.isFinite = true
  factor_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 prior.lower i j)| ≤ 2
  covariance_diagonal_cap
    : ∀ i, FactorRecursion.gram (matrix 2 2 prior.lower) i i ≤ 13 / 4
  covariance_floor
    : (FactorRecursion.gram (matrix 2 2 prior.lower) - (15 / 16 : ℝ) • 1).PosSemidef

def localCovarianceRadius : ℝ :=
  let e := productRadius 2 8
  qrGramRadius 4 2 (fun _ => 21 / 8)
  + 2 * (2 * e * (2 * 1 * 2) + e ^ 2)
  + (diagonalRadius 2 8 + divisionRadius 2 8 (1 / 2) 2)

def localInnovationRadius : ℝ :=
  let e := productRadius 2 8
  qrGramRadius 4 2 (fun _ => 25 / 8) + 2 * (2 * e * 2 + e ^ 2) + (2 : ℝ) ^ (-42 : Int)

end
end Kalman.Proofs.DiagonalStages.Prediction

/-! ----------------------------------------------------------------------
## Diagonal mean correction domain
-------------------------------------------------------------------------- -/

/-! Original local mean/measurement conditions for full-observation diagonal
correction. Profiles, successful runs and desired errors are not premises. -/

namespace Kalman.Proofs.DiagonalStages.Mean

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Flare.Binary64.Value

noncomputable section

structure VectorDomain (mean measurement : Array Float) : Prop where
  mean_size : mean.size = 2
  measurement_size : measurement.size = 2
  mean_finite : mean.all Float.isFinite = true
  measurement_finite : measurement.all Float.isFinite = true
  mean_bound : ∀ i, i < 2 → |value (mean.getD i 0.0)| ≤ 19 / 16
  measurement_bound : ∀ i, i < 2 → |value (measurement.getD i 0.0)| ≤ 1

structure TwoStateDomain (input : Input.Model) (prior : Input.FactorState) : Prop
    extends Kalman.Proofs.DiagonalStages.Prediction.InnovationDomain input prior where
  state_dimension : input.stateDimension = 2
  diagonal : DecodedDiagonal 2 prior.lower
  vectors : VectorDomain prior.mean input.measurement

end
end Kalman.Proofs.DiagonalStages.Mean

/-! ----------------------------------------------------------------------
## Diagonal posterior correction domain
-------------------------------------------------------------------------- -/

/-! Posterior covariance allowance for the fully observed diagonal family.
The prearray allowance includes arithmetic, original-R Cholesky and the exact
quadratic gain perturbation. Its derivation is in FloatObservablePosterior. -/

namespace Kalman.Proofs.DiagonalStages.Posterior

open Kalman.Proofs.QRProfiles

noncomputable def localCovarianceRadius : ℝ :=
  qrGramRadius 4 2 (fun _ => 15 / 8) + (2 : ℝ) ^ (-36 : Int)

end Kalman.Proofs.DiagonalStages.Posterior

/-! ----------------------------------------------------------------------
## Local step comparator and propagated allowances
-------------------------------------------------------------------------- -/

namespace Kalman.Proofs.DiagonalStages

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation

noncomputable section

/-- Only dimension metadata is fixed; every arithmetic input word is identical. -/
def exactStep (input : Input.Model) (initial : Input.FactorState) : LinearModel.State 2 :=
  CovarianceRecursion.step .joseph
    (model (Kalman.Implementation.Correctness.InputInterpretation.atDimensions 2 2 input))
    (factorState 2 initial) (vector 2 input.measurement)

def localCovarianceRadius : ℝ :=
  (2 : ℝ) ^ (-29 : Int) + 2 / 5 * (7 * (2 : ℝ) ^ (-32 : Int))

def localMeanRadius : ℝ :=
  9 * (2 : ℝ) ^ (-29 : Int)
  + 8 / 13 * (2 : ℝ) ^ (-46 : Int)
  + 17 / 30 * (7 * (2 : ℝ) ^ (-32 : Int))

def localJointRadius : ℝ := 5 * (2 : ℝ) ^ (-28 : Int)

end
end Kalman.Proofs.DiagonalStages

/-! ----------------------------------------------------------------------
## Scalar projections for exact horizon proofs
-------------------------------------------------------------------------- -/

namespace Kalman.Proofs.DiagonalStages.Horizon

open Kalman.Definitions
open Kalman.Definitions.LinearModel
open Kalman.Implementation.Correctness.InputInterpretation

noncomputable section

def transition (input : Input.Model) : Vector 2 :=
  fun i => matrix 2 2 input.transition i i

def processVariance (input : Input.Model) : Vector 2 :=
  fun i => matrix 2 2 input.processNoise i i

def measurementVariance (input : Input.Model) : Vector 2 :=
  fun i => matrix 2 2 input.measurementNoise i i

end
end Kalman.Proofs.DiagonalStages.Horizon
