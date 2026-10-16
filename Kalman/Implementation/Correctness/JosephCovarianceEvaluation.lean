import Kalman.Implementation.CovarianceFilter
import Kalman.Implementation.Correctness.InputInterpretation

namespace Kalman.Implementation.Correctness.JosephCovarianceEvaluation

open Kalman.Definitions
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.Correctness.InputInterpretation
open Flare.Binary64.Value

noncomputable section

/-! Numerical result statements with proof witnesses. -/

/-! ----------------------------------------------------------------------
## Completed result statements
-------------------------------------------------------------------------- -/

/-- Evaluation error of the complete direct Joseph covariance kernel, at the
same stored gain K. Gain-design and prediction errors are separate obligations.
Proof witness: `Kalman.Proofs.FloatErrorBounds.josephCovarianceAccuracy`. -/
def JosephCovarianceAccuracy (ε : ℝ) (input : Input.Model) (prior : Input.State)
    (k output : Array Float)
    : Prop :=
  Kalman.Implementation.CovarianceFilter.covarianceUnchecked .joseph input prior k
    = .ok output
  ∧ EntrywiseWithin ε (matrix input.stateDimension input.stateDimension output)
      (CovarianceRecursion.joseph (model input) (state input.stateDimension prior)
        (matrix input.stateDimension input.measurementDimension k))

/-! ----------------------------------------------------------------------
## Stored-input covariance evaluation domain
-------------------------------------------------------------------------- -/

/-- Sufficient two-state operand ranges for direct Joseph covariance evaluation.
The gain is supplied storage, not assumed exact or assumed to be a successful
solve. No intermediate execution or desired output accuracy is a premise. -/
structure TwoStateDomain (input : Input.Model) (prior : Input.State) (k : Array Float)
    : Prop where
  state_dimension : input.stateDimension = 2
  measurement_dimension : input.measurementDimension = 2
  covariance_size : prior.covariance.size = 4
  observation_size : input.observation.size = 4
  noise_size : input.measurementNoise.size = 4
  gain_size : k.size = 4
  covariance_finite : prior.covariance.all Float.isFinite = true
  observation_finite : input.observation.all Float.isFinite = true
  noise_finite : input.measurementNoise.all Float.isFinite = true
  gain_finite : k.all Float.isFinite = true
  covariance_bound : ∀ i j, |matrix 2 2 prior.covariance i j| ≤ 4
  observation_bound : ∀ i j, |matrix 2 2 input.observation i j| ≤ 1
  noise_bound : ∀ i j, |matrix 2 2 input.measurementNoise i j| ≤ 3 / 2
  gain_bound : ∀ i j, |matrix 2 2 k i j| ≤ 1

/-- Complete covariance-kernel execution and absolute entrywise error 2^-34
from stored operands alone. This result does not yet include prediction,
computed-gain error, mean error, or a horizon invariant.
Proof witness: `Kalman.Proofs.FloatJosephDomain.stored_input_accuracy`. -/
def StoredInputAccuracy : Prop :=
  ∀ (input : Input.Model) (prior : Input.State) (k : Array Float),
    TwoStateDomain input prior k
    → ∃ output,
        output.size = 4
        ∧ output.all Float.isFinite = true
        ∧ JosephCovarianceAccuracy ((2 : ℝ) ^ (-34 : Int)) input prior k output

/-! ----------------------------------------------------------------------
## Local diagonal covariance positivity
-------------------------------------------------------------------------- -/

/-- Under full observation, diagonal prior/noise variances at least one half,
and the stored-input bounds above, the actual rounded Joseph kernel retains a
strict diagonal floor and is positive definite. The bounded supplied gain need
not be optimal. This result does not certify prediction, gain computation, or
a full-filter horizon.
Proof witness: `Kalman.Proofs.FloatJosephStructure.stored_input_positive`. -/
def StoredDiagonalPositive : Prop :=
  ∀ (input : Input.Model) (prior : Input.State) (k : Array Float),
    TwoStateDomain input prior k
    → DecodedDiagonal 2 prior.covariance
    → matrix 2 2 input.observation = 1
    → DecodedDiagonal 2 input.measurementNoise
    → DecodedDiagonal 2 k
    → (∀ i, (1 : ℝ) / 2 ≤ matrix 2 2 prior.covariance i i)
    → (∀ i, (1 : ℝ) / 2 ≤ matrix 2 2 input.measurementNoise i i)
    → ∃ output,
        output.size = 4
        ∧ output.all Float.isFinite = true
        ∧ JosephCovarianceAccuracy ((2 : ℝ) ^ (-34 : Int)) input prior k output
        ∧ DecodedDiagonal 2 output
        ∧ (∀ i, (1 : ℝ) / 8 ≤ matrix 2 2 output i i)
        ∧ (matrix 2 2 output).PosDef

end
end Kalman.Implementation.Correctness.JosephCovarianceEvaluation
