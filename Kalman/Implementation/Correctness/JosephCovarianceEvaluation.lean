import Kalman.Implementation.CovarianceFilter
import Kalman.Implementation.Correctness.InputInterpretation

namespace Kalman.Implementation.Correctness.JosephCovarianceEvaluation

open Kalman.Definitions
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.Correctness.InputInterpretation

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

end
end Kalman.Implementation.Correctness.JosephCovarianceEvaluation
