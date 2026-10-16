import Kalman.Implementation.UncertaintyIntervals
import Kalman.Definitions.Theorems.UncertaintyBounds
import Flare.Binary64.Value

namespace Kalman.Implementation.Correctness.UncertaintyIntervals

open Kalman.Definitions Kalman.Implementation.UncertaintyIntervals
  Kalman.Definitions.Theorems.UncertaintyBounds
  Flare.Binary64.Value

noncomputable section

/-- Normalized original finite inputs to the executable interval API. Caller
allowances may be zero; signed zero and subnormal variances are included. -/
structure Domain (mean variance covarianceError meanError multiplier : Float) : Prop where
  mean_finite : mean.isFinite = true
  variance_finite : variance.isFinite = true
  covariance_error_finite : covarianceError.isFinite = true
  mean_error_finite : meanError.isFinite = true
  multiplier_finite : multiplier.isFinite = true
  mean_bound : |value mean| ≤ 1
  variance_lower : 0 ≤ value variance
  variance_upper : value variance ≤ 2
  covariance_error_lower : 0 ≤ value covarianceError
  covariance_error_upper : value covarianceError ≤ 1
  mean_error_lower : 0 ≤ value meanError
  mean_error_upper : value meanError ≤ 2
  multiplier_lower : 0 ≤ value multiplier
  multiplier_upper : value multiplier ≤ 8

/-- Complete execution, native conservative variance and actual returned
endpoint coverage. Statistical coverage of the ideal interval is a caller
premise. Witness: `FloatUncertaintyIntervals.bounds_enclose`. -/
def Enclosure (mean variance covarianceError meanError multiplier : Float)
    (referenceMean referenceVariance : ℝ)
    : Prop :=
  ∃ output,
    Kalman.Implementation.UncertaintyIntervals.bounds mean variance
        covarianceError meanError multiplier
      = .ok output
    ∧ output.varianceUpper.isFinite = true
    ∧ output.radius.isFinite = true
    ∧ output.lower.isFinite = true
    ∧ output.upper.isFinite = true
    ∧ referenceVariance ≤ value output.varianceUpper
    ∧ value multiplier * Real.sqrt (value output.varianceUpper) + value meanError
      ≤ value output.radius
    ∧ value output.lower ≤ value mean - value output.radius
    ∧ value mean + value output.radius ≤ value output.upper
    ∧ (∀ truth,
        IntervalCovered truth referenceMean referenceVariance (value multiplier)
        → value output.lower ≤ truth ∧ truth ≤ value output.upper)

end
end Kalman.Implementation.Correctness.UncertaintyIntervals
