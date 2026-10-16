import Kalman.Implementation.CovarianceFilter
import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Definitions.Theorems.JosephPositionCorrection

/-! Original stored-input domain and complete local position-only Joseph
correction. The original prior may be correlated. Prediction and a horizon are
not included. No intermediate arithmetic success or desired error is assumed. -/

namespace Kalman.Implementation.Correctness.JosephPositionCorrection

open Matrix Kalman.Definitions Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Definitions.Theorems.JosephPositionCorrection
open Flare.Binary64.Value

noncomputable section

/-- Normalized, well-conditioned local operating envelope. Original model
validation is a storage/finite/noise-symmetry guard, not a gain-solve premise. -/
structure Domain (input : Input.Model) (prior : Input.State) : Prop where
  state_dimension : input.stateDimension = 2
  measurement_dimension : input.measurementDimension = 1
  input_valid : input.validate = .ok ()
  observation : input.observation = #[1.0, 0.0]
  prior_size : prior.covariance.size = 4
  mean_size : prior.mean.size = 2
  noise_size : input.measurementNoise.size = 1
  measurement_size : input.measurement.size = 1
  prior_finite : prior.covariance.all Float.isFinite = true
  mean_finite : prior.mean.all Float.isFinite = true
  noise_finite : input.measurementNoise.all Float.isFinite = true
  measurement_finite : input.measurement.all Float.isFinite = true
  prior_floor : (matrix 2 2 prior.covariance - (1 / 2 : ℝ) • 1).PosSemidef
  prior_bound : ∀ i j, |matrix 2 2 prior.covariance i j| ≤ 2
  noise_lower : 1 ≤ value (input.measurementNoise.getD 0 0.0)
  noise_upper : value (input.measurementNoise.getD 0 0.0) ≤ 3 / 2
  mean_bound : ∀ i, i < 2 → |value (prior.mean.getD i 0.0)| ≤ 1
  measurement_bound : |value (input.measurement.getD 0 0.0)| ≤ 1

/-- The unchanged checked native update succeeds. Its covariance can be
asymmetric: positivity is asserted for its exact symmetric part, and asymmetry
is quantitatively bounded. Witness: `FloatJosephPositionCorrection.update_accuracy`. -/
def CorrectionAccuracy (input : Input.Model) (prior output : Input.State) : Prop :=
  CovarianceFilter.update .joseph input prior = .ok output
  ∧ output.mean.size = 2
  ∧ output.covariance.size = 4
  ∧ output.mean.all Float.isFinite = true
  ∧ output.covariance.all Float.isFinite = true
  ∧ StateWithin ((2 : ℝ) ^ (-28 : Int)) ((2 : ℝ) ^ (-28 : Int)) (state 2 output)
      (CovarianceRecursion.update .joseph (model (atDimensions 2 1 input)) (state 2 prior)
        (vector 1 input.measurement))
  ∧ (∀ i j,
      |matrix 2 2 output.covariance i j - matrix 2 2 output.covariance j i|
      ≤ (2 : ℝ) ^ (-27 : Int))
  ∧ (symmetricPart (matrix 2 2 output.covariance) - (1 / 8 : ℝ) • 1).PosSemidef

end
end Kalman.Implementation.Correctness.JosephPositionCorrection
