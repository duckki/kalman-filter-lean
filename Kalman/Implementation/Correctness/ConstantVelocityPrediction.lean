import Kalman.Implementation.Correctness.SymmetricJosephCorrection
import Kalman.Definitions.Theorems.ConstantVelocity

/-! Original-word bounded constant-velocity prediction domain. This domain is
local and allows correlated state and process covariances. -/

namespace Kalman.Implementation.Correctness.ConstantVelocityPrediction

open Matrix Kalman.Definitions
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Definitions.Theorems.RecursionSensitivity

noncomputable section

/-- Normalized original input bounds; no intermediate product is assumed. -/
structure Domain (input : Input.Model) (posterior : Input.State) (dt : Float) : Prop where
  state_dimension : input.stateDimension = 2
  measurement_dimension : input.measurementDimension = 1
  input_valid : input.validate = .ok ()
  state_valid : posterior.validate 2 = .ok ()
  transition_words : input.transition = #[1.0, dt, 0.0, 1.0]
  dt_finite : dt.isFinite = true
  dt_bound : |Flare.Binary64.Value.value dt| ≤ 1
  covariance_finite : posterior.covariance.all Float.isFinite = true
  mean_finite : posterior.mean.all Float.isFinite = true
  process_finite : input.processNoise.all Float.isFinite = true
  covariance_bound : ∀ i j, |matrix 2 2 posterior.covariance i j| ≤ 2
  mean_bound : ∀ i j, |matrix 2 1 posterior.mean i j| ≤ 1
  process_bound : ∀ i j, |matrix 2 2 input.processNoise i j| ≤ 2
  covariance_psd : (matrix 2 2 posterior.covariance).PosSemidef
  process_psd : (matrix 2 2 input.processNoise).PosSemidef

/-- Repaired prediction has finite shaped storage, exact stored symmetry, and
local original-word comparison radii. Witness:
`FloatConstantVelocityPrediction.predict_accuracy`. -/
def PredictionAccuracy (input : Input.Model) (posterior output : Input.State) : Prop :=
  SymmetricJosephFilter.predict input posterior = .ok output
  ∧ output.mean.size = 2
  ∧ output.covariance.size = 4
  ∧ output.mean.all Float.isFinite = true
  ∧ output.covariance.all Float.isFinite = true
  ∧ StateWithin ((2 : ℝ) ^ (-36 : Int)) ((2 : ℝ) ^ (-41 : Int)) (state 2 output)
      (CovarianceRecursion.predict (model (atDimensions 2 1 input)) (state 2 posterior))
  ∧ (matrix 2 2 output.covariance).IsHermitian

end
end Kalman.Implementation.Correctness.ConstantVelocityPrediction
