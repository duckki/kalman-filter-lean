import Kalman.Implementation.Correctness.ConstantVelocityPrediction
import Kalman.Definitions.Theorems.TrackingCovarianceTube

/-! Original-input domains for a nonstationary correlated tracking envelope.
The matrix neighborhood and parameter bounds are original mathematical
conditions, never assumptions about intermediate execution or desired outputs. -/

namespace Kalman.Implementation.Correctness.CorrelatedTracking

open Matrix Kalman.Definitions
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.TrackingCovarianceTube
  Kalman.Definitions.Theorems.RecursionSensitivity
  Flare.Binary64.Value

noncomputable section

/-- Valid original stored model with bounded changes around the nominal
position/velocity model. Measurement noise may increase from one. -/
structure ModelDomain (input : Input.Model) (dt : Float) : Prop where
  state_dimension : input.stateDimension = 2
  measurement_dimension : input.measurementDimension = 1
  input_valid : input.validate = .ok ()
  transition_words : input.transition = #[1.0, dt, 0.0, 1.0]
  dt_finite : dt.isFinite = true
  dt_bound : |value dt| ≤ 1
  observation_words : input.observation = #[1.0, 0.0]
  process_finite : input.processNoise.all Float.isFinite = true
  noise_finite : input.measurementNoise.all Float.isFinite = true
  measurement_finite : input.measurement.all Float.isFinite = true
  noise_size : input.measurementNoise.size = 1
  measurement_size : input.measurement.size = 1
  process_psd : (matrix 2 2 input.processNoise).PosSemidef
  transition_close
    : EntrywiseWithin parameterRadius (matrix 2 2 input.transition)
        trackingModel.transition
  process_close
    : EntrywiseWithin parameterRadius (matrix 2 2 input.processNoise)
        trackingModel.processNoise
  noise_close
    : EntrywiseWithin parameterRadius (matrix 1 1 input.measurementNoise)
        trackingModel.measurementNoise
  noise_lower : 1 ≤ value (input.measurementNoise.getD 0 0.0)
  measurement_bound : |value (input.measurement.getD 0 0.0)| ≤ (2 : ℝ) ^ (-24 : Int)

/-- Finite native storage and a genuine covariance neighborhood, allowing
initial and subsequent covariances different from the nominal fixed point. -/
structure StateDomain (r : ℝ) (s : Input.State) : Prop where
  mean_size : s.mean.size = 2
  covariance_size : s.covariance.size = 4
  mean_finite : s.mean.all Float.isFinite = true
  covariance_finite : s.covariance.all Float.isFinite = true
  covariance_tube : Tube (matrix 2 2 s.covariance)
  mean_envelope : WeightedWithin r (state 2 s).mean 0

/-- Actual checked step stays inside the covariance tube. The mean comparison
uses the nominal affine map and includes covariance/parameter changes as well
as native roundoff. Witness: `FloatCorrelatedTracking.step_envelope`. -/
def StepEnvelope (input : Input.Model) (s output : Input.State) : Prop :=
  SymmetricJosephFilter.step input s = .ok output
  ∧ output.mean.size = 2
  ∧ output.covariance.size = 4
  ∧ output.mean.all Float.isFinite = true
  ∧ output.covariance.all Float.isFinite = true
  ∧ Tube (matrix 2 2 output.covariance)
  ∧ WeightedWithin ((2 : ℝ) ^ (-8 : Int)) (state 2 output).mean
      (trackingMean (state 2 s).mean (value (input.measurement.getD 0 0.0)))

/-- Original data only, for a short covariance-transient tracking horizon.
The mean envelope, rather than covariance positivity, limits this horizon. -/
structure HorizonDomain (inputs : Nat → Input.Model) (increments : Nat → Float)
    (initial : Input.State) (horizon : Nat)
    : Prop where
  horizon_bound : horizon ≤ 16
  initial_state : StateDomain (1 / 8) initial
  input_domain : ∀ t, t < horizon → ModelDomain (inputs t) (increments t)

/-- Successful native prefix and the retained nonstationary neighborhood.
Witness: `FloatCorrelatedTracking.horizon_preservation`. -/
def HorizonPreserved (inputs : Nat → Input.Model) (initial : Input.State)
    (t : Nat) (output : Input.State)
    : Prop :=
  SymmetricJosephFilter.run inputs initial t = .ok output
  ∧ StateDomain (1 / 8 + t * ((2 : ℝ) ^ (-25 : Int) + (2 : ℝ) ^ (-8 : Int))) output

end
end Kalman.Implementation.Correctness.CorrelatedTracking
