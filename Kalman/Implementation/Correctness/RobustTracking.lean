import Kalman.Implementation.PositionVelocityModel
import Kalman.Implementation.Correctness.CorrelatedTracking

namespace Kalman.Implementation.Correctness.RobustTracking

open Kalman.Definitions Kalman.Implementation.PositionVelocityModel
  Kalman.Definitions.Theorems.TrackingCovarianceTube
  Flare.Binary64.Value

noncomputable section

/-- A concrete original-word scalar parameter box. Changes in time step and
process variances are two-sided; measurement variance lies in `[1,1+theta]`. -/
structure ParameterDomain (p : Parameters) : Prop where
  time_finite : p.timeStep.isFinite = true
  position_process_finite : p.positionProcessVariance.isFinite = true
  velocity_process_finite : p.velocityProcessVariance.isFinite = true
  measurement_finite : p.measurementVariance.isFinite = true
  time_close : |value p.timeStep - 1 / 4| ≤ parameterRadius
  position_process_close : |value p.positionProcessVariance - 5 / 16| ≤ parameterRadius
  velocity_process_close : |value p.velocityProcessVariance - 1 / 8| ≤ parameterRadius
  measurement_lower : 1 ≤ value p.measurementVariance
  measurement_upper : value p.measurementVariance ≤ 1 + parameterRadius

/-- Original scalar parameter and measurement sequences, with a genuinely
nonstationary initial covariance allowed by the inherited state domain.
Witness: `FloatRobustTracking.horizon_preservation`. -/
structure HorizonDomain (parameters : Nat → Parameters) (measurements : Nat → Float)
    (initial : Input.State) (horizon : Nat)
    : Prop where
  horizon_bound : horizon ≤ 16
  initial_state : CorrelatedTracking.StateDomain (1 / 8) initial
  parameters_bound : ∀ t, t < horizon → ParameterDomain (parameters t)
  measurements_finite : ∀ t, t < horizon → (measurements t).isFinite = true
  measurements_bound : ∀ t, t < horizon → |value (measurements t)| ≤ (2 : ℝ) ^ (-24 : Int)

end
end Kalman.Implementation.Correctness.RobustTracking
