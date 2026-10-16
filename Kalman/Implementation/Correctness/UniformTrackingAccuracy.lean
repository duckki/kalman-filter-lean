import Kalman.Implementation.Correctness.ConstantVelocityTracking

namespace Kalman.Implementation.Correctness.UniformTrackingAccuracy

open Kalman.Definitions Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Definitions.Theorems.RecursionSensitivity

/-- The checked correlated tracking horizon has a time-independent mean
radius `2^-29` and exactly zero covariance error. Its original input domain
is unchanged. Witness: `FloatUniformTracking.horizon_accuracy`. -/
def UniformAccuracy (measurements : Nat → Float) (initial : Input.State)
    (t : Nat) (output : Input.State)
    : Prop :=
  SymmetricJosephFilter.run
      (fun k => ConstantVelocityTracking.trackingInput (measurements k)) initial t
    = .ok output
  ∧ StateWithin 0 ((2 : ℝ) ^ (-29 : Int)) (state 2 output)
      (exactRun 2 1 (fun k => ConstantVelocityTracking.trackingInput (measurements k))
        (state 2 initial) t)

end Kalman.Implementation.Correctness.UniformTrackingAccuracy
