import Kalman.Implementation.Correctness.ConstantVelocityPrediction
import Kalman.Definitions.Theorems.ConstantVelocityTracking

namespace Kalman.Implementation.Correctness.ConstantVelocityTracking

open Kalman.Definitions Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Definitions.Theorems.ConstantVelocityTracking

noncomputable section

/-- Fixed normalized posterior covariance, with a nonzero correlation. -/
def posteriorWords : Array Float := #[0.5, 0.25, 0.25, 1.0]

/-- Fixed normalized predicted covariance. -/
def priorWords : Array Float := #[1.0, 0.5, 0.5, 1.125]

/-- Original stored inputs for the first coupled tracking envelope. The
measurement varies; time increment and noise covariances are held fixed. -/
def trackingInput (z : Float) : Input.Model :=
  ⟨2, 1, #[1.0, 0.25, 0.0, 1.0], #[1.0, 0.0], #[0.3125, 0.0, 0.0, 0.125], #[1.0], #[z]⟩

/-- A bounded mean and the exact correlated steady covariance in native words. -/
structure TrackingState (radius : ℝ) (s : Input.State) : Prop where
  mean_size : s.mean.size = 2
  mean_finite : s.mean.all Float.isFinite = true
  covariance_words : s.covariance = posteriorWords
  mean_envelope : WeightedWithin radius (state 2 s).mean 0

/-- Checked full step, exact retained correlated covariance and a weighted
local mean error. Witness: `FloatConstantVelocityTracking.step_accuracy`. -/
def StepAccuracy (z : Float) (s output : Input.State) : Prop :=
  SymmetricJosephFilter.step (trackingInput z) s = .ok output
  ∧ output.mean.size = 2
  ∧ output.mean.all Float.isFinite = true
  ∧ output.covariance = posteriorWords
  ∧ WeightedWithin ((2 : ℝ) ^ (-36 : Int)) (state 2 output).mean
      (trackingMean (state 2 s).mean (Flare.Binary64.Value.value z))

end
end Kalman.Implementation.Correctness.ConstantVelocityTracking
