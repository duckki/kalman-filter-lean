import Kalman.Implementation.Correctness.ConstantVelocityPrediction
import Kalman.Definitions.Theorems.ConstantVelocityTracking

namespace Kalman.Implementation.Correctness.ConstantVelocityTracking

open Kalman.Definitions Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.RecursionSensitivity

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

/-- Original finite measurements and an initial stored-state envelope. The
horizon cap pays for accumulated local errors and keeps local domains closed. -/
structure HorizonDomain (measurements : Nat → Float) (initial : Input.State)
    (horizon : Nat)
    : Prop where
  horizon_bound : horizon ≤ 1048576
  initial_state : TrackingState (1 / 8) initial
  measurements_finite : ∀ t, t < horizon → (measurements t).isFinite = true
  measurements_bound
    : ∀ t,
        t < horizon
        → |Flare.Binary64.Value.value (measurements t)| ≤ (2 : ℝ) ^ (-24 : Int)

/-- Actual checked execution, retained operating envelope, exact stored
covariance, and accumulated error against an independently propagated Real
trajectory from the original initial state and every original measurement.
Witness: `FloatConstantVelocityHorizon.horizon_accuracy`. -/
def HorizonAccuracy (measurements : Nat → Float) (initial : Input.State)
    (t : Nat) (output : Input.State)
    : Prop :=
  SymmetricJosephFilter.run (fun k => trackingInput (measurements k)) initial t
    = .ok output
  ∧ TrackingState (1 / 8 + t * ((2 : ℝ) ^ (-25 : Int) + (2 : ℝ) ^ (-36 : Int))) output
  ∧ StateWithin 0 (4 * t * (2 : ℝ) ^ (-36 : Int)) (state 2 output)
      (exactRun 2 1 (fun k => trackingInput (measurements k)) (state 2 initial) t)

end
end Kalman.Implementation.Correctness.ConstantVelocityTracking
