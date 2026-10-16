import Kalman.Definitions.Theorems.ConstantVelocityTracking

namespace Kalman.Definitions.Theorems.TrackingContraction

open Kalman.Definitions.LinearModel Kalman.Definitions.Theorems.ConstantVelocityTracking

/-- Exact two-step contraction with the same two measurements on both paths.
Witness: `TrackingContraction.two_step_contraction`. -/
def TwoStepContraction : Prop :=
  ∀ (x y : Vector 2) (z w r : ℝ),
    WeightedWithin r x y
    → WeightedWithin (15 / 16 * r) (trackingMean (trackingMean x z) w)
        (trackingMean (trackingMean y z) w)

/-- Uniform response to bounded local mean errors, from identical initial
means. Witness: `TrackingContraction.uniform_perturbation`. -/
def UniformPerturbation : Prop :=
  ∀ (actual reference : Nat → Vector 2) (measurements : Nat → ℝ) (horizon : Nat) (δ : ℝ),
    0 ≤ δ
    → actual 0 = reference 0
    → (∀ t,
        t < horizon
        → WeightedWithin δ (actual (t + 1)) (trackingMean (actual t) (measurements t)))
    → (∀ t, t < horizon → reference (t + 1) = trackingMean (reference t) (measurements t))
    → ∀ t, t ≤ horizon → WeightedWithin (32 * δ) (actual t) (reference t)

end Kalman.Definitions.Theorems.TrackingContraction
