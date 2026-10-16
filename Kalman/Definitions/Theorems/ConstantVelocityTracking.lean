import Kalman.Definitions.Theorems.ConstantVelocity

/-! A normalized correlated steady-covariance tracking family and its weighted
mean comparison. These project choices specialize the attributed linear model. -/

namespace Kalman.Definitions.Theorems.ConstantVelocityTracking
open Matrix Kalman.Definitions.LinearModel
noncomputable section

def posteriorCovariance : Square 2 := !![1 / 2, 1 / 4; 1 / 4, 1]
def priorCovariance : Square 2 := !![1, 1 / 2; 1 / 2, 9 / 8]

def trackingModel : Model 2 1 :=
  ⟨!![1, 1 / 4; 0, 1], !![1, 0], !![5 / 16, 0; 0, 1 / 8], !![1]⟩

def correctedMean (x : Vector 2) (z : ℝ) : Vector 2 :=
  ![x 0 / 2 + z / 2, x 1 - x 0 / 4 + z / 4]

def trackingMean (x : Vector 2) (z : ℝ) : Vector 2 :=
  ![x 0 / 2 + x 1 / 8 + z / 2, -x 0 / 4 + 15 * x 1 / 16 + z / 4]

def WeightedWithin (r : ℝ) (x y : Vector 2) : Prop :=
  0 ≤ r ∧ |x 0 - y 0| ≤ r ∧ |x 1 - y 1| ≤ 4 * r

/-- Exact steady covariance and coupled mean recursion.
Witness: `ConstantVelocityTracking.stationaryStep`. -/
def StationaryStep : Prop :=
  ∀ (x : Vector 2) (z : ℝ),
    Kalman.Definitions.CovarianceRecursion.step .joseph trackingModel
      ⟨x, posteriorCovariance⟩ (fun _ => z)
    = ⟨trackingMean x z, posteriorCovariance⟩

/-- Same-measurement perturbations do not grow in the weighted mean comparison.
Witness: `ConstantVelocityTracking.meanNonexpansive`. -/
def MeanNonexpansive : Prop :=
  ∀ (x y : Vector 2) (z r : ℝ),
    WeightedWithin r x y → WeightedWithin r (trackingMean x z) (trackingMean y z)
end
end Kalman.Definitions.Theorems.ConstantVelocityTracking
