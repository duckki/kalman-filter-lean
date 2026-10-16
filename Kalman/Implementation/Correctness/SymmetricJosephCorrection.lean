import Kalman.Implementation.SymmetricJosephFilter
import Kalman.Implementation.Correctness.JosephPositionCorrection

/-! Stored symmetry and positive definiteness for the opt-in repaired correction.
The domain is the same original correlated-prior domain as the raw correction. -/

namespace Kalman.Implementation.Correctness.SymmetricJosephCorrection

open Matrix Kalman.Definitions
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Definitions.Theorems.RecursionSensitivity

noncomputable section

/-- Complete checked repaired update, with the same local error radii as the
raw update and a floor on the stored matrix itself.
Witness: `FloatSymmetricJosephCorrection.update_accuracy`. -/
def CorrectionAccuracy (input : Input.Model) (prior output : Input.State) : Prop :=
  SymmetricJosephFilter.update input prior = .ok output
  ∧ output.mean.size = 2
  ∧ output.covariance.size = 4
  ∧ output.mean.all Float.isFinite = true
  ∧ output.covariance.all Float.isFinite = true
  ∧ StateWithin ((2 : ℝ) ^ (-28 : Int)) ((2 : ℝ) ^ (-28 : Int)) (state 2 output)
      (CovarianceRecursion.update .joseph (model (atDimensions 2 1 input)) (state 2 prior)
        (vector 1 input.measurement))
  ∧ (matrix 2 2 output.covariance).IsHermitian
  ∧ (matrix 2 2 output.covariance - (1 / 8 : ℝ) • 1).PosSemidef

end
end Kalman.Implementation.Correctness.SymmetricJosephCorrection
