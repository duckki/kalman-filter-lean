import Kalman.Definitions.Theorems.RecursionSensitivity

/-! Deterministic uncertainty transfer. Statistical coverage of the ideal
interval is an external premise, not a consequence of numerical accuracy.
Proof witnesses are in `Kalman.Proofs.UncertaintyBounds`. -/

namespace Kalman.Definitions.Theorems.UncertaintyBounds

open Matrix Kalman.Definitions.Theorems.RecursionSensitivity

noncomputable section

/-- A symmetric covariance difference is positive semidefinite. -/
def CovarianceOverbound {n : Nat} (upper reference : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (upper - reference).PosSemidef

/-- Coverage of a scalar ideal interval, interpreted entirely over Real. -/
def IntervalCovered (truth center variance multiplier : ℝ) : Prop :=
  |truth - center| ≤ multiplier * Real.sqrt variance

/-- Exact diagonal inflation transfers an entrywise covariance error into
semidefinite order. Proof witness: `UncertaintyBounds.diagonal_overbound`. -/
def DiagonalInflation : Prop :=
  ∀ {n : Nat} (actual reference : Fin n → ℝ) (ε : ℝ),
    EntrywiseWithin ε (diagonal actual) (diagonal reference)
    → CovarianceOverbound (diagonal (fun i => actual i + ε)) (diagonal reference)

end
end Kalman.Definitions.Theorems.UncertaintyBounds
