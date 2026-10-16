import Kalman.Definitions.Theorems.UncertaintyBounds

/-! Exact position-observation geometry and the symmetric part used to describe
rounded outputs without assuming exact stored symmetry. -/

namespace Kalman.Definitions.Theorems.JosephPositionCorrection

open Matrix Kalman.Definitions.LinearModel Kalman.Definitions.CovarianceRecursion

noncomputable section

/-- One scalar position observation of a position/velocity state. -/
def positionRow : Matrix (Fin 1) (Fin 2) ℝ :=
  Matrix.of (fun _ (j : Fin 2) => if j = 0 then 1 else 0)

/-- Exact symmetric part; this is an interpretation, not native symmetry repair. -/
def symmetricPart {n : Nat} (a : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (a + a.transpose)

/-- A quantitative exact Joseph floor at arbitrary gains, sufficient to pay
for native correction error. Witness: `JosephPositionCorrection.covariance_floor`. -/
def CovarianceFloor : Prop :=
  ∀ (input : Model 2 1) (prior : State 2),
    (prior.covariance - (1 / 2 : ℝ) • 1).PosSemidef
    → input.observation = positionRow
    → 1 ≤ input.measurementNoise 0 0
    → ∀ k : Matrix (Fin 2) (Fin 1) ℝ, (joseph input prior k - (1 / 4 : ℝ) • 1).PosSemidef

end
end Kalman.Definitions.Theorems.JosephPositionCorrection
