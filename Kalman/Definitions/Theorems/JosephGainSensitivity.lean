import Kalman.Definitions.Theorems.RecursionSensitivity

/-! Exact optimal-gain completion of the square, in arbitrary dimensions.
Proof witnesses are in `Kalman.Proofs.JosephGainSensitivity`. These standard
identities concern exact arithmetic; native evaluation errors remain separate. -/

namespace Kalman.Definitions.Theorems.JosephGainSensitivity

open Matrix Kalman.Definitions.LinearModel Kalman.Definitions.CovarianceRecursion
open Kalman.Definitions.Theorems.RecursionSensitivity

noncomputable section

/-- Exact gain error enters Joseph covariance quadratically. -/
def GainDifference : Prop :=
  ∀ {n m : Nat} (input : Model n m) (prior : State n),
    prior.covariance.PosSemidef
    → input.measurementNoise.PosDef
    → ∀ k : Matrix (Fin n) (Fin m) ℝ,
        joseph input prior k - joseph input prior (gain input prior)
        = (k - gain input prior) * innovationCovariance input prior
          * (k - gain input prior).transpose

/-- An arbitrary exact gain overbounds the optimal-gain Joseph covariance. -/
def OptimalOverbound : Prop :=
  ∀ {n m : Nat} (input : Model n m) (prior : State n),
    prior.covariance.PosSemidef
    → input.measurementNoise.PosDef
    → ∀ k : Matrix (Fin n) (Fin m) ℝ,
        (joseph input prior k - joseph input prior (gain input prior)).PosSemidef

end
end Kalman.Definitions.Theorems.JosephGainSensitivity
