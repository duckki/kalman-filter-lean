import Kalman.Definitions.FactorRecursion

/-!
# Exact agreement between Kalman formulations

Statements comparing covariance formulas, the complete information-form update,
and covariance factors from exact QR stages. Each statement describes exactly
which outputs agree and names its proof witness.
-/

namespace Kalman.Definitions.Theorems.FormulationEquivalence

open Kalman.Definitions.LinearModel
open Kalman.Definitions.CovarianceRecursion
open Kalman.Definitions.FactorRecursion

noncomputable section

/-! ----------------------------------------------------------------------
## Covariance-form agreement
-------------------------------------------------------------------------- -/

/-- All three exact covariance formulas agree at the optimal gain.
Proof witness: `Kalman.Proofs.RealRecursion.covarianceFormulationsAgree`. -/
def CovarianceFormulationsAgree : Prop :=
  ∀ (n m : Nat) (model : Model n m) (prior : State n),
    prior.covariance.PosDef
    → model.measurementNoise.PosDef
    → compact model prior (gain model prior) = subtractive model prior (gain model prior)
      ∧ subtractive model prior (gain model prior) = joseph model prior (gain model prior)

/-! ----------------------------------------------------------------------
## Information-form agreement for covariance and mean
-------------------------------------------------------------------------- -/

/-- Information covariance and mean equal the Joseph correction.
Proof witness: `Kalman.Proofs.RealRecursion.informationFormAgrees`. -/
def InformationFormAgrees : Prop :=
  ∀ (n m : Nat) (model : Model n m) (prior : State n) (measurement : Vector m),
    prior.covariance.PosDef
    → model.measurementNoise.PosDef
    → informationUpdate model prior measurement = update .joseph model prior measurement

/-! ----------------------------------------------------------------------
## Square-root stage agreement for represented covariances
-------------------------------------------------------------------------- -/

/-- Exact factors denoting the source covariances make the QR stages agree with
the predicted covariance and direct Joseph correction.
Proof witness: `Kalman.Proofs.FactorStructure.squareRootStagesAgree`. -/
def SquareRootStagesAgree : Prop :=
  ∀ (n m : Nat) (model : Model n m) (prior : State n)
    (l tq predicted posterior : Square n) (tr innovationFactor : Square m)
    (k : Matrix (Fin n) (Fin m) ℝ),
    CovarianceFactor prior.covariance l
    → SquareRootStages model l tq tr predicted innovationFactor posterior k
    → gram predicted = (predict model prior).covariance
      ∧ gram posterior = (update .joseph model (predict model prior) 0).covariance

end
end Kalman.Definitions.Theorems.FormulationEquivalence
