import Kalman.Implementation.Correctness.InputInterpretation

namespace Kalman.Implementation.Correctness.SquareRootFilterProperties

open Kalman.Definitions Kalman.Implementation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.Correctness.InputInterpretation

noncomputable section

/-! Successful square-root steps denote positive-definite covariances.
Optional rounded dense output has a separate accuracy guarantee; its positivity
requires the horizon margins in the complete original-input results. -/

/-! ----------------------------------------------------------------------
## Shared factor and comparison relations
-------------------------------------------------------------------------- -/

/-- A finite, lower triangular native factor with positive decoded diagonal. -/
def ValidFactor (n : Nat) (output : Input.FactorState) : Prop :=
  output.validate n = .ok () ∧ FactorRecursion.LowerPositive (matrix n n output.lower)

def MaterializationWithin (ε : ℝ) (n : Nat) (factor : Input.FactorState)
    (output : Input.State)
    : Prop :=
  ValidFactor n factor
  ∧ SquareRootFilter.materialize n factor = .ok output
  ∧ output.validate n = .ok ()
  ∧ EntrywiseWithin ε (state n output).covariance (factorState n factor).covariance

/-- Both the covariance and mean are compared with an independently supplied
exact state. Validation and native success are conclusions of the witnesses. -/
def FactorAccuracy (covarianceError meanError : ℝ) (n : Nat)
    (output : Input.FactorState) (reference : LinearModel.State n)
    : Prop :=
  ValidFactor n output
  ∧ EntrywiseWithin covarianceError (factorState n output).covariance reference.covariance
  ∧ 0 ≤ meanError
  ∧ ∀ i, |vector n output.mean i - reference.mean i| ≤ meanError

/-! ----------------------------------------------------------------------
## Positive definiteness of the retained factor
-------------------------------------------------------------------------- -/

/-- Every successful checked step returns a full-rank factor denoting a PD matrix.
Proved by `FloatFactorValidity`; this does not claim successful execution on
every mathematically valid input.
Proof witness: `Kalman.Proofs.FloatFactorValidity.successfulStepPositiveDefinite`. -/
def SuccessfulStepPositiveDefinite : Prop :=
  ∀ (input : Input.Model) (initial output : Input.FactorState),
    input.validate = .ok ()
    → initial.validate input.stateDimension = .ok ()
    → SquareRootFilter.step input initial = .ok output
    → ValidFactor input.stateDimension output
      ∧ (factorState input.stateDimension output).covariance.PosDef

/-! ----------------------------------------------------------------------
## Rounded covariance materialization
-------------------------------------------------------------------------- -/

/-- Optional dense output is within n·2⁻⁵⁰·M of the stored factor's exact Gram.
This statement guarantees finite valid output; dense strict PD is separate.
Proof witness: `Kalman.Proofs.FloatErrorBounds.factorMaterializationAccuracy`. -/
def FactorMaterializationAccuracy (n : Nat) (factor : Input.FactorState) (M : ℝ) : Prop :=
  ∃ output, MaterializationWithin (n * (2 : ℝ) ^ (-50 : Int) * M) n factor output

end
end Kalman.Implementation.Correctness.SquareRootFilterProperties
