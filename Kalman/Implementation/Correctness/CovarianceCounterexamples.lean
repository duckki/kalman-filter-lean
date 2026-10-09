import Kalman.Implementation.CovarianceFilter
import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Definitions.Theorems.CovariancePositiveDefiniteness

/-!
# Certified covariance failures

Valid finite inputs can make compact and subtractive covariance updates return
a negative quadratic form while the exact Real covariance is positive-definite.
The witness relation records exactly the input, execution, and comparison facts.
-/

namespace Kalman.Implementation.Correctness.CovarianceCounterexamples

open Matrix
open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation

noncomputable section

def realForm (form : Kalman.Implementation.CovarianceFilter.Form)
    : CovarianceRecursion.Form :=
  match form with
  | .compact => .compact
  | .subtractive => .subtractive
  | .joseph => .joseph

/-- The strongest simple failure certificate: an explicitly negative quadratic
form in the decoded dense posterior, while the exact full-step result is PD.
Proof witnesses: `Kalman.Proofs.FloatCounterexamples.compact_negative_witness`
and `Kalman.Proofs.FloatCounterexamples.subtractive_negative_witness`. -/
def NegativeQuadraticWitness (form : Kalman.Implementation.CovarianceFilter.Form)
    (input : Input.Model) (initial output : Input.State)
    (v : LinearModel.Vector input.stateDimension)
    : Prop :=
  input.validate = .ok ()
  ∧ initial.validate input.stateDimension = .ok ()
  ∧ Theorems.CovariancePositiveDefiniteness.StrictDomain (model input)
      (state input.stateDimension initial)
  ∧ Kalman.Implementation.CovarianceFilter.step form input initial = .ok output
  ∧ output.validate input.stateDimension = .ok ()
  ∧ v ≠ 0
  ∧ dotProduct v ((state input.stateDimension output).covariance *ᵥ v) < 0
  ∧ (CovarianceRecursion.step (realForm form) (model input)
      (state input.stateDimension initial)
      (vector input.measurementDimension input.measurement)).covariance.PosDef

/-! ----------------------------------------------------------------------
## Completed failure statements
-------------------------------------------------------------------------- -/

/-- Valid finite inputs can make the compact native filter return a negative
quadratic form while its exact Real step is positive-definite.
Proof witness: `Kalman.Proofs.FloatCounterexamples.compactCanReturnNegativeCovariance`. -/
def CompactCanReturnNegativeCovariance : Prop :=
  ∃ (input : Input.Model) (initial output : Input.State)
    (v : LinearModel.Vector input.stateDimension),
    NegativeQuadraticWitness .compact input initial output v

/-- The same failure is possible for the subtractive native covariance update.
Proof witness: `Kalman.Proofs.FloatCounterexamples.subtractiveCanReturnNegativeCovariance`. -/
def SubtractiveCanReturnNegativeCovariance : Prop :=
  ∃ (input : Input.Model) (initial output : Input.State)
    (v : LinearModel.Vector input.stateDimension),
    NegativeQuadraticWitness .subtractive input initial output v

end
end Kalman.Implementation.Correctness.CovarianceCounterexamples
