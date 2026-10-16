import Kalman.Implementation.UncertaintyInflation
import Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
import Kalman.Definitions.Theorems.UncertaintyBounds

/-! Rounded variance inflation for the completed diagonal Joseph horizon.
Proof witnesses: `FloatJosephUncertainty.inflate_variance` and
`FloatJosephUncertainty.horizon_overbound`. -/

namespace Kalman.Implementation.Correctness.JosephUncertainty

open Kalman.Definitions Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
open Flare.Binary64.Value

noncomputable section

/-- Actual finite rounded output bounds both the supplied ideal variance and
its own extra allowance; no successful addition is assumed. -/
def InflatedVariance (variance : Float) (reference : ℝ) : Prop :=
  ∃ upper,
    Kalman.Implementation.UncertaintyInflation.inflateVariance variance = .ok upper
    ∧ upper.isFinite = true
    ∧ reference ≤ value upper
    ∧ value upper ≤ value variance + (2 : ℝ) ^ (-28 : Int)

/-- Each original-input Joseph prefix supplies conservative rounded diagonal
variances. This is a deterministic ideal-covariance comparison, not a claim
about a physical error distribution. -/
def HorizonOverbound : Prop :=
  ∀ (initial : Input.State) (inputs : Nat → Input.Model) (horizon : Nat),
    HorizonDomain initial inputs horizon
    → ∀ t,
        t ≤ horizon
        → ∃ output,
            josephRun inputs initial t = .ok output
            ∧ ∀ i : Fin 2,
                InflatedVariance (output.covariance.getD (i.val * 2 + i.val) 0.0)
                  ((exactRun 2 2 inputs (state 2 initial) t).covariance i i)

end
end Kalman.Implementation.Correctness.JosephUncertainty
