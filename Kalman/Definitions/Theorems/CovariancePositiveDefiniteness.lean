import Kalman.Definitions.CovarianceRecursion

/-!
# Exact positive-definiteness results

Statements for full-step covariance preservation and Joseph covariance positivity
at any gain. Proof witnesses are in `Kalman.Proofs.RealRecursion`.
Supporting source definitions remain in `Kalman.Definitions`.
-/

namespace Kalman.Definitions.Theorems.CovariancePositiveDefiniteness

open Matrix
open Kalman.Definitions.LinearModel
open Kalman.Definitions.CovarianceRecursion

noncomputable section

/-! ----------------------------------------------------------------------
## Positive-definiteness assumptions
-------------------------------------------------------------------------- -/

/-- Project's strict-PD profile, sufficient even for a singular transition.
The source permits weaker PSD hypotheses; see `docs/project-notes/project-background.md`, §4. -/
def StrictDomain {n m : Nat} (model : Model n m) (state : State n) : Prop :=
  0 < n
  ∧ 0 < m
  ∧ state.covariance.PosDef
  ∧ model.processNoise.PosDef
  ∧ model.measurementNoise.PosDef

/-! ----------------------------------------------------------------------
## Full-step preservation
-------------------------------------------------------------------------- -/

/-- The chosen full-step profile preserves strict positive definiteness.
Proof witness: `Kalman.Proofs.RealRecursion.stepPositiveDefinite`. -/
def StepPositiveDefinite : Prop :=
  ∀ (n m : Nat) (model : Model n m) (state : State n) (measurement : Vector m),
    StrictDomain model state
    → ∀ form, (step form model state measurement).covariance.PosDef

/-! ----------------------------------------------------------------------
## Joseph positivity at an arbitrary gain
-------------------------------------------------------------------------- -/

/-- Joseph positivity is valid for any gain when both input covariances are PD.
Proof witness: `Kalman.Proofs.RealRecursion.josephPositiveDefinite`. -/
def JosephPositiveDefinite : Prop :=
  ∀ (n m : Nat) (model : Model n m) (prior : State n) (k : Matrix (Fin n) (Fin m) ℝ),
    prior.covariance.PosDef
    → model.measurementNoise.PosDef
    → (joseph model prior k).PosDef

end
end Kalman.Definitions.Theorems.CovariancePositiveDefiniteness
