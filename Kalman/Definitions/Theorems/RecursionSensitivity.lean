import Flare.Analysis.EntrywiseError
import Kalman.Definitions.CovarianceRecursion
import Kalman.Definitions.DiagonalObservation

/-!
# Exact Real sensitivity and contraction

Exact perturbation and contraction statements, with the comparison relations,
budgets, and operating domains needed to express them. Each result names its
proof witness; native roundoff guarantees are separate results.
-/

namespace Kalman.Definitions.Theorems.RecursionSensitivity

open Matrix
open Kalman.Definitions
open Kalman.Definitions.LinearModel
open Kalman.Definitions.DiagonalObservation

noncomputable section

/-! ----------------------------------------------------------------------
## General covariance and mean perturbation budgets
-------------------------------------------------------------------------- -/

/-! Explicit exact-recursion perturbation budgets for covariance and mean.
These are project propagation constants, independent of the native operation schedule. -/

/-- Absolute entrywise comparison of two Real matrices. -/
abbrev EntrywiseWithin {n m : Nat} (ε : ℝ) (a b : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  Flare.Analysis.EntrywiseError.EntrywiseWithin ε a b

def StateWithin {n : Nat} (covarianceError meanError : ℝ)
    (actual reference : LinearModel.State n)
    : Prop :=
  EntrywiseWithin covarianceError actual.covariance reference.covariance
  ∧ 0 ≤ meanError
  ∧ ∀ i, |actual.mean i - reference.mean i| ≤ meanError

def gainMagnitude (n m : Nat) (α P H : ℝ) : ℝ := (m : ℝ) * (n * P * H) / α

def correctionGainRadius (n m : Nat) (α P H eP : ℝ) : ℝ :=
  (m : ℝ) * (n * eP * H + m * (n ^ 2 * H ^ 2 * eP) * gainMagnitude n m α (P + eP) H) / α

def correctionCovarianceRadius (n m : Nat) (α P R H eP : ℝ) : ℝ :=
  let Ka := gainMagnitude n m α (P + eP) H
  let K := gainMagnitude n m α P H
  let eg := correctionGainRadius n m α P H eP
  let ew := m * eg * H
  n ^ 2 * (1 + m * Ka * H) ^ 2 * eP
  + (n ^ 2 * P * (2 * ew * (1 + m * K * H) + ew ^ 2) + m ^ 2 * R * (2 * eg * K + eg ^ 2))

def correctionMeanRadius (n m : Nat) (α P H Z eP eX : ℝ) : ℝ :=
  let eg := correctionGainRadius n m α P H eP
  let K := gainMagnitude n m α P H
  eX + m * (eg * Z + K * (n * H * eX) + eg * (n * H * eX))

/-! ----------------------------------------------------------------------
## Exact fully observed diagonal domains
-------------------------------------------------------------------------- -/

/-! Domains for the independent Real fully observed diagonal family.
These propositions specify operating conditions and comparison relations;
they are not native Float success or accuracy theorems. -/

structure DiagonalModelDomain {n : Nat} (f q r z : Vector n) : Prop where
  transition_bound : ∀ i, |f i| ≤ 1
  process_lower : ∀ i, 1 ≤ q i
  process_upper : ∀ i, q i ≤ 3 / 2
  measurement_lower : ∀ i, 1 ≤ r i
  measurement_upper : ∀ i, r i ≤ 3 / 2
  measurement_bound : ∀ i, |z i| ≤ 1

structure DiagonalStateInvariant {n : Nat} (reference : State n) : Prop where
  diagonal : reference.covariance = Matrix.diagonal (fun i => reference.covariance i i)
  covariance_lower : ∀ i, 1 / 2 ≤ reference.covariance i i
  covariance_upper : ∀ i, reference.covariance i i ≤ 3 / 2
  mean_bound : ∀ i, |reference.mean i| ≤ 1

structure DiagonalInitialDomain {n : Nat} (x p : Vector n) : Prop where
  covariance_lower : ∀ i, 1 / 2 ≤ p i
  covariance_upper : ∀ i, p i ≤ 3 / 2
  mean_bound : ∀ i, |x i| ≤ 1

/-- Joint radius with covariance weighted by two. The completed theorem
`RealObservableSensitivity.joint_step_contraction` proves coefficient 17/20
under the Real domain. Native local errors and accumulated componentwise
budgets are separately proved in FloatObservableFilter/FloatObservableHorizon. -/
def DiagonalJointWithin {n : Nat} (radius : ℝ) (actual reference : State n) : Prop :=
  StateWithin (radius / 2) radius actual reference

/-! ----------------------------------------------------------------------
## PredictionSensitivity
-------------------------------------------------------------------------- -/

/-- Exact Real predict_sensitivity statement.
Proof witness: `Kalman.Proofs.RecursionSensitivity.predictionSensitivity`. -/
def PredictionSensitivity : Prop :=
  ∀ {n m : Nat} (input : LinearModel.Model n m)
    (actual reference : LinearModel.State n) (F eP eX : ℝ) (_ : 0 ≤ F)
    (_ : ∀ i j, |input.transition i j| ≤ F)
    (_ : StateWithin eP eX actual reference),
    StateWithin (n ^ 2 * F ^ 2 * eP) (n * F * eX)
      (CovarianceRecursion.predict input actual)
      (CovarianceRecursion.predict input reference)

/-! ----------------------------------------------------------------------
## CorrectionSensitivity
-------------------------------------------------------------------------- -/

/-- Exact Real update_sensitivity statement.
Proof witness: `Kalman.Proofs.RecursionSensitivity.correctionSensitivity`. -/
def CorrectionSensitivity : Prop :=
  ∀ {n m : Nat} (input : LinearModel.Model n m)
    (actual reference : LinearModel.State n) (measurement : LinearModel.Vector m)
    (α P R H Z eP eX : ℝ) (_ : 0 < α) (_ : 0 ≤ P) (_ : 0 ≤ R)
    (_ : 0 ≤ H) (_ : 0 ≤ Z)
    (_ : actual.covariance.PosSemidef) (_ : reference.covariance.PosSemidef)
    (_ : (input.measurementNoise - α • 1).PosSemidef)
    (_ : ∀ i j, |reference.covariance i j| ≤ P)
    (_ : ∀ i j, |input.measurementNoise i j| ≤ R)
    (_ : ∀ i j, |input.observation i j| ≤ H)
    (_ : ∀ i, |CovarianceRecursion.innovation input reference measurement i| ≤ Z)
    (_ : StateWithin eP eX actual reference),
    StateWithin (correctionCovarianceRadius n m α P R H eP)
      (correctionMeanRadius n m α P H Z eP eX)
      (CovarianceRecursion.update .joseph input actual measurement)
      (CovarianceRecursion.update .joseph input reference measurement)

/-! ----------------------------------------------------------------------
## DiagonalStepSensitivity
-------------------------------------------------------------------------- -/

/-- Exact Real step_sensitivity statement.
Proof witness: `Kalman.Proofs.RealObservableSensitivity.diagonalStepSensitivity`. -/
def DiagonalStepSensitivity : Prop :=
  ∀ {n : Nat} (form : CovarianceRecursion.Form) (f q r z : Vector n)
    (actual reference : State n) (eP eX : ℝ) (_ : DiagonalModelDomain f q r z)
    (_ : actual.covariance = diagonal (fun i => actual.covariance i i))
    (_ : ∀ i, 0 ≤ actual.covariance i i) (_ : DiagonalStateInvariant reference)
    (_ : StateWithin eP eX actual reference),
    StateWithin (9 / 25 * eP) (3 / 5 * eX + 1 / 2 * eP)
      (CovarianceRecursion.step form (model f q r) actual z)
      (CovarianceRecursion.step form (model f q r) reference z)

/-! ----------------------------------------------------------------------
## DiagonalJointContraction
-------------------------------------------------------------------------- -/

/-- Exact Real joint_step_contraction statement.
Proof witness: `Kalman.Proofs.RealObservableSensitivity.diagonalJointContraction`. -/
def DiagonalJointContraction : Prop :=
  ∀ {n : Nat} (form : CovarianceRecursion.Form) (f q r z : Vector n)
    (actual reference : State n) (radius : ℝ) (_ : DiagonalModelDomain f q r z)
    (_ : actual.covariance = diagonal (fun i => actual.covariance i i))
    (_ : ∀ i, 0 ≤ actual.covariance i i) (_ : DiagonalStateInvariant reference)
    (_ : DiagonalJointWithin radius actual reference),
    DiagonalJointWithin (17 / 20 * radius)
      (CovarianceRecursion.step form (model f q r) actual z)
      (CovarianceRecursion.step form (model f q r) reference z)

/-! ----------------------------------------------------------------------
## DiagonalHorizonContraction
-------------------------------------------------------------------------- -/

/-- Exact Real horizon_contraction statement.
Proof witness: `Kalman.Proofs.RealObservableSensitivity.diagonalHorizonContraction`. -/
def DiagonalHorizonContraction : Prop :=
  ∀ {n : Nat} (f q r z : Nat → Vector n)
    (x p y v : Vector n) (horizon : Nat) (radius : ℝ)
    (_ : ∀ t, t < horizon → DiagonalModelDomain (f t) (q t) (r t) (z t))
    (_ : DiagonalInitialDomain x p) (_ : DiagonalInitialDomain y v)
    (_ : DiagonalJointWithin radius (state x p) (state y v)),
  ∀ t,
    t ≤ horizon
    → DiagonalJointWithin ((17 / 20 : ℝ) ^ t * radius) (run f q r z x p t)
        (run f q r z y v t)

end
end Kalman.Definitions.Theorems.RecursionSensitivity
