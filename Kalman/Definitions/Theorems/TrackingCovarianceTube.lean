import Kalman.Definitions.Theorems.ConstantVelocityTracking

/-! A correlated covariance neighborhood with an explicit Lyapunov weight. -/

namespace Kalman.Definitions.Theorems.TrackingCovarianceTube
open Matrix Kalman.Definitions.LinearModel
  Kalman.Definitions.Theorems.ConstantVelocityTracking
noncomputable section

def weight : Square 2 := !![75 / 47, 40 / 47; 40 / 47, 272 / 47]
def closedTransition : Square 2 := !![1 / 2, 1 / 8; -1 / 4, 15 / 16]
def steadyGain : Matrix (Fin 2) (Fin 1) ℝ := !![1 / 2; 1 / 4]
def radius : ℝ := (2 : ℝ) ^ (-12 : Int)
def parameterRadius : ℝ := (2 : ℝ) ^ (-21 : Int)

def Tube (p : Square 2) : Prop :=
  (radius • weight + (p - posteriorCovariance)).PosSemidef
  ∧ (radius • weight - (p - posteriorCovariance)).PosSemidef

/-- Exact Lyapunov identity. Witness: `TrackingCovarianceTube.lyapunovIdentity`. -/
def LyapunovIdentity : Prop :=
  closedTransition * weight * closedTransition.transpose = weight - 1

/-- Entrywise extent of the covariance neighborhood.
Witness: `TrackingCovarianceTube.tubeEntryBound`. -/
def TubeEntryBound : Prop :=
  ∀ p : Square 2,
    Tube p
    → Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin
        (6 * radius) p posteriorCovariance
end
end Kalman.Definitions.Theorems.TrackingCovarianceTube
