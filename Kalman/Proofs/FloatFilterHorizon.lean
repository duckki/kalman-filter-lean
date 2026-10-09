import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Proofs.FloatFullFilter
import Kalman.Proofs.FloatFilterInitialization

/-! Successful checked native execution, full covariance/mean accuracy and
strict positivity at every prefix of a time-varying finite filter horizon. -/

namespace Kalman.Proofs.FloatFilterHorizon

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.FilterComposition.Horizon

theorem atDimensions_eq (n m : Nat) (input : Input.Model)
    (hn : input.stateDimension = n) (hm : input.measurementDimension = m)
    : atDimensions n m input = input := by
  cases input
  simp_all [atDimensions]

theorem factorAccuracy_mono {n : Nat} {output : Input.FactorState}
    {reference : LinearModel.State n} {eP eX fP fX : ℝ}
    (h : FactorAccuracy eP eX n output reference) (hP : eP ≤ fP) (hX : eX ≤ fX)
    : FactorAccuracy fP fX n output reference :=
  ⟨
    h.1,
    ⟨h.2.1.1.trans hP, fun i j => (h.2.1.2 i j).trans hP⟩,
    h.2.2.1.trans hX,
    fun i => (h.2.2.2 i).trans hX
  ⟩

/-- Both references use the same original native input words. Each prefix is
proved to succeed before its domain witness is used to establish the next.
Initial Cholesky error may be included in the two initial radii. -/
theorem finite_horizon_accuracy (n m horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State n) (eP eX : Nat → ℝ)
    (d : HorizonDomain n m horizon inputs initial reference eP eX)
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            nativeRun inputs initial t = .ok output
            ∧ FactorAccuracy (eP t) (eX t) n output (exactRun n m inputs reference t)
            ∧ (factorState n output).covariance.PosDef
            ∧ (exactRun n m inputs reference t).covariance.PosDef := by
  intro t ht
  induction t with
  | zero =>
      exact ⟨initial, rfl, d.initial_accuracy,
        FloatFactorValidity.validFactor_posDef n initial d.initial_accuracy.1, d.initial_positive⟩
  | succ t ih =>
      have hth : t < horizon := by omega
      obtain ⟨current, hrun, ha, _, href⟩ := ih (by omega)
      let input := atDimensions n m (inputs t)
      have hin : input = inputs t := atDimensions_eq n m (inputs t)
        (d.dimensions t hth).1 (d.dimensions t hth).2
      let p := d.profile t hth current hrun
      let env := d.environment t hth
      obtain ⟨output, hs, ho⟩ := FloatFullFilter.step_accuracy input current _ p env (eP t) (eX t)
        (by rw [hin]; exact d.input_valid t hth) ha.1 href.posSemidef
        (FloatFullFilter.factorAccuracy_stateWithin ha)
      have hout : nativeRun inputs initial (t + 1) = .ok output := by
        have hrun' : Kalman.Implementation.SquareRootFilter.run inputs initial t = .ok current :=
          hrun
        rw [nativeRun, Kalman.Implementation.SquareRootFilter.run, hrun']
        simpa only [bind, Except.bind, hin] using hs
      have hm := factorAccuracy_mono ho (d.covariance_cap t hth current hrun)
        (d.mean_cap t hth current hrun)
      have hp := RealRecursion.step_posDef .joseph (model input) (exactRun n m inputs reference t)
        (vector m (inputs t).measurement) href.posSemidef
        (d.process_positive t hth)
        (Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ _ env.floor_positive env.noise_lower)
      exact ⟨output, hout, hm, FloatFactorValidity.validFactor_posDef n output hm.1, hp⟩

/-- The whole pipeline starts from the original decoded covariance. The
initializer supplies initial accuracy; only its explicit radius must fit the
chosen initial budget. The reference is never changed to a rounded factor Gram. -/
theorem initialized_horizon_accuracy (initializer : Input.Model) (original : Input.State)
    (lower : Array Float) (M δ D : ℝ)
    (p
      : Kalman.Proofs.CholeskyProfiles.FactorProfile initializer.stateDimension
          original.covariance lower M δ D)
    (hinput : initializer.validate = .ok ())
    (hstate : original.validate initializer.stateDimension = .ok ())
    (hsym : Input.symmetric initializer.stateDimension original.covariance = true)
    (m horizon : Nat) (inputs : Nat → Input.Model) (eP eX : Nat → ℝ)
    (d
      : HorizonOperands initializer.stateDimension m horizon inputs ⟨original.mean, lower⟩
          (state initializer.stateDimension original))
    (hP
      : Kalman.Proofs.CholeskyProfiles.diagonalRadius initializer.stateDimension M
          + Kalman.Proofs.CholeskyProfiles.divisionRadius initializer.stateDimension M δ D
        ≤ eP 0)
    (hX : 0 ≤ eX 0)
    (hcov
      : ∀ t (ht : t < horizon) current
          (hrun : nativeRun inputs ⟨original.mean, lower⟩ t = .ok current),
          Kalman.Proofs.FilterComposition.stepCovarianceRadius
            (d.profile t ht current hrun) (d.environment t ht) (eP t)
          ≤ eP (t + 1))
    (hmean
      : ∀ t (ht : t < horizon) current
          (hrun : nativeRun inputs ⟨original.mean, lower⟩ t = .ok current),
          Kalman.Proofs.FilterComposition.stepMeanRadius
            (d.profile t ht current hrun) (d.environment t ht) (eP t) (eX t)
          ≤ eX (t + 1))
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            Except.bind
                (Kalman.Implementation.SquareRootFilter.fromCovariance initializer
                  original)
                (fun initial => nativeRun inputs initial t)
              = .ok output
            ∧ FactorAccuracy (eP t) (eX t) initializer.stateDimension output
                (exactRun initializer.stateDimension m inputs
                  (state initializer.stateDimension original) t)
            ∧ (factorState initializer.stateDimension output).covariance.PosDef
            ∧ (exactRun initializer.stateDimension m inputs
                (state initializer.stateDimension original) t).covariance.PosDef := by
  obtain ⟨hi, ha⟩ := FloatFilterInitialization.fromCovariance_accuracy initializer original lower
    M δ D p hinput hstate hsym
  let domain : HorizonDomain initializer.stateDimension m horizon inputs ⟨original.mean, lower⟩
      (state initializer.stateDimension original) eP eX := {
    toHorizonOperands := d
    initial_accuracy := factorAccuracy_mono ha hP hX
    covariance_cap := hcov
    mean_cap := hmean
  }
  intro t ht
  obtain ⟨output, hrun, haccuracy, hnative, hreal⟩ := finite_horizon_accuracy initializer.stateDimension
    m horizon inputs ⟨original.mean, lower⟩ (state initializer.stateDimension original) eP eX domain t ht
  exact ⟨output, by rw [hi]; exact hrun, haccuracy, hnative, hreal⟩

/-- Proof witness for the result catalogue statement. -/
theorem finiteHorizonAccuracy
    : Kalman.Proofs.FilterComposition.Horizon.FiniteHorizonAccuracy :=
  finite_horizon_accuracy

end Kalman.Proofs.FloatFilterHorizon
