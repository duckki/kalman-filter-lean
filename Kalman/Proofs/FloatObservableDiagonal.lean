import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FloatObservableInnovation
import Kalman.Proofs.FloatQRDiagonal

/-! Diagonal native prediction/innovation and their exact Real covariances.
The numerical input domains derive success independently; adding decoded
diagonality of the incoming factor supplies the structural invariant needed
by RealObservableSensitivity. Full correction and checked steps are composed
in FloatObservablePosterior and FloatObservableFilter. -/

namespace Kalman.Proofs.FloatObservableDiagonal

open Matrix
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.DiagonalStages.Prediction
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Flare.Binary64.Value

private theorem bind_success {α β : Type} (p : Except Input.Error α)
    (f : α → Except Input.Error β) (b : β) (h : (p >>= f) = .ok b)
    : ∃ a, p = .ok a ∧ f a = .ok b := by
  cases p with
  | error e => simp only [bind, Except.bind, reduceCtorEq] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem noise_finite (a l : Array Float) (d : NoiseDomain a)
    (h : cholesky 2 a = .ok l)
    : l.all Float.isFinite = true := by
  obtain ⟨l', _, hl, hf, _⟩ := FloatCholeskyDomain.cholesky_accuracy a d.covariance
  have he : l' = l := Except.ok.inj (hl.symm.trans h)
  exact he ▸ hf

/-- Full observation is decoded diagonal even when zero words have different
signs. The premise is the exact interpretation of the original native H. -/
theorem observation_diagonal (input : Input.Model) (o : ObservationInputs input)
    : DecodedDiagonal 2 input.observation := by
  intro i j hi hj hij
  change matrix 2 2 input.observation ⟨i, hi⟩ ⟨j, hj⟩ = 0
  rw [o.observation_identity]
  exact Matrix.one_apply_ne (fun h => hij (congrArg Fin.val h))

/-- Actual native prediction preserves a diagonal working factor. Success is
a premise of this structural statement; prediction_innovation_diagonal derives
it from the same original local inputs and includes the numerical guarantees. -/
theorem prediction_diagonal (input : Input.Model) (initial output : Input.FactorState)
    (d : TwoStateDomain input initial) (di : DecodedDiagonal 2 initial.lower)
    (h
      : Kalman.Implementation.SquareRootFilter.predictUnchecked input initial
        = .ok output)
    : DecodedDiagonal 2 output.lower := by
  unfold Kalman.Implementation.SquareRootFilter.predictUnchecked at h
  simp only [d.state_dimension] at h
  obtain ⟨tq, hq, h⟩ := bind_success _ _ _ h
  obtain ⟨fl, hf, h⟩ := bind_success _ _ _ h
  obtain ⟨l, hl, h⟩ := bind_success _ _ _ h
  obtain ⟨mean, _, h⟩ := bind_success _ _ _ h
  have he : l = output.lower := congrArg Input.FactorState.lower (Except.ok.inj h)
  rw [← he]
  obtain ⟨fl', _, hfl, _, hff, _⟩ := FloatObservablePrediction.transition_product input initial d
  have eq : fl' = fl := Except.ok.inj (hfl.symm.trans hf)
  subst fl'
  exact FloatQRDiagonal.gramFactor_diagonal_two fl tq l hff (noise_finite _ _ d.noise hq)
    (FloatDiagonalStorage.multiply_diagonal_two _ _ _ d.transition_finite d.factor_finite
      d.transition_diagonal di hf)
    (FloatDiagonalStorage.cholesky_diagonal_two _ d.noise.covariance d.noise.diagonal _ hq) hl

/-- The original-R noise factor, rounded HL and retained innovation QR preserve
decoded diagonality when the incoming prior factor is diagonal. -/
theorem innovation_diagonal (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (di : DecodedDiagonal 2 prior.lower)
    (tr hl s : Array Float) (hr : cholesky 2 input.measurementNoise = .ok tr)
    (hh : multiply 2 2 2 input.observation prior.lower = .ok hl)
    (hs : gramFactor 2 4 (fromCols 2 2 2 tr hl) = .ok s)
    : DecodedDiagonal 2 s := by
  obtain ⟨hl', _, hhl, _, hlf, _⟩ := FloatObservableInnovation.observation_product input prior d
  have eq : hl' = hl := Except.ok.inj (hhl.symm.trans hh)
  subst hl'
  exact FloatQRDiagonal.gramFactor_diagonal_two tr hl s
    (noise_finite _ _ d.observation.noise hr) hlf
    (FloatDiagonalStorage.cholesky_diagonal_two _ d.observation.noise.covariance
      d.observation.noise.diagonal _ hr)
    (FloatDiagonalStorage.multiply_diagonal_two _ _ _ d.observation.observation_finite
      d.factor_finite (observation_diagonal input d.observation) di hh) hs

/-- Input-derived prediction accuracy and the reached innovation domain now
include an exactly diagonal stored factor and exactly diagonal Real covariance.
No native execution, arithmetic profile or error is assumed. -/
theorem prediction_innovation_diagonal (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial) (o : ObservationInputs input)
    (di : DecodedDiagonal 2 initial.lower)
    : ∃ prior,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok prior
        ∧ FactorAccuracy ((2 : ℝ) ^ (-24 : Int)) ((2 : ℝ) ^ (-46 : Int))
            input.stateDimension prior
            (CovarianceRecursion.predict (model input)
              (factorState input.stateDimension initial))
        ∧ InnovationDomain input prior
        ∧ DecodedDiagonal 2 prior.lower
        ∧ FactorRecursion.gram (matrix 2 2 prior.lower)
          = diagonal (fun i => (matrix 2 2 prior.lower i i) ^ 2) := by
  obtain ⟨prior, hr, ha, domain⟩ :=
    FloatObservablePrediction.prediction_innovation_domain input initial d o
  have hd := prediction_diagonal input initial prior d di hr
  exact ⟨prior, hr, ha, domain, hd, FloatDiagonalStorage.gram_diagonal 2 prior.lower hd⟩

/-- The full-observation innovation stage succeeds from a diagonal stored prior,
with its proved error/floor and an exactly diagonal Real Gram. The reference is
original decoded R plus the incoming stored prior covariance. -/
theorem innovation_accuracy_diagonal (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (di : DecodedDiagonal 2 prior.lower)
    : ∃ tr hl s,
        cholesky 2 input.measurementNoise = .ok tr
        ∧ multiply 2 2 2 input.observation prior.lower = .ok hl
        ∧ gramFactor 2 4 (fromCols 2 2 2 tr hl) = .ok s
        ∧ DecodedDiagonal 2 s
        ∧ FactorRecursion.gram (matrix 2 2 s) = diagonal (fun i => (matrix 2 2 s i i) ^ 2)
        ∧ (FactorRecursion.gram (matrix 2 2 s)).PosDef
        ∧ (FactorRecursion.gram (matrix 2 2 s) - (29 / 16 : ℝ) • 1).PosSemidef
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-23 : Int)) (FactorRecursion.gram (matrix 2 2 s))
            (FactorRecursion.gram (matrix 2 2 prior.lower)
              + matrix 2 2 input.measurementNoise) := by
  obtain ⟨tr, hl, s, hr, hh, hs, _, _, _, hpd, hfloor, _, _, he⟩ :=
    FloatObservableInnovation.factor_accuracy input prior d
  have hd := innovation_diagonal input prior d di tr hl s hr hh hs
  exact ⟨tr, hl, s, hr, hh, hs, hd, FloatDiagonalStorage.gram_diagonal 2 s hd, hpd, hfloor, he⟩

end Kalman.Proofs.FloatObservableDiagonal
