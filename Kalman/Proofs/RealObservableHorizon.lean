import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.FilterComposition
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Proofs.FloatObservableInitialization

/-! The independently propagated matrix Real trace uses exactly the native
input words, with fixed dimensions justified by the original model domain. -/

namespace Kalman.Proofs.RealObservableHorizon

open Matrix
open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.DiagonalStages.Horizon

/-- The full stored model is the exact full-observation diagonal specification. -/
theorem model_diagonal (input : Input.Model)
    (d
      : Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.ModelDomain
          input)
    : model (atDimensions 2 2 input)
      = DiagonalObservation.model (transition input) (processVariance input)
          (measurementVariance input) := by
  have hF := FloatDiagonalStorage.matrix_diagonal 2 input.transition d.transition_diagonal
  have hQ := FloatDiagonalStorage.matrix_diagonal 2 input.processNoise d.process_noise.diagonal
  have hR := FloatDiagonalStorage.matrix_diagonal 2 input.measurementNoise d.noise.diagonal
  change (⟨matrix 2 2 input.transition, matrix 2 2 input.observation,
    matrix 2 2 input.processNoise, matrix 2 2 input.measurementNoise⟩ : LinearModel.Model 2 2)
      = ⟨diagonal (transition input), 1, diagonal (processVariance input), diagonal (measurementVariance input)⟩
  rw [hF, d.observation_identity, hQ, hR]
  rfl

/-- Original native bounds imply the exact model's operating conditions. -/
theorem model_domain (input : Input.Model)
    (d
      : Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.ModelDomain
          input)
    : Kalman.Definitions.Theorems.RecursionSensitivity.DiagonalModelDomain
        (transition input) (processVariance input) (measurementVariance input)
        (vector 2 input.measurement) :=
  ⟨
    fun i => d.transition_bound i.val i.val i.isLt i.isLt,
    fun i => d.process_noise.covariance.diagonal_lower i.val i.isLt,
    fun i => d.process_noise.diagonal_cap i.val i.isLt,
    fun i => d.noise.covariance.diagonal_lower i.val i.isLt,
    fun i => d.noise.diagonal_cap i.val i.isLt,
    fun i => d.measurement_bound i.val i.isLt
  ⟩

/-- Independent ideal invariance follows from original initialization and
original time-varying models, without referring to a native factor trace. -/
theorem run_invariant (initializationInput : Input.Model) (initial : Input.State)
    (inputs : Nat → Input.Model) (horizon : Nat)
    (d : HorizonDomain initializationInput initial inputs horizon)
    : ∀ t,
        t ≤ horizon
        → Kalman.Definitions.Theorems.RecursionSensitivity.DiagonalStateInvariant
            (exactRun 2 2 inputs (state 2 initial) t) := by
  intro t ht
  induction t with
  | zero =>
      exact FloatObservableInitialization.exact_initial_invariant initial d.initial_state
  | succ t ih =>
      rw [exactRun, model_diagonal (inputs t) (d.models t (by omega))]
      exact (RealObservableInvariant.step_invariant .joseph _ _ _ _ _
              (model_domain (inputs t) (d.models t (by omega))) (ih (by omega))).1

end Kalman.Proofs.RealObservableHorizon
