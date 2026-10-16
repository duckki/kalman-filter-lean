import Kalman.Proofs.FloatJosephPrediction
import Kalman.Proofs.FloatObservableFilter

/-! A complete checked native direct-Joseph step: validation, dense prediction,
computed gain, mean/covariance correction, and local exact-step error. -/

namespace Kalman.Proofs.FloatJosephFilter

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy (ModelDomain)
open Kalman.Definitions.Theorems.RecursionSensitivity

set_option maxHeartbeats 1200000

/-! ----------------------------------------------------------------------
## Checked native step and invariant preservation
-------------------------------------------------------------------------- -/

/-- Finite, correctly shaped dense storage passes the actual state guards. -/
theorem state_validate (current : Input.State) (s : StateInvariant current)
    : current.validate 2 = .ok () := by
  have shape : (current.mean.size == 2 && current.covariance.size == 2 * 2) = true := by
    simp [s.mean_size, s.covariance_size]
  have finite : (current.mean.all Float.isFinite && current.covariance.all Float.isFinite) = true := by
    rw [s.mean_finite, s.covariance_finite]
    rfl
  simp [Input.State.validate, shape, finite, pure, Except.pure]

/-- A checked native step derives all stages, preserves the dense invariant,
and has local covariance/mean errors at most 2^-32 against an exact full step
of the same incoming stored state. Prediction rounding is charged through
the perturbed gain, not discarded. -/
theorem step_accuracy (input : Input.Model) (current : Input.State)
    (p : ModelDomain input) (s : StateInvariant current)
    : ∃ output, StepAccuracy input current output := by
  obtain ⟨prior, hpred, ep, d⟩ := FloatJosephPrediction.prediction_accuracy input current p s
  obtain ⟨output, hupdate, so, ec⟩ := FloatJosephUpdate.update_accuracy input prior d
  let m : LinearModel.Model 2 2 := model (atDimensions 2 2 input)
  let ideal : LinearModel.State 2 := CovarianceRecursion.predict m (state 2 current)
  have hb := FloatJosephPrediction.exact_prediction_bounds input current p s
  change ideal.covariance = diagonal (fun i => ideal.covariance i i)
    ∧ (∀ i, 1 ≤ ideal.covariance i i) ∧ (∀ i, |ideal.mean i| ≤ 9 / 8) at hb
  have da : (state 2 prior).covariance = diagonal (fun i => (state 2 prior).covariance i i) :=
    FloatDiagonalStorage.matrix_diagonal 2 prior.covariance d.gain.prior_diagonal
  have hR : m.measurementNoise = diagonal (fun i => m.measurementNoise i i) :=
    FloatDiagonalStorage.matrix_diagonal 2 input.measurementNoise p.noise.diagonal
  have er := RealObservableCorrection.update_sensitivity m (state 2 prior) ideal
    (vector 2 input.measurement) (fun i => m.measurementNoise i i)
    ((2 : ℝ)^(-42 : Int)) ((2 : ℝ)^(-46 : Int)) p.observation_identity hR da hb.1
    d.gain.prior_floor
    (fun i => (by norm_num : (15 : ℝ) / 16 ≤ 1).trans (hb.2.1 i))
    (fun i => p.noise.covariance.diagonal_lower i.val i.isLt)
    (fun i => p.noise.diagonal_cap i.val i.isLt) hb.2.2
    (fun i => p.measurement_bound i.val i.isLt) ep
  have joined := FloatFullFilter.stateWithin_trans ec er
  have localAccuracy : StateWithin ((2 : ℝ)^(-32 : Int)) ((2 : ℝ)^(-32 : Int)) (state 2 output)
      (CovarianceRecursion.step .joseph m (state 2 current) (vector 2 input.measurement)) := by
    refine ⟨⟨by positivity, fun i j => (joined.1.2 i j).trans ?_⟩,
      by positivity, fun i => (joined.2.2 i).trans ?_⟩ <;> norm_num
  have hv := FloatObservableFilter.input_validate input p
  have hs := state_validate current s
  refine ⟨output, ?_, so, localAccuracy⟩
  simp [Kalman.Implementation.CovarianceFilter.step, hv, p.state_dimension, hs,
    hpred, hupdate, bind, Except.bind]

end Kalman.Proofs.FloatJosephFilter
