import Kalman.Proofs.FloatConstantVelocityHorizon
import Kalman.Proofs.TrackingContraction
import Kalman.Implementation.Correctness.UniformTrackingAccuracy

namespace Kalman.Proofs.FloatUniformTracking

open Kalman.Definitions Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.ConstantVelocityTracking
  Kalman.Implementation.Correctness.UniformTrackingAccuracy
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Proofs.FloatConstantVelocityTracking
  Kalman.Proofs.FloatConstantVelocityHorizon
  Kalman.Proofs.TrackingContraction
  Flare.Binary64.Value

set_option maxHeartbeats 1200000

/-- Composition with two-step contraction replaces linear accumulation by a
uniform bound. Every native local premise comes from the original domain. -/
theorem horizon_accuracy (measurements : Nat → Float) (initial : Input.State)
    (horizon : Nat) (d : HorizonDomain measurements initial horizon)
    : ∀ t, t ≤ horizon → ∃ output, UniformAccuracy measurements initial t output := by
  classical
  have reached (t : Nat) (ht : t ≤ horizon) : ∃ output,
      Kalman.Implementation.SymmetricJosephFilter.run
        (fun k => trackingInput (measurements k)) initial t = .ok output
      ∧ TrackingState (envelope t) output := by
    obtain ⟨output, run, invariant, _⟩ := weighted_horizon measurements initial horizon d t ht
    exact ⟨output, run, invariant⟩
  let actual (t : Nat) := if ht : t ≤ horizon then Classical.choose (reached t ht) else initial
  have success (t : Nat) (ht : t ≤ horizon) :
      Kalman.Implementation.SymmetricJosephFilter.run
        (fun k => trackingInput (measurements k)) initial t = .ok (actual t)
      ∧ TrackingState (envelope t) (actual t) := by
    simpa only [actual, dite_eq_left ht] using Classical.choose_spec (reached t ht)
  have initialEqual : actual 0 = initial := by
    have h := (success 0 (by omega)).1
    exact (Except.ok.inj h).symm
  have localStep (t : Nat) (ht : t < horizon) :
      WeightedWithin ((2 : ℝ)^(-36 : Int)) (state 2 (actual (t+1))).mean
        (trackingMean (state 2 (actual t)).mean (value (measurements t))) := by
    obtain ⟨output, runStep, _, _, _, error⟩ := step_accuracy (measurements t) (actual t)
      (envelope t) (d.measurements_finite t ht) (d.measurements_bound t ht)
      (success t (by omega)).2 (envelope_bound t (by have := d.horizon_bound; omega))
    have next : Kalman.Implementation.SymmetricJosephFilter.run
        (fun k => trackingInput (measurements k)) initial (t+1) = .ok output := by
      simp [Kalman.Implementation.SymmetricJosephFilter.run,
        (success t (by omega)).1, runStep, bind, Except.bind]
    have same : output = actual (t+1) :=
      Except.ok.inj (next.symm.trans (success (t+1) (by omega)).1)
    simpa only [same] using error
  have uniform := uniform_perturbation
    (fun t => (state 2 (actual t)).mean)
    (fun t => (exactRun 2 1 (fun k => trackingInput (measurements k)) (state 2 initial) t).mean)
    (fun t => value (measurements t)) horizon ((2 : ℝ)^(-36 : Int)) (by positivity)
    (by simp only [initialEqual, exactRun]) localStep
    (fun t _ => ideal_mean measurements initial d.initial_state.covariance_words t)
  intro t ht
  have error := uniform t ht
  have cov := ideal_covariance measurements initial d.initial_state.covariance_words t
  refine ⟨actual t, (success t ht).1, ?_, by positivity, ?_⟩
  · refine ⟨le_rfl, ?_⟩
    intro i j
    change |matrix 2 2 (actual t).covariance i j - _| ≤ 0
    rw [(success t ht).2.covariance_words, FloatConstantVelocityStorage.posterior_decode,
      cov]
    simp
  · intro i
    fin_cases i
    · exact error.2.1.trans (by norm_num)
    · exact error.2.2.trans (by norm_num)

end Kalman.Proofs.FloatUniformTracking
