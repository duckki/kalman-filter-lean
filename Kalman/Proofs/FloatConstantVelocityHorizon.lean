import Kalman.Proofs.FloatConstantVelocityTracking

/-! Actual checked tracking prefixes compared with one independent original-
input Real trajectory. Native domain preservation and mean nonexpansiveness
supply all induction premises; no reached-state success is assumed. -/

namespace Kalman.Proofs.FloatConstantVelocityHorizon

open Matrix Kalman.Definitions
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.ConstantVelocityTracking
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.RecursionSensitivity
  Kalman.Proofs.ConstantVelocityTracking
  Kalman.Proofs.FloatConstantVelocityTracking
  Kalman.Proofs.FloatConstantVelocityStorage
  Flare.Binary64.Value

set_option maxHeartbeats 1000000

/-- Decode a complete original-input source step at explicit dimensions. -/
theorem source_step (z : Float) (s : LinearModel.State 2)
    : CovarianceRecursion.step .joseph (model (atDimensions 2 1 (trackingInput z))) s
        (vector 1 (trackingInput z).measurement)
      = CovarianceRecursion.step .joseph trackingModel s (fun _ => value z) := by
  have measurement : vector 1 (trackingInput z).measurement = fun _ => value z := by
    funext i
    fin_cases i
    rfl
  rw [measurement]
  exact congrArg (fun m : LinearModel.Model 2 1 =>
    CovarianceRecursion.step .joseph m s (fun _ => value z)) (model_decode z)

/-- One source step at any mean in the exact covariance family. -/
theorem ideal_step (z : Float) (reference : LinearModel.State 2)
    (hc : reference.covariance = posteriorCovariance)
    : CovarianceRecursion.step .joseph (model (atDimensions 2 1 (trackingInput z)))
        reference (vector 1 (trackingInput z).measurement)
      = ⟨trackingMean reference.mean (value z), posteriorCovariance⟩ := by
  have eta : reference = ⟨reference.mean, posteriorCovariance⟩ :=
    congrArg (fun cov => (⟨reference.mean, cov⟩ : LinearModel.State 2)) hc
  have next : CovarianceRecursion.step .joseph trackingModel reference (fun _ => value z)
      = ⟨trackingMean reference.mean (value z), posteriorCovariance⟩ := by
    rw [eta]
    exact step_exact _ _
  exact (source_step z reference).trans next

/-- The independent source trajectory also retains the fixed covariance. -/
theorem ideal_covariance (measurements : Nat → Float) (initial : Input.State)
    (hc : initial.covariance = posteriorWords) (t : Nat)
    : (exactRun 2 1 (fun k => trackingInput (measurements k)) (state 2 initial)
        t).covariance
      = posteriorCovariance := by
  induction t with
  | zero =>
      change matrix 2 2 initial.covariance = _
      rw [hc, posterior_decode]
  | succ t ih =>
      exact congrArg LinearModel.State.covariance (ideal_step (measurements t) _ ih)

/-- Explicit ideal mean recurrence follows from the independent full source
trajectory, not from native outputs or a rounded gain substituted into it. -/
theorem ideal_mean (measurements : Nat → Float) (initial : Input.State)
    (hc : initial.covariance = posteriorWords) (t : Nat)
    : (exactRun 2 1 (fun k => trackingInput (measurements k)) (state 2 initial)
        (t + 1)).mean
      = trackingMean
          (exactRun 2 1 (fun k => trackingInput (measurements k)) (state 2 initial)
            t).mean
          (value (measurements t)) := by
  exact congrArg LinearModel.State.mean (ideal_step (measurements t) _
    (ideal_covariance measurements initial hc t))

/-- Strong weighted prefix induction, retaining actual successful execution
and the native operating envelope at every prefix. -/
theorem weighted_horizon (measurements : Nat → Float) (initial : Input.State)
    (horizon : Nat) (d : HorizonDomain measurements initial horizon)
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            Kalman.Implementation.SymmetricJosephFilter.run
                (fun k => trackingInput (measurements k)) initial t
              = .ok output
            ∧ TrackingState (envelope t) output
            ∧ WeightedWithin (t * (2 : ℝ) ^ (-36 : Int)) (state 2 output).mean
                (exactRun 2 1 (fun k => trackingInput (measurements k)) (state 2 initial)
                  t).mean := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨initial, rfl, ?_, ?_⟩
      · simpa only [envelope, Nat.cast_zero, zero_mul, add_zero] using d.initial_state
      · norm_num [WeightedWithin, exactRun]
  | succ t ih =>
      intro ht
      obtain ⟨previous, runPrevious, invariant, error⟩ := ih (by omega)
      obtain ⟨output, runStep, nextInvariant, localError⟩ := domain_preservation
        (measurements t) previous t (by have := d.horizon_bound; omega)
        (d.measurements_finite t (by omega)) (d.measurements_bound t (by omega)) invariant
      have propagated := mean_nonexpansive _ _ (value (measurements t))
        (t*(2 : ℝ)^(-36 : Int)) error
      rw [← ideal_mean measurements initial d.initial_state.covariance_words t] at propagated
      have total := weighted_trans localError propagated
      have radius : (2 : ℝ)^(-36 : Int) + t*(2 : ℝ)^(-36 : Int)
          = ((t+1 : Nat) : ℝ)*(2 : ℝ)^(-36 : Int) := by push_cast; ring
      rw [radius] at total
      refine ⟨output, ?_, nextInvariant, total⟩
      simp [Kalman.Implementation.SymmetricJosephFilter.run, runPrevious, runStep,
        bind, Except.bind]

/-- Complete original-input finite-horizon certificate for the correlated
constant-velocity family, including every checked native prefix. -/
theorem horizon_accuracy (measurements : Nat → Float) (initial : Input.State)
    (horizon : Nat) (d : HorizonDomain measurements initial horizon)
    : ∀ t, t ≤ horizon → ∃ output, HorizonAccuracy measurements initial t output := by
  intro t ht
  obtain ⟨output, run, invariant, error⟩ := weighted_horizon measurements initial horizon d t ht
  have cov : (state 2 output).covariance =
      (exactRun 2 1 (fun k => trackingInput (measurements k)) (state 2 initial) t).covariance := by
    change matrix 2 2 output.covariance = _
    rw [invariant.covariance_words, posterior_decode,
      ideal_covariance measurements initial d.initial_state.covariance_words t]
  refine ⟨output, run, invariant, ?_, by positivity, ?_⟩
  · refine ⟨le_rfl, ?_⟩
    intro i j
    simp [cov]
  · intro i
    fin_cases i
    · exact error.2.1.trans (by have := error.1; nlinarith)
    · exact error.2.2.trans (by ring_nf; rfl)

/-- Every certified native prefix has strictly positive stored covariance. -/
theorem horizon_posDef (measurements : Nat → Float) (initial : Input.State)
    (t : Nat) (output : Input.State) (h : HorizonAccuracy measurements initial t output)
    : (matrix 2 2 output.covariance).PosDef :=
  state_posDef _ output h.2.1

/-- The accumulated componentwise mean radius is at most `2^-14` over the
whole allowed horizon; the sharper prefix-dependent bound remains public. -/
theorem horizon_radius_bound (horizon t : Nat) (hh : horizon ≤ 1048576) (ht : t ≤ horizon)
    : (4 : ℝ) * t * (2 : ℝ) ^ (-36 : Int) ≤ (2 : ℝ) ^ (-14 : Int) := by
  have h : (t : ℝ) ≤ 1048576 := by exact_mod_cast (ht.trans hh)
  norm_num
  linarith

/-- The full permitted horizon has an inhabited original-input domain. The
main theorem also allows arbitrary finite bounded measurement sequences. -/
theorem horizon_domain_nonempty
    : ∃ initial, HorizonDomain (fun _ => 0.0) initial 1048576 := by
  obtain ⟨initial, stateDomain, _⟩ := domain_nonempty
  refine ⟨initial, le_rfl, stateDomain, ?_, ?_⟩
  · intro _ _
    decide +kernel
  · intro _ _
    norm_num [Flare.Binary64.Arithmetic.zero_value]

end Kalman.Proofs.FloatConstantVelocityHorizon
