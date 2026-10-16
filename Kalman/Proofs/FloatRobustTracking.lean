import Kalman.Implementation.Correctness.RobustTracking
import Kalman.Proofs.FloatCorrelatedInitialization

/-! Scalar original-word parameter bounds discharge the entire general model
domain, including validation and positivity, for every native prefix. -/

namespace Kalman.Proofs.FloatRobustTracking

open Matrix Kalman.Definitions Kalman.Implementation.PositionVelocityModel
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.RobustTracking
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.TrackingCovarianceTube
  Flare.Binary64.Value

set_option maxHeartbeats 1600000

/-- No intermediate native success is assumed by the scalar parameter API. -/
theorem input_domain (p : Parameters) (z : Float) (d : ParameterDomain p)
    (hz : z.isFinite = true) (hb : |value z| ≤ (2 : ℝ) ^ (-24 : Int))
    : Kalman.Implementation.Correctness.CorrelatedTracking.ModelDomain (input p z)
        p.timeStep := by
  have oneFinite : (1.0 : Float).isFinite = true := by decide +kernel
  have zeroNe : ((0.0 : Float) != 0.0) = false := by decide +kernel
  have qsym : Input.symmetric 2 #[p.positionProcessVariance, 0.0, 0.0, p.velocityProcessVariance] = true := by
    simp [Input.symmetric, Std.Legacy.Range.forIn_eq_forIn_range', List.range', pure, Id.run, bind, zeroNe]
  have rsym : Input.symmetric 1 #[p.measurementVariance] = true := by
    simp [Input.symmetric, Std.Legacy.Range.forIn_eq_forIn_range', List.range', pure, Id.run, bind]
  have valid : (input p z).validate = .ok () := by
    simp [Input.Model.validate, input, oneFinite, d.time_finite, d.position_process_finite,
      d.velocity_process_finite, d.measurement_finite, hz, qsym, rsym, pure, Except.pure]
  have timeBound : |value p.timeStep| ≤ 1 := by
    have h := abs_sub_le (value p.timeStep) (1/4 : ℝ) 0
    norm_num only [sub_zero, show |(1/4 : ℝ)| = 1/4 by norm_num] at h
    exact (h.trans (add_le_add d.time_close (le_refl (1/4 : ℝ)))).trans (by norm_num [parameterRadius])
  have q0 : 0 ≤ value p.positionProcessVariance := by
    have h := (abs_le.mp d.position_process_close).1
    norm_num [parameterRadius] at h
    linarith
  have q1 : 0 ≤ value p.velocityProcessVariance := by
    have h := (abs_le.mp d.velocity_process_close).1
    norm_num [parameterRadius] at h
    linarith
  have qdecode : matrix 2 2 (input p z).processNoise = diagonal
      ![value p.positionProcessVariance, value p.velocityProcessVariance] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [input, matrix, Flare.Matrix.Value.matrix, Matrix.diagonal_apply,
        Flare.Binary64.Arithmetic.zero_value]
  refine ⟨rfl, rfl, valid, rfl, d.time_finite, timeBound, rfl, ?_, ?_, ?_,
    rfl, rfl, ?_, ?_, ?_, ?_, d.measurement_lower, hb⟩
  · simp [input, d.position_process_finite, d.velocity_process_finite]
  · simp [input, d.measurement_finite]
  · simp [input, hz]
  · rw [qdecode]
    apply PosSemidef.diagonal
    intro i
    fin_cases i
    · exact q0
    · exact q1
  · refine ⟨by norm_num [parameterRadius], ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [input, matrix, Flare.Matrix.Value.matrix, trackingModel,
        Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value, parameterRadius]
    have h := d.time_close
    norm_num [parameterRadius] at h
    exact h
  · refine ⟨by norm_num [parameterRadius], ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [input, matrix, Flare.Matrix.Value.matrix, trackingModel,
        Flare.Binary64.Arithmetic.zero_value, parameterRadius]
    · have h := d.position_process_close
      norm_num [parameterRadius] at h
      exact h
    · have h := d.velocity_process_close
      norm_num [parameterRadius] at h
      exact h
  · refine ⟨by norm_num [parameterRadius], ?_⟩
    intro i j
    fin_cases i
    fin_cases j
    change |value p.measurementVariance-1| ≤ parameterRadius
    rw [abs_of_nonneg (by linarith [d.measurement_lower])]
    linarith [d.measurement_upper]

/-- Finite varying-parameter native traces retain the nonstationary covariance
neighborhood and its positive floor under original scalar input conditions. -/
theorem horizon_preservation (parameters : Nat → Parameters) (measurements : Nat → Float)
    (initial : Input.State) (horizon : Nat)
    (d : HorizonDomain parameters measurements initial horizon)
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            Kalman.Implementation.Correctness.CorrelatedTracking.HorizonPreserved
              (fun k => input (parameters k) (measurements k)) initial t output := by
  apply FloatCorrelatedTracking.horizon_preservation _ (fun k => (parameters k).timeStep)
    initial horizon
  exact ⟨d.horizon_bound, d.initial_state, fun t ht => input_domain _ _
    (d.parameters_bound t ht) (d.measurements_finite t ht) (d.measurements_bound t ht)⟩

/-- The scalar box contains a nonnominal original time increment. -/
theorem parameter_domain_nonempty
    : ∃ p, ParameterDomain p ∧ value p.timeStep ≠ (1 : ℝ) / 4 := by
  let p : Parameters := ⟨0.250000476837158203125, 0.3125, 0.125, 1.0⟩
  have ht : value (0.250000476837158203125 : Float) = (1 : ℝ)/4 + parameterRadius := by
    change (4503608217305088 : ℝ)*(2 : ℝ)^(-54 : Int) = _
    norm_num [parameterRadius]
  have hq : value (0.3125 : Float) = (5 : ℝ)/16 := by
    change (5629499534213120 : ℝ)*(2 : ℝ)^(-54 : Int) = _
    norm_num
  have hv : value (0.125 : Float) = (1 : ℝ)/8 := by
    change (4503599627370496 : ℝ)*(2 : ℝ)^(-55 : Int) = _
    norm_num
  refine ⟨p, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    norm_num [p, ht, hq, hv, parameterRadius, Flare.Binary64.Arithmetic.one_value]

end Kalman.Proofs.FloatRobustTracking
