import Kalman.Proofs.FloatCorrelatedTracking

/-! Concrete original-input witnesses and nominal-model instantiation of the
nonstationary covariance-neighborhood certificate. -/

namespace Kalman.Proofs.FloatCorrelatedInitialization

open Matrix Kalman.Definitions
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.CorrelatedTracking
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.TrackingCovarianceTube
  Kalman.Definitions.Theorems.RecursionSensitivity
  Kalman.Proofs.TrackingCovarianceTube
  Flare.Binary64.Value

set_option maxHeartbeats 1200000

/-- The nominal stored model is a special case of the original parameter box. -/
theorem nominal_model_domain (z : Float) (hz : z.isFinite = true)
    (hb : |value z| ≤ (2 : ℝ) ^ (-24 : Int))
    : ModelDomain
        (Kalman.Implementation.Correctness.ConstantVelocityTracking.trackingInput z)
        0.25 := by
  let input := Kalman.Implementation.Correctness.ConstantVelocityTracking.trackingInput z
  have decode := FloatConstantVelocityStorage.model_decode z
  have f := congrArg LinearModel.Model.transition decode
  have q := congrArg LinearModel.Model.processNoise decode
  have r := congrArg LinearModel.Model.measurementNoise decode
  change matrix 2 2 input.transition = trackingModel.transition at f
  change matrix 2 2 input.processNoise = trackingModel.processNoise at q
  change matrix 1 1 input.measurementNoise = trackingModel.measurementNoise at r
  have eqWithin {n m : Nat} (a b : Matrix (Fin n) (Fin m) ℝ) (h : a = b)
      : EntrywiseWithin parameterRadius a b := by
    rw [h]
    exact ⟨by norm_num [parameterRadius], by intro i j; simp; norm_num [parameterRadius]⟩
  refine ⟨
    rfl,
    rfl,
    FloatConstantVelocityStorage.input_valid z hz,
    rfl,
    by decide +kernel,
    ?_,
    rfl,
    ?_,
    ?_,
    ?_,
    rfl,
    rfl,
    ?_,
    eqWithin _ _ f,
    eqWithin _ _ q,
    eqWithin _ _ r,
    ?_,
    hb
  ⟩
  · change |(4503599627370496 : ℝ)*(2 : ℝ)^(-54 : Int)| ≤ 1
    norm_num
  · dsimp only [Kalman.Implementation.Correctness.ConstantVelocityTracking.trackingInput]
    decide +kernel
  · dsimp only [Kalman.Implementation.Correctness.ConstantVelocityTracking.trackingInput]
    decide +kernel
  · change (#[z] : Array Float).all Float.isFinite = true
    simp [hz]

  · rw [q]
    exact FloatConstantVelocityStorage.process_psd
  · change 1 ≤ value (1.0 : Float)
    norm_num [Flare.Binary64.Arithmetic.one_value]

/-- A stored covariance different from the nominal fixed point. -/
def transientCovariance : Array Float := #[0.500244140625, 0.25, 0.25, 1.000244140625]

theorem transient_decode
    : matrix 2 2 transientCovariance = posteriorCovariance + radius • 1 := by
  have a : value (0.500244140625 : Float) = (2049 : ℝ)/4096 := by
    change (4505798650626048 : ℝ)*(2 : ℝ)^(-53 : Int) = _
    norm_num
  have c : value (1.000244140625 : Float) = (4097 : ℝ)/4096 := by
    change (4504699138998272 : ℝ)*(2 : ℝ)^(-52 : Int) = _
    norm_num
  have b : value (0.25 : Float) = (1 : ℝ)/4 := by
    change (4503599627370496 : ℝ)*(2 : ℝ)^(-54 : Int) = _
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transientCovariance, matrix, Flare.Matrix.Value.matrix,
      posteriorCovariance, radius, Matrix.one_apply, a, b, c]

theorem shifted_tube : Tube (posteriorCovariance + radius • 1) := by
  constructor
  · have h := (weight_psd.add (PosSemidef.one (n := Fin 2) (R := ℝ))).smul
      (by norm_num [radius] : (0 : ℝ) ≤ radius)
    convert h using 1
    module
  · have h := weight_lower.smul (by norm_num [radius] : (0 : ℝ) ≤ radius)
    convert h using 1
    module

/-- The native original-input domain contains a nonstationary covariance. -/
theorem domain_nonempty
    : ∃ s,
        StateDomain (1 / 8) s
        ∧ s.covariance
          ≠ Kalman.Implementation.Correctness.ConstantVelocityTracking.posteriorWords := by
  let s : Input.State := ⟨#[0.0, 0.0], transientCovariance⟩
  refine ⟨s, ⟨rfl, rfl, by decide +kernel, by decide +kernel, ?_, ?_⟩, ?_⟩
  · rw [transient_decode]
    exact shifted_tube
  · norm_num [WeightedWithin, s, state, vector, Flare.Binary64.Arithmetic.zero_value]
  · change transientCovariance ≠ _
    decide +kernel

end Kalman.Proofs.FloatCorrelatedInitialization
