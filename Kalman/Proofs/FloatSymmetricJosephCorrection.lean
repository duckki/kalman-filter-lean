import Kalman.Proofs.FloatJosephPositionCorrection
import Kalman.Implementation.Correctness.SymmetricJosephCorrection
import Flare.Matrix.MatrixFormation

/-! Copying the lower triangle preserves the local comparison to the exact
Joseph covariance. The resulting stored matrix has a positive spectral floor;
the argument does not infer positivity merely from a symmetry repair. -/

namespace Kalman.Proofs.FloatSymmetricJosephCorrection

open Matrix Kalman.Definitions
  Kalman.Implementation.Correctness.InputInterpretation
  Kalman.Implementation.Correctness.JosephPositionCorrection
  Kalman.Definitions.Theorems.RecursionSensitivity
  Kalman.Implementation.SymmetricJosephFilter

set_option maxHeartbeats 800000

/-- A reusable dimension-independent storage lemma. Against a Hermitian exact
reference, copying the lower triangle costs no additional entrywise error and
leaves the mean words unchanged. -/
theorem mirror_accuracy {n : Nat} (actual : Input.State) (reference : LinearModel.State n)
    (eP eX : ℝ) (hs : actual.covariance.size = n * n)
    (hf : actual.covariance.all Float.isFinite = true)
    (hH : reference.covariance.IsHermitian)
    (he : StateWithin eP eX (state n actual) reference)
    : (mirrorCovariance n actual).covariance.size = n * n
      ∧ (mirrorCovariance n actual).covariance.all Float.isFinite = true
      ∧ (matrix n n (mirrorCovariance n actual).covariance).IsHermitian
      ∧ StateWithin eP eX (state n (mirrorCovariance n actual)) reference := by
  obtain ⟨size, finite, hermitian, error, _⟩ :=
    Flare.Matrix.MatrixFormation.mirrorLower_accuracy n actual.covariance
      reference.covariance eP hs hf hH he.1.1 he.1.2
  exact ⟨size, finite, hermitian, ⟨⟨he.1.1, error⟩, he.2⟩⟩

/-- On the original-input position-correction domain the repaired stored
covariance, not just its symmetric part, has floor `1/8`. -/
theorem update_accuracy (input : Input.Model) (prior : Input.State)
    (d : Domain input prior)
    : ∃ output,
        Kalman.Implementation.Correctness.SymmetricJosephCorrection.CorrectionAccuracy
          input prior output := by
  obtain ⟨raw, run, ms, cs, mf, cf, error, _, _⟩ :=
    FloatJosephPositionCorrection.update_accuracy input prior d
  let m : LinearModel.Model 2 1 := model (atDimensions 2 1 input)
  let p : LinearModel.State 2 := state 2 prior
  let reference := CovarianceRecursion.update .joseph m p (vector 1 input.measurement)
  have observation := FloatJosephPositionGain.observation_decode input prior d
  have exactFloor := JosephPositionCorrection.covariance_floor m p d.prior_floor
    observation d.noise_lower (CovarianceRecursion.gain m p)
  have referencePSD : reference.covariance.PosSemidef := by
    have extra := (PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : (0 : ℝ) ≤ 1/4)
    convert exactFloor.add extra using 1
    change CovarianceRecursion.joseph m p (CovarianceRecursion.gain m p) = _
    module
  obtain ⟨size, finite, hermitian, accuracy⟩ :=
    mirror_accuracy raw reference _ _ cs cf referencePSD.isHermitian error
  have lower := Flare.Analysis.EntrywiseError.lower_bound_of_error _ _ (1/4)
    ((2 : ℝ)^(-28 : Int)) exactFloor hermitian accuracy.1
  have floor : (matrix 2 2 (mirrorCovariance 2 raw).covariance - (1/8 : ℝ) • 1).PosSemidef := by
    have extra := (PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : (0 : ℝ) ≤ 1/4 - 2*(2 : ℝ)^(-28 : Int) - 1/8)
    convert lower.add extra using 1
    norm_num
    module
  refine ⟨mirrorCovariance 2 raw, ?_, ms, size, mf, finite, accuracy, hermitian, floor⟩
  simp [update, run, d.state_dimension, bind, Except.bind, pure, Except.pure]

/-- In particular, native stored covariance is strictly positive definite. -/
theorem output_posDef (input : Input.Model) (prior output : Input.State)
    (h
      : Kalman.Implementation.Correctness.SymmetricJosephCorrection.CorrectionAccuracy
          input prior output)
    : (matrix 2 2 output.covariance).PosDef :=
  Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ (1 / 8) (by norm_num)
    h.2.2.2.2.2.2.2

end Kalman.Proofs.FloatSymmetricJosephCorrection
