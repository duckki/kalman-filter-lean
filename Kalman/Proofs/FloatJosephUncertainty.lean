import Kalman.Proofs.FloatJosephHorizon
import Kalman.Proofs.UncertaintyBounds
import Kalman.Implementation.Correctness.JosephUncertainty

/-! Roundoff-aware uncertainty transfer for the completed Joseph domain. -/

namespace Kalman.Proofs.FloatJosephUncertainty

open Matrix Kalman.Definitions Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
open Kalman.Implementation.Correctness.JosephUncertainty
open Flare.Binary64.Value

/-- The binary64 padding is exactly 2^-29. -/
theorem padding_value
    : value (0.00000000186264514923095703125 : Float) = (2 : ℝ) ^ (-29 : Int) := by
  change (4503599627370496 : ℝ) * (2 : ℝ) ^ (-81 : Int) = _
  norm_num

/-- The spare half of the padding dominates the addition's 2^-51 error. -/
theorem inflate_variance (variance : Float) (reference : ℝ)
    (hf : variance.isFinite = true) (hl : 0 ≤ value variance)
    (hu : value variance ≤ 13 / 8)
    (he : |value variance - reference| ≤ (2 : ℝ) ^ (-30 : Int))
    : InflatedVariance variance reference := by
  have hr := Flare.Binary64.Arithmetic.add_error variance
    0.00000000186264514923095703125 1 hf (by decide +kernel)
    (by norm_num) (by norm_num) (by
      rw [padding_value, abs_of_nonneg (by positivity)]
      norm_num
      linarith)
  refine ⟨variance + 0.00000000186264514923095703125, ?_, hr.1, ?_, ?_⟩
  · exact FloatDenseError.finite_ok _ hr.1
  · have h := (abs_le.mp hr.2).1
    rw [padding_value] at h
    have he' := (abs_le.mp he).1
    norm_num at h he' ⊢
    linarith
  · have h := (abs_le.mp hr.2).2
    rw [padding_value] at h
    norm_num at h ⊢
    linarith

theorem horizon_overbound : HorizonOverbound := by
  intro initial inputs horizon d t ht
  obtain ⟨output, run, inv, error, _, _⟩ :=
    FloatJosephHorizon.initialized_horizon_accuracy initial inputs horizon d t ht
  refine ⟨output, run, ?_⟩
  intro i
  apply inflate_variance
  · exact Flare.Matrix.Storage.getD_finite _ _ inv.covariance_finite
  · exact (by norm_num : (0 : ℝ) ≤ 7 / 16).trans (inv.covariance_floor i)
  · exact inv.covariance_cap i
  · exact error.1.2 i i

/-- Each ideal interval can be transported using the returned native mean and
an actual rounded variance allowance. Interval endpoint arithmetic stays Real. -/
theorem horizon_interval (initial : Input.State) (inputs : Nat → Input.Model)
    (horizon t : Nat) (d : HorizonDomain initial inputs horizon) (ht : t ≤ horizon)
    : ∃ output,
        josephRun inputs initial t = .ok output
        ∧ ∀ (i : Fin 2) (truth multiplier : ℝ),
            0 ≤ multiplier
            → Kalman.Definitions.Theorems.UncertaintyBounds.IntervalCovered truth
                ((exactRun 2 2 inputs (state 2 initial) t).mean i)
                ((exactRun 2 2 inputs (state 2 initial) t).covariance i i) multiplier
            → ∃ upper,
                Kalman.Implementation.UncertaintyInflation.inflateVariance
                    (output.covariance.getD (i.val * 2 + i.val) 0.0)
                  = .ok upper
                ∧ |truth - (state 2 output).mean i|
                  ≤ meanBudget + multiplier * Real.sqrt (value upper) := by
  obtain ⟨output, run, inv, error, _, _⟩ :=
    FloatJosephHorizon.initialized_horizon_accuracy initial inputs horizon d t ht
  refine ⟨output, run, ?_⟩
  intro i truth multiplier hk covered
  obtain ⟨upper, hu, _, bound, _⟩ := inflate_variance
    (output.covariance.getD (i.val * 2 + i.val) 0.0) _
    (Flare.Matrix.Storage.getD_finite _ _ inv.covariance_finite)
    ((by norm_num : (0 : ℝ) ≤ 7 / 16).trans (inv.covariance_floor i))
    (inv.covariance_cap i) (error.1.2 i i)
  exact ⟨upper, hu, UncertaintyBounds.interval_transfer _ _ _ _ _ _ _
    (error.2.2 i) bound hk covered⟩

end Kalman.Proofs.FloatJosephUncertainty
