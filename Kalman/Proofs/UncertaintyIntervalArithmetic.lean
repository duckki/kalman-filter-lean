import Kalman.Proofs.FloatDenseError
import Kalman.Implementation.Correctness.UncertaintyIntervals
import Flare.Binary64.Sqrt

namespace Kalman.Proofs.UncertaintyIntervalArithmetic

open Kalman.Implementation.UncertaintyIntervals Flare.Binary64.Value

noncomputable section

/-- A common absolute arithmetic allowance on exact results of magnitude 64. -/
abbrev roundingRadius : ℝ := 1 / 70368744177664

theorem padding_value : value padding = (1 : ℝ) / 1099511627776 := by
  change (4503599627370496 : ℝ)*(2 : ℝ)^(-92 : Int) = _
  norm_num

theorem padding_finite : padding.isFinite = true := by decide +kernel

theorem add_round (a b : Float) (A B : ℝ)
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hA : |value a| ≤ A) (hB : |value b| ≤ B) (cap : A + B ≤ 64)
    : (a + b).isFinite = true
      ∧ |value (a + b) - (value a + value b)| ≤ roundingRadius := by
  have h := Flare.Binary64.Arithmetic.add_error a b 6 ha hb (by norm_num) (by norm_num)
    (by exact (abs_add_le _ _).trans ((add_le_add hA hB).trans (by norm_num; exact cap)))
  exact ⟨h.1, h.2.trans (by norm_num [roundingRadius])⟩

theorem sub_round (a b : Float) (A B : ℝ)
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hA : |value a| ≤ A) (hB : |value b| ≤ B) (cap : A + B ≤ 64)
    : (a - b).isFinite = true
      ∧ |value (a - b) - (value a - value b)| ≤ roundingRadius := by
  have h := Flare.Binary64.Arithmetic.sub_error a b 6 ha hb (by norm_num) (by norm_num)
    (by exact (abs_sub _ _).trans ((add_le_add hA hB).trans (by norm_num; exact cap)))
  exact ⟨h.1, h.2.trans (by norm_num [roundingRadius])⟩

theorem mul_round (a b : Float) (A B : ℝ)
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hA : |value a| ≤ A) (hB : |value b| ≤ B) (cap : A * B ≤ 64)
    : (a * b).isFinite = true
      ∧ |value (a * b) - (value a * value b)| ≤ roundingRadius := by
  have h := Flare.Binary64.Arithmetic.mul_error a b 6 ha hb (by norm_num) (by norm_num)
    (by
      rw [abs_mul]
      exact (mul_le_mul hA hB (abs_nonneg _) ((abs_nonneg _).trans hA)).trans
        (by norm_num; exact cap))
  exact ⟨h.1, h.2.trans (by norm_num [roundingRadius])⟩

theorem bound_from_error (x : Float) (y c : ℝ)
    (he : |value x - y| ≤ roundingRadius) (hy : |y| ≤ c)
    : |value x| ≤ c + roundingRadius := by
  have h := abs_sub_le (value x) y 0
  simp only [sub_zero] at h
  linarith

end
end Kalman.Proofs.UncertaintyIntervalArithmetic
