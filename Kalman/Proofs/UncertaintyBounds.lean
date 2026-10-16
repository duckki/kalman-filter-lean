import Kalman.Definitions.Theorems.UncertaintyBounds
import Mathlib.Tactic

/-! Exact order and interval transfer, independent of any floating-point model. -/

namespace Kalman.Proofs.UncertaintyBounds

open Matrix Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Definitions.Theorems.UncertaintyBounds

/-- A one-sided diagonal comparison suffices; the supplied overbound can be
larger than the minimum error inflation. -/
theorem diagonal_overbound_of_le {n : Nat} (upper reference : Fin n → ℝ)
    (h : ∀ i, reference i ≤ upper i)
    : CovarianceOverbound (diagonal upper) (diagonal reference) := by
  unfold CovarianceOverbound
  rw [diagonal_sub]
  exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (h i))

theorem diagonal_overbound : DiagonalInflation := by
  intro n actual reference ε h
  apply diagonal_overbound_of_le
  intro i
  have hi := (abs_le.mp (h.2 i i)).1
  simp only [diagonal_apply_eq] at hi
  linarith

/-- Transfer any externally established ideal interval to a nearby center and
an overbounding variance. No distribution or risk premise is inferred. -/
theorem interval_transfer (truth ideal actual variance upper multiplier meanError : ℝ)
    (hm : |actual - ideal| ≤ meanError) (hv : variance ≤ upper)
    (hk : 0 ≤ multiplier) (h : IntervalCovered truth ideal variance multiplier)
    : |truth - actual| ≤ meanError + multiplier * Real.sqrt upper := by
  have hc : |truth - actual| ≤ |truth - ideal| + |actual - ideal| := by
    simpa only [abs_sub_comm actual ideal] using abs_sub_le truth ideal actual
  exact hc.trans
    ((add_le_add h hm).trans
      (by
        have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) hk
        linarith))

end Kalman.Proofs.UncertaintyBounds
