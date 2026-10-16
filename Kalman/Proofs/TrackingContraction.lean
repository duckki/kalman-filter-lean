import Kalman.Definitions.Theorems.TrackingContraction
import Kalman.Proofs.ConstantVelocityTracking

namespace Kalman.Proofs.TrackingContraction

open Kalman.Definitions.LinearModel
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.TrackingContraction
  Kalman.Proofs.ConstantVelocityTracking

set_option maxHeartbeats 1000000

/-- The weighted absolute row sums of the squared closed-loop matrix are
both `15/16`. Measurement values cancel in the difference. -/
theorem two_step_contraction : TwoStepContraction := by
  intro x y z w r h
  refine ⟨by have := h.1; positivity, ?_, ?_⟩
  · have he : trackingMean (trackingMean x z) w 0 - trackingMean (trackingMean y z) w 0
        = 7/32*(x 0-y 0) + 23/128*(x 1-y 1) := by simp [trackingMean]; ring
    rw [he]
    have ht := abs_add_le (7/32*(x 0-y 0)) (23/128*(x 1-y 1))
    norm_num only [abs_mul, show |(7/32 : ℝ)| = 7/32 by norm_num,
      show |(23/128 : ℝ)| = 23/128 by norm_num] at ht
    linarith [h.2.1, h.2.2]
  · have he : trackingMean (trackingMean x z) w 1 - trackingMean (trackingMean y z) w 1
        = -(23/64)*(x 0-y 0) + 217/256*(x 1-y 1) := by simp [trackingMean]; ring
    rw [he]
    have ht := abs_add_le (-(23/64)*(x 0-y 0)) (217/256*(x 1-y 1))
    norm_num only [abs_mul, show |(-(23/64) : ℝ)| = 23/64 by norm_num,
      show |(217/256 : ℝ)| = 217/256 by norm_num] at ht
    linarith [h.2.1, h.2.2]

/-- Two interleaved inductions pay for two local errors per contraction.
The resulting bound is independent of the number of steps. -/
theorem uniform_perturbation : UniformPerturbation := by
  intro actual reference measurements horizon δ hδ initial localStep referenceStep
  have initialError : WeightedWithin 0 (actual 0) (reference 0) := by
    rw [initial]
    norm_num [WeightedWithin]
  have bound : ∀ t, t ≤ horizon → WeightedWithin (32*δ) (actual t) (reference t) := by
    intro t
    induction t using Nat.twoStepInduction with
    | zero =>
        intro _
        exact weighted_mono initialError (by positivity)
    | one =>
        intro ht
        have exactError := mean_nonexpansive _ _ (measurements 0) 0 initialError
        rw [← referenceStep 0 (by omega)] at exactError
        exact weighted_mono (weighted_trans (localStep 0 (by omega)) exactError)
          (by linarith)
    | more t ih _ =>
        intro ht
        have l0 := localStep t (by omega)
        have l1 := localStep (t+1) (by omega)
        have propagated := mean_nonexpansive _ _ (measurements (t+1)) δ l0
        have pair := weighted_trans l1 propagated
        have contracted := two_step_contraction _ _ (measurements t) (measurements (t+1))
          (32*δ) (ih (by omega))
        rw [← referenceStep t (by omega), ← referenceStep (t+1) (by omega)] at contracted
        exact weighted_mono (weighted_trans pair contracted) (by linarith)
  exact bound

end Kalman.Proofs.TrackingContraction
