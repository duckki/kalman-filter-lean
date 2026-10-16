import Kalman.Definitions.Theorems.ConstantVelocityTracking
import Kalman.Proofs.JosephPositionCorrection

/-! Exact covariance cycle and weighted mean nonexpansiveness for the first
coupled tracking envelope. These are completed Real proofs, not native bounds. -/

namespace Kalman.Proofs.ConstantVelocityTracking
open Matrix Kalman.Definitions.LinearModel Kalman.Definitions.CovarianceRecursion
  Kalman.Definitions.Theorems.ConstantVelocityTracking
set_option maxHeartbeats 1000000

theorem prediction_covariance (x : Vector 2)
    : (predict trackingModel ⟨x, posteriorCovariance⟩).covariance = priorCovariance := by
  ext i j
  simp only [predict, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [trackingModel, posteriorCovariance, priorCovariance]

theorem exact_gain (x : Vector 2)
    : gain trackingModel ⟨x, priorCovariance⟩ = !![1 / 2; 1 / 4] := by
  have hH : trackingModel.observation =
      Kalman.Definitions.Theorems.JosephPositionCorrection.positionRow := by
    ext i j
    fin_cases j <;>
      norm_num [trackingModel, Kalman.Definitions.Theorems.JosephPositionCorrection.positionRow]
  ext i j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  rw [Kalman.Proofs.JosephPositionCorrection.gain_entry _ _ hH]
  fin_cases i <;> norm_num [priorCovariance, trackingModel]

theorem correction_exact (x : Vector 2) (z : ℝ)
    : update .joseph trackingModel ⟨x, priorCovariance⟩ (fun _ => z)
      = ⟨correctedMean x z, posteriorCovariance⟩ := by
  have hg := exact_gain x
  simp only [update, hg, correctedCovariance]
  congr 1
  · funext i
    fin_cases i <;>
      simp [innovation, correctedMean, trackingModel, dotProduct, Fin.sum_univ_two] <;> ring
  · ext i j
    simp only [joseph, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two, Fin.sum_univ_one]
    fin_cases i <;> fin_cases j <;>
      norm_num [trackingModel, priorCovariance, posteriorCovariance, Matrix.one_apply]

theorem corrected_predict_mean (x : Vector 2) (z : ℝ)
    : correctedMean (trackingModel.transition *ᵥ x) z = trackingMean x z := by
  funext i
  fin_cases i <;>
    simp [correctedMean, trackingMean, trackingModel, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem corrected_perturbation (x y : Vector 2) (z ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i, |x i - y i| ≤ ε)
    : WeightedWithin ε (correctedMean x z) (correctedMean y z) := by
  refine ⟨hε, ?_, ?_⟩
  · have he : correctedMean x z 0 - correctedMean y z 0 = (x 0-y 0)/2 := by
      simp [correctedMean]; ring
    rw [he, abs_div]
    norm_num only [show |(2 : ℝ)| = 2 by norm_num]
    linarith [h 0]
  · have he : correctedMean x z 1 - correctedMean y z 1 =
        (x 1-y 1) - (x 0-y 0)/4 := by simp [correctedMean]; ring
    rw [he]
    have ht := abs_sub (x 1-y 1) ((x 0-y 0)/4)
    norm_num only [abs_div, show |(4 : ℝ)| = 4 by norm_num] at ht
    linarith [h 0, h 1]

theorem step_exact (x : Vector 2) (z : ℝ)
    : step .joseph trackingModel ⟨x, posteriorCovariance⟩ (fun _ => z)
      = ⟨trackingMean x z, posteriorCovariance⟩ := by
  have hp : predict trackingModel ⟨x, posteriorCovariance⟩ =
      ⟨trackingModel.transition *ᵥ x, priorCovariance⟩ := by
    unfold predict
    congr 1
    exact prediction_covariance x
  rw [step, hp, correction_exact]
  congr 1
  funext i
  fin_cases i <;>
    simp [correctedMean, trackingMean, trackingModel, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem weighted_trans {r s : ℝ} {x y z : Vector 2}
    (h : WeightedWithin r x y) (g : WeightedWithin s y z)
    : WeightedWithin (r + s) x z := by
  refine ⟨by linarith [h.1, g.1], ?_, ?_⟩
  · exact (abs_sub_le _ _ _).trans (add_le_add h.2.1 g.2.1)
  · exact (abs_sub_le _ _ _).trans ((add_le_add h.2.2 g.2.2).trans (by ring_nf; rfl))

theorem weighted_mono {r s : ℝ} {x y : Vector 2} (h : WeightedWithin r x y) (hrs : r ≤ s)
    : WeightedWithin s x y :=
  ⟨h.1.trans hrs, h.2.1.trans hrs, h.2.2.trans (by linarith)⟩

theorem mean_nonexpansive (x y : Vector 2) (z r : ℝ) (h : WeightedWithin r x y)
    : WeightedWithin r (trackingMean x z) (trackingMean y z) := by
  refine ⟨h.1, ?_, ?_⟩
  · have he : trackingMean x z 0 - trackingMean y z 0 =
        (x 0 - y 0)/2 + (x 1 - y 1)/8 := by simp [trackingMean]; ring
    rw [he]
    calc
      _ ≤ |x 0 - y 0| / 2 + |x 1 - y 1| / 8 := by
        simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 8)]
          using abs_add_le ((x 0 - y 0) / 2) ((x 1 - y 1) / 8)
      _ ≤ r := by linarith [h.2.1, h.2.2]
  · have he : trackingMean x z 1 - trackingMean y z 1 =
        -(x 0-y 0)/4 + 15*(x 1-y 1)/16 := by simp [trackingMean]; ring
    rw [he]
    calc
      _ ≤ |x 0 - y 0| / 4 + 15 * |x 1 - y 1| / 16 := by
        simpa only [abs_div, abs_neg, abs_mul,
          show |(4 : ℝ)| = 4 by norm_num, show |(15 : ℝ)| = 15 by norm_num,
          show |(16 : ℝ)| = 16 by norm_num]
          using abs_add_le (-(x 0 - y 0) / 4) (15 * (x 1 - y 1) / 16)
      _ ≤ 4 * r := by linarith [h.2.1, h.2.2]

theorem mean_envelope (x : Vector 2) (z r : ℝ) (h : WeightedWithin r x 0)
    : WeightedWithin (r + |z| / 2) (trackingMean x z) 0 := by
  have hd := mean_nonexpansive x 0 z r h
  have hz : WeightedWithin (|z|/2) (trackingMean 0 z) 0 := by
    refine ⟨by positivity, ?_, ?_⟩
    · norm_num [trackingMean, abs_div]
    · norm_num [trackingMean, abs_div]
      linarith [abs_nonneg z]
  exact weighted_trans hd hz

/-- Public exact steady-family result. -/
theorem stationaryStep : StationaryStep := step_exact

/-- Public weighted nonexpansiveness result. -/
theorem meanNonexpansive : MeanNonexpansive := mean_nonexpansive

end Kalman.Proofs.ConstantVelocityTracking
