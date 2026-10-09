import Kalman.Proofs.RealObservableSensitivity

/-! Full-observation correction sensitivity with slack around the reached
native prediction. The covariance-dependent gain change is included exactly;
these are Real propagation lemmas, independently of native rounding. -/

namespace Kalman.Proofs.RealObservableCorrection

open Matrix
open Kalman.Definitions
open Kalman.Definitions.LinearModel
open Kalman.Definitions.DiagonalObservation
open Kalman.Definitions.Theorems.RecursionSensitivity

theorem correction_weight_bound (a r : ℝ) (ha : 15 / 16 ≤ a) (hr : 0 < r) (hR : r ≤ 3 / 2)
    : 0 ≤ r / (a + r) ∧ r / (a + r) ≤ 8 / 13 := by
  have hd : 0 < a + r := by linarith
  refine ⟨div_nonneg hr.le hd.le, (div_le_iff₀ hd).mpr ?_⟩
  linarith

theorem gain_sensitivity (a b r : ℝ) (ha : 15 / 16 ≤ a) (hb : 15 / 16 ≤ b) (hr : 0 < r)
    : |optimalGain a r - optimalGain b r| ≤ 4 / 15 * |a - b| := by
  have hda : 0 < a + r := by linarith
  have hdb : 0 < b + r := by linarith
  have hd := mul_pos hda hdb
  have hsmall : (15 / 16 + r) * (15 / 16 + r) ≤ (a + r) * (b + r) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hda.le
  have hc : r / ((a + r) * (b + r)) ≤ 4 / 15 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (r - 15 / 16)]
  rw [RealObservableSensitivity.gain_difference a b r hda.ne' hdb.ne', abs_mul,
    abs_of_nonneg (div_nonneg hr.le hd.le)]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)

/-- The reference mean may have magnitude 9/8. No bound on the perturbed
mean is needed for this difference estimate. -/
theorem scalar_sensitivity (a b r x y z : ℝ) (ha : 15 / 16 ≤ a) (hb : 15 / 16 ≤ b)
    (hr : 1 ≤ r) (hR : r ≤ 3 / 2) (hy : |y| ≤ 9 / 8) (hz : |z| ≤ 1)
    : |posteriorVariance a r - posteriorVariance b r| ≤ 2 / 5 * |a - b|
      ∧ |posteriorMean a r x z - posteriorMean b r y z|
        ≤ 8 / 13 * |x - y| + 17 / 30 * |a - b| := by
  have hr0 : 0 < r := by linarith
  have hda : 0 < a + r := by linarith
  have hdb : 0 < b + r := by linarith
  obtain ⟨wa0, wa1⟩ := correction_weight_bound a r ha hr0 hR
  obtain ⟨wb0, wb1⟩ := correction_weight_bound b r hb hr0 hR
  have hcoef : r / (a + r) * (r / (b + r)) ≤ 2 / 5 := by
    exact (mul_le_mul wa1 wb1 wb0 (by norm_num : (0 : ℝ) ≤ 8 / 13)).trans (by norm_num)
  constructor
  · rw [RealObservableSensitivity.covariance_difference a b r hda.ne' hdb.ne', abs_mul,
      abs_of_nonneg (mul_nonneg wa0 wb0)]
    exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
  · have hm := RealObservableSensitivity.mean_difference a b r 1 x y z hda.ne' hdb.ne'
    simp only [one_mul, mul_one] at hm
    rw [hm]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg wa0]
    have hz' : |z - y| ≤ 17 / 8 := (abs_sub _ _).trans ((add_le_add hz hy).trans (by norm_num))
    have h1 := mul_le_mul_of_nonneg_right wa1 (abs_nonneg (x - y))
    have h2 := mul_le_mul (gain_sensitivity a b r ha hb hr0) hz'
      (abs_nonneg _) (by positivity : 0 ≤ (4 / 15 : ℝ) * |a - b|)
    nlinarith

/-- Correction depends only on H/R, not on the unused dynamics F/Q. -/
theorem update_eq_full_observation {n : Nat} (form : CovarianceRecursion.Form)
    (m : Model n n) (s : State n) (z p r : Vector n)
    (hH : m.observation = 1) (hP : s.covariance = diagonal p)
    (hR : m.measurementNoise = diagonal r) (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < r i)
    : CovarianceRecursion.update form m s z
      = state (fun i => posteriorMean (p i) (r i) (s.mean i) (z i))
          (fun i => posteriorVariance (p i) (r i)) := by
  have he := RealDiagonalObservation.update_eq form (fun _ : Fin n => (0 : ℝ))
    (fun _ => 0) r z s.mean p hp hr
  have hi : CovarianceRecursion.update form m s z
      = CovarianceRecursion.update form (model (fun _ => 0) (fun _ => 0) r) (state s.mean p) z := by
    cases form <;> simp only [CovarianceRecursion.update, CovarianceRecursion.gain,
      CovarianceRecursion.innovation, CovarianceRecursion.innovationCovariance,
      CovarianceRecursion.correctedCovariance, CovarianceRecursion.compact,
      CovarianceRecursion.subtractive, CovarianceRecursion.joseph, model, state, hH, hP, hR]
  exact hi.trans he

/-- Matrix sensitivity for two diagonal priors at full observation. This
includes the exact gain change and retains the local prediction's slack. -/
theorem update_sensitivity {n : Nat} (m : Model n n) (actual reference : State n)
    (z r : Vector n) (eP eX : ℝ) (hH : m.observation = 1)
    (hR : m.measurementNoise = diagonal r)
    (da : actual.covariance = diagonal (fun i => actual.covariance i i))
    (dr : reference.covariance = diagonal (fun i => reference.covariance i i))
    (ha : ∀ i, 15 / 16 ≤ actual.covariance i i)
    (hb : ∀ i, 15 / 16 ≤ reference.covariance i i)
    (hr : ∀ i, 1 ≤ r i) (hRu : ∀ i, r i ≤ 3 / 2)
    (hy : ∀ i, |reference.mean i| ≤ 9 / 8) (hz : ∀ i, |z i| ≤ 1)
    (he : StateWithin eP eX actual reference)
    : StateWithin (2 / 5 * eP) (8 / 13 * eX + 17 / 30 * eP)
        (CovarianceRecursion.update .joseph m actual z)
        (CovarianceRecursion.update .joseph m reference z) := by
  have ea := update_eq_full_observation .joseph m actual z _ r hH da hR
    (fun i => by linarith [ha i]) (fun i => by linarith [hr i])
  have er := update_eq_full_observation .joseph m reference z _ r hH dr hR
    (fun i => by linarith [hb i]) (fun i => by linarith [hr i])
  rw [ea, er]
  have heP := he.1.1
  have heX := he.2.1
  refine ⟨⟨by positivity, ?_⟩, by positivity, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp only [state, diagonal_apply_eq]
      exact (scalar_sensitivity (actual.covariance i i) (reference.covariance i i) (r i)
        (actual.mean i) (reference.mean i) (z i) (ha i) (hb i) (hr i) (hRu i) (hy i) (hz i)).1.trans
        (mul_le_mul_of_nonneg_left (he.1.2 i i) (by norm_num))
    · simpa [state, diagonal, hij] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5) he.1.1
  · intro i
    exact (scalar_sensitivity (actual.covariance i i) (reference.covariance i i) (r i)
        (actual.mean i) (reference.mean i) (z i) (ha i) (hb i) (hr i) (hRu i) (hy i) (hz i)).2.trans
      (add_le_add (mul_le_mul_of_nonneg_left (he.2.2 i) (by norm_num))
        (mul_le_mul_of_nonneg_left (he.1.2 i i) (by norm_num)))

/-- Generic diagonal prediction, with no observation restriction. -/
theorem predict_eq_diagonal {n m : Nat} (g : Model n m) (s : State n)
    (f q p : Vector n) (hF : g.transition = diagonal f) (hQ : g.processNoise = diagonal q)
    (hP : s.covariance = diagonal p)
    : CovarianceRecursion.predict g s
      = state (fun i => f i * s.mean i) (fun i => priorVariance (f i) (q i) (p i)) := by
  apply congrArg₂ State.mk
  · change g.transition *ᵥ s.mean = _
    rw [hF]
    funext i
    exact Matrix.mulVec_diagonal f s.mean i
  · change g.transition * s.covariance * g.transition.transpose + g.processNoise = _
    rw [hF, hQ, hP]
    simp only [diagonal_transpose, diagonal_mul_diagonal]
    rw [diagonal_add]
    apply congrArg diagonal
    funext i
    dsimp [priorVariance]
    ring

end Kalman.Proofs.RealObservableCorrection
