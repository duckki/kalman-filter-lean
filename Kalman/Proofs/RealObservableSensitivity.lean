import Kalman.Definitions.Theorems.RecursionSensitivity
import Kalman.Proofs.RealObservableInvariant

/-! Exact correction contracts covariance/mean perturbations for full diagonal
observation, even at identity dynamics. Gain changes are included exactly.
The joint radius weights covariance by two. Native local-error certificates
for this larger-dynamics family are supplied separately by FloatObservableFilter;
FloatObservableHorizon instantiates accumulated accuracy from original inputs. -/

namespace Kalman.Proofs.RealObservableSensitivity

open Matrix
open Kalman.Definitions
open Kalman.Definitions.LinearModel
open Kalman.Definitions.DiagonalObservation
open Kalman.Definitions.Theorems.RecursionSensitivity

theorem correction_weight_bound (a r : ℝ) (ha : 1 ≤ a) (hr : 0 < r) (hR : r ≤ 3 / 2)
    : 0 ≤ r / (a + r) ∧ r / (a + r) ≤ 3 / 5 := by
  have hd : 0 < a + r := by linarith
  refine ⟨div_nonneg hr.le hd.le, (div_le_iff₀ hd).mpr ?_⟩
  linarith

theorem gain_difference (a b r : ℝ) (ha : a + r ≠ 0) (hb : b + r ≠ 0)
    : optimalGain a r - optimalGain b r = r / ((a + r) * (b + r)) * (a - b) := by
  unfold optimalGain
  field_simp [ha, hb]
  ring

theorem covariance_difference (a b r : ℝ) (ha : a + r ≠ 0) (hb : b + r ≠ 0)
    : posteriorVariance a r - posteriorVariance b r
      = r / (a + r) * (r / (b + r)) * (a - b) := by
  unfold posteriorVariance
  field_simp [ha, hb]
  ring

/-- Uniform gain sensitivity needs no upper bound on either incoming variance. -/
theorem gain_sensitivity (a b r : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : 0 < r)
    : |optimalGain a r - optimalGain b r| ≤ 1 / 4 * |a - b| := by
  have hda : 0 < a + r := by linarith
  have hdb : 0 < b + r := by linarith
  have hprod := mul_pos hda hdb
  have hsmall : (1 + r) * (1 + r) ≤ (a + r) * (b + r) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hda.le
  have hcoef : r / ((a + r) * (b + r)) ≤ 1 / 4 := by
    apply (div_le_iff₀ hprod).mpr
    nlinarith [sq_nonneg (r - 1)]
  rw [gain_difference a b r hda.ne' hdb.ne', abs_mul,
    abs_of_nonneg (div_nonneg hr.le hprod.le)]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

theorem covariance_sensitivity (a b r : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : 0 < r)
    (hR : r ≤ 3 / 2)
    : |posteriorVariance a r - posteriorVariance b r| ≤ 9 / 25 * |a - b| := by
  obtain ⟨wa0, wa1⟩ := correction_weight_bound a r ha hr hR
  obtain ⟨wb0, wb1⟩ := correction_weight_bound b r hb hr hR
  have hda : 0 < a + r := by linarith
  have hdb : 0 < b + r := by linarith
  have hc : r / (a + r) * (r / (b + r)) ≤ 9 / 25 := by
    have h := mul_le_mul wa1 wb1 wb0 (by norm_num : (0 : ℝ) ≤ 3 / 5)
    norm_num at h
    exact h
  rw [covariance_difference a b r hda.ne' hdb.ne', abs_mul,
    abs_of_nonneg (mul_nonneg wa0 wb0)]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)

/-- Exact decomposition includes the covariance-dependent gain perturbation
times the reference innovation; no first-order remainder is discarded. -/
theorem mean_difference (a b r f x y z : ℝ) (ha : a + r ≠ 0) (hb : b + r ≠ 0)
    : posteriorMean a r (f * x) z - posteriorMean b r (f * y) z
      = r / (a + r) * f * (x - y)
        + (optimalGain a r - optimalGain b r) * (z - f * y) := by
  unfold posteriorMean optimalGain
  field_simp [ha, hb]
  ring

theorem prior_variance_sensitivity (f q p s : ℝ) (hf : |f| ≤ 1)
    : |priorVariance f q p - priorVariance f q s| ≤ |p - s| := by
  have hf2 : f ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hf).1, (abs_le.mp hf).2]
  have he : priorVariance f q p - priorVariance f q s = f ^ 2 * (p - s) := by
    unfold priorVariance
    ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg f)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hf2 (abs_nonneg (p - s))

/-- Full scalar step: process noise supplies prior floor one, observation
contracts both errors, and the changed gain couples covariance error into mean. -/
theorem scalar_step_sensitivity (f q r z x p y s : ℝ) (hf : |f| ≤ 1) (hq : 1 ≤ q)
    (hr : 1 ≤ r) (hR : r ≤ 3 / 2) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hy : |y| ≤ 1) (hz : |z| ≤ 1)
    : |posteriorVariance (priorVariance f q p) r
          - posteriorVariance (priorVariance f q s) r|
        ≤ 9 / 25 * |p - s|
      ∧ |posteriorMean (priorVariance f q p) r (f * x) z
          - posteriorMean (priorVariance f q s) r (f * y) z|
        ≤ 3 / 5 * |x - y| + 1 / 2 * |p - s| := by
  let a := priorVariance f q p
  let b := priorVariance f q s
  have ha : 1 ≤ a := by dsimp [a, priorVariance]; linarith [mul_nonneg (sq_nonneg f) hp]
  have hb : 1 ≤ b := by dsimp [b, priorVariance]; linarith [mul_nonneg (sq_nonneg f) hs]
  have hr0 : 0 < r := by linarith
  have hda : 0 < a + r := by linarith
  have hdb : 0 < b + r := by linarith
  have hep := prior_variance_sensitivity f q p s hf
  have hcov := covariance_sensitivity a b r ha hb hr0 hR
  have hgain := gain_sensitivity a b r ha hb hr0
  have hw := correction_weight_bound a r ha hr0 hR
  have hfy : |f * y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hf hy (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hZ : |z - f * y| ≤ 2 := (abs_sub _ _).trans ((add_le_add hz hfy).trans (by norm_num))
  have hfirst : |r / (a + r) * f| ≤ 3 / 5 := by
    rw [abs_mul, abs_of_nonneg hw.1]
    exact (mul_le_mul hw.2 hf (abs_nonneg _) (by norm_num)).trans (by norm_num)
  constructor
  · exact hcov.trans (mul_le_mul_of_nonneg_left hep (by norm_num))
  · rw [mean_difference a b r f x y z hda.ne' hdb.ne']
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul_of_nonneg_right hfirst (abs_nonneg (x - y))
    have h2 := mul_le_mul (hgain.trans (mul_le_mul_of_nonneg_left hep (by norm_num)))
      hZ (abs_nonneg _) (by positivity : 0 ≤ (1 / 4 : ℝ) * |p - s|)
    simp only [abs_mul] at h1 ⊢
    nlinarith

/-- Matrix-specification sensitivity, with arbitrary nonnegative actual
diagonal covariance and an independently bounded ideal reference. All three
covariance forms are covered. This does not assume a native local error bound. -/
theorem step_sensitivity {n : Nat} (form : CovarianceRecursion.Form) (f q r z : Vector n)
    (actual reference : State n) (eP eX : ℝ) (d : DiagonalModelDomain f q r z)
    (ha : actual.covariance = diagonal (fun i => actual.covariance i i))
    (hp : ∀ i, 0 ≤ actual.covariance i i) (s : DiagonalStateInvariant reference)
    (he : StateWithin eP eX actual reference)
    : StateWithin (9 / 25 * eP) (3 / 5 * eX + 1 / 2 * eP)
        (CovarianceRecursion.step form (model f q r) actual z)
        (CovarianceRecursion.step form (model f q r) reference z) := by
  let x := actual.mean
  let p := fun i => actual.covariance i i
  let y := reference.mean
  let v := fun i => reference.covariance i i
  have hq : ∀ i, 0 ≤ q i := fun i => (by norm_num : (0 : ℝ) ≤ 1).trans (d.process_lower i)
  have hr : ∀ i, 0 < r i := fun i => (by norm_num : (0 : ℝ) < 1).trans_le (d.measurement_lower i)
  have hv : ∀ i, 0 ≤ v i := fun i => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (s.covariance_lower i)
  have hactual : CovarianceRecursion.step form (model f q r) actual z = step f q r z x p := by
    calc
      _ = CovarianceRecursion.step form (model f q r) (state x p) z :=
        congrArg (fun current => CovarianceRecursion.step form (model f q r) current z)
          (RealDiagonalObservation.state_eq_of_diagonal actual ha)
      _ = _ := RealDiagonalObservation.step_eq form f q r z x p hp hq hr
  have href : CovarianceRecursion.step form (model f q r) reference z = step f q r z y v := by
    calc
      _ = CovarianceRecursion.step form (model f q r) (state y v) z :=
        congrArg (fun current => CovarianceRecursion.step form (model f q r) current z)
          (RealDiagonalObservation.state_eq_of_diagonal reference s.diagonal)
      _ = _ := RealDiagonalObservation.step_eq form f q r z y v hv hq hr
  have hb := fun i => scalar_step_sensitivity (f i) (q i) (r i) (z i) (x i) (p i) (y i) (v i)
    (d.transition_bound i) (d.process_lower i) (d.measurement_lower i) (d.measurement_upper i)
    (hp i) (hv i) (s.mean_bound i) (d.measurement_bound i)
  have hP := he.1.1
  have hX := he.2.1
  rw [hactual, href]
  refine ⟨⟨by positivity, ?_⟩, by positivity, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp only [step, state, diagonal_apply_eq]
      exact (hb i).1.trans (mul_le_mul_of_nonneg_left (he.1.2 i i) (by norm_num))
    · simpa [step, state, diagonal, hij] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 25) he.1.1
  · intro i
    exact (hb i).2.trans (add_le_add
      (mul_le_mul_of_nonneg_left (he.2.2 i) (by norm_num))
      (mul_le_mul_of_nonneg_left (he.1.2 i i) (by norm_num)))

/-- Covariance receives weight two. The coupled mean estimate then gives
a dimension-independent joint contraction 17/20, with gain error included. -/
theorem joint_step_contraction {n : Nat} (form : CovarianceRecursion.Form)
    (f q r z : Vector n) (actual reference : State n) (radius : ℝ)
    (d : DiagonalModelDomain f q r z)
    (ha : actual.covariance = diagonal (fun i => actual.covariance i i))
    (hp : ∀ i, 0 ≤ actual.covariance i i) (s : DiagonalStateInvariant reference)
    (he : DiagonalJointWithin radius actual reference)
    : DiagonalJointWithin (17 / 20 * radius)
        (CovarianceRecursion.step form (model f q r) actual z)
        (CovarianceRecursion.step form (model f q r) reference z) := by
  have h := step_sensitivity form f q r z actual reference (radius / 2) radius d ha hp s he
  have h0 := he.2.1
  refine ⟨⟨by positivity, ?_⟩, by positivity, ?_⟩
  · intro i j
    exact (h.1.2 i j).trans (by nlinarith)
  · intro i
    exact (h.2.2 i).trans (by linarith)

/-- Two exact trajectories using the same time-varying original model and
measurement sequence forget their initial joint discrepancy geometrically. -/
theorem horizon_contraction {n : Nat} (f q r z : Nat → Vector n)
    (x p y v : Vector n) (horizon : Nat) (radius : ℝ)
    (d : ∀ t, t < horizon → DiagonalModelDomain (f t) (q t) (r t) (z t))
    (a : DiagonalInitialDomain x p) (b : DiagonalInitialDomain y v)
    (he : DiagonalJointWithin radius (state x p) (state y v))
    : ∀ t,
        t ≤ horizon
        → DiagonalJointWithin ((17 / 20 : ℝ) ^ t * radius) (run f q r z x p t)
            (run f q r z y v t) := by
  intro t ht
  induction t with
  | zero => simpa only [run, pow_zero, one_mul] using he
  | succ t ih =>
      have hs := RealObservableInvariant.run_invariant f q r z y v horizon d b t (by omega)
      have ha := RealObservableInvariant.run_invariant f q r z x p horizon d a t (by omega)
      have hp : ∀ i, 0 ≤ (run f q r z x p t).covariance i i :=
        fun i => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (ha.covariance_lower i)
      have h := joint_step_contraction .joseph (f t) (q t) (r t) (z t) _ _ _
        (d t (by omega)) ha.diagonal hp hs (ih (by omega))
      simpa only [run, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

theorem jointWithin_trans {n : Nat} {a b c : State n} {e f : ℝ}
    (hab : DiagonalJointWithin e a b) (hbc : DiagonalJointWithin f b c)
    : DiagonalJointWithin (e + f) a c := by
  have he := hab.2.1
  have hf := hbc.2.1
  refine ⟨⟨by positivity, ?_⟩, add_nonneg he hf, ?_⟩
  · intro i j
    have h := (abs_sub_le (a.covariance i j) (b.covariance i j) (c.covariance i j)).trans
      (add_le_add (hab.1.2 i j) (hbc.1.2 i j))
    convert h using 1
    ring
  · intro i
    exact (abs_sub_le _ _ _).trans (add_le_add (hab.2.2 i) (hbc.2.2 i))

/-- Conditional propagation interface accepting a native local-error proof:
the supplied local joint radius is charged in addition to exact contraction. -/
theorem joint_step_with_local_error {n : Nat} (form : CovarianceRecursion.Form)
    (f q r z : Vector n) (actual reference output : State n) (radius localError : ℝ)
    (d : DiagonalModelDomain f q r z)
    (ha : actual.covariance = diagonal (fun i => actual.covariance i i))
    (hp : ∀ i, 0 ≤ actual.covariance i i) (s : DiagonalStateInvariant reference)
    (he : DiagonalJointWithin radius actual reference)
    (hl
      : DiagonalJointWithin localError output
          (CovarianceRecursion.step form (model f q r) actual z))
    : DiagonalJointWithin (localError + 17 / 20 * radius) output
        (CovarianceRecursion.step form (model f q r) reference z) :=
  jointWithin_trans hl
    (joint_step_contraction form f q r z actual reference radius d ha hp s he)

/-- The fixed joint allowance 20/3 times a supplied local allowance closes
the perturbed-step recurrence. No native local bound is asserted here. -/
theorem joint_uniform_budget {n : Nat} (form : CovarianceRecursion.Form)
    (f q r z : Vector n) (actual reference output : State n) (localError : ℝ)
    (d : DiagonalModelDomain f q r z)
    (ha : actual.covariance = diagonal (fun i => actual.covariance i i))
    (hp : ∀ i, 0 ≤ actual.covariance i i) (s : DiagonalStateInvariant reference)
    (he : DiagonalJointWithin (20 / 3 * localError) actual reference)
    (hl
      : DiagonalJointWithin localError output
          (CovarianceRecursion.step form (model f q r) actual z))
    : DiagonalJointWithin (20 / 3 * localError) output
        (CovarianceRecursion.step form (model f q r) reference z) := by
  have h := joint_step_with_local_error form f q r z actual reference output _ localError d ha hp s he hl
  convert h using 1
  ring

/-- Proof witness for the exact Real result statement. -/
theorem diagonalStepSensitivity
    : Kalman.Definitions.Theorems.RecursionSensitivity.DiagonalStepSensitivity :=
  step_sensitivity

/-- Proof witness for the exact Real result statement. -/
theorem diagonalJointContraction
    : Kalman.Definitions.Theorems.RecursionSensitivity.DiagonalJointContraction :=
  joint_step_contraction

/-- Proof witness for the exact Real result statement. -/
theorem diagonalHorizonContraction
    : Kalman.Definitions.Theorems.RecursionSensitivity.DiagonalHorizonContraction :=
  horizon_contraction

end Kalman.Proofs.RealObservableSensitivity
