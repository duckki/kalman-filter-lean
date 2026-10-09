import Kalman.Proofs.RealDiagonalObservation

/-! Independent Real covariance/mean invariants for full diagonal observation.
Transition entries may reach ±1; the correction supplies boundedness even at
identity dynamics. These theorems make no native execution or rounding claim. -/

namespace Kalman.Proofs.RealObservableInvariant

open Matrix
open Kalman.Definitions
open Kalman.Definitions.LinearModel
open Kalman.Definitions.DiagonalObservation
open Kalman.Definitions.Theorems.RecursionSensitivity

structure PriorInvariant {n : Nat} (prior : State n) : Prop where
  diagonal : prior.covariance = Matrix.diagonal (fun i => prior.covariance i i)
  covariance_lower : ∀ i, 1 ≤ prior.covariance i i
  covariance_upper : ∀ i, prior.covariance i i ≤ 3
  mean_bound : ∀ i, |prior.mean i| ≤ 1

theorem prior_variance_bounds (f q p : ℝ) (hf : |f| ≤ 1)
    (hq0 : 1 ≤ q) (hq1 : q ≤ 3 / 2) (hp0 : 1 / 2 ≤ p) (hp1 : p ≤ 3 / 2)
    : 1 ≤ priorVariance f q p ∧ priorVariance f q p ≤ 3 := by
  have hf2 : f ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hf).1, (abs_le.mp hf).2]
  have hp : 0 ≤ p := by linarith
  have hm := mul_le_mul hf2 hp1 hp (by norm_num : (0 : ℝ) ≤ 1)
  unfold priorVariance
  constructor
  · linarith [mul_nonneg (sq_nonneg f) hp]
  · linarith

theorem gain_bounds (p r : ℝ) (hp0 : 1 ≤ p) (hp1 : p ≤ 3) (hr0 : 1 ≤ r) (hr1 : r ≤ 3 / 2)
    : 2 / 5 ≤ optimalGain p r ∧ optimalGain p r ≤ 3 / 4 := by
  have hd : 0 < p + r := by linarith
  unfold optimalGain
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_le_iff₀ hd).mpr
    linarith

theorem posterior_variance_bounds (p r : ℝ) (hp0 : 1 ≤ p) (hp1 : p ≤ 3)
    (hr0 : 1 ≤ r) (hr1 : r ≤ 3 / 2)
    : 1 / 2 ≤ posteriorVariance p r ∧ posteriorVariance p r ≤ 1 := by
  have hd : 0 < p + r := by linarith
  have hm := mul_nonneg (by linarith : 0 ≤ p - 1) (by linarith : 0 ≤ r - 1)
  have hu := mul_le_mul (by linarith : p - 1 ≤ 2) (by linarith : r - 1 ≤ 1 / 2)
    (by linarith : 0 ≤ r - 1) (by norm_num : (0 : ℝ) ≤ 2)
  unfold posteriorVariance
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith

/-- Exact correction is a convex combination of the prior mean and measurement. -/
theorem posterior_mean_bound (p r x z : ℝ) (hp : 0 ≤ p) (hr : 0 < r) (hx : |x| ≤ 1)
    (hz : |z| ≤ 1)
    : |posteriorMean p r x z| ≤ 1 := by
  have hd := add_pos_of_nonneg_of_pos hp hr
  have hw : 0 ≤ r / (p + r) := div_nonneg hr.le hd.le
  have hk : 0 ≤ optimalGain p r := div_nonneg hp hd.le
  have hs : r / (p + r) + optimalGain p r = 1 := by
    unfold optimalGain
    field_simp [hd.ne']
    ring
  unfold posteriorMean
  calc
    _ ≤ |r / (p + r) * x| + |optimalGain p r * z| := abs_add_le _ _
    _ = r / (p + r) * |x| + optimalGain p r * |z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hk]
    _ ≤ r / (p + r) * 1 + optimalGain p r * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hx hw) (mul_le_mul_of_nonneg_left hz hk)
    _ = 1 := by simpa only [mul_one] using hs

theorem initial_invariant {n : Nat} (x p : Vector n) (d : DiagonalInitialDomain x p)
    : DiagonalStateInvariant (state x p) := by
  refine ⟨?_, ?_, ?_, d.mean_bound⟩
  · simp [state]
  · simpa only [state, diagonal_apply_eq] using d.covariance_lower
  · simpa only [state, diagonal_apply_eq] using d.covariance_upper

theorem covariance_positive {n : Nat} (reference : State n)
    (s : DiagonalStateInvariant reference)
    : reference.covariance.PosDef := by
  rw [s.diagonal]
  apply Matrix.PosDef.diagonal
  intro i
  linarith [s.covariance_lower i]

theorem covariance_floor {n : Nat} (reference : State n)
    (s : DiagonalStateInvariant reference)
    : (reference.covariance - (1 / 2 : ℝ) • 1).PosSemidef := by
  have he : reference.covariance - (1 / 2 : ℝ) • 1 =
      diagonal (fun i => reference.covariance i i - 1 / 2) := by
    rw [s.diagonal]
    simp [smul_one_eq_diagonal, diagonal_sub]
  rw [he]
  exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (s.covariance_lower i))

theorem prediction_invariant {n : Nat} (f q r z : Vector n) (reference : State n)
    (d : DiagonalModelDomain f q r z) (s : DiagonalStateInvariant reference)
    : PriorInvariant (CovarianceRecursion.predict (model f q r) reference) := by
  let x := reference.mean
  let p := fun i => reference.covariance i i
  have he : reference = state x p := RealDiagonalObservation.state_eq_of_diagonal reference s.diagonal
  rw [he, RealDiagonalObservation.predict_eq]
  have hc := fun i => prior_variance_bounds (f i) (q i) (p i) (d.transition_bound i)
    (d.process_lower i) (d.process_upper i) (s.covariance_lower i) (s.covariance_upper i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [state]
  · simpa only [state, diagonal_apply_eq] using fun i => (hc i).1
  · simpa only [state, diagonal_apply_eq] using fun i => (hc i).2
  · intro i
    change |f i * x i| ≤ 1
    rw [abs_mul]
    exact (mul_le_mul (d.transition_bound i) (s.mean_bound i) (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem update_invariant {n : Nat} (form : CovarianceRecursion.Form) (f q r z : Vector n)
    (prior : State n) (d : DiagonalModelDomain f q r z) (s : PriorInvariant prior)
    : DiagonalStateInvariant (CovarianceRecursion.update form (model f q r) prior z)
      ∧ ∀ i,
          (CovarianceRecursion.update form (model f q r) prior z).covariance i i ≤ 1 := by
  let x := prior.mean
  let p := fun i => prior.covariance i i
  have he : prior = state x p := RealDiagonalObservation.state_eq_of_diagonal prior s.diagonal
  have hp : ∀ i, 0 ≤ p i := fun i => (by norm_num : (0 : ℝ) ≤ 1).trans (s.covariance_lower i)
  have hr : ∀ i, 0 < r i := fun i => (by norm_num : (0 : ℝ) < 1).trans_le (d.measurement_lower i)
  rw [he, RealDiagonalObservation.update_eq form f q r z x p hp hr]
  have hc := fun i => posterior_variance_bounds (p i) (r i) (s.covariance_lower i)
    (s.covariance_upper i) (d.measurement_lower i) (d.measurement_upper i)
  have hm := fun i => posterior_mean_bound (p i) (r i) (x i) (z i) (hp i) (hr i)
    (s.mean_bound i) (d.measurement_bound i)
  refine ⟨⟨?_, ?_, ?_, hm⟩, ?_⟩
  · simp [state]
  · simpa only [state, diagonal_apply_eq] using fun i => (hc i).1
  · intro i
    simpa only [state, diagonal_apply_eq] using ((hc i).2).trans (by norm_num : (1 : ℝ) ≤ 3 / 2)
  · simpa only [state, diagonal_apply_eq] using fun i => (hc i).2

/-- Observation stabilizes the exact step even when the diagonal transition
reaches identity; prediction itself need not contract the mean. -/
theorem step_invariant {n : Nat} (form : CovarianceRecursion.Form) (f q r z : Vector n)
    (reference : State n) (d : DiagonalModelDomain f q r z)
    (s : DiagonalStateInvariant reference)
    : DiagonalStateInvariant (CovarianceRecursion.step form (model f q r) reference z)
      ∧ ∀ i,
          (CovarianceRecursion.step form (model f q r) reference z).covariance i i ≤ 1 :=
  update_invariant form f q r z _ d (prediction_invariant f q r z reference d s)

/-- Every finite prefix of the original matrix Joseph recursion preserves the
independently derived diagonal covariance/mean invariant. -/
theorem run_invariant {n : Nat} (f q r z : Nat → Vector n) (x p : Vector n)
    (horizon : Nat) (d : ∀ t, t < horizon → DiagonalModelDomain (f t) (q t) (r t) (z t))
    (s : DiagonalInitialDomain x p)
    : ∀ t, t ≤ horizon → DiagonalStateInvariant (run f q r z x p t) := by
  intro t ht
  induction t with
  | zero => exact initial_invariant x p s
  | succ t ih =>
      exact (step_invariant .joseph (f t) (q t) (r t) (z t) _ (d t (by omega))
              (ih (by omega))).1

theorem horizon_covariance_floor {n : Nat} (f q r z : Nat → Vector n) (x p : Vector n)
    (horizon : Nat) (d : ∀ t, t < horizon → DiagonalModelDomain (f t) (q t) (r t) (z t))
    (s : DiagonalInitialDomain x p) (t : Nat) (ht : t ≤ horizon)
    : ((run f q r z x p t).covariance - (1 / 2 : ℝ) • 1).PosSemidef
      ∧ (run f q r z x p t).covariance.PosDef := by
  have h := run_invariant f q r z x p horizon d s t ht
  exact ⟨covariance_floor _ h, covariance_positive _ h⟩

/-- A fully observed identity transition is in the operating domain; this
family is not restricted to the strongly stable transition cap of the Float theorem. -/
theorem identity_domain_nonempty (n : Nat)
    : ∃ f q r z x p : Vector n,
        DiagonalModelDomain f q r z ∧ DiagonalInitialDomain x p ∧ (∀ i, f i = 1) := by
  refine ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => -1, fun _ => 1, fun _ => 1,
    ?_, ?_, fun _ => rfl⟩
  · constructor <;> intro i <;> norm_num
  · constructor <;> intro i <;> norm_num

end Kalman.Proofs.RealObservableInvariant
