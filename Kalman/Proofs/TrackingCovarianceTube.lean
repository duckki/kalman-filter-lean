import Kalman.Proofs.FloatConstantVelocityStorage
import Kalman.Proofs.JosephGainSensitivity
import Kalman.Definitions.Theorems.TrackingCovarianceTube

/-! Covariance-neighborhood geometry and roundoff transfer calculations. -/

namespace Kalman.Proofs.TrackingCovarianceTube
open Matrix Kalman.Definitions.LinearModel Kalman.Definitions.CovarianceRecursion
  Kalman.Definitions.Theorems.ConstantVelocityTracking
  Kalman.Definitions.Theorems.TrackingCovarianceTube
  Kalman.Definitions.Theorems.RecursionSensitivity
set_option maxHeartbeats 2000000

theorem weight_lower : (weight - (1 : Square 2)).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [weight, Matrix.one_apply]
  · intro x
    simp [weight, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
    nlinarith [sq_nonneg (7*x 0+10*x 1), sq_nonneg (x 1)]

theorem weight_psd : weight.PosSemidef := by
  convert weight_lower.add (PosSemidef.one (n := Fin 2) (R := ℝ)) using 1
  abel

theorem weight_upper : ((6 : ℝ) • (1 : Square 2) - weight).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [weight, Matrix.one_apply]
  · intro x
    simp [weight, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
    nlinarith [sq_nonneg (x 1-4*x 0), sq_nonneg (x 0)]

theorem lyapunov_identity
    : closedTransition * weight * closedTransition.transpose = weight - 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [weight, closedTransition, Matrix.one_apply]

/-- In dimension two, two Loewner inequalities bound each entry using only the
reference diagonals. Opposite-sign test vectors cancel the unknown diagonals. -/
theorem sandwich_entries (b d : Square 2) (cap : ℝ) (hb : b.IsHermitian)
    (h0 : b 0 0 ≤ cap) (h1 : b 1 1 ≤ cap)
    (plus : (b + d).PosSemidef) (minus : (b - d).PosSemidef)
    : ∀ i j, |d i j| ≤ cap := by
  have hd : d.IsHermitian := by
    convert plus.isHermitian.sub hb using 1
    abel
  have sym : d 1 0 = d 0 1 := by
    have h := congrArg (fun a : Square 2 => a 0 1) hd.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have p0 := plus.diag_nonneg (i := 0)
  have p1 := plus.diag_nonneg (i := 1)
  have m0 := minus.diag_nonneg (i := 0)
  have m1 := minus.diag_nonneg (i := 1)
  have pp := plus.dotProduct_mulVec_nonneg ![(1 : ℝ), 1]
  have pm := plus.dotProduct_mulVec_nonneg ![(1 : ℝ), -1]
  have mp := minus.dotProduct_mulVec_nonneg ![(1 : ℝ), 1]
  have mm := minus.dotProduct_mulVec_nonneg ![(1 : ℝ), -1]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sym] at p0 p1 m0 m1 pp pm mp mm
  intro i j
  fin_cases i <;> fin_cases j
  · change |d 0 0| ≤ cap
    rw [abs_le]; constructor <;> linarith
  · change |d 0 1| ≤ cap
    rw [abs_le]; constructor <;> linarith
  · change |d 1 0| ≤ cap
    rw [sym, abs_le]; constructor <;> linarith
  · change |d 1 1| ≤ cap
    rw [abs_le]; constructor <;> linarith

theorem tube_entries (p : Square 2) (h : Tube p)
    : EntrywiseWithin (6 * radius) p posteriorCovariance := by
  refine ⟨by norm_num [radius], ?_⟩
  exact sandwich_entries (radius • weight) (p - posteriorCovariance) (6 * radius)
    ((weight_psd.smul (by norm_num [radius] : (0 : ℝ) ≤ radius)).isHermitian)
    (by norm_num [weight, radius]) (by norm_num [weight, radius]) h.1 h.2

theorem predicted_tube_entries (p : Square 2) (h : Tube p)
    : EntrywiseWithin (6 * radius)
        (trackingModel.transition * p * trackingModel.transition.transpose
          + trackingModel.processNoise)
        priorCovariance := by
  have lo := h.1.mul_mul_conjTranspose_same trackingModel.transition
  have hi := h.2.mul_mul_conjTranspose_same trackingModel.transition
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at lo hi
  let b := radius • (trackingModel.transition * weight * trackingModel.transition.transpose)
  let d := trackingModel.transition * (p-posteriorCovariance) * trackingModel.transition.transpose
  have hb : b.IsHermitian := by
    exact (by
      simpa [b, Matrix.conjTranspose_eq_transpose_of_trivial]
        using ((weight_psd.mul_mul_conjTranspose_same trackingModel.transition).smul
                (by norm_num [radius])).isHermitian)
  have h0 : b 0 0 ≤ 6*radius := by
    simp only [b, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    norm_num [trackingModel, weight, radius]
  have h1 : b 1 1 ≤ 6*radius := by
    simp only [b, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    norm_num [trackingModel, weight, radius]
  have plus : (b+d).PosSemidef := by
    convert lo using 1
    simp [b, d, Matrix.mul_add, Matrix.add_mul, ]
  have minus : (b-d).PosSemidef := by
    convert hi using 1
    simp [b, d, Matrix.mul_sub, Matrix.sub_mul, ]
  have entries := sandwich_entries b d (6*radius) hb h0 h1 plus minus
  have nominal := Kalman.Proofs.ConstantVelocityTracking.prediction_covariance (0 : Vector 2)
  change trackingModel.transition * posteriorCovariance * trackingModel.transition.transpose
    + trackingModel.processNoise = priorCovariance at nominal
  refine ⟨by norm_num [radius], ?_⟩
  intro i j
  rw [← nominal]
  convert entries i j using 1
  simp [d, Matrix.mul_sub, Matrix.sub_mul]

theorem error_shift (a b : Square 2) (e : ℝ) (ha : a.IsHermitian) (hb : b.IsHermitian)
    (h : EntrywiseWithin e a b)
    : ((2 * e) • (1 : Square 2) + (a - b)).PosSemidef
      ∧ ((2 * e) • (1 : Square 2) - (a - b)).PosSemidef := by
  have plus := Flare.Analysis.NumericalBounds.perturbation_lower_bound 0 (a-b) 0 e h.1
    (by simpa using (PosSemidef.zero (n := Fin 2) (R := ℝ))) (ha.sub hb) h.2
  have minus := Flare.Analysis.NumericalBounds.perturbation_lower_bound 0 (b-a) 0 e h.1
    (by simpa using (PosSemidef.zero (n := Fin 2) (R := ℝ))) (hb.sub ha) (by intro i j; simpa only [Matrix.sub_apply, abs_sub_comm] using h.2 i j)
  constructor
  · convert plus using 1
    simp
    abel
  · convert minus using 1
    simp
    abel

noncomputable def fixedCovariance (p : Square 2) : Square 2 :=
  joseph trackingModel (predict trackingModel ⟨0, p⟩) steadyGain

theorem fixed_covariance_identity (p : Square 2)
    : fixedCovariance p
      = posteriorCovariance
        + closedTransition * (p - posteriorCovariance) * closedTransition.transpose := by
  ext i j
  simp only [fixedCovariance, joseph, predict, Matrix.add_apply, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Fin.sum_univ_one]
  fin_cases i <;> fin_cases j <;>
    norm_num [trackingModel, steadyGain, closedTransition, posteriorCovariance,
      Matrix.one_apply] <;> ring

theorem fixed_sandwich (p : Square 2) (h : Tube p)
    : (radius • (weight - 1) + (fixedCovariance p - posteriorCovariance)).PosSemidef
      ∧ (radius • (weight - 1)
          - (fixedCovariance p - posteriorCovariance)).PosSemidef := by
  have lo := h.1.mul_mul_conjTranspose_same closedTransition
  have hi := h.2.mul_mul_conjTranspose_same closedTransition
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at lo hi
  constructor
  · convert lo using 1
    simp [fixed_covariance_identity, Matrix.mul_add, Matrix.add_mul,
      lyapunov_identity]
  · convert hi using 1
    simp [fixed_covariance_identity, Matrix.mul_sub, Matrix.sub_mul,
      lyapunov_identity]

theorem fixed_hermitian (p : Square 2) (h : Tube p)
    : (fixedCovariance p).IsHermitian := by
  have hd : (p-posteriorCovariance).IsHermitian := by
    convert h.1.isHermitian.sub
      ((weight_psd.smul (by norm_num [radius] : (0 : ℝ) ≤ radius)).isHermitian) using 1
    abel
  rw [fixed_covariance_identity]
  apply Kalman.Proofs.FloatConstantVelocityStorage.posterior_psd.isHermitian.add
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
    using Matrix.isHermitian_mul_mul_conjTranspose closedTransition hd

/-- An internal transfer calculation pays for prediction, parameter variation,
gain optimization and native correction. Every premise is discharged by the
native theorem; these are not original-input domain assumptions. -/
theorem tube_transfer (p j o u : Square 2) (hp : Tube p)
    (hj : j.IsHermitian) (ho : o.IsHermitian) (hu : u.IsHermitian)
    (fixedError
      : EntrywiseWithin (4 * (2 : ℝ) ^ (-36 : Int) + 73 * parameterRadius) j
          (fixedCovariance p))
    (optimal : (j - o).PosSemidef)
    (gainError : EntrywiseWithin ((7 / 2 : ℝ) * (7 * radius) ^ 2) j o)
    (rounding : EntrywiseWithin ((2 : ℝ) ^ (-28 : Int)) u o)
    : Tube u := by
  have nom := fixed_sandwich p hp
  have fe := error_shift j (fixedCovariance p) _ hj (fixed_hermitian p hp) fixedError
  have ge := error_shift j o _ hj ho gainError
  have re := error_shift u o _ hu ho rounding
  have spareUpper := (PosSemidef.one (n := Fin 2) (R := ℝ)).smul
    (by norm_num [radius, parameterRadius] :
      0 ≤ radius - 2*(4*(2 : ℝ)^(-36 : Int)+73*parameterRadius) - 2*(2 : ℝ)^(-28 : Int))
  have spareLower := (PosSemidef.one (n := Fin 2) (R := ℝ)).smul
    (by norm_num [radius, parameterRadius] :
      0 ≤ radius - 2*(4*(2 : ℝ)^(-36 : Int)+73*parameterRadius)
        - 2*((7/2 : ℝ)*(7*radius)^2) - 2*(2 : ℝ)^(-28 : Int))
  constructor
  · convert (((nom.1.add fe.1).add ge.2).add re.1).add spareLower using 1
    simp only [sub_smul, smul_sub]
    module
  · convert (((nom.2.add fe.2).add optimal).add re.2).add spareUpper using 1
    simp only [sub_smul, smul_sub]
    module

/-- The entire neighborhood is Hermitian and has a uniform positive floor. -/
theorem tube_floor (p : Square 2) (h : Tube p) : (p - (1 / 8 : ℝ) • 1).PosSemidef := by
  have hd : (p-posteriorCovariance).IsHermitian := by
    convert h.1.isHermitian.sub
      ((weight_psd.smul (by norm_num [radius] : (0 : ℝ) ≤ radius)).isHermitian) using 1
    abel
  have hp : p.IsHermitian := by
    convert hd.add Kalman.Proofs.FloatConstantVelocityStorage.posterior_psd.isHermitian using 1
    abel
  have lower := Flare.Analysis.EntrywiseError.lower_bound_of_error posteriorCovariance p
    (1/4) (6*radius) Kalman.Proofs.FloatConstantVelocityStorage.posterior_floor hp (tube_entries p h)
  have extra := (PosSemidef.one (n := Fin 2) (R := ℝ)).smul
    (by norm_num [radius] : (0 : ℝ) ≤ 1/4 - 2*(6*radius) - 1/8)
  convert lower.add extra using 1
  norm_num
  module

theorem nominal_prior_floor : (priorCovariance - (17 / 32 : ℝ) • 1).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [priorCovariance, Matrix.one_apply]
  · intro x
    simp [priorCovariance, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
    nlinarith [sq_nonneg (15*x 0+16*x 1), sq_nonneg (x 1)]

/-- Scalar innovation geometry turns prior/noise perturbations into a gain
bound, without importing an inverse Lipschitz estimate for general matrices. -/
theorem quotient_gain_bound (p p0 a r k e θ : ℝ)
    (he : 0 ≤ e) (hθ : 0 ≤ θ) (hs : 3 / 2 ≤ a + r)
    (hp : |p - p0| ≤ e) (ha : |a - 1| ≤ e) (hr : |r - 1| ≤ θ)
    (hk : |k| ≤ 1 / 2) (hstation : p0 = 2 * k)
    : |p / (a + r) - k| ≤ e + θ / 3 := by
  have positive : 0 < a+r := by linarith
  have identity : p/(a+r)-k = ((p-p0)-k*((a-1)+(r-1)))/(a+r) := by
    rw [hstation]
    field_simp
    ring
  rw [identity, abs_div, abs_of_pos positive]
  apply (div_le_iff₀ positive).mpr
  have ht := abs_sub (p-p0) (k*((a-1)+(r-1)))
  have hb := abs_add_le (a-1) (r-1)
  have hm : |k*((a-1)+(r-1))| ≤ (1/2 : ℝ)*(e+θ) := by
    rw [abs_mul]
    exact mul_le_mul hk (hb.trans (add_le_add ha hr)) (abs_nonneg _) (by norm_num)
  have hz : 0 ≤ e+θ/3 := by positivity
  have hd := mul_le_mul_of_nonneg_right hs hz
  nlinarith

/-- Public exact Lyapunov result. -/
theorem lyapunovIdentity : LyapunovIdentity := lyapunov_identity

/-- Public covariance-neighborhood entry bound. -/
theorem tubeEntryBound : TubeEntryBound := tube_entries

end Kalman.Proofs.TrackingCovarianceTube
