import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FloatObservableGain
import Kalman.Proofs.FloatPosteriorPrearray
import Kalman.Proofs.RealObservablePosterior
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Proofs.FloatObservableMean

/-! Posterior covariance arithmetic for full diagonal observation. Original
noise words and gain error remain explicit; all arithmetic stages are derived.
The retained native factor represents an exact Real Gram, separately from any
rounded dense covariance materialization. -/

namespace Kalman.Proofs.FloatObservablePosterior

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.DiagonalStages.Prediction
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.CorrelatedStages.Posterior (TwoStateStages)
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1000000

private theorem product_success (a b : Array Float) (p : ProductProfile 2 2 2 a b 8)
    : ∃ r,
        multiply 2 2 2 a b = .ok r
        ∧ r.size = 4
        ∧ r.all Float.isFinite = true
        ∧ EntrywiseWithin (productRadius 2 8) (matrix 2 2 r)
            (matrix 2 2 a * matrix 2 2 b) := by
  obtain ⟨r, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy 2 2 2 a b
    (fun _ _ => (8 : ℝ)) p.inner_le p.finite_left p.finite_right
    (fun _ _ _ _ => p.upper) (fun _ _ _ _ => p.lower) p.mass
  exact ⟨r, hr, hs, hf, ⟨by norm_num [productRadius], he⟩⟩

/-- Separate arithmetic and Gram perturbation allowances, including cross terms. -/
theorem arithmetic_radius_cap
    : 2
          * (2 * (productRadius 2 8 + 4 * (sumRadius 2 + productRadius 2 8)) * 8
              + (productRadius 2 8 + 4 * (sumRadius 2 + productRadius 2 8)) ^ 2)
        + 2 * (2 * productRadius 2 8 * 4 + (productRadius 2 8) ^ 2)
      ≤ (2 : ℝ) ^ (-38 : Int) := by norm_num [productRadius, sumRadius]

/-- Every actual posterior product/sum succeeds from stored matrix entry
bounds. The prearray Gram error refers to the same stored gain/noise factor. -/
theorem arithmetic_stages (k h l tr : Array Float)
    (hkf : k.all Float.isFinite = true) (hhf : h.all Float.isFinite = true)
    (hlf : l.all Float.isFinite = true) (htf : tr.all Float.isFinite = true)
    (dk : DecodedDiagonal 2 k)
    (hk
      : ∀ i,
          i < 2 → (3 : ℝ) / 8 ≤ value (entry 2 k i i) ∧ value (entry 2 k i i) ≤ 13 / 16)
    (hH : matrix 2 2 h = 1)
    (hl : ∀ i j, i < 2 → j < 2 → |value (entry 2 l i j)| ≤ 2)
    (ht : ∀ i j, i < 2 → j < 2 → |value (entry 2 tr i j)| ≤ 2)
    : ∃ s : TwoStateStages k h l tr,
        EntrywiseWithin ((2 : ℝ) ^ (-38 : Int))
          (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)))
          (FactorRecursion.gram
              (((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrix 2 2 k) * matrix 2 2 l)
            + FactorRecursion.gram (matrix 2 2 k * matrix 2 2 tr)) := by
  have hkb : ∀ i j, i < 2 → j < 2 → |value (entry 2 k i j)| ≤ 13 / 16 := by
    intro i j hi hj
    by_cases hij : i = j
    · subst j
      rw [abs_of_nonneg (by linarith [(hk i hi).1])]
      exact (hk i hi).2
    · rw [dk i j hi hj hij, abs_zero]; norm_num
  have hhb : ∀ i j, i < 2 → j < 2 → |value (entry 2 h i j)| ≤ 1 := by
    intro i j hi hj
    change |matrix 2 2 h ⟨i, hi⟩ ⟨j, hj⟩| ≤ 1
    rw [hH]
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have pkh := FloatGainDomain.product_profile_two k h (13 / 16) 1
    hkf hhf (by norm_num) (by norm_num) (by norm_num) hkb hhb
  obtain ⟨kh, hkh, _, hkhf, ekh⟩ := product_success k h pkh
  rw [hH, Matrix.mul_one] at ekh
  have hkhm : ∀ i j, |matrix 2 2 kh i j| ≤ 7 / 8 := by
    intro i j
    have he := abs_sub_le (matrix 2 2 kh i j) (matrix 2 2 k i j) 0
    simp only [sub_zero] at he
    have he' := ekh.2 i j
    have hm' := hkb i.val j.val i.isLt j.isLt
    change |matrix 2 2 k i j| ≤ _ at hm'
    norm_num [productRadius] at he'
    linarith
  have ps : SumProfile (identity 2) kh 2 true := by
    refine ⟨
      by norm_num,
      by norm_num,
      Flare.Matrix.JacobiInitialization.identity_finite 2,
      hkhf,
      ?_
    ⟩
    intro t hti
    have hti' : t < 4 := by simpa [identity, Flare.Matrix.Dense.identity] using hti
    have hi : t / 2 < 2 := by omega
    have hj : t % 2 < 2 := by omega
    have hm := hkhm ⟨t / 2, hi⟩ ⟨t % 2, hj⟩
    have hid : |value ((identity 2).getD t 0.0)| ≤ (1 : ℝ) := by
      interval_cases t <;> norm_num [identity, Flare.Matrix.Dense.identity,
        Flare.Binary64.Arithmetic.zero_value, Flare.Binary64.Arithmetic.one_value]
    have hidx : t / 2 * 2 + t % 2 = t := by omega
    change |value (kh.getD (t / 2 * 2 + t % 2) 0.0)| ≤ _ at hm
    rw [hidx] at hm
    simpa only [↓reduceIte, ← sub_eq_add_neg, show (2 : ℝ)^(2 : Int) = 4 by norm_num]
      using (abs_sub _ _).trans ((add_le_add hid hm).trans (by norm_num))
  obtain ⟨w, hw, _, hwf, _⟩ := FloatDenseError.sub_accuracy (identity 2) kh 2
    ps.exponent_lower ps.exponent_upper ps.finite_left ps.finite_right
    (by simpa only [↓reduceIte, ← sub_eq_add_neg] using ps.magnitude)
  have ew := FloatJosephError.subtract_within (n := 2) (m := 2) ps (by simp [identity, Flare.Matrix.Dense.identity]) hw
  rw [FloatJosephError.identity_matrix] at ew
  have ewideal := within_trans ew (within_sub (within_refl (1 : Matrix (Fin 2) (Fin 2) ℝ)) ekh)
  simp only [zero_add] at ewideal
  have hwi : ∀ i j, |((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrix 2 2 k) i j| ≤ 5 / 8 := by
    rw [FloatDiagonalStorage.matrix_diagonal 2 k dk, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      have hb := hk i.val i.isLt
      change (3 : ℝ) / 8 ≤ matrix 2 2 k i i ∧ matrix 2 2 k i i ≤ 13 / 16 at hb
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [Matrix.diagonal_apply_ne _ hij, abs_zero]; norm_num
  have hwm : ∀ i j, |matrix 2 2 w i j| ≤ 3 / 4 := by
    intro i j
    have he := abs_sub_le (matrix 2 2 w i j) ((1 - matrix 2 2 k) i j) 0
    simp only [sub_zero] at he
    have he' := ewideal.2 i j
    have hm := hwi i j
    norm_num [sumRadius, productRadius] at he'
    simp only [Matrix.sub_apply] at he hm
    linarith
  have pwl := FloatGainDomain.product_profile_two w l (3 / 4) 2 hwf hlf
    (by norm_num) (by norm_num) (by norm_num)
    (fun i j hi hj => hwm ⟨i, hi⟩ ⟨j, hj⟩) hl
  obtain ⟨wl, hwl, _, _, ewl⟩ := product_success w l pwl
  have pkt := FloatGainDomain.product_profile_two k tr (13 / 16) 2 hkf htf
    (by norm_num) (by norm_num) (by norm_num) hkb ht
  obtain ⟨ktr, hktr, _, _, ekt⟩ := product_success k tr pkt
  have ewlideal := within_trans ewl (within_mul_right ewideal (matrix 2 2 l) (by norm_num : (0 : ℝ) ≤ 2)
    (fun i j => hl i.val j.val i.isLt j.isLt))
  have hgwl := FloatPrearray.gram_within ewlideal (by norm_num : (0 : ℝ) ≤ 8)
    (by
      intro i j
      exact (product_magnitude ((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrix 2 2 k)
        (matrix 2 2 l) (5 / 8) 2 hwi (fun i j => hl i.val j.val i.isLt j.isLt) i j).trans (by norm_num))
  have hgkt := FloatPrearray.gram_within ekt (by norm_num : (0 : ℝ) ≤ 4)
    (by
      intro i j
      exact (product_magnitude (matrix 2 2 k) (matrix 2 2 tr) (13 / 16) 2
        (fun i j => hkb i.val j.val i.isLt j.isLt) (fun i j => ht i.val j.val i.isLt j.isLt) i j).trans (by norm_num))
  have hpre := within_add hgwl hgkt
  let s : TwoStateStages k h l tr := ⟨kh, w, wl, ktr, pkh, hkh, ps, hw, pwl, hwl, pkt, hktr⟩
  refine ⟨s, by positivity, ?_⟩
  intro i j
  rw [FloatPrearray.fromCols_gram 2 2 2 wl ktr]
  have he := hpre.2 i j
  norm_num only [Nat.cast_ofNat] at he
  exact he.trans (by convert arithmetic_radius_cap using 1; ring)

/-- No linear gain term remains in the exact diagonal Joseph reference. -/
theorem reference_accuracy (p r k : Fin 2 → ℝ)
    (hp : ∀ i, 15 / 16 ≤ p i) (hP : ∀ i, p i ≤ 13 / 4)
    (hr : ∀ i, 1 ≤ r i) (hR : ∀ i, r i ≤ 3 / 2)
    (hk
      : ∀ i, |k i - DiagonalObservation.optimalGain (p i) (r i)| ≤ (2 : ℝ) ^ (-27 : Int))
    : EntrywiseWithin ((2 : ℝ) ^ (-50 : Int))
        ((1 - diagonal k) * diagonal p * (1 - diagonal k).transpose
          + diagonal k * diagonal r * (diagonal k).transpose)
        (diagonal (fun i => DiagonalObservation.posteriorVariance (p i) (r i)))
      ∧ (diagonal (fun i => DiagonalObservation.posteriorVariance (p i) (r i))
          - (15 / 31 : ℝ) • 1).PosSemidef
      ∧ (∀ i, DiagonalObservation.posteriorVariance (p i) (r i) ≤ 39 / 38) := by
  rw [RealObservablePosterior.joseph_diagonal]
  refine ⟨⟨by positivity, ?_⟩, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      exact RealObservablePosterior.joseph_gain_accuracy _ _ _ (hp i) (hP i) (hr i) (hR i) (hk i)
    · simp only [diagonal_apply_ne _ hij, sub_self, abs_zero]
      positivity
  · rw [← diagonal_one, ← diagonal_smul, diagonal_sub]
    exact Matrix.PosSemidef.diagonal (fun i => by
      simpa using sub_nonneg.mpr
        (RealObservablePosterior.posterior_variance_bounds _ _ (hp i) (hP i) (hr i) (hR i)).1)
  · intro i
    exact (RealObservablePosterior.posterior_variance_bounds _ _ (hp i) (hP i) (hr i) (hR i)).2

/-- Original noise factorization succeeds, is diagonal, and has a quantified
backward error against the original stored covariance words. -/
theorem noise_factor (r tr : Array Float) (d : NoiseDomain r)
    (htr : cholesky 2 r = .ok tr)
    : tr.all Float.isFinite = true
      ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 tr i j)| ≤ 2)
      ∧ DecodedDiagonal 2 tr
      ∧ EntrywiseWithin ((2 : ℝ) ^ (-42 : Int)) (FactorRecursion.gram (matrix 2 2 tr))
          (matrix 2 2 r) := by
  obtain ⟨tr', _, p, _, _, _⟩ := FloatCholeskyDomain.cholesky_profile r d.covariance
  have heq : tr' = tr := Except.ok.inj (p.execution.symm.trans htr)
  subst tr'
  have he := FloatCholeskyFactor.factor_backward_error 2 r tr 8 (1 / 2) 2 p
  have dt := FloatDiagonalStorage.cholesky_diagonal_two r d.covariance d.diagonal tr htr
  refine ⟨
    p.finite_lower,
    ?_,
    dt,
    ⟨by positivity, fun i j => (he.2 i j).trans FloatCholeskyDomain.backward_radius_cap⟩
  ⟩
  intro i j hi hj
  by_cases hij : i = j
  · subst j
    exact p.diagonal_bound i hi
  · rw [dt i j hi hj hij, abs_zero]; norm_num

/-- Derive the original-R and optimal-gain covariance reference from the same
stored prior, with prearray error at most 2^-36. -/
theorem prearray_accuracy (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (di : DecodedDiagonal 2 prior.lower)
    (k tr : Array Float) (dk : DecodedDiagonal 2 k)
    (hk : ∀ i j, |matrix 2 2 k i j| ≤ 13 / 16)
    (ek
      : EntrywiseWithin ((2 : ℝ) ^ (-27 : Int)) (matrix 2 2 k)
          (FactorRecursion.gram (matrix 2 2 prior.lower)
            * (FactorRecursion.gram (matrix 2 2 prior.lower)
                + matrix 2 2 input.measurementNoise)⁻¹))
    (htr : cholesky 2 input.measurementNoise = .ok tr)
    (s : TwoStateStages k input.observation prior.lower tr)
    (es
      : EntrywiseWithin ((2 : ℝ) ^ (-38 : Int))
          (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)))
          (FactorRecursion.gram ((1 - matrix 2 2 k) * matrix 2 2 prior.lower)
            + FactorRecursion.gram (matrix 2 2 k * matrix 2 2 tr)))
    : EntrywiseWithin ((2 : ℝ) ^ (-36 : Int))
        (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)))
        (diagonal
          (fun i =>
            DiagonalObservation.posteriorVariance
              (FactorRecursion.gram (matrix 2 2 prior.lower) i i)
              (matrix 2 2 input.measurementNoise i i)))
      ∧ (diagonal
            (fun i =>
              DiagonalObservation.posteriorVariance
                (FactorRecursion.gram (matrix 2 2 prior.lower) i i)
                (matrix 2 2 input.measurementNoise i i))
          - (15 / 31 : ℝ) • 1).PosSemidef
      ∧ (∀ i,
          DiagonalObservation.posteriorVariance
            (FactorRecursion.gram (matrix 2 2 prior.lower) i i)
            (matrix 2 2 input.measurementNoise i i)
          ≤ 39 / 38) := by
  obtain ⟨_, _, _, er⟩ := noise_factor input.measurementNoise tr d.observation.noise htr
  have en := within_mul_right (within_mul_left (matrix 2 2 k) er (by norm_num : (0 : ℝ) ≤ 13 / 16) hk)
    (matrix 2 2 k).transpose (by norm_num : (0 : ℝ) ≤ 13 / 16) (fun i j => hk j i)
  have en' : EntrywiseWithin (2 * (2 * (13 / 16) * (2 : ℝ)^(-42 : Int)) * (13 / 16))
      (FactorRecursion.gram (matrix 2 2 k * matrix 2 2 tr))
      (matrix 2 2 k * matrix 2 2 input.measurementNoise * (matrix 2 2 k).transpose) := by
    simpa only [FactorStructure.gram_mul, Nat.cast_ofNat] using en
  have eg := within_trans es (within_add
    (within_refl (FactorRecursion.gram ((1 - matrix 2 2 k) * matrix 2 2 prior.lower))) en')
  simp only [FactorStructure.gram_mul] at eg
  have dp : FactorRecursion.gram (matrix 2 2 prior.lower)
      = diagonal (fun i => FactorRecursion.gram (matrix 2 2 prior.lower) i i) := by
    rw [FloatDiagonalStorage.gram_diagonal 2 prior.lower di]
    simp only [diagonal_apply_eq]
  have dr := FloatDiagonalStorage.matrix_diagonal 2 input.measurementNoise d.observation.noise.diagonal
  have dkm := FloatDiagonalStorage.matrix_diagonal 2 k dk
  have hp : ∀ i, 15 / 16 ≤ FactorRecursion.gram (matrix 2 2 prior.lower) i i := by
    intro i
    have hf := d.covariance_floor.diag_nonneg (i := i)
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one, sub_nonneg] using hf
  have hr : ∀ i : Fin 2, 1 ≤ matrix 2 2 input.measurementNoise i i :=
    fun i => d.observation.noise.covariance.diagonal_lower i.val i.isLt
  have hR : ∀ i : Fin 2, matrix 2 2 input.measurementNoise i i ≤ 3 / 2 :=
    fun i => d.observation.noise.diagonal_cap i.val i.isLt
  rw [FloatObservableGain.ideal_gain_diagonal input prior d di] at ek
  have ke : ∀ i, |matrix 2 2 k i i - DiagonalObservation.optimalGain
      (FactorRecursion.gram (matrix 2 2 prior.lower) i i) (matrix 2 2 input.measurementNoise i i)|
        ≤ (2 : ℝ)^(-27 : Int) := by
    intro i
    simpa only [diagonal_apply_eq, DiagonalObservation.optimalGain] using ek.2 i i
  obtain ⟨ej, hf, hb⟩ := reference_accuracy _ _ _ hp d.covariance_diagonal_cap hr hR ke
  have eg' := eg
  rw [dp, dr, dkm] at eg'
  have et := within_trans eg' ej
  exact ⟨⟨by positivity, fun i j => (et.2 i j).trans (by norm_num)⟩, hf, hb⟩

/-- Original-input margins derive posterior QR success at budget 15/8.
Both the covariance floor and row-energy headroom concern exact decoding of
the rounded prearray, before the QR computation runs. -/
theorem prearray_domain (k h l tr : Array Float) (s : TwoStateStages k h l tr)
    (p : Fin 2 → ℝ)
    (he
      : EntrywiseWithin ((2 : ℝ) ^ (-36 : Int))
          (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr))) (diagonal p))
    (hf : (diagonal p - (15 / 31 : ℝ) • 1).PosSemidef) (hb : ∀ i, p i ≤ 39 / 38)
    : GramFactorInputDomain 2 4 (fromCols 2 2 2 s.wl s.ktr) (15 / 8)
      ∧ (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr))
          - (15 / 32 : ℝ) • 1).PosSemidef
      ∧ (∀ i,
          FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)) i i
          ≤ 17 / 16) := by
  have hg := CovarianceStructure.gram_posSemidef (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr))
  have hs := lower_bound_of_error _ _ (15 / 31) ((2 : ℝ)^(-36 : Int)) hf hg.isHermitian he
  have hpad : 0 ≤ (15 / 31 : ℝ) - 2 * (2 : ℝ)^(-36 : Int) - 15 / 32 := by norm_num
  have hfloor : (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr))
      - (15 / 32 : ℝ) • 1).PosSemidef := by
    convert hs.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad) using 1
    norm_num
    module
  have henergy : ∀ i, FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)) i i ≤ 17 / 16 := by
    intro i
    have hd := (abs_le.mp (he.2 i i)).2
    simp only [diagonal_apply_eq] at hd
    norm_num at hd
    linarith [hb i]
  refine ⟨
    ⟨
      by decide,
      by decide,
      FloatPrearray.fromCols_size 2 2 2 s.wl s.ktr,
      FloatPrearray.fromCols_finite 2 2 2 s.wl s.ktr
        (FloatJosephError.product_within s.wl_product s.compute_wl).2.1
        (FloatJosephError.product_within s.ktr_product s.compute_ktr).2.1,
      ?_,
      ?_,
      ?_,
      ?_
    ⟩,
    hfloor,
    henergy
  ⟩
  · exact (show (2 : ℝ)^(-896 : Int) ≤ 1 by
      simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-896 : Int) ≤ 0)).trans (by norm_num)
  · apply le_trans (by norm_num : (15 : ℝ) / 8 ≤ 2)
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : Int) ≤ 900)
  · intro i
    have he' := (henergy i).trans (by norm_num : (17 : ℝ) / 16 ≤ (15 / 8)^2 / 2)
    simpa only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using he'
  · convert hfloor.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : 0 ≤ (15 / 32 : ℝ) - (15 / 8)^2 / 8)) using 1
    norm_num
    module

theorem local_covariance_radius_cap
    : Kalman.Proofs.DiagonalStages.Posterior.localCovarianceRadius
      ≤ (2 : ℝ) ^ (-29 : Int) := by
  simp only [Kalman.Proofs.DiagonalStages.Posterior.localCovarianceRadius,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius,
    columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Rounded posterior blocks preserve decoded diagonality in every actual
product/subtraction and in signed QR retention. -/
theorem factor_diagonal (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (di : DecodedDiagonal 2 prior.lower)
    (k tr lower : Array Float) (hkf : k.all Float.isFinite = true)
    (dk : DecodedDiagonal 2 k) (htr : cholesky 2 input.measurementNoise = .ok tr)
    (s : TwoStateStages k input.observation prior.lower tr)
    (hl
      : Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
          (fromCols 2 2 2 s.wl s.ktr)
        = .ok lower)
    : DecodedDiagonal 2 lower := by
  have hdh := FloatObservableDiagonal.observation_diagonal input d.observation
  have hdkh := FloatDiagonalStorage.multiply_diagonal_two k input.observation s.kh hkf
    d.observation.observation_finite dk hdh s.compute_kh
  have hdi : DecodedDiagonal 2 (identity 2) := by
    intro i j hi hj hij
    change matrix 2 2 (identity 2) ⟨i, hi⟩ ⟨j, hj⟩ = 0
    rw [FloatJosephError.identity_matrix]
    exact Matrix.one_apply_ne (fun h => hij (congrArg Fin.val h))
  have hdw := FloatDiagonalStorage.sub_diagonal_two (identity 2) s.kh s.w s.w_sum
    (by simp [identity, Flare.Matrix.Dense.identity]) hdi hdkh s.compute_w
  have hdwl := FloatDiagonalStorage.multiply_diagonal_two s.w prior.lower s.wl
    s.wl_product.finite_left d.factor_finite hdw di s.compute_wl
  obtain ⟨htf, _, dt, _⟩ := noise_factor input.measurementNoise tr d.observation.noise htr
  have hdkt := FloatDiagonalStorage.multiply_diagonal_two k tr s.ktr hkf htf dk dt s.compute_ktr
  exact FloatQRDiagonal.gramFactor_diagonal_two s.wl s.ktr lower
    (FloatJosephError.product_within s.wl_product s.compute_wl).2.1
    (FloatJosephError.product_within s.ktr_product s.compute_ktr).2.1 hdwl hdkt hl

/-- Gain, posterior arithmetic and QR all succeed from the local stored-input
domain. Returned exact covariance is diagonal and strictly PD, has floor 7/16,
diagonal cap 17/16 and error 2^-29 against the original-R ideal correction.
No stage run, operand profile or desired error is an input premise. -/
theorem factor_accuracy (input : Input.Model) (prior : Input.FactorState)
    (hn : input.stateDimension = 2) (d : InnovationDomain input prior)
    (di : DecodedDiagonal 2 prior.lower)
    : ∃ innovation : InnovationProfile input prior,
      ∃ gain : GainProfile innovation,
      ∃ s : TwoStateStages (gainArray gain) input.observation prior.lower innovation.tr,
      ∃ lower,
        gain.gainBound = 13 / 16
        ∧ DecodedDiagonal 2 (gainArray gain)
        ∧ solveCholesky input.measurementDimension input.stateDimension innovation.lower
            (transpose input.stateDimension input.measurementDimension gain.pht)
          = .ok gain.solution
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-27 : Int))
            (matrix input.stateDimension input.measurementDimension (gainArray gain))
            (CovarianceRecursion.gain (model input)
              (factorState input.stateDimension prior))
        ∧ (∀ i,
            i < 2
            → (3 : ℝ) / 8 ≤ value (entry 2 (gainArray gain) i i)
              ∧ value (entry 2 (gainArray gain) i i) ≤ 13 / 16)
        ∧ Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
            (fromCols 2 2 2 s.wl s.ktr)
          = .ok lower
        ∧ lower.size = 4
        ∧ lower.all Float.isFinite = true
        ∧ FactorRecursion.LowerPositive (matrix 2 2 lower)
        ∧ DecodedDiagonal 2 lower
        ∧ (FactorRecursion.gram (matrix 2 2 lower)).PosDef
        ∧ (FactorRecursion.gram (matrix 2 2 lower) - (7 / 16 : ℝ) • 1).PosSemidef
        ∧ (∀ i, FactorRecursion.gram (matrix 2 2 lower) i i ≤ 17 / 16)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 lower i j)| ≤ 9 / 8)
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-29 : Int))
            (FactorRecursion.gram (matrix 2 2 lower))
            (diagonal
              (fun i =>
                DiagonalObservation.posteriorVariance
                  (FactorRecursion.gram (matrix 2 2 prior.lower) i i)
                  (matrix 2 2 input.measurementNoise i i))) := by
  obtain ⟨innovation, gain, _, _, _, _, hg, dk, hsolve, ek, hk⟩ :=
    FloatObservableGain.gain_accuracy input prior hn d di
  have hm := d.observation.measurement_dimension
  have hkf : (gainArray gain).all Float.isFinite = true :=
    (Flare.Matrix.Multiplication.transpose_storage _ _ gain.solution gain.finite_solution).2.1
  have htr : cholesky 2 input.measurementNoise = .ok innovation.tr := by
    simpa only [hm] using innovation.noise.execution
  obtain ⟨htf, htb, _, _⟩ := noise_factor input.measurementNoise innovation.tr d.observation.noise htr
  obtain ⟨s, es⟩ := arithmetic_stages (gainArray gain) input.observation prior.lower innovation.tr
    hkf d.observation.observation_finite d.factor_finite htf dk hk
    d.observation.observation_identity d.factor_bound htb
  have ek' : EntrywiseWithin ((2 : ℝ)^(-27 : Int)) (matrix 2 2 (gainArray gain))
      (FactorRecursion.gram (matrix 2 2 prior.lower)
        * (FactorRecursion.gram (matrix 2 2 prior.lower) + matrix 2 2 input.measurementNoise)⁻¹) := by
    have e := ek
    simp only [CovarianceRecursion.gain, CovarianceRecursion.innovationCovariance, model, factorState] at e
    exact FloatObservableGain.full_observation_gain_reference _ _ _ _ _ _ _ hn hm
      d.observation.observation_identity e
  have hkb : ∀ i j, |matrix 2 2 (gainArray gain) i j| ≤ 13 / 16 := by
    intro i j
    by_cases hij : i = j
    · subst j
      have h := hk i.val i.isLt
      change (3 : ℝ) / 8 ≤ matrix 2 2 (gainArray gain) i i
        ∧ matrix 2 2 (gainArray gain) i i ≤ 13 / 16 at h
      exact abs_le.mpr ⟨by linarith, h.2⟩
    · have hz := dk i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
      change matrix 2 2 (gainArray gain) i j = 0 at hz
      rw [hz, abs_zero]; norm_num
  obtain ⟨epre, hfloor, henergy⟩ := prearray_accuracy input prior d di (gainArray gain)
    innovation.tr dk hkb ek' htr s es
  obtain ⟨qr, _, _⟩ := prearray_domain _ _ _ _ s _ epre hfloor henergy
  obtain ⟨_, _, lower, hl, hs, hf, hp, hpd, eqr⟩ :=
    FloatQRInitialDomain.gramFactor_accuracy_initial 2 4 _ (15 / 8) qr
  have ec := within_trans eqr epre
  have ec' : EntrywiseWithin ((2 : ℝ)^(-29 : Int)) (FactorRecursion.gram (matrix 2 2 lower))
      (diagonal (fun i => DiagonalObservation.posteriorVariance
        (FactorRecursion.gram (matrix 2 2 prior.lower) i i) (matrix 2 2 input.measurementNoise i i))) :=
    ⟨by positivity, fun i j => (ec.2 i j).trans local_covariance_radius_cap⟩
  have hspectral := lower_bound_of_error _ _ (15 / 31) ((2 : ℝ)^(-29 : Int)) hfloor hpd.isHermitian ec'
  have hpad : 0 ≤ (15 / 31 : ℝ) - 2 * (2 : ℝ)^(-29 : Int) - 7 / 16 := by norm_num
  have hreturned : (FactorRecursion.gram (matrix 2 2 lower) - (7 / 16 : ℝ) • 1).PosSemidef := by
    convert hspectral.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad) using 1
    norm_num
    module
  have hb : ∀ i, FactorRecursion.gram (matrix 2 2 lower) i i ≤ 17 / 16 := by
    intro i
    have he := (abs_le.mp (ec'.2 i i)).2
    simp only [diagonal_apply_eq] at he
    norm_num at he
    linarith [henergy i]
  refine ⟨innovation, gain, s, lower, hg, dk, hsolve, ek, hk, hl, hs, hf, hp,
    factor_diagonal input prior d di _ _ _ hkf dk htr s hl, hpd, hreturned, hb, ?_, ec'⟩
  intro i j hi hj
  have hsq := FloatQRDomain.columnGram_entry_sq_le (matrix 2 2 lower).transpose ⟨j, hj⟩ ⟨i, hi⟩
  change (value (entry 2 lower i j))^2 ≤ FactorRecursion.gram (matrix 2 2 lower) ⟨i, hi⟩ ⟨i, hi⟩ at hsq
  nlinarith [hb ⟨i, hi⟩, sq_abs (value (entry 2 lower i j)), abs_nonneg (value (entry 2 lower i j))]

private theorem covariance_reference (n m : Nat) (ε : ℝ)
    (f h q r lower mean measurement output : Array Float) (hn : n = 2) (hm : m = 2)
    (hH : matrix 2 2 h = 1) (dp : DecodedDiagonal 2 lower) (dr : DecodedDiagonal 2 r)
    (hp : ∀ i : Fin 2, 0 ≤ FactorRecursion.gram (matrix 2 2 lower) i i)
    (hr : ∀ i : Fin 2, 0 < matrix 2 2 r i i)
    (e
      : EntrywiseWithin ε (FactorRecursion.gram (matrix 2 2 output))
          (diagonal
            (fun i =>
              DiagonalObservation.posteriorVariance
                (FactorRecursion.gram (matrix 2 2 lower) i i) (matrix 2 2 r i i))))
    : EntrywiseWithin ε (FactorRecursion.gram (matrix n n output))
        (CovarianceRecursion.update .joseph
          (⟨matrix n n f, matrix m n h, matrix n n q, matrix m m r⟩
            : LinearModel.Model n m)
          (⟨vector n mean, FactorRecursion.gram (matrix n n lower)⟩ : LinearModel.State n)
          (vector m measurement)).covariance := by
  subst n m
  have hP : FactorRecursion.gram (matrix 2 2 lower)
      = diagonal (fun i => FactorRecursion.gram (matrix 2 2 lower) i i) := by
    rw [FloatDiagonalStorage.gram_diagonal 2 lower dp]
    simp only [diagonal_apply_eq]
  have hR := FloatDiagonalStorage.matrix_diagonal 2 r dr
  have eq := congrArg LinearModel.State.covariance (RealDiagonalObservation.update_eq .joseph
    (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 0) (fun i => matrix 2 2 r i i)
    (vector 2 measurement) (vector 2 mean) (fun i => FactorRecursion.gram (matrix 2 2 lower) i i) hp hr)
  simp only [CovarianceRecursion.update, CovarianceRecursion.correctedCovariance,
    CovarianceRecursion.joseph, CovarianceRecursion.gain, CovarianceRecursion.innovationCovariance,
    DiagonalObservation.model, DiagonalObservation.state, mul_one, one_mul,
    transpose_one] at eq
  have he := e
  rw [← eq] at he
  simp only [CovarianceRecursion.update, CovarianceRecursion.correctedCovariance,
    CovarianceRecursion.joseph, CovarianceRecursion.gain, CovarianceRecursion.innovationCovariance,
    hH, mul_one, one_mul, transpose_one]
  rw [hP, hR]
  exact he

/-- Complete native measurement correction from the original local domain:
success, validation, diagonal strict-PD exact covariance, error 2^-29 in
covariance and 9·2^-29 in mean, and returned bounds for the next prediction.
The ideal reference starts from the same stored prior and original H/R/z. -/
theorem correction_accuracy_and_bounds_sharp (input : Input.Model)
    (prior : Input.FactorState)
    (d : Kalman.Proofs.DiagonalStages.Mean.TwoStateDomain input prior)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.updateUnchecked input prior = .ok output
        ∧ Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
            ((2 : ℝ) ^ (-29 : Int)) (9 * (2 : ℝ) ^ (-29 : Int)) input.stateDimension
            output
            (CovarianceRecursion.update .joseph (model input)
              (factorState input.stateDimension prior)
              (vector input.measurementDimension input.measurement))
        ∧ DecodedDiagonal 2 output.lower
        ∧ (FactorRecursion.gram (matrix 2 2 output.lower)).PosDef
        ∧ (FactorRecursion.gram (matrix 2 2 output.lower) - (7 / 16 : ℝ) • 1).PosSemidef
        ∧ (∀ i, FactorRecursion.gram (matrix 2 2 output.lower) i i ≤ 17 / 16)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 output.lower i j)| ≤ 9 / 8)
        ∧ (∀ i, i < 2 → |value (output.mean.getD i 0.0)| ≤ 9 / 8) := by
  have hn := d.state_dimension
  have hm := d.observation.measurement_dimension
  obtain ⟨innovation, gain, s, lower, _, dk, hsolve, ek, hk, hl, hs, hf, hp,
    dl, hpd, hfloor, hb, hfactor, ec⟩ := factor_accuracy input prior hn d.toInnovationDomain d.diagonal
  obtain ⟨mp, _, _, _, _, hms, hmf, hmb, eval⟩ := FloatObservableMean.mean_profile input prior
    innovation gain hn d.toInnovationDomain d.vectors dk hk
  have em := FloatObservableMean.mean_accuracy_sharp input prior d innovation gain mp dk ek eval
  have pc : ∀ i : Fin 2, 0 ≤ FactorRecursion.gram (matrix 2 2 prior.lower) i i :=
    fun i => (CovarianceStructure.gram_posSemidef (matrix 2 2 prior.lower)).diag_nonneg
  have rc : ∀ i : Fin 2, 0 < matrix 2 2 input.measurementNoise i i :=
    fun i => (by norm_num : (0 : ℝ) < 1).trans_le (d.observation.noise.covariance.diagonal_lower i.val i.isLt)
  have ec' := covariance_reference _ _ _ input.transition input.observation input.processNoise
    input.measurementNoise prior.lower prior.mean input.measurement lower hn hm
    d.observation.observation_identity d.diagonal d.observation.noise.diagonal pc rc ec
  have htr : cholesky input.measurementDimension input.measurementNoise = .ok innovation.tr :=
    innovation.noise.execution
  have hinc : multiply input.stateDimension input.measurementDimension 1
      (transpose input.measurementDimension input.stateDimension gain.solution) mp.residual = .ok mp.increment :=
    mp.computeIncrement
  have hkh : multiply input.stateDimension input.measurementDimension input.stateDimension
      (transpose input.measurementDimension input.stateDimension gain.solution) input.observation = .ok s.kh := by
    simpa only [gainArray, hn, hm] using s.compute_kh
  have hw := s.compute_w
  have hwl : multiply input.stateDimension input.stateDimension input.stateDimension s.w prior.lower = .ok s.wl := by
    simpa only [hn] using s.compute_wl
  have hktr : multiply input.stateDimension input.measurementDimension input.measurementDimension
      (transpose input.measurementDimension input.stateDimension gain.solution) innovation.tr = .ok s.ktr := by
    simpa only [gainArray, hn, hm] using s.compute_ktr
  have hqr : Kalman.Implementation.OrthogonalFactorization.gramFactor input.stateDimension
      (input.stateDimension + input.measurementDimension)
      (fromCols input.stateDimension input.stateDimension input.measurementDimension s.wl s.ktr) = .ok lower := by
    simpa only [hn, hm, show 2 + 2 = 4 from rfl] using hl
  have hw' : sub (identity input.stateDimension) s.kh = .ok s.w := by simpa only [hn] using hw
  have hp' : FactorRecursion.LowerPositive (matrix input.stateDimension input.stateDimension lower) := by
    rw [hn]
    exact hp
  refine ⟨
    ⟨mp.mean, lower⟩,
    ?_,
    ⟨?_, ec', by positivity, em⟩,
    dl,
    hpd,
    hfloor,
    hb,
    hfactor,
    hmb
  ⟩
  · simp [Kalman.Implementation.SquareRootFilter.updateUnchecked, htr,
      innovation.computeProduct, innovation.computeQR, gain.computeProduct, hsolve,
      mp.computeProjected, mp.computeResidual, hinc, mp.computeMean, hkh, hw', hwl, hktr, hqr,
      bind, Except.bind, pure, Except.pure]
  · exact FloatFactorValidity.factor_validate_complete input.stateDimension ⟨mp.mean, lower⟩
      (by simpa only [hn] using hms) (by simpa only [hn] using hs) hmf hf
      hp'

/-- Compatibility mean allowance for the same complete local correction. -/
theorem correction_accuracy_and_bounds (input : Input.Model) (prior : Input.FactorState)
    (d : Kalman.Proofs.DiagonalStages.Mean.TwoStateDomain input prior)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.updateUnchecked input prior = .ok output
        ∧ Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
            ((2 : ℝ) ^ (-29 : Int)) ((2 : ℝ) ^ (-25 : Int)) input.stateDimension output
            (CovarianceRecursion.update .joseph (model input)
              (factorState input.stateDimension prior)
              (vector input.measurementDimension input.measurement))
        ∧ DecodedDiagonal 2 output.lower
        ∧ (FactorRecursion.gram (matrix 2 2 output.lower)).PosDef
        ∧ (FactorRecursion.gram (matrix 2 2 output.lower) - (7 / 16 : ℝ) • 1).PosSemidef
        ∧ (∀ i, FactorRecursion.gram (matrix 2 2 output.lower) i i ≤ 17 / 16)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 output.lower i j)| ≤ 9 / 8)
        ∧ (∀ i, i < 2 → |value (output.mean.getD i 0.0)| ≤ 9 / 8) := by
  obtain ⟨output, hr, ha, hd, hp, hf, hc, hb, hm⟩ := correction_accuracy_and_bounds_sharp input prior d
  exact ⟨
    output,
    hr,
    ⟨ha.1, ha.2.1, by positivity, fun i => (ha.2.2.2 i).trans (by norm_num)⟩,
    hd,
    hp,
    hf,
    hc,
    hb,
    hm
  ⟩

end Kalman.Proofs.FloatObservablePosterior
