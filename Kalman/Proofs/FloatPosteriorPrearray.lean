import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.FloatMeanDomain
import Kalman.Proofs.PosteriorStructure

/-! Rounded posterior arithmetic and the QR prearray's original-input domain.
Rounding relative to the same stored gain/noise factor stays explicit. -/

namespace Kalman.Proofs.FloatPosteriorPrearray

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.CorrelatedStages.Posterior
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
theorem prearray_radius_cap
    : 2
          * (2 * (productRadius 2 8 + 4 * (sumRadius 2 + productRadius 2 8)) * 8
              + (productRadius 2 8 + 4 * (sumRadius 2 + productRadius 2 8)) ^ 2)
        + 2 * (2 * productRadius 2 8 * 2 + (productRadius 2 8) ^ 2)
      ≤ (2 : ℝ) ^ (-38 : Int) := by norm_num [productRadius, sumRadius]

/-- Every actual posterior product/sum succeeds from stored matrix entry
bounds. The prearray Gram error refers to the same stored gain/noise factor. -/
theorem arithmetic_stages (k h l tr : Array Float)
    (hkf : k.all Float.isFinite = true) (hhf : h.all Float.isFinite = true)
    (hlf : l.all Float.isFinite = true) (htf : tr.all Float.isFinite = true)
    (hk : ∀ i j, i < 2 → j < 2 → |value (entry 2 k i j)| ≤ 1 / 6)
    (hh : ∀ i j, i < 2 → j < 2 → |value (entry 2 h i j)| ≤ 1 / 64)
    (hl : ∀ i j, i < 2 → j < 2 → |value (entry 2 l i j)| ≤ 2)
    (ht : ∀ i j, i < 2 → j < 2 → |value (entry 2 tr i j)| ≤ 2)
    : ∃ s : TwoStateStages k h l tr,
        EntrywiseWithin ((2 : ℝ) ^ (-38 : Int))
          (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)))
          (FactorRecursion.gram
              (((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrix 2 2 k * matrix 2 2 h)
                * matrix 2 2 l)
            + FactorRecursion.gram (matrix 2 2 k * matrix 2 2 tr)) := by
  have pkh := FloatGainDomain.product_profile_two k h (1 / 6) (1 / 64)
    hkf hhf (by norm_num) (by norm_num) (by norm_num) hk hh
  obtain ⟨kh, hkh, _, hkhf, ekh⟩ := product_success k h pkh
  have hkhm : ∀ i j, |matrix 2 2 kh i j| ≤ 1 / 128 := by
    have hm := product_magnitude (matrix 2 2 k) (matrix 2 2 h) (1 / 6) (1 / 64)
      (fun i j => hk i.val j.val i.isLt j.isLt) (fun i j => hh i.val j.val i.isLt j.isLt)
    intro i j
    have he := abs_sub_le (matrix 2 2 kh i j) ((matrix 2 2 k * matrix 2 2 h) i j) 0
    simp only [sub_zero] at he
    have he' := ekh.2 i j
    have hm' := hm i j
    norm_num [productRadius] at he' hm'
    linarith only [he, he', hm']
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
  have hwm : ∀ i j, |matrix 2 2 w i j| ≤ 33 / 32 := by
    intro i j
    have hid : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      simp [Matrix.one_apply]; split_ifs <;> norm_num
    have hm := (abs_sub _ _).trans (add_le_add hid (hkhm i j))
    have he := abs_sub_le (matrix 2 2 w i j) ((1 - matrix 2 2 kh) i j) 0
    simp only [sub_zero, Matrix.sub_apply] at he
    have he' := ew.2 i j
    norm_num [sumRadius] at he'
    linarith only [he, he', hm]
  have pwl := FloatGainDomain.product_profile_two w l (33 / 32) 2 hwf hlf
    (by norm_num) (by norm_num) (by norm_num)
    (fun i j hi hj => hwm ⟨i, hi⟩ ⟨j, hj⟩) hl
  obtain ⟨wl, hwl, _, _, ewl⟩ := product_success w l pwl
  have pkt := FloatGainDomain.product_profile_two k tr (1 / 6) 2 hkf htf
    (by norm_num) (by norm_num) (by norm_num) hk ht
  obtain ⟨ktr, hktr, _, _, ekt⟩ := product_success k tr pkt
  have ewlideal := within_trans ewl (within_mul_right ewideal (matrix 2 2 l) (by norm_num : (0 : ℝ) ≤ 2)
    (fun i j => hl i.val j.val i.isLt j.isLt))
  have hwi : ∀ i j, |((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrix 2 2 k * matrix 2 2 h) i j| ≤ 2 := by
    intro i j
    have hid : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      simp [Matrix.one_apply]; split_ifs <;> norm_num
    have hm := product_magnitude (matrix 2 2 k) (matrix 2 2 h) (1 / 6) (1 / 64)
      (fun i j => hk i.val j.val i.isLt j.isLt) (fun i j => hh i.val j.val i.isLt j.isLt) i j
    exact (abs_sub _ _).trans ((add_le_add hid hm).trans (by norm_num))
  have hgwl := FloatPrearray.gram_within ewlideal (by norm_num : (0 : ℝ) ≤ 8)
    (by
      intro i j
      exact (product_magnitude ((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrix 2 2 k * matrix 2 2 h)
        (matrix 2 2 l) 2 2 hwi (fun i j => hl i.val j.val i.isLt j.isLt) i j).trans (by norm_num))
  have hgkt := FloatPrearray.gram_within ekt (by norm_num : (0 : ℝ) ≤ 2)
    (by
      intro i j
      exact (product_magnitude (matrix 2 2 k) (matrix 2 2 tr) (1 / 6) 2
        (fun i j => hk i.val j.val i.isLt j.isLt) (fun i j => ht i.val j.val i.isLt j.isLt) i j).trans (by norm_num))
  have hpre := within_add hgwl hgkt
  let s : TwoStateStages k h l tr := ⟨kh, w, wl, ktr, pkh, hkh, ps, hw, pwl, hwl, pkt, hktr⟩
  refine ⟨s, by positivity, ?_⟩
  intro i j
  rw [FloatPrearray.fromCols_gram 2 2 2 wl ktr]
  have he := hpre.2 i j
  norm_num only [Nat.cast_ofNat] at he
  exact he.trans (by convert prearray_radius_cap using 1; ring)

/-- The rounded prearray meets the QR domain and retains extra energy headroom.
The exact reference uses the stored gain and stored noise factor. -/
theorem prearray_domain (k h l tr : Array Float) (s : TwoStateStages k h l tr)
    (he
      : EntrywiseWithin ((2 : ℝ) ^ (-38 : Int))
          (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)))
          (FactorRecursion.gram
              (((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrix 2 2 k * matrix 2 2 h)
                * matrix 2 2 l)
            + FactorRecursion.gram (matrix 2 2 k * matrix 2 2 tr)))
    (hh : ∀ i j, |matrix 2 2 h i j| ≤ 1 / 64) (hk : ∀ i j, |matrix 2 2 k i j| ≤ 1 / 6)
    (hp : ∀ i j, |FactorRecursion.gram (matrix 2 2 l) i j| ≤ 7 / 4)
    (hf : (FactorRecursion.gram (matrix 2 2 l) - (2 / 3 : ℝ) • 1).PosSemidef)
    (ht : ∀ i j, |FactorRecursion.gram (matrix 2 2 tr) i j| ≤ 25 / 16)
    : GramFactorInputDomain 2 4 (fromCols 2 2 2 s.wl s.ktr) 2
      ∧ (∀ i,
          FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)) i i
          ≤ 63 / 32) := by
  obtain ⟨hfloor, henergy⟩ := PosteriorStructure.prearray_reference_bounds
    (matrix 2 2 h) (matrix 2 2 k) (matrix 2 2 l) (matrix 2 2 tr) hh hk hp hf ht
  have hg := CovarianceStructure.gram_posSemidef (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr))
  have hreturned := lower_bound_of_error _ _ (20 / 39) ((2 : ℝ)^(-38 : Int)) hfloor hg.isHermitian he
  have hpad : 0 ≤ (20 / 39 : ℝ) - 2 * (2 : ℝ)^(-38 : Int) - 1 / 2 := by norm_num
  have hpadded := hreturned.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad)
  have hb : ∀ i, FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 s.wl s.ktr)) i i ≤ 63 / 32 := by
    intro i
    have hd := (abs_le.mp (he.2 i i)).2
    exact ((sub_le_iff_le_add).mp hd).trans ((add_le_add le_rfl (henergy i)).trans (by norm_num))
  have hid := FloatQRInitialDomain.identity_input_domain 2 (by decide)
  refine ⟨
    ⟨
      by decide,
      by decide,
      FloatPrearray.fromCols_size 2 2 2 s.wl s.ktr,
      FloatPrearray.fromCols_finite 2 2 2 s.wl s.ktr
        (FloatJosephError.product_within s.wl_product s.compute_wl).2.1
        (FloatJosephError.product_within s.ktr_product s.compute_ktr).2.1,
      hid.budget_lower,
      hid.budget_upper,
      ?_,
      ?_
    ⟩,
    hb
  ⟩
  · intro i
    have hi := (hb i).trans (by norm_num : (63 : ℝ) / 32 ≤ 2^2 / 2)
    simpa only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hi
  · convert hpadded using 1
    norm_num
    module

end Kalman.Proofs.FloatPosteriorPrearray
