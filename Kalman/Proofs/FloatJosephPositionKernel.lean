import Kalman.Proofs.FloatJosephPositionArithmetic

namespace Kalman.Proofs.FloatJosephPositionKernel

open Matrix hiding transpose
open Kalman.Definitions Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles Kalman.Proofs.ErrorPropagation
open Kalman.Proofs.FloatJosephPositionArithmetic
open Flare.Binary64.Value

set_option maxHeartbeats 1600000

/-- Complete rectangular Joseph covariance evaluation, from stored operand caps. -/
theorem covariance_accuracy (input : Input.Model) (prior : Input.State) (k : Array Float)
    (hn : input.stateDimension = 2) (hm : input.measurementDimension = 1)
    (pf : prior.covariance.all Float.isFinite = true)
    (hf : input.observation.all Float.isFinite = true)
    (rf : input.measurementNoise.all Float.isFinite = true)
    (kf : k.all Float.isFinite = true) (pb : ∀ i j, |matrix 2 2 prior.covariance i j| ≤ 2)
    (hb : ∀ i j, |matrix 1 2 input.observation i j| ≤ 1)
    (rb : ∀ i j, |matrix 1 1 input.measurementNoise i j| ≤ 3 / 2)
    (kb : ∀ i j, |matrix 2 1 k i j| ≤ 2)
    : ∃ output,
        output.size = 4
        ∧ output.all Float.isFinite = true
        ∧ Kalman.Implementation.CovarianceFilter.covarianceUnchecked .joseph input prior k
          = .ok output
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-32 : Int)) (matrix 2 2 output)
            (CovarianceRecursion.joseph (model (atDimensions 2 1 input)) (state 2 prior)
              (matrix 2 1 k)) := by
  obtain ⟨kh, pkh, hkh, khs, khf, ekh⟩ := product 2 1 2 k input.observation 2 1
    (by decide) kf hf (by norm_num) (by norm_num) (by norm_num) kb hb
  have khcap := near_bound kh _ _ 2 (9/4) ekh
    (by intro i j; exact (product_magnitude (matrix 2 1 k) (matrix 1 2 input.observation) 2 1 kb hb i j).trans (by norm_num))
    (by norm_num)
  have idf : (identity 2).all Float.isFinite = true := by decide +kernel
  have idb : ∀ i j, |matrix 2 2 (identity 2) i j| ≤ (1 : ℝ) := by
    rw [FloatJosephError.identity_matrix]
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have pw := sum_profile 2 2 (identity 2) kh 1 (9/4) 2 true (by decide)
    (by simp [identity, Flare.Matrix.Dense.identity]) idf khf (by norm_num) (by norm_num) (by norm_num) idb khcap
  obtain ⟨w, hw, ws, wf, _⟩ := FloatDenseError.sub_accuracy (identity 2) kh 2
    pw.exponent_lower pw.exponent_upper idf khf
    (by simpa only [↓reduceIte, ← sub_eq_add_neg] using pw.magnitude)
  have ew := FloatJosephError.subtract_within (n := 2) (m := 2) pw (by simp [identity, Flare.Matrix.Dense.identity]) hw
  have wb : ∀ i j, |matrix 2 2 w i j| ≤ 7/2 := near_bound w _ _ (13/4) (7/2) ew
    (fun i j => (abs_sub _ _).trans ((add_le_add (idb i j) (khcap i j)).trans (by norm_num))) (by norm_num [sumRadius])
  obtain ⟨wp, pwp, hwp, _, wpf, ewp⟩ := product 2 2 2 w prior.covariance (7/2) 2
    (by decide) wf pf (by norm_num) (by norm_num) (by norm_num) wb pb
  have wpb := near_bound wp _ _ 14 15 ewp
    (by intro i j; exact (product_magnitude (matrix 2 2 w) (matrix 2 2 prior.covariance) (7/2) 2 wb pb i j).trans (by norm_num))
    (by norm_num)
  have wt := transpose_bound 2 2 w (7/2) wf wb
  obtain ⟨first, pfirst, hfirst, fs, ff, ef⟩ := product 2 2 2 wp (transpose 2 2 w) 15 (7/2)
    (by decide) wpf wt.1 (by norm_num) (by norm_num) (by norm_num) wpb wt.2
  have fb := near_bound first _ _ 105 106 ef
    (by intro i j; exact (product_magnitude (matrix 2 2 wp) (matrix 2 2 (transpose 2 2 w)) 15 (7/2) wpb wt.2 i j).trans (by norm_num))
    (by norm_num)
  obtain ⟨kr, pkr, hkr, _, krf, ekr⟩ := product 2 1 1 k input.measurementNoise 2 (3/2)
    (by decide) kf rf (by norm_num) (by norm_num) (by norm_num) kb rb
  have krb := near_bound kr _ _ 3 4 ekr
    (by intro i j; exact (product_magnitude (matrix 2 1 k) (matrix 1 1 input.measurementNoise) 2 (3/2) kb rb i j).trans (by norm_num))
    (by norm_num)
  have kt := transpose_bound 2 1 k 2 kf kb
  obtain ⟨second, psecond, hsecond, _, sf, es⟩ := product 2 1 2 kr (transpose 2 1 k) 4 2
    (by decide) krf kt.1 (by norm_num) (by norm_num) (by norm_num) krb kt.2
  have sb := near_bound second _ _ 8 9 es
    (by intro i j; exact (product_magnitude (matrix 2 1 kr) (matrix 1 2 (transpose 2 1 k)) 4 2 krb kt.2 i j).trans (by norm_num))
    (by norm_num)
  have po := sum_profile 2 2 first second 106 9 8 false (by decide) fs ff sf
    (by norm_num) (by norm_num) (by norm_num) fb sb
  obtain ⟨output, ho, os, outputFinite, _⟩ := FloatDenseError.add_accuracy first second 8
    po.exponent_lower po.exponent_upper ff sf
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using po.magnitude)
  let profile : JosephProfile (atDimensions 2 1 input) prior k output :=
    { kh := kh, w := w, wp := wp, first := first, kr := kr, second := second
      massKH := 256, massWP := 256, massFirst := 256, massKR := 256, massSecond := 256
      exponentW := 2, exponentSum := 8
      computeKH := by simpa only [atDimensions] using hkh
      computeW := by simpa only [atDimensions] using hw
      computeWP := by simpa only [atDimensions] using hwp
      computeFirst := by simpa only [atDimensions] using hfirst
      computeKR := by simpa only [atDimensions] using hkr
      computeSecond := by simpa only [atDimensions] using hsecond
      computeSum := ho
      profileKH := by simpa only [atDimensions] using pkh
      profileW := by simpa only [atDimensions] using pw
      profileWP := by simpa only [atDimensions] using pwp
      profileFirst := by simpa only [atDimensions] using pfirst
      profileKR := by simpa only [atDimensions] using pkr
      profileSecond := by simpa only [atDimensions] using psecond
      profileSum := po }
  have wbExact : ∀ i j, |((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      matrix 2 1 k * matrix 1 2 input.observation) i j| ≤ 3 := by
    intro i j
    have hi : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      simp only [Matrix.one_apply]; split_ifs <;> norm_num
    have hh := product_magnitude (matrix 2 1 k) (matrix 1 2 input.observation) 2 1 kb hb i j
    exact (abs_sub _ _).trans ((add_le_add hi hh).trans (by norm_num))
  have ee := FloatJosephError.joseph_evaluation_error profile 2 3 2
    (by norm_num) (by norm_num) (by norm_num)
    (by exact pb) (by
      change ∀ i j : Fin 2, |((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrix 2 1 k * matrix 1 2 input.observation) i j| ≤ 3
      exact wbExact)
    (by exact kb)
  refine ⟨output, by omega, outputFinite, ?_, by positivity, ?_⟩
  · simpa only [Kalman.Implementation.CovarianceFilter.covarianceUnchecked,
      atDimensions, hn, hm] using ee.1
  · intro i j
    apply (ee.2.2 i j).trans
    norm_num [josephRadius, profile, atDimensions, productRadius, sumRadius]

end Kalman.Proofs.FloatJosephPositionKernel
