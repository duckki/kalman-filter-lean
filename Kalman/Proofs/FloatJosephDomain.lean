import Kalman.Proofs.FloatJosephError
import Kalman.Implementation.Correctness.JosephCovarianceEvaluation

/-! Direct Joseph covariance evaluation from stored-input bounds. All five
products and both sums succeed with derived profiles. The comparator uses the
same stored gain; a complete filter theorem must additionally charge its error. -/

namespace Kalman.Proofs.FloatJosephDomain

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.JosephCovarianceEvaluation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-! ----------------------------------------------------------------------
## Native products from entry bounds
-------------------------------------------------------------------------- -/

private theorem product (a b : Array Float) (A B : ℝ)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hA : 0 ≤ A) (hm : A * B ≤ 128)
    (ham : ∀ i j, |matrix 2 2 a i j| ≤ A)
    (hbm : ∀ i j, |matrix 2 2 b i j| ≤ B)
    : ∃ r,
        ProductProfile 2 2 2 a b 256
        ∧ multiply 2 2 2 a b = .ok r
        ∧ r.size = 4
        ∧ r.all Float.isFinite = true
        ∧ (∀ i j, |matrix 2 2 r i j| ≤ 2 * A * B + productRadius 2 256) := by
  have p : ProductProfile 2 2 2 a b 256 := by
    refine ⟨by decide, ha, hb, ?_, ?_, ?_⟩
    · simpa only [show (2 : ℝ) ^ (8 : Int) = 256 by norm_num]
        using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (8 : Int) ≤ 990)
    · simpa only [show (2 : ℝ) ^ (8 : Int) = 256 by norm_num]
        using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (-1022 : Int) ≤ 8)
    · intro i j hi hj
      calc
        _ ≤ ∑ _k ∈ Finset.range 2, A * B := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          exact mul_le_mul (ham ⟨i, hi⟩ ⟨k, Finset.mem_range.mp hk⟩)
            (hbm ⟨k, Finset.mem_range.mp hk⟩ ⟨j, hj⟩) (abs_nonneg _) hA
        _ ≤ 256 := by simp; linarith only [hm]
  obtain ⟨r, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy
    2 2 2 a b (fun _ _ => (256 : ℝ)) p.inner_le ha hb
    (fun _ _ _ _ => p.upper) (fun _ _ _ _ => p.lower) p.mass
  refine ⟨r, p, hr, hs, hf, ?_⟩
  intro i j
  have ht := product_magnitude (matrix 2 2 a) (matrix 2 2 b) A B ham hbm i j
  have hd := abs_sub_le (matrix 2 2 r i j) ((matrix 2 2 a * matrix 2 2 b) i j) 0
  have herr := he i j
  simp only [sub_zero] at hd
  norm_num only [Nat.cast_ofNat] at ht
  change |matrix 2 2 r i j - _| ≤ productRadius 2 256 at herr
  linarith only [hd, ht, herr]

private theorem array_bound (a : Array Float) (A : ℝ)
    (h : ∀ i j, |matrix 2 2 a i j| ≤ A) (t : Nat) (ht : t < 4)
    : |value (a.getD t 0.0)| ≤ A := by
  have hi : t / 2 < 2 := by omega
  have hj : t % 2 < 2 := by omega
  have hm := h ⟨t / 2, hi⟩ ⟨t % 2, hj⟩
  have hidx : t / 2 * 2 + t % 2 = t := by omega
  change |value (a.getD (t / 2 * 2 + t % 2) 0.0)| ≤ A at hm
  simpa only [hidx] using hm

private theorem transpose_bound (a : Array Float) (A : ℝ)
    (hf : a.all Float.isFinite = true)
    (h : ∀ i j, |matrix 2 2 a i j| ≤ A)
    : ∀ i j, |matrix 2 2 (transpose 2 2 a) i j| ≤ A := by
  have ht : matrix 2 2 (transpose 2 2 a) = (matrix 2 2 a).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 a hf
  intro i j
  rw [ht]
  exact h j i

/-! ----------------------------------------------------------------------
## Derived Joseph arithmetic profiles
-------------------------------------------------------------------------- -/

/-- The complete seven-operation covariance kernel derives its own successful
executions, finite outputs, and numerical profiles from stored input bounds. -/
theorem covariance_stages (input : Input.Model) (prior : Input.State) (k : Array Float)
    (d : TwoStateDomain input prior k)
    : ∃ output,
      ∃ p : JosephProfile input prior k output,
        output.size = 4
        ∧ output.all Float.isFinite = true
        ∧ p.massKH = 256
        ∧ p.massWP = 256
        ∧ p.massFirst = 256
        ∧ p.massKR = 256
        ∧ p.massSecond = 256
        ∧ p.exponentW = 2
        ∧ p.exponentSum = 8 := by
  obtain ⟨kh, pkh, hkh, _, khf, khb⟩ := product k input.observation
    1 1 d.gain_finite d.observation_finite
    (by norm_num) (by norm_num) d.gain_bound d.observation_bound
  have khcap : ∀ i j, |matrix 2 2 kh i j| ≤ 9 / 4 := by
    intro i j
    exact (khb i j).trans (by norm_num [productRadius])
  have idf : (identity 2).all Float.isFinite = true := by decide +kernel
  have idb : ∀ i j, |matrix 2 2 (identity 2) i j| ≤ (1 : ℝ) := by
    rw [FloatJosephError.identity_matrix]
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have pw : SumProfile (identity 2) kh 2 true := by
    refine ⟨by norm_num, by norm_num, idf, khf, ?_⟩
    intro t ht
    have ht' : t < 4 := by simpa [identity, Flare.Matrix.Dense.identity] using ht
    have hi := array_bound _ _ idb t ht'
    have hk := array_bound _ _ khcap t ht'
    simpa only [↓reduceIte, ← sub_eq_add_neg, show (2 : ℝ) ^ (2 : Int) = 4 by norm_num]
      using (abs_sub _ _).trans ((add_le_add hi hk).trans (by norm_num))
  obtain ⟨w, hw, _, wf, _⟩ := FloatDenseError.sub_accuracy (identity 2) kh 2
    pw.exponent_lower pw.exponent_upper pw.finite_left pw.finite_right
    (by simpa only [↓reduceIte, ← sub_eq_add_neg] using pw.magnitude)
  have ew := FloatJosephError.subtract_within (n := 2) (m := 2) pw
    (by simp [identity, Flare.Matrix.Dense.identity]) hw
  have wb : ∀ i j, |matrix 2 2 w i j| ≤ 7 / 2 := by
    intro i j
    have hm := (abs_sub _ _).trans (add_le_add (idb i j) (khcap i j))
    have hd := abs_sub_le (matrix 2 2 w i j) ((matrix 2 2 (identity 2) - matrix 2 2 kh) i j) 0
    have he := ew.2 i j
    simp only [sub_zero, Matrix.sub_apply] at hd
    norm_num [sumRadius] at he
    linarith only [hd, hm, he]
  obtain ⟨wp, pwp, hwp, _, wpf, wpb⟩ := product w prior.covariance
    (7 / 2) 4 wf d.covariance_finite (by norm_num) (by norm_num) wb d.covariance_bound
  have wpcap : ∀ i j, |matrix 2 2 wp i j| ≤ 29 := by
    intro i j
    exact (wpb i j).trans (by norm_num [productRadius])
  have wtf := (Flare.Matrix.Multiplication.transpose_storage 2 2 w wf).2.1
  obtain ⟨first, pf, hfirst, fs, ff, fb⟩ := product wp (transpose 2 2 w)
    29 (7 / 2) wpf wtf (by norm_num) (by norm_num) wpcap (transpose_bound w _ wf wb)
  have fcap : ∀ i j, |matrix 2 2 first i j| ≤ 204 := by
    intro i j
    exact (fb i j).trans (by norm_num [productRadius])
  obtain ⟨kr, pkr, hkr, _, krf, krb⟩ := product k input.measurementNoise
    1 (3 / 2) d.gain_finite d.noise_finite
    (by norm_num) (by norm_num) d.gain_bound d.noise_bound
  have krcap : ∀ i j, |matrix 2 2 kr i j| ≤ 4 := by
    intro i j
    exact (krb i j).trans (by norm_num [productRadius])
  have ktf := (Flare.Matrix.Multiplication.transpose_storage 2 2 k d.gain_finite).2.1
  obtain ⟨second, ps, hsecond, _, sf, sb⟩ := product kr (transpose 2 2 k)
    4 1 krf ktf (by norm_num) (by norm_num) krcap
    (transpose_bound k _ d.gain_finite d.gain_bound)
  have scap : ∀ i j, |matrix 2 2 second i j| ≤ 9 := by
    intro i j
    exact (sb i j).trans (by norm_num [productRadius])
  have po : SumProfile first second 8 false := by
    refine ⟨by norm_num, by norm_num, ff, sf, ?_⟩
    intro t ht
    have ht' : t < 4 := by omega
    have hf := array_bound _ _ fcap t ht'
    have hs := array_bound _ _ scap t ht'
    simpa only [Bool.false_eq_true, ↓reduceIte,
      show (2 : ℝ) ^ (8 : Int) = 256 by norm_num]
      using (abs_add_le _ _).trans ((add_le_add hf hs).trans (by norm_num))
  obtain ⟨output, ho, os, outputFinite, _⟩ := FloatDenseError.add_accuracy first second 8
    po.exponent_lower po.exponent_upper po.finite_left po.finite_right
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using po.magnitude)
  let p : JosephProfile input prior k output :=
    { kh := kh, w := w, wp := wp, first := first, kr := kr, second := second
      massKH := 256, massWP := 256, massFirst := 256, massKR := 256, massSecond := 256
      exponentW := 2, exponentSum := 8
      computeKH := by simpa only [d.state_dimension, d.measurement_dimension] using hkh
      computeW := by simpa only [d.state_dimension] using hw
      computeWP := by simpa only [d.state_dimension] using hwp
      computeFirst := by simpa only [d.state_dimension] using hfirst
      computeKR := by simpa only [d.state_dimension, d.measurement_dimension] using hkr
      computeSecond := by simpa only [d.state_dimension, d.measurement_dimension] using hsecond
      computeSum := ho
      profileKH := by simpa only [d.state_dimension, d.measurement_dimension] using pkh
      profileW := by simpa only [d.state_dimension] using pw
      profileWP := by simpa only [d.state_dimension] using pwp
      profileFirst := by simpa only [d.state_dimension] using pf
      profileKR := by simpa only [d.state_dimension, d.measurement_dimension] using pkr
      profileSecond := by simpa only [d.state_dimension, d.measurement_dimension] using ps
      profileSum := po }
  exact ⟨output, p, os.trans fs, outputFinite, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ----------------------------------------------------------------------
## Concrete covariance accuracy from stored inputs
-------------------------------------------------------------------------- -/

/-- Original stored operands alone imply success and a 2^-34 absolute
entrywise covariance error at the same stored gain. -/
theorem stored_input_accuracy : StoredInputAccuracy := by
  intro input prior k d
  obtain ⟨output, p, os, outputFinite, hkh, hwp, hfirst, hkr, hsecond, hw, hsum⟩ :=
    covariance_stages input prior k d
  have hwbound : ∀ i j,
      |((1 : Matrix (Fin input.stateDimension) (Fin input.stateDimension) ℝ)
        - matrix input.stateDimension input.measurementDimension k
          * matrix input.measurementDimension input.stateDimension input.observation) i j|
        ≤ 3 := by
    rw [d.state_dimension, d.measurement_dimension]
    intro i j
    have hid : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    have hprod := product_magnitude (matrix 2 2 k) (matrix 2 2 input.observation)
      1 1 d.gain_bound d.observation_bound i j
    exact (abs_sub _ _).trans ((add_le_add hid hprod).trans (by norm_num))
  have he := FloatJosephError.joseph_evaluation_error p 4 3 1
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [d.state_dimension]; exact d.covariance_bound) hwbound
    (by rw [d.state_dimension, d.measurement_dimension]; exact d.gain_bound)
  have hcap : josephRadius p 4 3 1 ≤ (2 : ℝ) ^ (-34 : Int) := by
    norm_num [josephRadius, d.state_dimension, d.measurement_dimension,
      hkh, hwp, hfirst, hkr, hsecond, hw, hsum, productRadius, sumRadius]
  exact ⟨
    output,
    os,
    outputFinite,
    he.1,
    ⟨by positivity, fun i j => (he.2.2 i j).trans hcap⟩
  ⟩

/-- Correlated dense covariance with nonzero observation and gain inhabits the
stored-input domain. The theorem is not limited to zero-gain arithmetic. -/
theorem stored_input_domain_nonempty
    : ∃ input : Input.Model,
      ∃ prior : Input.State,
      ∃ k : Array Float,
        TwoStateDomain input prior k
        ∧ prior.covariance = #[1.0, 0.125, 0.125, 1.0]
        ∧ k = #[0.25, 0.0, 0.0, 0.25] := by
  let input : Input.Model :=
    ⟨2, 2, identity 2, #[0.015625, 0.0, 0.0, 0.015625], identity 2, identity 2, #[0.0, 0.0]⟩
  let prior : Input.State := ⟨#[0.0, 0.0], #[1.0, 0.125, 0.125, 1.0]⟩
  let k : Array Float := #[0.25, 0.0, 0.0, 0.25]
  have hh : value (0.015625 : Float) = (1 : ℝ) / 64 := by
    change (4503599627370496 : ℝ) * (2 : ℝ) ^ (-58 : Int) = _
    norm_num
  have hp : value (0.125 : Float) = (1 : ℝ) / 8 := by
    change (4503599627370496 : ℝ) * (2 : ℝ) ^ (-55 : Int) = _
    norm_num
  have hk : value (0.25 : Float) = (1 : ℝ) / 4 := by
    change (4503599627370496 : ℝ) * (2 : ℝ) ^ (-54 : Int) = _
    norm_num
  refine ⟨input, prior, k, ?_, rfl, rfl⟩
  refine ⟨
    rfl,
    rfl,
    by decide,
    by decide,
    by simp [input, identity, Flare.Matrix.Dense.identity],
    by decide,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    ?_,
    ?_,
    ?_,
    ?_
  ⟩
  all_goals
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [input, prior, k, matrix, Flare.Matrix.Value.matrix, identity,
        Flare.Matrix.Dense.identity, hh, hp, hk,
        Flare.Binary64.Arithmetic.zero_value, Flare.Binary64.Arithmetic.one_value]

end Kalman.Proofs.FloatJosephDomain
