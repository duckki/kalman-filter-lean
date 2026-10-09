import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRTriangular
import Kalman.Proofs.OrthogonalStructure
import Mathlib.Order.Interval.Finset.Nat

/-! One native QR iteration's exact column-Gram error. Previous triangular zeros
turn the selected-panel comparison into a full Gram-preserving reflection.
The local profile is not yet a preserved domain for the whole pivot loop. -/

namespace Kalman.Proofs.FloatQRGram

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Definitions.OrthogonalFactorization
open Flare.Binary64.Value

private theorem active_sum (height pivot : Nat) (hp : pivot ≤ height) (f : Nat → ℝ)
    : (∑ i : Fin height, if pivot ≤ i.val then f i.val else 0)
      = ((List.range' pivot (height - pivot)).map f).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if pivot ≤ i then f i else 0) height,
    ← List.sum_toFinset _ List.nodup_range', List.toFinset_range'_1, Nat.add_sub_of_le hp]
  calc
    _ = ∑ i ∈ Finset.Ico pivot height, if pivot ≤ i then f i else 0 := by
      symm
      apply Finset.sum_subset
        (by intro i hi; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
      intro i hi hn
      have hn' : ¬pivot ≤ i := fun h => hn (Finset.mem_Ico.mpr ⟨h, Finset.mem_range.mp hi⟩)
      simp [hn']
    _ = _ := Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_Ico.mp hi).1)

theorem iterationUnitVector_unit (height pivot : Nat) (v : Array Float) (norm : Float)
    (hp : pivot ≤ height)
    (hu
      : ((List.range' pivot (height - pivot)).map
          (fun i =>
            (constructedUnitComponent pivot (List.range' pivot (height - pivot)) v norm i)
            ^ 2)).sum
        = 1)
    : ∑ i, (iterationUnitVector height pivot v norm i) ^ 2 = 1 := by
  simp only [iterationUnitVector, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [active_sum height pivot hp (fun i => (constructedUnitComponent pivot (List.range' pivot (height - pivot)) v norm i)^2)]
  exact hu

theorem reflect_eq_constructed (height width pivot : Nat) (v a : Array Float)
    (norm : Float) (hp : pivot ≤ height) (i : Fin height) (j : Fin width)
    (hi : pivot ≤ i.val)
    : reflect (iterationUnitVector height pivot v norm) (matrix height width a) i j
      = constructedAppliedValue width j.val pivot (List.range' pivot (height - pivot)) v
          norm a i.val := by
  unfold reflect Flare.Analysis.Householder.reflect constructedAppliedValue
  simp only [iterationUnitVector, ite_eq_left hi]
  have hd : (∑ k : Fin height,
      (if pivot ≤ k.val then
        constructedUnitComponent pivot (List.range' pivot (height - pivot)) v norm k.val else 0)
      * value (entry width a k.val j.val))
      = ((List.range' pivot (height - pivot)).map
        (fun k => constructedUnitComponent pivot (List.range' pivot (height - pivot)) v norm k
          * value (entry width a k j.val))).sum := by
    simp only [ite_mul, zero_mul]
    exact active_sum height pivot hp (fun k => constructedUnitComponent pivot (List.range' pivot (height - pivot)) v norm k * value (entry width a k j.val))
  change value (entry width a i.val j.val) - 2 * constructedUnitComponent pivot (List.range' pivot (height - pivot)) v norm i.val * (∑ k : Fin height, (if pivot ≤ k.val then constructedUnitComponent pivot (List.range' pivot (height - pivot)) v norm k.val else 0) * value (entry width a k.val j.val)) = _
  rw [hd]

private theorem top_slot_ne (width i j r c : Nat) (hw : 0 < width)
    (hj : j < width) (hc : c < width) (hne : i ≠ r)
    : i * width + j ≠ r * width + c := by
  intro he
  have hd := congrArg (fun t => t / width) he
  simp only [Nat.mul_comm _ width, Nat.mul_add_div hw, Nat.div_eq_of_lt hj,
    Nat.div_eq_of_lt hc, Nat.add_zero] at hd
  exact hne hd

private theorem reflect_prefix (height width pivot : Nat) (v a : Array Float)
    (norm : Float) (i : Fin height) (j : Fin width) (hi : i.val < pivot)
    : reflect (iterationUnitVector height pivot v norm) (matrix height width a) i j
      = value (entry width a i.val j.val) := by
  unfold reflect Flare.Analysis.Householder.reflect
  rw [show iterationUnitVector height pivot v norm i = 0 from by simp [iterationUnitVector, Nat.not_le.mpr hi], mul_zero, zero_mul, sub_zero]
  rfl

private theorem reflect_earlierColumn (height width pivot : Nat) (v a : Array Float)
    (norm : Float) (hz : ProcessedColumns height width pivot a) (i : Fin height)
    (j : Fin width) (hj : j.val < pivot)
    : reflect (iterationUnitVector height pivot v norm) (matrix height width a) i j
      = value (entry width a i.val j.val) := by
  unfold reflect Flare.Analysis.Householder.reflect
  have hd : (∑ k, iterationUnitVector height pivot v norm k * matrix height width a k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : pivot ≤ k.val
    · change iterationUnitVector height pivot v norm k * value (entry width a k.val j.val) = 0
      rw [hz j.val hj j.isLt k.val k.isLt (by omega), Flare.Binary64.Arithmetic.zero_value, mul_zero]
    · simp [iterationUnitVector, hk]
  rw [hd, mul_zero, sub_zero]
  rfl

/-- The selected-panel numerical theorem extends to a full exact reflection
because processed columns have zero active tails and the prefix rows are copied. -/
theorem qrIteration_orthogonal_accuracy (height width pivot : Nat) (a : Array Float)
    (M : ℝ) (p : IterationProfile height width pivot a M)
    (hz : ProcessedColumns height width pivot a)
    : IterationOrthogonalAccuracy height width pivot a M := by
  obtain ⟨scale, v, norm, _, _, _, output, hnorm, _, _, _, hrun, hs, hf, hcopy, _, _, _, _, _, _, _,
      hunit, _, _, _, _, _, _, _, herr⟩ := FloatQRIteration.qrIteration_accuracy height width pivot a M p
  have hM : 0 ≤ M := (zpow_pos (by norm_num : (0 : ℝ) < 2) (-900 : Int)).le.trans p.budget_lower
  have hE : 0 ≤ iterationRadius (height - pivot) M := by
    unfold iterationRadius sourceWriteRadius sourceResidualRadius columnNormRadius squareSumRadius reflectorRadius
    positivity
  refine ⟨
    scale,
    v,
    norm,
    output,
    hnorm,
    hrun,
    hs,
    hf,
    iterationUnitVector_unit height pivot v norm (Nat.le_of_lt p.pivot_height) hunit,
    hE,
    ?_
  ⟩
  intro i j
  by_cases hi : pivot ≤ i.val
  · by_cases hj : pivot ≤ j.val
    · rw [reflect_eq_constructed height width pivot v a norm (Nat.le_of_lt p.pivot_height) i j hi]
      change |value (entry width output i.val j.val) - _| ≤ _
      simpa only [List.length_range'] using herr j.val (by
        by_cases he : j.val = pivot
        · simp [he]
        · apply List.mem_cons_of_mem
          rw [List.mem_range'_1]
          exact ⟨by omega, by omega⟩)
        i.val (by rw [List.mem_range'_1]; exact ⟨hi, by omega⟩)
    · rw [reflect_earlierColumn height width pivot v a norm hz i j (by omega)]
      have he := FloatQRTriangular.qrIteration_earlierColumn height width pivot a output
        p.pivot_height p.pivot_width p.matrix_size p.matrix_finite hrun j.val (by omega) i.val
      change |value (entry width output i.val j.val) - value (entry width a i.val j.val)| ≤ _
      rw [← he, sub_self, abs_zero]
      exact hE
  · rw [reflect_prefix height width pivot v a norm i j (by omega)]
    have hc := hcopy (i.val*width+j.val) (by
      intro r hr c hc
      have hrp : pivot ≤ r := (List.mem_range'_1.mp hr).1
      have hcb : c < width := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact p.pivot_width
        · have := (List.mem_range'_1.mp hc).2; have hw := p.pivot_width; omega
      exact top_slot_ne width i.val j.val r c (by omega) j.isLt hcb (by omega))
    change |value (entry width output i.val j.val) - value (entry width a i.val j.val)| ≤ _
    rw [show entry width output i.val j.val = entry width a i.val j.val from hc, sub_self, abs_zero]
    exact hE

/-- Exact perturbation algebra with unchanged prefix rows. The row count in the
allowance is the active height, rather than the full stored matrix height. -/
theorem columnGram_active_perturbation {height width : Nat} (pivot : Nat)
    (hp : pivot ≤ height) (b c : Matrix (Fin height) (Fin width) ℝ) (B E : ℝ) (hB : 0 ≤ B)
    (he : EntrywiseWithin E b c) (hc : ∀ i, pivot ≤ i.val → ∀ j, |c i j| ≤ B)
    (hprefix : ∀ i, i.val < pivot → ∀ j, b i j = c i j)
    : EntrywiseWithin (((height - pivot : Nat) : ℝ) * (2 * B * E + E ^ 2))
        (b.transpose * b) (c.transpose * c) := by
  have hE := he.1
  refine ⟨by positivity, fun j k => ?_⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin height, |b i j * b i k - c i j * c i k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin height, if pivot ≤ i.val then 2 * B * E + E ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : pivot ≤ i.val
      · rw [ite_eq_left hi,
          show b i j*b i k-c i j*c i k =
            (b i j-c i j)*c i k+c i j*(b i k-c i k)+(b i j-c i j)*(b i k-c i k) by ring]
        apply ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
        simp only [abs_mul]
        have h1 := mul_le_mul (he.2 i j) (hc i hi k) (abs_nonneg _) he.1
        have h2 := mul_le_mul (hc i hi j) (he.2 i k) (abs_nonneg _) hB
        have h3 := mul_le_mul (he.2 i j) (he.2 i k) (abs_nonneg _) he.1
        nlinarith
      · rw [ite_eq_right hi, hprefix i (by omega) j, hprefix i (by omega) k, sub_self, abs_zero]
    _ = _ := by
      rw [active_sum height pivot hp (fun _ => 2 * B * E + E^2)]
      simp; ring

private theorem active_input_bound (height width pivot : Nat) (a : Array Float) (M : ℝ)
    (p : IterationProfile height width pivot a M)
    (hz : ProcessedColumns height width pivot a) (i : Fin height) (hi : pivot ≤ i.val)
    (j : Fin width)
    : |matrix height width a i j| ≤ M := by
  by_cases hj : pivot ≤ j.val
  · exact p.panel_magnitude i.val hi i.isLt j.val hj j.isLt
  · change |value (entry width a i.val j.val)| ≤ M
    rw [hz j.val (by omega) j.isLt i.val i.isLt (by omega), Flare.Binary64.Arithmetic.zero_value,
      abs_zero]
    exact (zpow_pos (by norm_num : (0 : ℝ) < 2) (-900 : Int)).le.trans p.budget_lower

private theorem reflection_active_bound (height width pivot : Nat) (a v : Array Float)
    (norm : Float) (M : ℝ) (p : IterationProfile height width pivot a M)
    (hz : ProcessedColumns height width pivot a)
    (hu : ∑ i, (iterationUnitVector height pivot v norm i) ^ 2 = 1) (i : Fin height)
    (hi : pivot ≤ i.val) (j : Fin width)
    : |reflect (iterationUnitVector height pivot v norm) (matrix height width a) i j|
      ≤ (1 + 2 * ((height - pivot : Nat) : ℝ)) * M := by
  let u := iterationUnitVector height pivot v norm
  let A := matrix height width a
  have hm := active_input_bound height width pivot a M p hz
  have hc := OrthogonalStructure.unit_component_bound u hu
  have hd : |∑ k, u k * A k j| ≤ ((height - pivot : Nat) : ℝ) * M := by
    calc
      _ ≤ ∑ k : Fin height, |u k * A k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin height, if pivot ≤ k.val then M else 0 := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : pivot ≤ k.val
        · rw [ite_eq_left hk, abs_mul]
          exact (mul_le_mul (hc k) (hm k hk j) (abs_nonneg _) (by norm_num)).trans_eq (one_mul M)
        · simp [u, iterationUnitVector, hk]
      _ = _ := by
        rw [active_sum height pivot (Nat.le_of_lt p.pivot_height) (fun _ => M)]; simp
  change |A i j - 2 * u i * ∑ k, u k * A k j| ≤ _
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_left (hc i) (by norm_num : (0 : ℝ) ≤ 2)) hd
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2*1)
  have hsum := add_le_add (hm i hi j) hmul
  nlinarith

/-- A complete native iteration changes its incoming exact column Gram by the
stated absolute allowance. The incoming triangular zeros and local operand
profile are hypotheses; the numerical error and successful run are conclusions. -/
theorem qrIteration_gram_accuracy (height width pivot : Nat) (a : Array Float) (M : ℝ)
    (p : IterationProfile height width pivot a M)
    (hz : ProcessedColumns height width pivot a)
    : IterationGramAccuracy height width pivot a M := by
  obtain ⟨_, v, norm, output, _, hrun, hs, hf, hunit, herr⟩ :=
    qrIteration_orthogonal_accuracy height width pivot a M p hz
  let u := iterationUnitVector height pivot v norm
  let A := matrix height width a
  have hM : 0 ≤ M := (zpow_pos (by norm_num : (0 : ℝ) < 2) (-900 : Int)).le.trans p.budget_lower
  have hc := (FloatQRTriangular.qrIteration_storage height width pivot a output
    p.pivot_height p.pivot_width p.matrix_size p.matrix_finite hrun).2.2.1
  have hprefix : ∀ i : Fin height, i.val < pivot → ∀ j : Fin width,
      matrix height width output i j = reflect u A i j := by
    intro i hi j
    rw [reflect_prefix height width pivot v a norm i j hi]
    apply congrArg value
    exact hc (i.val*width+j.val) (by
      intro r hr c hcol
      have hrp : pivot ≤ r := (List.mem_range'_1.mp hr).1
      have hcb : c < width := by
        rcases List.mem_cons.mp hcol with rfl | hcol
        · exact p.pivot_width
        · have := (List.mem_range'_1.mp hcol).2; have hw := p.pivot_width; omega
      exact top_slot_ne width i.val j.val r c (by omega) j.isLt hcb (by omega))
  have hg := columnGram_active_perturbation pivot (Nat.le_of_lt p.pivot_height)
    (matrix height width output) (reflect u A) ((1 + 2 * ((height - pivot : Nat) : ℝ)) * M)
    (iterationRadius (height - pivot) M) (by positivity) herr
    (reflection_active_bound height width pivot a v norm M p hz hunit) hprefix
  rw [OrthogonalStructure.reflect_gram u A hunit] at hg
  refine ⟨output, hrun, hs, hf, ?_⟩
  convert hg using 1
  unfold iterationGramRadius
  ring

/-- A simple conservative cap; the dimension-dependent formula is usually more
informative. This is not a relative error or a sharp classical stability constant. -/
theorem iterationGramRadius_le {terms : Nat} (M : ℝ) (hk : terms ≤ 32) (hM : 0 ≤ M)
    : iterationGramRadius terms M ≤ (2 : ℝ) ^ (-4 : Int) * M ^ 2 := by
  have hn : (terms : ℝ) ≤ 32 := by exact_mod_cast hk
  have hE := FloatQRIteration.iterationRadius_le M hk hM
  have hE0 : 0 ≤ iterationRadius terms M := by
    unfold iterationRadius sourceWriteRadius sourceResidualRadius columnNormRadius squareSumRadius reflectorRadius
    positivity
  have hB : 2 * (1 + 2 * (terms : ℝ)) * M ≤ 130 * M :=
    mul_le_mul_of_nonneg_right (by linarith) hM
  have hp := mul_le_mul hB hE hE0 (by positivity : (0 : ℝ) ≤ 130*M)
  have hs := mul_le_mul hE hE hE0 (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(-17 : Int)*M)
  unfold iterationGramRadius
  calc
    _ ≤ terms
        * (130 * M * ((2 : ℝ) ^ (-17 : Int) * M)
            + ((2 : ℝ) ^ (-17 : Int) * M) * ((2 : ℝ) ^ (-17 : Int) * M)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg terms)
      simpa only [pow_two] using add_le_add hp hs
    _ ≤ 32
        * (130 * M * ((2 : ℝ) ^ (-17 : Int) * M)
            + ((2 : ℝ) ^ (-17 : Int) * M) * ((2 : ℝ) ^ (-17 : Int) * M)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ _ := by norm_num; nlinarith [sq_nonneg M]

end Kalman.Proofs.FloatQRGram
