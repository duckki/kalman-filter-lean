import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRDomain
import Mathlib.LinearAlgebra.Matrix.Block

/-! Quantitative active-source witnesses from a column-Gram lower bound,
processed-column zeros and nonzero leading diagonals. These are exact Real
arguments applied to the same stored native QR prefix. -/

namespace Kalman.Proofs.FloatQRSourceTail

open Matrix
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.LinearAlgebra
open Flare.Binary64.Value

/-- Cancel the processed rows using earlier columns, leaving the active
source tail unchanged. The source coefficient is exactly one. -/
theorem source_tail_combination {height width : Nat}
    (a : Matrix (Fin height) (Fin width) ℝ) (pivot : Nat)
    (hh : width ≤ height) (hp : pivot < width)
    (hz : ∀ i j, j.val < pivot → j.val < i.val → a i j = 0)
    (hd : ∀ j : Fin width, j.val < pivot → a (Fin.castLE hh j) j ≠ 0)
    : ∃ x : Fin width → ℝ,
        x ⟨pivot, hp⟩ = 1
        ∧ ∀ i, a.mulVec x i = if i.val < pivot then 0 else a i ⟨pivot, hp⟩ := by
  let source : Fin width := ⟨pivot, hp⟩
  let b : Matrix (Fin width) (Fin width) ℝ := fun i j =>
    if i.val < pivot then
      if j.val < pivot then a (Fin.castLE hh i) j else 0
    else
      if i = j then 1 else 0
  have ht : b.IsUpperTriangular := by
    intro i j hij
    by_cases hi : i.val < pivot
    · have hj : j.val < pivot := (show j.val < i.val from hij).trans hi
      simp only [b, hi, hj, ite_eq_left]
      exact hz _ _ hj hij
    · have hne : i ≠ j := ne_of_gt hij
      simp [b, hi, hne]
  have hdiag : ∀ j : Fin width, b j j ≠ 0 := by
    intro j
    by_cases hj : j.val < pivot
    · simpa only [b, hj, ite_eq_left] using hd j hj
    · simp [b, hj]
  have hu : IsUnit b := by
    apply (Matrix.isUnit_iff_isUnit_det b).2
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_of_isUpperTriangular ht]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hdiag j)
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu)
    (fun i => if i.val < pivot then -a (Fin.castLE hh i) source else 0)
  have hc0 : ∀ j : Fin width, pivot ≤ j.val → c j = 0 := by
    intro j hj
    have h := congr_fun hc j
    simpa [b, show ¬j.val < pivot by omega, Matrix.mulVec, dotProduct] using h
  have hprefix : ∀ i : Fin height, i.val < pivot → a.mulVec c i = -a i source := by
    intro i hi
    let row : Fin width := ⟨i.val, hi.trans hp⟩
    have hrow : Fin.castLE hh row = i := Fin.ext rfl
    have h := congr_fun hc row
    have hsum : b.mulVec c row = a.mulVec c i := by
      change (∑ j, b row j * c j) = ∑ j, a i j * c j
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val < pivot
      · simp only [b, show row.val < pivot from hi, hj, ite_eq_left, hrow]
      · rw [hc0 j (by omega)]
        simp
    rw [hsum] at h
    simpa only [ite_eq_left (show row.val < pivot from hi), hrow] using h
  have htail : ∀ i : Fin height, pivot ≤ i.val → a.mulVec c i = 0 := by
    intro i hi
    change (∑ j, a i j * c j) = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < pivot
    · rw [hz i j hj (by omega), zero_mul]
    · rw [hc0 j (by omega), mul_zero]
  refine ⟨c + Pi.single source 1, ?_, ?_⟩
  · change c source + (Pi.single source 1 : Fin width → ℝ) source = 1
    simp [hc0 source le_rfl]
  · intro i
    simp only [Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec_single_one, Matrix.col_apply]
    by_cases hi : i.val < pivot
    · rw [hprefix i hi, ite_eq_left hi]
      ring
    · rw [htail i (by omega), ite_eq_right hi, zero_add]

/-- A column-Gram lower bound forces at least that much squared energy in
the next source column's active tail, after exact prefix cancellation. -/
theorem source_tail_energy_lower {height width : Nat}
    (a : Matrix (Fin height) (Fin width) ℝ) (pivot : Nat) (β : ℝ)
    (hh : width ≤ height) (hp : pivot < width) (hβ : 0 ≤ β)
    (hz : ∀ i j, j.val < pivot → j.val < i.val → a i j = 0)
    (hd : ∀ j : Fin width, j.val < pivot → a (Fin.castLE hh j) j ≠ 0)
    (hg : (a.transpose * a - β • 1).PosSemidef)
    : β ≤ ∑ i : Fin height with pivot ≤ i.val, (a i ⟨pivot, hp⟩) ^ 2 := by
  obtain ⟨x, hx, ha⟩ := source_tail_combination a pivot hh hp hz hd
  have hs : 1 ≤ ∑ j, (x j) ^ 2 := by
    have h := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ ⟨pivot, hp⟩)
    simpa only [hx, one_pow] using h
  have hq := Flare.Analysis.NumericalBounds.quadratic_lower_bound (a.transpose * a) β hg x
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at hq
  have he : a.mulVec x ⬝ᵥ a.mulVec x
      = ∑ i : Fin height with pivot ≤ i.val, (a i ⟨pivot, hp⟩) ^ 2 := by
    rw [dotProduct, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [ha i]
    by_cases hi : i.val < pivot
    · simp [hi, show ¬pivot ≤ i.val by omega]
    · simp [hi, show pivot ≤ i.val by omega, pow_two]
  rw [he] at hq
  exact (by nlinarith : β ≤ β * ∑ j, (x j) ^ 2).trans hq

/-- A quantitative source entry exists whenever its threshold's worst-case
energy over all rows is smaller than the retained column-Gram floor. -/
theorem source_tail_entry_witness {height width : Nat}
    (a : Matrix (Fin height) (Fin width) ℝ) (pivot : Nat) (β τ : ℝ)
    (hh : width ≤ height) (hp : pivot < width) (hτ : 0 ≤ τ)
    (hmargin : height * τ ^ 2 < β)
    (hz : ∀ i j, j.val < pivot → j.val < i.val → a i j = 0)
    (hd : ∀ j : Fin width, j.val < pivot → a (Fin.castLE hh j) j ≠ 0)
    (hg : (a.transpose * a - β • 1).PosSemidef)
    : ∃ i : Fin height, pivot ≤ i.val ∧ τ ≤ |a i ⟨pivot, hp⟩| := by
  have hβ : 0 ≤ β := (by positivity : 0 ≤ (height : ℝ) * τ ^ 2).trans hmargin.le
  have he := source_tail_energy_lower a pivot β hh hp hβ hz hd hg
  by_contra h
  push Not at h
  have hu : (∑ i : Fin height with pivot ≤ i.val, (a i ⟨pivot, hp⟩) ^ 2)
      ≤ height * τ ^ 2 := by
    rw [Finset.sum_filter]
    calc
      _ ≤ ∑ _i : Fin height, τ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : pivot ≤ i.val
        · rw [ite_eq_left hi]
          have hb := h i hi
          nlinarith [sq_abs (a i ⟨pivot, hp⟩), abs_nonneg (a i ⟨pivot, hp⟩)]
        · rw [ite_eq_right hi]
          positivity
      _ = _ := by simp
  linarith

/-- For at most eight rows, Gram floor `M² / 16` forces an active stored
source entry of magnitude at least `M / 16`. No success or witness is assumed. -/
theorem source_witness_eight (height width pivot : Nat) (current : Array Float) (M : ℝ)
    (hh : height ≤ 8) (hw : width ≤ height) (hp : pivot < width) (hM : 0 < M)
    (hz : ProcessedColumns height width pivot current)
    (hd : ∀ j, j < pivot → value (entry width current j j) ≠ 0)
    (hg
      : ((matrix height width current).transpose * matrix height width current
          - (M ^ 2 / 16) • 1).PosSemidef)
    : ∃ i, pivot ≤ i ∧ i < height ∧ M / 16 ≤ |value (entry width current i pivot)| := by
  have hzero : ∀ i j, j.val < pivot → j.val < i.val → matrix height width current i j = 0 := by
    intro i j hj hij
    change value (entry width current i.val j.val) = 0
    rw [hz j.val hj j.isLt i.val i.isLt hij, Flare.Binary64.Arithmetic.zero_value]
  have hdiag : ∀ j : Fin width, j.val < pivot →
      matrix height width current (Fin.castLE hw j) j ≠ 0 := by
    intro j hj
    exact hd j.val hj
  have hn : (height : ℝ) ≤ 8 := by exact_mod_cast hh
  have hcap := mul_le_mul_of_nonneg_right hn (sq_nonneg (M / 16))
  have hmargin : (height : ℝ) * (M / 16) ^ 2 < M ^ 2 / 16 := by
    nlinarith [sq_pos_of_pos hM]
  obtain ⟨i, hi, hm⟩ := source_tail_entry_witness (matrix height width current) pivot
    (M ^ 2 / 16) (M / 16) hw hp (by positivity) hmargin hzero hdiag hg
  exact ⟨i.val, hi, i.isLt, hm⟩

/-- The initial energy/rank headroom and preceding native profiles establish
the next source witness, with explicit scale floor `M ≥ 2⁻⁸⁹⁶`.
Profiles of the next or future pivots and final success are not premises. -/
theorem qrIterations_prefix_source_witness_eight (height width pivot : Nat)
    (a current : Array Float) (M : ℝ) (hh : height ≤ 8) (hw : width ≤ height)
    (hp : pivot < width) (hf : a.all Float.isFinite = true)
    (hscale : (2 : ℝ) ^ (-896 : Int) ≤ M)
    (initial : InitialGramBounds height width a (M ^ 2 / 2) (M ^ 2 / 8))
    (profiles
      : ∀ previousPivot,
          previousPivot < pivot
          → ∀ previous,
              qrIterations height width (List.range previousPivot) a = .ok previous
              → IterationProfile height width previousPivot previous M)
    (hrun : qrIterations height width (List.range pivot) a = .ok current)
    : ∃ i,
        pivot ≤ i
        ∧ i < height
        ∧ (2 : ℝ) ^ (-900 : Int) ≤ |value (entry width current i pivot)| := by
  have hM : 0 < M := (by positivity : 0 < (2 : ℝ) ^ (-896 : Int)).trans_le hscale
  have enclosure := FloatQRDomain.qrIterations_prefix_enclosure height width pivot a current
    (fun _ => M) _ _ hf initial profiles hrun
  have hgram := (FloatQRDomain.prefixEnclosure_budget_eight height width pivot current M hh hw
    hp.le hM.le enclosure).2
  obtain ⟨output, houtput, _, _, hz, hd, _⟩ :=
    FloatQRComposition.qrIterations_prefix_accuracy_of_profiles height width pivot a (fun _ => M) hf profiles
  have he : output = current := Except.ok.inj (houtput.symm.trans hrun)
  subst output
  obtain ⟨i, hi, hib, hm⟩ := source_witness_eight height width pivot current M hh hw hp hM hz hd hgram
  have hfloor : (2 : ℝ) ^ (-900 : Int) ≤ M / 16 := by
    calc
      _ = (2 : ℝ) ^ (-896 : Int) / 16 := by
        rw [show (-900 : Int) = -896 + -4 by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right hscale (by norm_num)
  exact ⟨i, hi, hib, hfloor.trans hm⟩

end Kalman.Proofs.FloatQRSourceTail
