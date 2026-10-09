import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRApplication

/-! The source-column overwrite in native QR: checked diagonal rescaling, then
positive-zero tail writes. Bounds compare with the same decoded source column. -/

namespace Kalman.Proofs.FloatQRFinish

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.FloatDenseError
open Flare.Binary64.Value

theorem finishColumn_schedule (width column first : Nat) (tail : List Nat)
    (a : Array Float) (alpha scale : Float)
    : finishColumn width column first tail a alpha scale
      = (do
          let diagonal ← finite (alpha * scale)
          let mut a := a.set! (first * width + column) diagonal
          for i in tail do
            a := a.set! (i * width + column) 0.0
          return a) := by
  simp [finishColumn, zeroColumn]

/-- Extraction preserves the old QR range block on all operands, including
empty ranges and rejection of exceptional rescaling products. -/
theorem finishColumn_range_schedule (height width column first : Nat)
    (a : Array Float) (alpha scale : Float)
    : finishColumn width column first (List.range' (first + 1) (height - (first + 1))) a
        alpha scale
      = (do
          let diagonal ← finite (alpha * scale)
          let mut a := a.set! (first * width + column) diagonal
          for i in [first + 1:height] do
            a := a.set! (i * width + column) 0.0
          return a) := by
  simpa only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]
    using finishColumn_schedule width column first
      (List.range' (first + 1) (height - (first + 1))) a alpha scale

/-- Active QR range as a head followed by the exact zero-write tail. -/
theorem active_range_cons (height first : Nat) (h : first < height)
    : List.range' first (height - first)
      = first :: List.range' (first + 1) (height - (first + 1)) := by
  rw [show height - first = (height - (first + 1)) + 1 by omega, List.range'_succ]

private theorem set_read (a : Array Float) (k t : Nat) (x : Float) (hk : k < a.size)
    : (a.set! k x).getD t 0.0 = if t = k then x else a.getD t 0.0 := by
  by_cases ht : t = k
  · subst t
    simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hk]
  · simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, ht,
      Array.getElem?_setIfInBounds_ne (Ne.symm ht)]

private theorem zeroColumn_cons (width column i : Nat) (tail : List Nat) (a : Array Float)
    : zeroColumn width column (i :: tail) a
      = zeroColumn width column tail (a.set! (i * width + column) 0.0) := by
  simp [zeroColumn]

/-- Tail writes preserve shape, finiteness and every unvisited stored value.
Duplicates are harmless here; distinctness is needed for the reflector stages. -/
theorem zeroColumn_storage (width column : Nat) (tail : List Nat) (a : Array Float)
    (hf : a.all Float.isFinite = true) (hb : ∀ i ∈ tail, i * width + column < a.size)
    : ∃ output,
        zeroColumn width column tail a = .ok output
        ∧ output.size = a.size
        ∧ output.all Float.isFinite = true
        ∧ (∀ t,
            output.getD t 0.0
            = if ∃ i ∈ tail, t = i * width + column then 0.0 else a.getD t 0.0) := by
  induction tail generalizing a with
  | nil => exact ⟨a, rfl, rfl, hf, by simp⟩
  | cons i tail ih =>
      have hi := hb i (by simp)
      have hs : (a.set! (i * width + column) 0.0).size = a.size := by simp
      have hfinite := Flare.Matrix.Storage.all_set a (i * width + column) 0.0
        hf (by decide)
      obtain ⟨output, hout, hos, hof, hor⟩ := ih (a.set! (i * width + column) 0.0)
        hfinite
        (by simpa only [hs] using fun j hj => hb j (by simp [hj]))
      refine ⟨output, by rw [zeroColumn_cons]; exact hout, hos.trans hs, hof, ?_⟩
      intro t
      rw [hor, set_read a _ t _ hi]
      by_cases ht : t = i * width + column
      · simp [ht]
      · by_cases hex : ∃ j ∈ tail, t = j * width + column
        · simp [hex]
        · simp [hex, ht]

private theorem slot_ne {width column i j : Nat} (hw : 0 < width) (hij : i ≠ j)
    : i * width + column ≠ j * width + column :=
  fun he => hij (Nat.mul_right_cancel hw (Nat.add_right_cancel he))

/-- The rescaling multiplication is finite, stays away from zero, and has
absolute error at most 2^-49 times the stored scale. -/
theorem diagonal_rescaling (alpha scale : Float)
    (ha : alpha.isFinite = true) (hs : scale.isFinite = true)
    (hl : (2 : ℝ) ^ (-900 : Int) ≤ value scale)
    (hu : value scale ≤ (2 : ℝ) ^ (900 : Int))
    (hal : (1 : ℝ) / 2 ≤ |value alpha|) (hau : |value alpha| ≤ 6)
    : (alpha * scale).isFinite = true
      ∧ |value (alpha * scale) - value alpha * value scale|
        ≤ (2 : ℝ) ^ (-49 : Int) * value scale
      ∧ value scale / 4 ≤ |value (alpha * scale)|
      ∧ |value (alpha * scale)| ≤ 7 * value scale := by
  have hp : 0 < value scale := (zpow_pos (by norm_num) _).trans_le hl
  have hη : (2 : ℝ) ^ (-1022 : Int) ≤ value scale :=
    (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-1022 : Int) ≤ -900)).trans hl
  have hx : |value alpha * value scale| ≤ 6 * value scale := by
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_right hau hp.le
  have hlimit : 6 * value scale ≤ (2 : ℝ) ^ (1000 : Int) := by
    calc
      _ ≤ 8 * (2 : ℝ) ^ (900 : Int) := by
        exact (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 6)).trans
          (mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 8)
            (zpow_pos (by norm_num : (0 : ℝ) < 2) (900 : Int)).le)
      _ = (2 : ℝ) ^ (903 : Int) := by
        rw [show (903 : Int) = 3 + 900 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num only [show (2 : ℝ) ^ (3 : Int) = 8 by norm_num]
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨hf, he⟩ := Flare.Binary64.Nearest.mul_error_nearest alpha scale ha hs (hx.trans hlimit)
  have herr : |value (alpha * scale) - value alpha * value scale|
      ≤ (2 : ℝ) ^ (-49 : Int) * value scale := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hx hη)
      (by positivity : 0 ≤ (2 : ℝ) ^ (-53 : Int))
    norm_num only [show (2 : ℝ) ^ (-53 : Int) = 1 / 9007199254740992 by norm_num,
      show (2 : ℝ) ^ (-49 : Int) = 1 / 562949953421312 by norm_num] at he hh ⊢
    linarith
  have hlow : value scale / 2 ≤ |value alpha * value scale| := by
    rw [abs_mul, abs_of_pos hp]
    nlinarith
  have hd1 := abs_sub_le (value alpha * value scale) (value (alpha * scale)) 0
  have hd2 := abs_sub_le (value (alpha * scale)) (value alpha * value scale) 0
  rw [sub_zero, sub_zero, abs_sub_comm] at hd1
  rw [sub_zero, sub_zero] at hd2
  norm_num only [show (2 : ℝ) ^ (-49 : Int) = 1 / 562949953421312 by norm_num] at herr
  refine ⟨hf, ?_, by linarith, by linarith⟩
  norm_num only [show (2 : ℝ) ^ (-49 : Int) = 1 / 562949953421312 by norm_num]
  exact herr

private theorem abs_map_sum (indices : List Nat) (f : Nat → ℝ)
    : |(indices.map f).sum| ≤ (indices.map (fun i => |f i|)).sum := by
  induction indices with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

/-- A purely real annihilation estimate for the stored constructed vector b.
The small defect b-q+alpha*e_first includes both rounded divisions and subtraction. -/
theorem source_reflection_residual (first : Nat) (tail : List Nat) (q b : Nat → ℝ)
    (alpha : ℝ) (_hn : (first :: tail).length ≤ 32) (hf : first ∉ tail)
    (hq : ∀ i ∈ first :: tail, |q i| ≤ 1) (hb : ∀ i ∈ first :: tail, |b i| ≤ 9)
    (ha : |alpha| ≤ 6)
    (he
      : ∀ i ∈ first :: tail,
          |b i - q i + (if i = first then alpha else 0)| ≤ (2 : ℝ) ^ (-48 : Int))
    (hs : (1 : ℝ) / 16 ≤ ((first :: tail).map (fun i => (b i) ^ 2)).sum)
    (hnorm
      : |alpha ^ 2 - ((first :: tail).map (fun i => (q i) ^ 2)).sum|
        ≤ columnNormRadius (first :: tail).length)
    : ∀ i ∈ first :: tail,
        |q i
          - 2
            * b i
            * ((first :: tail).map (fun j => b j * q j)).sum
            / ((first :: tail).map (fun j => (b j) ^ 2)).sum
          - (if i = first then alpha else 0)|
        ≤ sourceResidualRadius (first :: tail).length := by
  let I := first :: tail
  let A := fun i => if i = first then alpha else 0
  let S := (I.map (fun i => (b i)^2)).sum
  let B := (I.map (fun i => b i * q i)).sum
  let T := (I.map (fun i => (q i)^2)).sum
  have hA : ∀ i, |A i| ≤ 6 := by
    intro i
    dsimp [A]
    split_ifs
    · exact ha
    · norm_num
  have hterm : ∀ i ∈ I, |(b i-q i)^2-(A i)^2| ≤ (2 : ℝ) ^ (-44 : Int) := by
    intro i hi
    have hrest : |b i-q i-A i| ≤ 16 := by
      have hh := abs_sub (b i-q i) (A i)
      have hh' := abs_sub (b i) (q i)
      linarith [hb i hi, hq i hi, hA i]
    rw [show (b i-q i)^2-(A i)^2 = (b i-q i+A i)*(b i-q i-A i) by ring, abs_mul]
    have hh := mul_le_mul (he i hi) hrest (abs_nonneg _) (by positivity)
    norm_num at hh ⊢
    exact hh
  have htail : ∀ i ∈ tail, |(b i - q i)^2| ≤ ((2 : ℝ) ^ (-48 : Int))^2 := by
    intro i hi
    have hif : i ≠ first := fun h => hf (h ▸ hi)
    have hei := he i (List.mem_cons_of_mem first hi)
    simp only [ite_eq_right hif, add_zero] at hei
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [(sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hei, sq_abs (b i - q i)]
  have hdiff : |(I.map (fun i => (b i-q i)^2)).sum-alpha^2|
      ≤ (2 : ℝ)^(-44 : Int) + I.length * ((2 : ℝ)^(-48 : Int))^2 := by
    have hh : |(tail.map (fun i => (b i-q i)^2)).sum|
        ≤ tail.length * ((2 : ℝ)^(-48 : Int))^2 := by
      calc
        _ ≤ _ := abs_map_sum tail _
        _ ≤ (tail.map (fun _ => ((2 : ℝ) ^ (-48 : Int)) ^ 2)).sum := List.sum_le_sum htail
        _ = _ := by simp
    have hfirst := hterm first (by simp [I])
    simp only [A, ite_eq_left rfl] at hfirst
    have ht := abs_add_le ((b first - q first)^2 - alpha^2)
      ((tail.map (fun i => (b i-q i)^2)).sum)
    change |(b first-q first)^2 + (tail.map (fun i => (b i-q i)^2)).sum-alpha^2| ≤ _
    rw [show (b first-q first)^2 + (tail.map (fun i => (b i-q i)^2)).sum-alpha^2 =
      ((b first-q first)^2-alpha^2) + (tail.map (fun i => (b i-q i)^2)).sum by ring]
    simp only [I, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hidentity : S - 2*B = (I.map (fun i => (b i-q i)^2)).sum-T := by
    dsimp [S, B, T]
    induction I with
    | nil => simp
    | cons i is ih => simp only [List.map_cons, List.sum_cons] at *; nlinarith
  let defect := (2 : ℝ)^(-44 : Int) + I.length * ((2 : ℝ)^(-48 : Int))^2
    + columnNormRadius I.length
  have hdefect : |S - 2*B| ≤ defect := by
    rw [hidentity]
    have hh := abs_sub_le ((I.map (fun i => (b i-q i)^2)).sum) (alpha^2) T
    change |alpha^2-T| ≤ columnNormRadius I.length at hnorm
    dsimp [defect]
    linarith
  have hd0 : 0 ≤ defect := (abs_nonneg _).trans hdefect
  intro i hi
  have hp : 0 < S := by dsimp [S, I]; linarith
  have hid : q i-2*b i*B/S-A i = -(b i-q i+A i)+b i*(S-2*B)/S := by
    field_simp [ne_of_gt hp]
    ring
  change |q i-2*b i*B/S-A i| ≤ _
  rw [hid]
  have hbsq : (b i) ^ 2 ≤ S := by
    apply List.single_le_sum
    · intro z hz
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
      positivity
    · exact List.mem_map.mpr ⟨i, hi, rfl⟩
  have hbS : |b i| ≤ 4 * S := by
    have hS : (1 : ℝ) / 16 ≤ S := hs
    nlinarith [sq_abs (b i), abs_nonneg (b i), mul_nonneg hp.le (sub_nonneg.mpr hS)]
  have hprod := mul_le_mul hbS hdefect (abs_nonneg _) (by positivity : 0 ≤ 4 * S)
  have hquot : |b i*(S-2*B)/S| ≤ 4 * defect := by
    rw [abs_div, abs_mul, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hh := abs_add_le (-(b i-q i+A i)) (b i*(S-2*B)/S)
  rw [abs_neg] at hh
  have hei : |b i-q i+A i| ≤ (2 : ℝ)^(-48 : Int) := he i hi
  change _ ≤ sourceResidualRadius I.length
  unfold sourceResidualRadius
  change _ ≤ (2 : ℝ)^(-48 : Int) + 4 * defect
  exact hh.trans (add_le_add hei hquot)

/-- Storage contract of the actual finish helper, independent of the numerical
construction of alpha. Unvisited entries are preserved as Float values. -/
theorem finishColumn_storage (height width column first : Nat) (tail : List Nat)
    (a : Array Float) (alpha scale : Float)
    (hf : a.all Float.isFinite = true) (hs : a.size = height * width)
    (hc : column < width) (hi : ∀ i ∈ first :: tail, i < height)
    (hn : first ∉ tail) (hd : (alpha * scale).isFinite = true)
    : ∃ output,
        finishColumn width column first tail a alpha scale = .ok output
        ∧ output.size = a.size
        ∧ output.all Float.isFinite = true
        ∧ entry width output first column = alpha * scale
        ∧ (∀ i ∈ tail, entry width output i column = 0.0)
        ∧ (∀ t,
            t ≠ first * width + column
            → (∀ i ∈ tail, t ≠ i * width + column)
            → output.getD t 0.0 = a.getD t 0.0) := by
  have hw : 0 < width := (Nat.zero_le column).trans_lt hc
  have hslot : ∀ i ∈ first :: tail, i * width + column < a.size := by
    intro i him
    rw [hs]
    have h := Nat.mul_le_mul_right width (show i + 1 ≤ height by have := hi i him; omega)
    rw [Nat.add_mul] at h
    omega
  let start := a.set! (first * width + column) (alpha * scale)
  have hstart : start.size = a.size := by simp [start]
  obtain ⟨output, hout, hos, hof, hor⟩ := zeroColumn_storage width column tail start
    (Flare.Matrix.Storage.all_set a _ _ hf hd)
    (fun i him => by rw [hstart]; exact hslot i (by simp [him]))
  refine ⟨output, ?_, hos.trans hstart, hof, ?_, ?_, ?_⟩
  · unfold finishColumn
    rw [finite_ok _ hd]
    exact hout
  · change output.getD (first * width + column) 0.0 = _
    rw [hor]
    have hno : ¬ ∃ i ∈ tail, first * width + column = i * width + column := by
      rintro ⟨i, him, he⟩
      exact slot_ne hw (show first ≠ i from fun heq => hn (heq.symm ▸ him)) he
    rw [ite_eq_right hno]
    exact (set_read a _ _ _ (hslot first (by simp))).trans (ite_eq_left rfl)
  · intro i him
    change output.getD (i * width + column) 0.0 = _
    rw [hor, ite_eq_left (show ∃ j ∈ tail, i * width + column = j * width + column from ⟨i, him, rfl⟩)]
  · intro t hfirst htail
    rw [hor, ite_eq_right (show ¬ ∃ i ∈ tail, t = i * width + column from
      fun ⟨i, him, he⟩ => htail i him he)]
    exact (set_read a _ t _ (hslot first (by simp))).trans (ite_eq_right hfirst)

private theorem squared_rescaling (alpha scale : Float) (T : ℝ)
    (he
      : |value (alpha * scale) - value alpha * value scale|
        ≤ (2 : ℝ) ^ (-49 : Int) * value scale)
    (hd : |value (alpha * scale)| ≤ 7 * value scale)
    (ha : |value alpha| ≤ 6) (hs : 0 < value scale)
    (hn : |(value alpha) ^ 2 - T| ≤ (2 : ℝ) ^ (-38 : Int))
    : |(value (alpha * scale)) ^ 2 - T * (value scale) ^ 2|
      ≤ (2 : ℝ) ^ (-37 : Int) * (value scale) ^ 2 := by
  have hex : |value alpha*value scale| ≤ 6*value scale := by
    rw [abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_right ha hs.le
  have hsum : |value (alpha * scale)+value alpha*value scale| ≤ 13*value scale :=
    (abs_add_le _ _).trans (by linarith)
  have hp : |(value (alpha * scale))^2-(value alpha*value scale)^2|
      ≤ 13*(2 : ℝ)^(-49 : Int)*(value scale)^2 := by
    rw [show (value (alpha * scale))^2-(value alpha*value scale)^2 =
      (value (alpha * scale)-value alpha*value scale)*(value (alpha * scale)+value alpha*value scale) by ring,
      abs_mul]
    have h := mul_le_mul he hsum (abs_nonneg _) (by positivity)
    nlinarith
  have hq : |(value alpha*value scale)^2-T*(value scale)^2|
      ≤ (2 : ℝ)^(-38 : Int)*(value scale)^2 := by
    rw [show (value alpha*value scale)^2-T*(value scale)^2 =
      ((value alpha)^2-T)*(value scale)^2 by ring, abs_mul, abs_of_nonneg (sq_nonneg (value scale))]
    exact mul_le_mul_of_nonneg_right hn (sq_nonneg _)
  have ht := abs_sub_le ((value (alpha * scale))^2) ((value alpha*value scale)^2) (T*(value scale)^2)
  norm_num only [show (2 : ℝ)^(-49 : Int) = 1/562949953421312 by norm_num,
    show (2 : ℝ)^(-38 : Int) = 1/274877906944 by norm_num,
    show (2 : ℝ)^(-37 : Int) = 1/137438953472 by norm_num] at hp hq ⊢
  nlinarith [sq_nonneg (value scale)]

private theorem source_square_scaling (width column : Nat) (indices : List Nat)
    (a : Array Float) (scale : Float) (hs : value scale ≠ 0)
    : sourceColumnSquares width column indices a
      = normalizedSquares indices (fun i => entry width a i column) scale
        * (value scale) ^ 2 := by
  unfold sourceColumnSquares normalizedSquares
  rw [← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  field_simp [hs]

private theorem constructed_source_formula (width column first : Nat) (indices : List Nat)
    (v a : Array Float) (norm scale : Float)
    (hS : 0 < vectorSquares indices (constructedVector first v norm))
    (hs : value scale ≠ 0) (i : Nat)
    : constructedAppliedValue width column first indices v norm a i
      = value scale
        * (value (entry width a i column) / value scale
            - 2
              * value ((constructedVector first v norm).getD i 0.0)
              * (indices.map
                  (fun j =>
                    value ((constructedVector first v norm).getD j 0.0)
                    * (value (entry width a j column) / value scale))).sum
              / vectorSquares indices (constructedVector first v norm)) := by
  let b := constructedVector first v norm
  let S := vectorSquares indices b
  let root := Real.sqrt S
  have hr : 0 < root := Real.sqrt_pos.mpr hS
  have hr2 : root^2 = S := Real.sq_sqrt hS.le
  have hd : (indices.map (fun j => value (b.getD j 0.0)/root * value (entry width a j column))).sum =
      (value scale/root)*(indices.map (fun j => value (b.getD j 0.0)
        * (value (entry width a j column)/value scale))).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    field_simp
  change value (entry width a i column)-2*(value (b.getD i 0.0)/root)*
    (indices.map (fun j => value (b.getD j 0.0)/root*value (entry width a j column))).sum = _
  rw [hd]
  change _ = value scale*(value (entry width a i column)/value scale-2*value (b.getD i 0.0)*
    (indices.map (fun j => value (b.getD j 0.0)*(value (entry width a j column)/value scale))).sum/S)
  rw [← hr2]
  field_simp [ne_of_gt hr, hs]

set_option maxHeartbeats 800000 in
/-- Original stored source-column conditions establish all three native stages,
including nonzero diagonal rescaling and the forced-zero approximation bound. -/
theorem scaledColumn_finish_accuracy (height width column first : Nat) (tail : List Nat)
    (a : Array Float) (p : SourceColumnProfile height width column first tail a)
    : SourceColumnAccuracy height width column first tail a := by
  let I := first :: tail
  let x := fun i => entry width a i column
  have input : ColumnProfile height I x := by
    refine ⟨p.length_le, p.in_bounds, ?_, ?_⟩
    · intro i _
      exact Flare.Matrix.Storage.getD_finite a _ p.matrix_finite
    · obtain ⟨i, hi, he⟩ := p.scale_witness
      refine ⟨i, hi, ?_⟩
      have hp := (zpow_pos (by norm_num : (0 : ℝ)<2) (-900 : Int)).trans_le he
      exact abs_pos.mp hp
  obtain ⟨scale, v, norm, hrun, hscale, hsf, hsp, hvs, hvf, _, hve, hnf, hnp, hsq, _⟩ :=
    FloatQRNorm.scaledColumnNorm_accuracy height I x input
  have hb : ∀ i ∈ I, |value (x i)| ≤ value scale := by
    rw [hscale]
    exact (FloatQRNorm.columnScale_correct I x input.finite input.nonzero).2.2.1
  have hc : ∃ i ∈ I, value scale = |value (x i)| := by
    rw [hscale]
    exact (FloatQRNorm.columnScale_correct I x input.finite input.nonzero).2.2.2
  have hsl : (2 : ℝ)^(-900 : Int) ≤ value scale := by
    obtain ⟨i, hi, he⟩ := p.scale_witness
    exact he.trans (hb i hi)
  have hsu : value scale ≤ (2 : ℝ)^(900 : Int) := by
    obtain ⟨i, hi, he⟩ := hc
    rw [he]
    exact p.entry_upper i hi
  obtain ⟨hlo, hhi⟩ := FloatQRNorm.normalizedSquares_bounds I x scale hsp hb hc
  have herr := hsq.trans (FloatQRNorm.columnNormRadius_le input.length_le)
  have hn32 : (I.length : ℝ) ≤ 32 := by exact_mod_cast input.length_le
  have hnormlo : (1 : ℝ)/2 ≤ value norm := by
    have h := (abs_le.mp herr).1
    norm_num at h
    nlinarith
  have hnormhi : value norm ≤ 6 := by
    have h := (abs_le.mp herr).2
    norm_num at h
    nlinarith
  have hq : ∀ i ∈ I, |value (x i)/value scale| ≤ 1 := by
    intro i hi
    rw [abs_div, abs_of_pos hsp]
    exact (div_le_one hsp).mpr (hb i hi)
  have hvb : ∀ i ∈ I, |value (v.getD i 0.0)| ≤ 2 := by
    intro i hi
    have h := abs_sub_le (value (v.getD i 0.0)) (value (x i)/value scale) 0
    simp only [sub_zero] at h
    have he := hve i hi
    have hqi := hq i hi
    norm_num at h he hqi ⊢
    linarith
  have hn : I.Nodup := List.nodup_cons.mpr ⟨p.first_not_tail, p.tail_nodup⟩
  have hfirst : first ∈ I := by simp [I]
  have profile : ReflectorProfile first I v norm :=
    ⟨input.length_le, hn, hfirst, by simpa [hvs] using input.in_bounds, hvf, hvb, hnf, hnormlo, hnormhi⟩
  obtain ⟨alpha, w, hreflect, halpha, haf, hab, _, hhead, hmargin, _, _, _, hwe, hunit⟩ :=
    FloatQRReflector.householderReflector_accuracy first I v norm profile
  have hablo : (1 : ℝ)/2 ≤ |value alpha| := by rw [hab]; exact hnormlo
  have habhi : |value alpha| ≤ 6 := by rw [hab]; exact hnormhi
  obtain ⟨hdf, hde, hdlo, hdhi⟩ := diagonal_rescaling alpha scale haf hsf hsl hsu hablo habhi
  obtain ⟨output, hout, hos, hof, hdiag, hzero, hcopy⟩ := finishColumn_storage height width column first
    tail a alpha scale p.matrix_finite p.matrix_size p.column_bound p.in_bounds p.first_not_tail hdf
  have hαsq : (value alpha)^2 = (value norm)^2 := by nlinarith [sq_abs (value alpha)]
  have hsqα : |(value alpha)^2-normalizedSquares I x scale| ≤ (2 : ℝ)^(-38 : Int) := by
    rw [hαsq]
    exact herr
  have hsquared := squared_rescaling alpha scale (normalizedSquares I x scale) hde hdhi habhi hsp hsqα
  have hsref := source_square_scaling width column I a scale (ne_of_gt hsp)
  let b := constructedVector first v norm
  have hread : ∀ i, b.getD i 0.0 = if i = first then v.getD first 0.0-alpha else v.getD i 0.0 := by
    intro i
    dsimp only [b, constructedVector]
    rw [← halpha, set_read v first i _ (profile.in_bounds first hfirst)]
  have hbb : ∀ i ∈ I, |value (b.getD i 0.0)| ≤ 9 := by
    intro i hi
    rw [hread i]
    by_cases heq : i = first
    · rw [ite_eq_left heq]
      have ht := abs_sub_le (value (v.getD first 0.0-alpha)) (value (v.getD first 0.0)-value alpha) 0
      have hu := abs_sub (value (v.getD first 0.0)) (value alpha)
      simp only [sub_zero] at ht
      have hvi := hvb first hfirst
      norm_num at ht hu hhead hvi habhi ⊢
      linarith
    · rw [ite_eq_right heq]
      exact (hvb i hi).trans (by norm_num)
  have hS : (1 : ℝ)/16 ≤ vectorSquares I b := by
    have hterm : (value (b.getD first 0.0))^2 ≤ vectorSquares I b := by
      apply List.single_le_sum
      · intro z hz
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
        exact sq_nonneg _
      · exact List.mem_map.mpr ⟨first, hfirst, rfl⟩
    have hreadfirst : b.getD first 0.0 = v.getD first 0.0-alpha := by simp [hread]
    rw [hreadfirst] at hterm
    nlinarith [sq_abs (value (v.getD first 0.0-alpha))]
  have hdefect : ∀ i ∈ I, |value (b.getD i 0.0)-value (x i)/value scale+
      (if i = first then value alpha else 0)| ≤ (2 : ℝ)^(-48 : Int) := by
    intro i hi
    rw [hread i]
    by_cases heq : i = first
    · subst i
      rw [ite_eq_left rfl, ite_eq_left rfl]
      have hid : value (v.getD first 0.0-alpha)-value (x first)/value scale+value alpha =
          (value (v.getD first 0.0-alpha)-(value (v.getD first 0.0)-value alpha))+
            (value (v.getD first 0.0)-value (x first)/value scale) := by ring
      rw [hid]
      have ht := abs_add_le
        (value (v.getD first 0.0-alpha)-(value (v.getD first 0.0)-value alpha))
        (value (v.getD first 0.0)-value (x first)/value scale)
      have he := hve first hi
      norm_num at ht hhead he ⊢
      linarith
    · rw [ite_eq_right heq, ite_eq_right heq, add_zero]
      exact (hve i hi).trans (by norm_num)
  have hres := source_reflection_residual first tail (fun i => value (x i)/value scale)
    (fun i => value (b.getD i 0.0)) (value alpha) p.length_le p.first_not_tail hq hbb habhi hdefect hS (by rw [hαsq]; exact hsq)
  have hconstructed : ∀ i ∈ I,
      |constructedAppliedValue width column first I v norm a i - value scale *
        (if i = first then value alpha else 0)| ≤ sourceResidualRadius I.length * value scale := by
    intro i hi
    rw [constructed_source_formula width column first I v a norm scale (by linarith) (ne_of_gt hsp) i]
    rw [← mul_sub, abs_mul, abs_of_pos hsp]
    have h := mul_le_mul_of_nonneg_left (hres i hi) hsp.le
    exact h.trans_eq (mul_comm _ _)
  have hperturb := FloatQRApplication.constructed_perturbation width column first I w v a norm (value scale)
    (FloatQRApplication.nearUnit_magnitude I w
      (hunit.trans (FloatQRReflector.reflectorRadius_le input.length_le))) hb hwe
  have hwrite : ∀ i ∈ I,
      |value (entry width output i column)-value scale*(if i = first then value alpha else 0)|
        ≤ (2 : ℝ)^(-49 : Int)*value scale := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hdiag, ite_eq_left rfl, mul_comm (value scale) (value alpha)]
      exact hde
    · have hne : i ≠ first := fun heq => p.first_not_tail (heq ▸ hi)
      rw [hzero i hi, ite_eq_right hne, mul_zero, Flare.Binary64.Arithmetic.zero_value, sub_self, abs_zero]
      positivity
  have hguard : 0.0 < (entry width output first column).abs := by
    rw [hdiag]
    obtain ⟨habsf, habsv⟩ := Flare.Binary64.Order.abs_value (alpha * scale) hdf
    apply (Flare.Binary64.Order.lt_iff _ _ (by decide) habsf).mpr
    rw [Flare.Binary64.Arithmetic.zero_value, habsv]
    linarith
  refine ⟨
    scale,
    v,
    norm,
    alpha,
    w,
    output,
    hrun,
    hreflect,
    hout,
    hsf,
    hsp,
    hos,
    hof,
    hdiag,
    by simpa only [hdiag] using hdlo,
    hguard,
    hzero,
    hcopy,
    ?_,
    ?_
  ⟩
  · rw [hdiag, hsref]
    exact hsquared
  · intro i hi
    have ht := abs_sub_le (value (entry width output i column))
      (value scale*(if i = first then value alpha else 0))
      (reflectorAppliedValue width column I w a i)
    have ht' := abs_sub_le (value scale*(if i = first then value alpha else 0))
      (constructedAppliedValue width column first I v norm a i)
      (reflectorAppliedValue width column I w a i)
    rw [abs_sub_comm (value scale*_) (constructedAppliedValue _ _ _ _ _ _ _ _),
      abs_sub_comm (constructedAppliedValue _ _ _ _ _ _ _ _) (reflectorAppliedValue _ _ _ _ _ _)] at ht'
    exact ht.trans (add_le_add (hwrite i hi) (ht'.trans (add_le_add (hconstructed i hi) (hperturb i hi))))
      |>.trans (by unfold sourceWriteRadius; ring_nf; exact le_rfl)

/-- The public source allowance increases with active length. -/
theorem sourceWriteRadius_mono {k l : Nat} (hkl : k ≤ l) (scale : ℝ) (hs : 0 ≤ scale)
    : sourceWriteRadius k scale ≤ sourceWriteRadius l scale := by
  unfold sourceWriteRadius sourceResidualRadius columnNormRadius squareSumRadius reflectorRadius
  gcongr

theorem sourceWriteRadius_le {k : Nat} (scale : ℝ) (hk : k ≤ 32) (hs : 0 ≤ scale)
    : sourceWriteRadius k scale ≤ (2 : ℝ) ^ (-18 : Int) * scale := by
  apply (sourceWriteRadius_mono hk scale hs).trans
  norm_num [sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius]
  nlinarith

/-- Sharper cap from the tightened reflector and source estimates. -/
theorem sourceWriteRadius_le_tight {k : Nat} (scale : ℝ) (hk : k ≤ 32) (hs : 0 ≤ scale)
    : sourceWriteRadius k scale ≤ (2 : ℝ) ^ (-32 : Int) * scale := by
  apply (sourceWriteRadius_mono hk scale hs).trans
  norm_num [sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius]
  nlinarith

end Kalman.Proofs.FloatQRFinish
