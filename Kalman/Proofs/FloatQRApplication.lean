import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRReflector

/-! Application of the actual stored Householder vector to one matrix column.
The proof follows the separately rounded dot, doubling, multiply/subtract, and
in-place writes. The first reference uses the same stored vector and column. -/

namespace Kalman.Proofs.FloatQRApplication

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.FloatDenseError
open Flare.Binary64.Value

theorem applyReflector_schedule (width column : Nat) (indices : List Nat)
    (v a : Array Float)
    : applyReflector width column indices v a
      = (do
          let mut dot := 0.0
          for i in indices do
            let term ← finite (v.getD i 0.0 * entry width a i column)
            dot ← finite (dot + term)
          let twice ← finite (2.0 * dot)
          let mut a := a
          for i in indices do
            let term ← finite (v.getD i 0.0 * twice)
            let value ← finite (entry width a i column - term)
            a := a.set! (i * width + column) value
          return a) := by
  simp [applyReflector, reflectorDot, reflectorUpdates]

/-- Extraction preserves the QR range block, including exceptional operands,
empty ranges, and all early finite-check rejections. -/
theorem applyReflector_range_schedule (height width column first : Nat)
    (v a : Array Float)
    : applyReflector width column (List.range' first (height - first)) v a
      = (do
          let mut dot := 0.0
          for i in [first:height] do
            let term ← finite (v.getD i 0.0 * entry width a i column)
            dot ← finite (dot + term)
          let twice ← finite (2.0 * dot)
          let mut a := a
          for i in [first:height] do
            let term ← finite (v.getD i 0.0 * twice)
            let value ← finite (entry width a i column - term)
            a := a.set! (i * width + column) value
          return a) := by
  simpa only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]
    using applyReflector_schedule width column (List.range' first (height - first)) v a

private theorem budget_pos (M : ℝ) (hl : (2 : ℝ) ^ (-1022 : Int) ≤ M) : 0 < M :=
  (zpow_pos (by norm_num) _).trans_le hl

private theorem budget_limit (M : ℝ) (hu : M ≤ (2 : ℝ) ^ (900 : Int))
    : 512 * M ≤ (2 : ℝ) ^ (1000 : Int) := by
  calc
    _ ≤ 512 * (2 : ℝ) ^ (900 : Int) := mul_le_mul_of_nonneg_left hu (by norm_num)
    _ = (2 : ℝ) ^ (909 : Int) := by
      rw [show (909 : Int) = 9 + 900 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num only [show (2 : ℝ) ^ (9 : Int) = 512 by norm_num]
    _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)

private theorem dot_budget (M : ℝ) (hl : (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hu : M ≤ (2 : ℝ) ^ (900 : Int))
    : (2 : ℝ) ^ (-1022 : Int) ≤ 64 * M ∧ 64 * M ≤ (2 : ℝ) ^ (990 : Int) := by
  refine ⟨by linarith [budget_pos M hl], ?_⟩
  calc
    _ ≤ 64 * (2 : ℝ) ^ (900 : Int) := mul_le_mul_of_nonneg_left hu (by norm_num)
    _ = (2 : ℝ) ^ (906 : Int) := by
      rw [show (906 : Int) = 6 + 900 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num only [show (2 : ℝ) ^ (6 : Int) = 64 by norm_num]
    _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)

private theorem rounding_radius (M t : ℝ) (hl : (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (ht : |t| ≤ 511 * M)
    : (2 : ℝ) ^ (-53 : Int) * (|t| + (2 : ℝ) ^ (-1022 : Int))
      ≤ (2 : ℝ) ^ (-44 : Int) * M := by
  have h := mul_le_mul_of_nonneg_left (add_le_add ht hl)
    (by positivity : 0 ≤ (2 : ℝ) ^ (-53 : Int))
  norm_num only [show (2 : ℝ) ^ (-53 : Int) = 1 / 9007199254740992 by norm_num,
    show (2 : ℝ) ^ (-44 : Int) = 1 / 17592186044416 by norm_num] at h ⊢
  linarith

private theorem reflectorDot_cons (width column i : Nat) (indices : List Nat)
    (v a : Array Float) (s : Float)
    : reflectorDot width column (i :: indices) v a s
      = (do
          let term ← finite (v.getD i 0.0 * entry width a i column)
          let next ← finite (s + term)
          reflectorDot width column indices v a next) := by
  simp [reflectorDot, List.forIn_cons, bind_assoc]

private theorem dot_loop (width column : Nat) (indices : List Nat) (v a : Array Float)
    (M : ℝ) (hv : v.all Float.isFinite = true) (ha : a.all Float.isFinite = true)
    (hbv : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 2)
    (hba : ∀ i ∈ indices, |value (entry width a i column)| ≤ M)
    (hl : (2 : ℝ) ^ (-1022 : Int) ≤ M) (hu : M ≤ (2 : ℝ) ^ (900 : Int)) (s : Float)
    (target : ℝ) (p : Nat) (hlen : p + indices.length ≤ 32) (hf : s.isFinite = true)
    (htarget : |target| ≤ 2 * p * M)
    (he : |value s - target| ≤ p * (2 : ℝ) ^ (-44 : Int) * M)
    : ∃ d,
        reflectorDot width column indices v a s = .ok d
        ∧ d.isFinite = true
        ∧ |value d - (target + reflectorDotValue width column indices v a)|
          ≤ (p + indices.length) * (2 : ℝ) ^ (-44 : Int) * M := by
  have hM := (budget_pos M hl).le
  obtain ⟨hlo, hhi⟩ := dot_budget M hl hu
  induction indices generalizing s target p with
  | nil => exact ⟨s, rfl, hf, by simpa [reflectorDotValue] using he⟩
  | cons i indices ih =>
      let x := v.getD i 0.0
      let y := entry width a i column
      have ht : |value x * value y| ≤ 2 * M := by
        rw [abs_mul]
        exact mul_le_mul (hbv i (by simp)) (hba i (by simp)) (abs_nonneg _) (by norm_num)
      have hp32 : (p : ℝ) ≤ 32 := by exact_mod_cast (show p ≤ 32 by omega)
      have hs := Flare.Matrix.Multiplication.dot_nearest_step x y s target (64 * M) p
        (Flare.Matrix.Storage.getD_finite v i hv) (Flare.Matrix.Storage.getD_finite a _ ha) hf
        (by simp only [List.length_cons] at hlen; omega) hhi hlo
        (ht.trans (by linarith)) (htarget.trans (by nlinarith))
        (by norm_num at he ⊢; linarith)
      have htgt : |target + value x * value y| ≤ 2 * (p + 1 : Nat) * M := by
        have hh := abs_add_le target (value x * value y)
        push_cast
        nlinarith
      have herr : |value (s + x * y) - (target + value x * value y)|
          ≤ (p + 1 : Nat) * (2 : ℝ) ^ (-44 : Int) * M := by
        have hh := hs.2.2
        norm_num at hh ⊢
        linarith
      obtain ⟨d, hd, hdf, hde⟩ := ih (fun j hj => hbv j (by simp [hj]))
        (fun j hj => hba j (by simp [hj])) (s + x * y) (target + value x * value y) (p + 1)
        (by simp only [List.length_cons] at hlen; omega) hs.2.1 htgt herr
      refine ⟨d, ?_, hdf, ?_⟩
      · rw [reflectorDot_cons, finite_ok _ hs.1]
        change (do
          let next ← finite (s + x * y)
          reflectorDot width column indices v a next) = .ok d
        rw [finite_ok _ hs.2.1]
        exact hd
      · simpa [reflectorDotValue, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          add_assoc, add_comm, add_left_comm, x, y]
          using hde

/-- Checked dot success and forward error from stored operand conditions.
FLARE's nearest dot step is instantiated with absolute term-mass budget 64M. -/
theorem reflectorDot_accuracy (height width column : Nat) (indices : List Nat)
    (v a : Array Float) (M : ℝ) (p : ApplicationProfile height width column indices v a M)
    : ∃ d,
        reflectorDot width column indices v a 0.0 = .ok d
        ∧ d.isFinite = true
        ∧ |value d - reflectorDotValue width column indices v a|
          ≤ indices.length * (2 : ℝ) ^ (-44 : Int) * M := by
  simpa [Flare.Binary64.Arithmetic.zero_value]
    using dot_loop width column indices v a M p.vector_finite p.matrix_finite
      p.vector_magnitude p.column_magnitude p.budget_lower p.budget_upper 0.0 0 0
      (by simpa using p.length_le) (by decide) (by simp)
      (by simp [Flare.Binary64.Arithmetic.zero_value])

private theorem abs_map_sum (indices : List Nat) (f : Nat → ℝ)
    : |(indices.map f).sum| ≤ (indices.map (fun i => |f i|)).sum := by
  induction indices with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

private theorem dotValue_bound (width column : Nat) (indices : List Nat)
    (v a : Array Float) (M : ℝ)
    (hv : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 2)
    (ha : ∀ i ∈ indices, |value (entry width a i column)| ≤ M)
    : |reflectorDotValue width column indices v a| ≤ 2 * indices.length * M := by
  unfold reflectorDotValue
  calc
    _ ≤ (indices.map
          (fun i => |value (v.getD i 0.0) * value (entry width a i column)|)).sum :=
      abs_map_sum indices _
    _ ≤ (indices.map (fun _ => 2 * M)).sum := by
      apply List.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hv i hi) (ha i hi) (abs_nonneg _) (by norm_num)
    _ = _ := by simp; ring

private theorem two_value : value (2.0 : Float) = 2 := by
  change (((2 ^ 52 : Nat) : ℝ) * (2 : ℝ) ^ (-51 : Int)) = 2
  norm_num

private theorem doubled_dot_accuracy (d : Float) (D M : ℝ) (k : Nat)
    (hf : d.isFinite = true) (hk : k ≤ 32)
    (hl : (2 : ℝ) ^ (-1022 : Int) ≤ M) (hu : M ≤ (2 : ℝ) ^ (900 : Int))
    (hD : |D| ≤ 64 * M)
    (he : |value d - D| ≤ k * (2 : ℝ) ^ (-44 : Int) * M)
    : (2.0 * d).isFinite = true
      ∧ |value (2.0 * d)| ≤ 132 * M
      ∧ |value (2.0 * d) - 2 * D| ≤ (2 * k + 1) * (2 : ℝ) ^ (-44 : Int) * M := by
  have hM := (budget_pos M hl).le
  have hk32 : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have hdm : |value d| ≤ 65 * M := by
    have ht := abs_sub_le (value d) D 0
    simp only [sub_zero] at ht
    norm_num at he
    nlinarith
  have hprod : |value (2.0 : Float) * value d| ≤ 130 * M := by
    rw [two_value, abs_mul]
    norm_num
    linarith
  have hm := Flare.Binary64.Nearest.mul_error_nearest 2.0 d (by decide) hf
    (hprod.trans ((by nlinarith : 130 * M ≤ 512 * M).trans (budget_limit M hu)))
  have hround := hm.2.trans (rounding_radius M _ hl (hprod.trans (by nlinarith)))
  have hround' : |value (2.0 * d) - 2 * value d| ≤ (2 : ℝ) ^ (-44 : Int) * M := by
    simpa only [two_value] using hround
  refine ⟨hm.1, ?_, ?_⟩
  · have ht := abs_sub_le (value (2.0 * d)) (2 * value d) 0
    simp only [sub_zero] at ht
    have hb : |2 * value d| ≤ 130 * M := by simpa only [two_value] using hprod
    norm_num at hround'
    linarith
  · have hid : value (2.0 * d) - 2 * D =
        (value (2.0 * d) - 2 * value d) + 2 * (value d - D) := by ring
    have ht := abs_add_le (value (2.0 * d) - 2 * value d) (2 * (value d - D))
    rw [← hid, abs_mul] at ht
    norm_num at hround' he ht ⊢
    linarith

private theorem update_entry_accuracy (w x twice : Float) (D M : ℝ) (k : Nat)
    (hw : w.isFinite = true) (hx : x.isFinite = true) (ht : twice.isFinite = true)
    (hbw : |value w| ≤ 2) (hbx : |value x| ≤ M)
    (hl : (2 : ℝ) ^ (-1022 : Int) ≤ M) (hu : M ≤ (2 : ℝ) ^ (900 : Int))
    (htm : |value twice| ≤ 132 * M)
    (hte : |value twice - 2 * D| ≤ (2 * k + 1) * (2 : ℝ) ^ (-44 : Int) * M)
    : (w * twice).isFinite = true
      ∧ (x - w * twice).isFinite = true
      ∧ |value (x - w * twice) - (value x - 2 * value w * D)|
        ≤ applicationRadius k M := by
  have hM := (budget_pos M hl).le
  have hprod : |value w * value twice| ≤ 264 * M := by
    rw [abs_mul]
    nlinarith [mul_le_mul hbw htm (abs_nonneg _) (by norm_num)]
  have hm := Flare.Binary64.Nearest.mul_error_nearest w twice hw ht
    (hprod.trans ((by nlinarith : 264 * M ≤ 512 * M).trans (budget_limit M hu)))
  have hme := hm.2.trans (rounding_radius M _ hl (hprod.trans (by nlinarith)))
  have hpm : |value (w * twice)| ≤ 265 * M := by
    have hh := abs_sub_le (value (w * twice)) (value w * value twice) 0
    simp only [sub_zero] at hh
    norm_num at hme
    linarith
  have hsub : |value x - value (w * twice)| ≤ 266 * M :=
    (abs_sub _ _).trans (by linarith)
  have hs := Flare.Binary64.Nearest.sub_error_nearest x (w * twice) hx hm.1
    (hsub.trans ((by nlinarith : 266 * M ≤ 512 * M).trans (budget_limit M hu)))
  have hse := hs.2.trans (rounding_radius M _ hl (hsub.trans (by nlinarith)))
  refine ⟨hm.1, hs.1, ?_⟩
  have hid : value (x - w * twice) - (value x - 2 * value w * D) =
      (value (x - w * twice) - (value x - value (w * twice)))
      - (value (w * twice) - value w * value twice)
      - value w * (value twice - 2 * D) := by ring
  rw [hid]
  have hh := abs_sub
    ((value (x - w * twice) - (value x - value (w * twice)))
      - (value (w * twice) - value w * value twice))
    (value w * (value twice - 2 * D))
  have hh' := abs_sub (value (x - w * twice) - (value x - value (w * twice)))
    (value (w * twice) - value w * value twice)
  rw [abs_mul] at hh
  have hmul := mul_le_mul hbw hte (abs_nonneg _) (by norm_num)
  norm_num [applicationRadius] at hme hse hte hmul ⊢
  linarith

private theorem set_read (a : Array Float) (k t : Nat) (x : Float) (hk : k < a.size)
    : (a.set! k x).getD t 0.0 = if t = k then x else a.getD t 0.0 := by
  by_cases ht : t = k
  · subst t
    simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hk]
  · simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, ht,
      Array.getElem?_setIfInBounds_ne (Ne.symm ht)]

private theorem slot_ne {width column i j : Nat} (hw : 0 < width) (hij : i ≠ j)
    : i * width + column ≠ j * width + column := by
  intro he
  exact hij (Nat.mul_right_cancel hw (Nat.add_right_cancel he))

private theorem reflectorUpdates_cons (width column i : Nat) (indices : List Nat)
    (v a : Array Float) (twice : Float)
    : reflectorUpdates width column (i :: indices) v a twice
      = (do
          let term ← finite (v.getD i 0.0 * twice)
          let x ← finite (entry width a i column - term)
          reflectorUpdates width column indices v (a.set! (i * width + column) x)
            twice) := by
  simp [reflectorUpdates, List.forIn_cons, bind_assoc]

private theorem updates_storage (width column : Nat) (indices : List Nat)
    (v a : Array Float) (twice : Float) (hw : 0 < width) (hn : indices.Nodup)
    (ha : a.all Float.isFinite = true) (hi : ∀ i ∈ indices, i * width + column < a.size)
    (hf
      : ∀ i ∈ indices,
          (v.getD i 0.0 * twice).isFinite = true
          ∧ (entry width a i column - v.getD i 0.0 * twice).isFinite = true)
    : ∃ output,
        reflectorUpdates width column indices v a twice = .ok output
        ∧ output.size = a.size
        ∧ output.all Float.isFinite = true
        ∧ (∀ i ∈ indices,
            entry width output i column = entry width a i column - v.getD i 0.0 * twice)
        ∧ (∀ t,
            (∀ i ∈ indices, t ≠ i * width + column)
            → output.getD t 0.0 = a.getD t 0.0) := by
  induction indices generalizing a with
  | nil => exact ⟨a, rfl, rfl, ha, by simp, by simp⟩
  | cons i indices ih =>
      have hn' := List.nodup_cons.mp hn
      have hfi := hf i (by simp)
      let next := a.set! (i * width + column) (entry width a i column - v.getD i 0.0 * twice)
      have hread : ∀ j ∈ indices, entry width next j column = entry width a j column := by
        intro j hj
        have hji : j ≠ i := fun h => hn'.1 (h ▸ hj)
        change next.getD (j * width + column) 0.0 = a.getD (j * width + column) 0.0
        dsimp only [next]
        rw [set_read a _ _ _ (hi i (by simp))]
        exact ite_eq_right (slot_ne hw hji)
      obtain ⟨output, hout, hos, hof, horead, hounused⟩ := ih next hn'.2
        (Flare.Matrix.Storage.all_set a _ _ ha hfi.2)
        (fun j hj => by simpa [next] using hi j (by simp [hj]))
        (fun j hj => by rw [hread j hj]; exact hf j (by simp [hj]))
      refine ⟨output, ?_, by simpa [next] using hos, hof, ?_, ?_⟩
      · rw [reflectorUpdates_cons, finite_ok _ hfi.1]
        change (do
          let x ← finite (entry width a i column - v.getD i 0.0 * twice)
          reflectorUpdates width column indices v (a.set! (i * width + column) x) twice) = .ok output
        rw [finite_ok _ hfi.2]
        exact hout
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · change output.getD (j * width + column) 0.0 = _
          have hslots : ∀ k ∈ indices, j * width + column ≠ k * width + column := by
            intro k hk
            apply slot_ne hw
            intro he
            exact hn'.1 (he.symm ▸ hk)
          rw [hounused _ hslots]
          simp only [next, set_read a _ _ _ (hi j (by simp)), ↓reduceIte]
        · rw [horead j hj, hread j hj]
      · intro t ht
        rw [hounused t (fun j hj => ht j (by simp [hj]))]
        simp only [next, set_read a _ _ _ (hi i (by simp)), ite_eq_right (ht i (by simp))]

theorem applicationRadius_le {k : Nat} (M : ℝ) (hk : k ≤ 32) (hM : 0 ≤ M)
    : applicationRadius k M ≤ (2 : ℝ) ^ (-36 : Int) * M := by
  have hn : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  norm_num [applicationRadius]
  nlinarith

/-- Input-only local application guarantee. All checked arithmetic succeeds;
the exact stored-operand reflector reference and untouched slots are explicit. -/
theorem applyReflector_accuracy (height width column : Nat) (indices : List Nat)
    (v a : Array Float) (M : ℝ) (p : ApplicationProfile height width column indices v a M)
    : ApplicationAccuracy width column indices v a M := by
  let D := reflectorDotValue width column indices v a
  obtain ⟨d, hd, hdf, hde⟩ := reflectorDot_accuracy height width column indices v a M p
  have hM := (budget_pos M p.budget_lower).le
  have hn32 : (indices.length : ℝ) ≤ 32 := by exact_mod_cast p.length_le
  have hD : |D| ≤ 64 * M := (dotValue_bound width column indices v a M
    p.vector_magnitude p.column_magnitude).trans (by nlinarith)
  obtain ⟨htf, htm, hte⟩ := doubled_dot_accuracy d D M indices.length hdf p.length_le
    p.budget_lower p.budget_upper hD hde
  have hentry := fun i hi => update_entry_accuracy (v.getD i 0.0) (entry width a i column)
    (2.0 * d) D M indices.length (Flare.Matrix.Storage.getD_finite v i p.vector_finite)
    (Flare.Matrix.Storage.getD_finite a _ p.matrix_finite) htf
    (p.vector_magnitude i hi) (p.column_magnitude i hi) p.budget_lower p.budget_upper htm hte
  obtain ⟨output, hout, hos, hof, horead, hounused⟩ := updates_storage width column indices v a (2.0 * d)
    (lt_of_le_of_lt (Nat.zero_le column) p.column_bound) p.nodup p.matrix_finite
    (fun i hi => by
      have hrow := p.in_bounds i hi
      have hcol := p.column_bound
      have hmul := Nat.mul_le_mul_right width (show i + 1 ≤ height by omega)
      rw [Nat.add_mul] at hmul
      rw [p.matrix_size]
      omega)
    (fun i hi => ⟨(hentry i hi).1, (hentry i hi).2.1⟩)
  refine ⟨output, ?_, hos, hof, hounused, ?_⟩
  · unfold applyReflector
    rw [hd]
    change (do
      let twice ← finite (2.0 * d)
      reflectorUpdates width column indices v a twice) = .ok output
    rw [finite_ok _ htf]
    exact hout
  · intro i hi
    rw [horead i hi]
    exact (hentry i hi).2.2

private theorem vectorSquares_term_le (indices : List Nat) (v : Array Float)
    (i : Nat) (hi : i ∈ indices)
    : (value (v.getD i 0.0)) ^ 2 ≤ vectorSquares indices v := by
  unfold vectorSquares
  apply List.single_le_sum
  · intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    exact sq_nonneg _
  · exact List.mem_map.mpr ⟨i, hi, rfl⟩

/-- Near-unit squared norm supplies a component bound without exact orthogonality. -/
theorem nearUnit_magnitude (indices : List Nat) (w : Array Float)
    (he : |vectorSquares indices w - 1| ≤ (2 : ℝ) ^ (-40 : Int))
    : ∀ i ∈ indices, |value (w.getD i 0.0)| ≤ 2 := by
  intro i hi
  have ht := vectorSquares_term_le indices w i hi
  have hhi := (abs_le.mp he).2
  have hε : (2 : ℝ) ^ (-40 : Int) ≤ 1 := by norm_num
  nlinarith [sq_abs (value (w.getD i 0.0)), abs_nonneg (value (w.getD i 0.0))]

private theorem constructedUnitComponent_bound (first : Nat) (indices : List Nat)
    (v : Array Float) (norm : Float) (i : Nat) (hi : i ∈ indices)
    : |constructedUnitComponent first indices v norm i| ≤ 1 := by
  let b := constructedVector first v norm
  let root := Real.sqrt (vectorSquares indices b)
  have hsum : 0 ≤ vectorSquares indices b := by
    unfold vectorSquares
    apply List.sum_nonneg
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    exact sq_nonneg _
  have hrootsq : root ^ 2 = vectorSquares indices b := Real.sq_sqrt hsum
  have ht := vectorSquares_term_le indices b i hi
  change |value (b.getD i 0.0) / root| ≤ 1
  by_cases hz : root = 0
  · simp only [hz, div_zero, abs_zero, zero_le_one]
  · have hrootp : 0 < root := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    have hb : |value (b.getD i 0.0)| ≤ root := by
      nlinarith [sq_abs (value (b.getD i 0.0)), abs_nonneg (value (b.getD i 0.0))]
    rw [abs_div, abs_of_pos hrootp]
    exact (div_le_one hrootp).mpr hb

private theorem map_sum_sub (indices : List Nat) (f g : Nat → ℝ)
    : (indices.map f).sum - (indices.map g).sum
      = (indices.map (fun i => f i - g i)).sum := by
  induction indices with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

/-- Propagate the stored vector component error into its exact column action.
Shared by trailing-column application and source-column finishing. -/
theorem constructed_perturbation (width column first : Nat) (indices : List Nat)
    (w v a : Array Float) (norm : Float) (M : ℝ)
    (hw : ∀ i ∈ indices, |value (w.getD i 0.0)| ≤ 2)
    (hx : ∀ i ∈ indices, |value (entry width a i column)| ≤ M)
    (he
      : ∀ i ∈ indices,
          |value (w.getD i 0.0) - constructedUnitComponent first indices v norm i|
          ≤ reflectorRadius indices.length)
    : ∀ i ∈ indices,
        |reflectorAppliedValue width column indices w a i
          - constructedAppliedValue width column first indices v norm a i|
        ≤ 6 * indices.length * reflectorRadius indices.length * M := by
  let U := constructedUnitComponent first indices v norm
  let D := reflectorDotValue width column indices w a
  let V := (indices.map (fun j => U j * value (entry width a j column))).sum
  have hD : |D| ≤ 2 * indices.length * M := dotValue_bound width column indices w a M hw hx
  have hdiff : |D - V| ≤ indices.length * (reflectorRadius indices.length * M) := by
    dsimp only [D, V, reflectorDotValue]
    rw [map_sum_sub]
    calc
      _ ≤ (indices.map
            (fun j =>
              |value (w.getD j 0.0) * value (entry width a j column)
                - U j * value (entry width a j column)|)).sum :=
        abs_map_sum indices _
      _ ≤ (indices.map (fun _ => reflectorRadius indices.length * M)).sum := by
        apply List.sum_le_sum
        intro j hj
        rw [show value (w.getD j 0.0) * value (entry width a j column)
          - U j * value (entry width a j column) =
          (value (w.getD j 0.0) - U j) * value (entry width a j column) by ring, abs_mul]
        exact mul_le_mul (he j hj) (hx j hj) (abs_nonneg _)
          (by unfold reflectorRadius; positivity)
      _ = _ := by simp
  intro i hi
  have hu : |U i| ≤ 1 := constructedUnitComponent_bound first indices v norm i hi
  have hid : reflectorAppliedValue width column indices w a i
      - constructedAppliedValue width column first indices v norm a i =
      -2 * (value (w.getD i 0.0) - U i) * D - 2 * U i * (D - V) := by
    dsimp [reflectorAppliedValue, constructedAppliedValue, U, D, V]
    ring
  rw [hid]
  have ht := abs_sub (-2 * (value (w.getD i 0.0) - U i) * D) (2 * U i * (D - V))
  simp only [abs_mul] at ht
  have hm1 := mul_le_mul (he i hi) hD (abs_nonneg _) (by unfold reflectorRadius; positivity)
  have hm2 := mul_le_mul hu hdiff (abs_nonneg _) (by norm_num)
  norm_num at ht hm1 hm2 ⊢
  nlinarith

theorem constructedApplicationRadius_le {k : Nat} (M : ℝ) (hk : k ≤ 32) (hM : 0 ≤ M)
    : constructedApplicationRadius k M ≤ (2 : ℝ) ^ (-18 : Int) * M := by
  have hn : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have hquad : (k : ℝ) * (9 * k + 5) ≤ 32 * 293 :=
    mul_le_mul hn (by linarith) (by positivity) (by norm_num)
  norm_num [constructedApplicationRadius, applicationRadius, reflectorRadius]
  nlinarith

/-- Sharper cap from the tightened reflector and source estimates. -/
theorem constructedApplicationRadius_le_tight {k : Nat} (M : ℝ) (hk : k ≤ 32) (hM : 0 ≤ M)
    : constructedApplicationRadius k M ≤ (2 : ℝ) ^ (-32 : Int) * M := by
  have hn : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have hquad : (k : ℝ) * (9 * k + 5) ≤ 32 * 293 :=
    mul_le_mul hn (by linarith) (by positivity) (by norm_num)
  norm_num [constructedApplicationRadius, applicationRadius, reflectorRadius]
  nlinarith

/-- Original source-column conditions establish construction and application.
The normalized constructed-vector reference includes the preceding stored-vector
error, rather than assuming that the returned native vector is exactly unit. -/
theorem scaledColumn_applyReflector_accuracy (height width column first : Nat)
    (indices : List Nat) (x : Nat → Float) (a : Array Float) (M : ℝ)
    (p : ColumnProfile height indices x) (hn : indices.Nodup) (hfirst : first ∈ indices)
    (target : TargetColumnProfile height width column indices a M)
    : ColumnApplicationAccuracy height width column first indices x a M := by
  obtain ⟨scale, v, norm, hnorm, hvs, hreflector⟩ :=
    FloatQRReflector.scaledColumn_reflector_accuracy height first indices x p hn hfirst
  obtain ⟨alpha, w, hreflect, _, _, _, _, _, _, hws, hwf, _, hwe, hunit⟩ := hreflector
  have hwm := nearUnit_magnitude indices w (hunit.trans (FloatQRReflector.reflectorRadius_le p.length_le))
  have app : ApplicationProfile height width column indices w a M :=
    ⟨p.length_le, hn, target.column_bound, p.in_bounds, hws.trans hvs,
      target.matrix_size, hwf, target.matrix_finite, hwm,
      target.budget_lower, target.budget_upper, target.column_magnitude⟩
  obtain ⟨output, hout, hos, hof, hounused, hoe⟩ := applyReflector_accuracy height width column
    indices w a M app
  have hperturb := constructed_perturbation width column first indices w v a norm M
    hwm target.column_magnitude hwe
  refine ⟨
    scale,
    v,
    norm,
    alpha,
    w,
    output,
    hnorm,
    hreflect,
    hout,
    hos,
    hof,
    hounused,
    hoe,
    ?_
  ⟩
  intro i hi
  have ht := abs_sub_le (value (entry width output i column))
    (reflectorAppliedValue width column indices w a i)
    (constructedAppliedValue width column first indices v norm a i)
  exact ht.trans
    (by
      unfold constructedApplicationRadius
      exact add_le_add (hoe i hi) (hperturb i hi))

end Kalman.Proofs.FloatQRApplication
