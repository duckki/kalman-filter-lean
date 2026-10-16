import Kalman.Proofs.FloatJosephError
import Flare.Binary64.Division
import Flare.Binary64.Order

namespace Kalman.Proofs.FloatJosephPositionArithmetic

open Matrix hiding transpose
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1200000

/-- All inner dimensions in the scalar-observation correction are at most two. -/
theorem product (rows inner cols : Nat) (a b : Array Float) (A B : ℝ)
    (hi : inner ≤ 2) (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A * B ≤ 128)
    (ham : ∀ i j, |matrix rows inner a i j| ≤ A)
    (hbm : ∀ i j, |matrix inner cols b i j| ≤ B)
    : ∃ r,
        ProductProfile rows inner cols a b 256
        ∧ multiply rows inner cols a b = .ok r
        ∧ r.size = rows * cols
        ∧ r.all Float.isFinite = true
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-41 : Int)) (matrix rows cols r)
            (matrix rows inner a * matrix inner cols b) := by
  have prof : ProductProfile rows inner cols a b 256 := by
    refine ⟨by omega, ha, hb, ?_, ?_, ?_⟩
    · simpa only [show (2 : ℝ)^(8 : Int) = 256 by norm_num]
        using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (8 : Int) ≤ 990)
    · simpa only [show (2 : ℝ)^(8 : Int) = 256 by norm_num]
        using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (-1022 : Int) ≤ 8)
    · intro i j hir hjc
      calc
        _ ≤ ∑ _k ∈ Finset.range inner, A * B := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          exact mul_le_mul (ham ⟨i, hir⟩ ⟨k, Finset.mem_range.mp hk⟩)
            (hbm ⟨k, Finset.mem_range.mp hk⟩ ⟨j, hjc⟩) (abs_nonneg _) hA
        _ ≤ 256 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have h := mul_le_mul_of_nonneg_right (show (inner : ℝ) ≤ 2 by exact_mod_cast hi)
            (mul_nonneg hA hB)
          nlinarith
  obtain ⟨r, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy rows inner cols a b
    (fun _ _ => (256 : ℝ)) prof.inner_le ha hb (fun _ _ _ _ => prof.upper)
    (fun _ _ _ _ => prof.lower) prof.mass
  refine ⟨r, prof, hr, hs, hf, by positivity, ?_⟩
  intro i j
  apply (he i j).trans
  have hi' : (inner : ℝ) ≤ 2 := by exact_mod_cast hi
  norm_num only [show (256 : ℝ) = 2^8 by norm_num]
  have hm := mul_le_mul_of_nonneg_right hi' (by positivity : (0 : ℝ) ≤ 2^(-50 : Int))
  norm_num at hm ⊢
  linarith

/-- Convert an entrywise matrix cap to an array cap on shaped storage. -/
theorem array_bound (rows cols : Nat) (a : Array Float) (A : ℝ)
    (hc : 0 < cols) (h : ∀ i j, |matrix rows cols a i j| ≤ A)
    (t : Nat) (ht : t < rows * cols)
    : |value (a.getD t 0.0)| ≤ A := by
  have hi : t / cols < rows := (Nat.div_lt_iff_lt_mul hc).mpr ht
  have hj : t % cols < cols := Nat.mod_lt t hc
  have hb := h ⟨t / cols, hi⟩ ⟨t % cols, hj⟩
  change |value (a.getD (t / cols * cols + t % cols) 0.0)| ≤ A at hb
  have hidx : t / cols * cols + t % cols = t := by
    simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div t cols
  simpa only [hidx] using hb

/-- Finite elementwise sums/subtractions, with their own exact operand cap. -/
theorem sum_profile (rows cols : Nat) (a b : Array Float) (A B : ℝ)
    (E : Int) (subtract : Bool) (hc : 0 < cols) (hs : a.size = rows * cols)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hE : -1022 ≤ E) (hE' : E ≤ 1022) (hm : A + B ≤ (2 : ℝ) ^ E)
    (ham : ∀ i j, |matrix rows cols a i j| ≤ A)
    (hbm : ∀ i j, |matrix rows cols b i j| ≤ B)
    : SumProfile a b E subtract := by
  refine ⟨hE, hE', ha, hb, ?_⟩
  intro t ht
  have ht' : t < rows * cols := by omega
  have ha' := array_bound rows cols a A hc ham t ht'
  have hb' := array_bound rows cols b B hc hbm t ht'
  cases subtract
  · simpa only [Bool.false_eq_true, ↓reduceIte]
      using (abs_add_le _ _).trans ((add_le_add ha' hb').trans hm)
  · simpa only [↓reduceIte, ← sub_eq_add_neg]
      using (abs_sub _ _).trans ((add_le_add ha' hb').trans hm)

/-- Stored-output entry caps follow from any proved entrywise enclosure. -/
theorem near_bound {rows cols : Nat} (a : Array Float)
    (reference : Matrix (Fin rows) (Fin cols) ℝ) (ε A cap : ℝ)
    (he : EntrywiseWithin ε (matrix rows cols a) reference)
    (hr : ∀ i j, |reference i j| ≤ A) (hc : A + ε ≤ cap)
    : ∀ i j, |matrix rows cols a i j| ≤ cap := by
  intro i j
  have h := abs_sub_le (matrix rows cols a i j) (reference i j) 0
  simp only [sub_zero] at h
  exact h.trans ((add_le_add (he.2 i j) (hr i j)).trans (by linarith))

/-- A transposed finite array has the transposed exact decoding and cap. -/
theorem transpose_bound (rows cols : Nat) (a : Array Float) (A : ℝ)
    (hf : a.all Float.isFinite = true) (h : ∀ i j, |matrix rows cols a i j| ≤ A)
    : (transpose rows cols a).all Float.isFinite = true
      ∧ (∀ i j, |matrix cols rows (transpose rows cols a) i j| ≤ A) := by
  refine ⟨(Flare.Matrix.Multiplication.transpose_storage rows cols a hf).2.1, ?_⟩
  have ht : matrix cols rows (transpose rows cols a) = (matrix rows cols a).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix rows cols a hf
  intro i j
  rw [ht]
  exact h j i

/-- The actual scalar LDL solve is two guarded divisions, with no elimination
or substitution products. No solve success is a premise. -/
theorem scalar_solve (a b : Array Float)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hlo : 1 ≤ value (a.getD 0 0.0))
    (hbound : ∀ j, j < 2 → |value (b.getD j 0.0)| ≤ 3)
    : ∃ out,
        solveSPD 1 2 a b = .ok out
        ∧ out.size = 2
        ∧ out.all Float.isFinite = true
        ∧ ∀ j : Fin 2,
            |value (out.getD j.val 0.0) - value (b.getD j.val 0.0) / value (a.getD 0 0.0)|
            ≤ (2 : ℝ) ^ (-49 : Int) := by
  let s := a.getD 0 0.0
  have sf := Flare.Matrix.Storage.getD_finite a 0 ha
  have sp : (0.0 : Float) < s := by
    apply (Flare.Binary64.Order.lt_iff _ _ (by decide) sf).mpr
    change (0 : ℝ) < value s
    linarith
  have spos : 0 < value s := by change 0 < value (a.getD 0 0.0); linarith
  have divs (j : Nat) (hj : j < 2) := Flare.Binary64.Division.div_error (b.getD j 0.0) s 2
    (Flare.Matrix.Storage.getD_finite b j hb) sf (by change value (a.getD 0 0.0) ≠ 0; linarith)
    (by norm_num) (by norm_num) (by
      rw [abs_div, abs_of_pos spos]
      apply (div_le_iff₀ spos).mpr
      have h := hbound j hj
      norm_num only [show (2 : ℝ)^2 = 4 by norm_num]
      have hslo : 1 ≤ value s := hlo
      linarith)
  let out := #[b.getD 0 0.0 / s, b.getD 1 0.0 / s]
  have h0 := divs 0 (by decide)
  have h1 := divs 1 (by decide)
  dsimp only [s] at sp h0 h1
  simp only [Array.getD_eq_getD_getElem?] at sp h0 h1
  refine ⟨out, ?_, rfl, ?_, ?_⟩
  · simp [solveSPD, adapt, Flare.Matrix.Dense.solveSPD, Flare.Matrix.Dense.factor,
      Flare.Matrix.Dense.solve, Flare.Matrix.Dense.entry, Flare.Matrix.Dense.finite,
      Std.Legacy.Range.forIn_eq_forIn_range', List.range', List.forIn_cons, List.forIn_nil,
      bind, Except.bind, pure, Except.pure, s, out, sp, h0.1, h1.1, Array.getD_eq_getD_getElem?, -bind_pure_comp]
    apply Array.ext
    · simp
    · intro i hi hj
      simp only [Array.size_setIfInBounds, Array.size_replicate] at hi
      interval_cases i <;> simp
  · simp [out, s, Array.getD_eq_getD_getElem?, h0.1, h1.1]
  · intro j
    fin_cases j
    · simpa [out, s, Array.getD_eq_getD_getElem?] using h0.2
    · simpa [out, s, Array.getD_eq_getD_getElem?] using h1.2

/-- Propagate numerator and scalar innovation errors through the native solve. -/
theorem quotient_accuracy (x b p s t : ℝ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hp : |p| ≤ 2) (hdiv : |x - b / s| ≤ (2 : ℝ) ^ (-49 : Int))
    (hb : |b - p| ≤ (2 : ℝ) ^ (-41 : Int))
    (herr : |s - t| ≤ (2 : ℝ) ^ (-38 : Int))
    : |x - p / t| ≤ (2 : ℝ) ^ (-36 : Int) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hst : 1 ≤ s*t := by nlinarith
  have identity : b/s - p/t = (b-p)/s + p*(t-s)/(s*t) := by
    field_simp
    ring
  have hnum : |(b-p)/s| ≤ (2 : ℝ)^(-41 : Int) := by
    rw [abs_div, abs_of_pos hs0]
    apply (div_le_iff₀ hs0).mpr
    norm_num at hb ⊢
    nlinarith
  have hprod : |p*(t-s)| ≤ 2*(2 : ℝ)^(-38 : Int) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul hp herr (abs_nonneg _) (by norm_num)
  have hden : |p*(t-s)/(s*t)| ≤ 2*(2 : ℝ)^(-38 : Int) := by
    rw [abs_div, abs_of_pos (mul_pos hs0 ht0)]
    apply (div_le_iff₀ (mul_pos hs0 ht0)).mpr
    norm_num at hprod ⊢
    nlinarith
  have hdiff : |b/s - p/t| ≤ (2 : ℝ)^(-41 : Int) + 2*(2 : ℝ)^(-38 : Int) := by
    rw [identity]
    exact (abs_add_le _ _).trans (add_le_add hnum hden)
  have hi := (abs_sub_le x (b/s) (p/t)).trans (add_le_add hdiv hdiff)
  exact hi.trans (by norm_num)

end Kalman.Proofs.FloatJosephPositionArithmetic
