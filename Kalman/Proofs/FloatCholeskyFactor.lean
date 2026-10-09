import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.FloatCholeskySolve

/-! Native Cholesky storage equations and a posteriori Gram backward error.
Successful execution and stored-operand profiles are distinct from an original
input domain guaranteeing that all pivots succeed. -/

namespace Kalman.Proofs.FloatCholeskyFactor

open Kalman.Implementation.LinearAlgebra
open Kalman.Proofs.CholeskyProfiles
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.FloatResidualError
open Kalman.Proofs.FloatCholeskySolve
open Flare.Binary64.Value Std.Do

set_option mvcgen.warning false

@[spec]
private theorem subtractProducts_result (indices : List Nat) (left right : Nat → Float)
    (initial : Float)
    : ⦃⌜True⌝
      ⦄ subtractProducts indices left right initial
      ⦃⇓? r => ⌜subtractProducts indices left right initial = .ok r⌝⦄ := by
  generalize he : subtractProducts indices left right initial = result
  cases result <;> mvcgen

@[spec]
private theorem positiveSqrt_result (pivot : Float)
    : ⦃⌜True⌝
      ⦄ positiveSqrt pivot
      ⦃⇓? r => ⌜positiveSqrt pivot = .ok r⌝⦄ := by
  generalize he : positiveSqrt pivot = result
  cases result <;> mvcgen

@[spec]
private theorem divideResidual_result (indices : List Nat) (left right : Nat → Float)
    (initial diagonal : Float)
    : ⦃⌜True⌝
      ⦄ divideResidual indices left right initial diagonal
      ⦃⇓? r => ⌜divideResidual indices left right initial diagonal = .ok r⌝⦄ := by
  generalize he : divideResidual indices left right initial diagonal = result
  cases result <;> mvcgen

private theorem entry_write (n : Nat) (r : Array Float) (i j a c : Nat)
    (s : Float) (hr : r.size = n * n) (hi : i < n) (hj : j < n) (hc : c < n)
    : entry n (r.set! (i * n + j) s) a c = if a = i ∧ c = j then s else entry n r a c :=
  Flare.Matrix.Storage.entry_set n r i j a c s hr hi hj hc

private theorem cell_congr (n : Nat) (a l l' : Array Float) (i j : Nat) (s : Float)
    (hi : ∀ k, k < j → entry n l i k = entry n l' i k)
    (hj : ∀ k, k < j → entry n l j k = entry n l' j k)
    (hd : i = j ∨ entry n l j j = entry n l' j j)
    : CellComputation n a l i j s ↔ CellComputation n a l' i j s := by
  unfold CellComputation
  split_ifs with he
  · have hr : subtractProducts (List.range j) (fun k => entry n l j k)
        (fun k => entry n l j k) (entry n a j j) =
      subtractProducts (List.range j) (fun k => entry n l' j k)
        (fun k => entry n l' j k) (entry n a j j) := by
      simp only [subtractProducts_bridge]
      rw [Flare.Matrix.Substitution.subtractProducts_congr _ _ _ _ _ _
        (fun k hk => hj k (List.mem_range.mp hk)) (fun k hk => hj k (List.mem_range.mp hk))]
    rw [hr]
  · have hdiag := hd.resolve_left he
    rw [divideResidual_congr _ _ _ _ _ _ _
      (fun k hk => hi k (List.mem_range.mp hk)) (fun k hk => hj k (List.mem_range.mp hk)), hdiag]

private def ColumnState (n : Nat) (a : Array Float) (column row : Nat) (l : Array Float)
    : Prop :=
  l.size = n * n
  ∧ (∀ i j, i < n → j < n → i < j → entry n l i j = 0.0)
  ∧ ∀ i j,
      i < n
      → j ≤ i
      → j < column ∨ j = column ∧ i < row
      → CellComputation n a l i j (entry n l i j)

private theorem column_write (n : Nat) (input l : Array Float) (j i : Nat) (s : Float)
    (hi : i < n) (hji : j ≤ i) (hr : ColumnState n input j i l)
    (hs : CellComputation n input l i j s)
    : ColumnState n input j (i + 1) (l.set! (i * n + j) s) := by
  have hj : j < n := by omega
  refine ⟨(Array.size_set! ..).trans hr.1, ?_, ?_⟩
  · intro a c ha hc hac
    rw [entry_write n l i j a c s hr.1 hi hj hc]
    have hn : ¬(a = i ∧ c = j) := by omega
    simp only [hn, ↓reduceIte]
    exact hr.2.1 a c ha hc hac
  · intro a c ha hca hac
    have hc : c < n := by omega
    have hcc : c ≤ j := by omega
    have reads (r : Nat) (k : Nat) (hk : k < c) :
        entry n (l.set! (i * n + j) s) r k = entry n l r k := by
      rw [entry_write n l i j r k s hr.1 hi hj (by omega)]
      have hn : ¬(r = i ∧ k = j) := by omega
      simp only [hn, ↓reduceIte]
    by_cases he : a = i ∧ c = j
    · obtain ⟨ha, hc⟩ := he
      subst a c
      rw [entry_write n l i j i j s hr.1 hi hj hj, ite_eq_left ⟨rfl, rfl⟩]
      apply (cell_congr n input l (l.set! (i * n + j) s) i j s
        (fun k hk => (reads i k hk).symm) (fun k hk => (reads j k hk).symm) ?_).mp hs
      by_cases hij : i = j
      · exact Or.inl hij
      · right
        rw [entry_write n l i j j j s hr.1 hi hj hj]
        simp [Ne.symm hij]
    · have hprev : c < j ∨ c = j ∧ a < i := by omega
      have hcell := hr.2.2 a c ha hca hprev
      have hdiag : entry n l c c = entry n (l.set! (i * n + j) s) c c := by
        rw [entry_write n l i j c c s hr.1 hi hj hc]
        have hn : ¬(c = i ∧ c = j) := by omega
        simp only [hn, ↓reduceIte]
      rw [entry_write n l i j a c s hr.1 hi hj hc, ite_eq_right he]
      exact (cell_congr n input l (l.set! (i * n + j) s) a c _
        (fun k hk => (reads a k hk).symm) (fun k hk => (reads c k hk).symm) (Or.inr hdiag)).mp hcell

private theorem range_from_current {a n k : Nat} {pref suff : List Nat}
    (h : [a:n].toList = pref ++ k :: suff)
    : k = a + pref.length ∧ k < n := by
  have hlist : List.range' a (n - a) = pref ++ k :: suff := by
    simpa [Std.Legacy.Range.toList] using h
  have hlen := congrArg List.length hlist
  simp only [List.length_range', List.length_append, List.length_cons] at hlen
  have he := congrArg (fun xs => xs[pref.length]?) hlist
  simp [show pref.length < n - a by omega] at he
  omega

private theorem cholesky_equations_triple (n : Nat) (a : Array Float)
    : ⦃⌜True⌝⦄ cholesky n a ⦃⇓? l => ⌜ColumnState n a n n l⌝⦄ := by
  unfold cholesky
  mvcgen
    invariants
      | inv1 => ⇓? ⟨xs, l⟩ => ⌜ColumnState n a xs.prefix.length xs.prefix.length l⌝
      | inv2 pref j suff hj lower hstate pivot hp diagonal hd =>
        ⇓? ⟨xs, l⟩ => ⌜ColumnState n a j (j + 1 + xs.prefix.length) l ∧ entry n l j j = diagonal⌝
    with
      | vc1 =>
        rename_i pref j suff hj lower hstate pivot hp diagonal hd prefI i suffI hi l hl s hs
        have hi' := range_from_current hi
        have hj' := Flare.Matrix.Storage.range_current hj
        have hstate' : ColumnState n a j i l := by simpa only [← hi'.1] using hl.1
        have hcell : CellComputation n a l i j s := by
          simp only [CellComputation, show i ≠ j by omega, ↓reduceIte]
          rw [hl.2]
          exact hs
        have hw := column_write n a l j i s hi'.2 (by omega) hstate' hcell
        refine ⟨?_, ?_⟩
        · convert hw using 1
          simp only [List.length_append, List.length_singleton]
          omega
        · rw [entry_write n l i j j j s hl.1.1 hi'.2 hj'.2 hj'.2]
          simp only [show j ≠ i by omega, false_and, ↓reduceIte]
          exact hl.2
      | vc3 =>
        rename_i pref j suff hj l hstate pivot hp diagonal hd
        have hj' := Flare.Matrix.Storage.range_current hj
        have hstate' : ColumnState n a j j l := by simpa only [← hj'.1] using hstate
        have hcell : CellComputation n a l j j diagonal := by
          simp only [CellComputation, ↓reduceIte]
          exact ⟨pivot, hp, hd⟩
        refine ⟨?_, ?_⟩
        · simpa only [List.length_nil, Nat.add_zero]
            using column_write n a l j j diagonal hj'.2 (le_refl j) hstate' hcell
        · rw [entry_write n l j j j j diagonal hstate'.1 hj'.2 hj'.2 hj'.2]
          simp
      | vc4 =>
        rename_i pref j suff hj initial hstate pivot hp diagonal hd l hl
        have hj' := Flare.Matrix.Storage.range_current hj
        have hl' : ColumnState n a j n l := by
          simpa [Std.Legacy.Range.toList, Nat.add_sub_of_le (by omega : j + 1 ≤ n)]
            using hl.1
        refine ⟨hl'.1, hl'.2.1, ?_⟩
        intro i c hi hci hc
        apply hl'.2.2 i c hi hci
        simp only [List.length_append, List.length_singleton] at hc
        omega
      | vc8 =>
        refine ⟨by simp, ?_, ?_⟩
        · intro i j hi hj hij
          simp only [entry, Flare.Matrix.Dense.entry, Array.getD_eq_getD_getElem?,
            Array.getElem?_replicate]
          split <;> rfl
        · intro i j hi hji hd
          simp only [List.length_nil] at hd
          omega
      | vc9 =>
        rename_i l hl
        simpa [Std.Legacy.Range.toList] using hl

theorem cholesky_equations (n : Nat) (a l : Array Float) (hl : cholesky n a = .ok l)
    : l.size = n * n
      ∧ (∀ i j, i < n → j < n → i < j → entry n l i j = 0.0)
      ∧ ∀ i j, i < n → j ≤ i → CellComputation n a l i j (entry n l i j) := by
  have h := cholesky_equations_triple n a
  rw [hl] at h
  refine ⟨(h True.intro).1, (h True.intro).2.1, ?_⟩
  intro i j hi hji
  exact (h True.intro).2.2 i j hi hji (Or.inl (by omega))

theorem positiveSqrt_success (pivot x : Float) (hf : pivot.isFinite = true)
    (hx : positiveSqrt pivot = .ok x)
    : x = pivot.sqrt
      ∧ x.isFinite = true
      ∧ 0 < value x
      ∧ |(value x) ^ 2 - value pivot|
        ≤ (2 * (2 : ℝ) ^ (-53 : Int) + ((2 : ℝ) ^ (-53 : Int)) ^ 2) * value pivot := by
  have hg : 0.0 < pivot := by
    by_contra hn
    simp only [positiveSqrt, hn, ↓reduceIte] at hx
    change Except.error Kalman.Definitions.Input.Error.nonpositivePivot = .ok x at hx
    cases hx
  have hp : 0 < value pivot := by
    simpa only [Flare.Binary64.Arithmetic.zero_value]
      using (Flare.Binary64.Order.lt_iff _ _ (by decide) hf).mp hg
  obtain ⟨hs, hsf, hsp, he⟩ := positiveSqrt_accuracy pivot hf hp
  have hxe : x = pivot.sqrt := Except.ok.inj (hx.symm.trans hs)
  subst x
  exact ⟨rfl, hsf, hsp, he⟩

theorem diagonal_backward_error (indices : List Nat) (left : Nat → Float)
    (initial x : Float) (M : ℝ) (p : ResidualProfile indices left left initial M)
    (hexec
      : ∃ pivot,
          subtractProducts indices left left initial = .ok pivot
          ∧ positiveSqrt pivot = .ok x)
    : 0 < value x
      ∧ |(value x) ^ 2
          - (value initial
              - (indices.map (fun k => value (left k) * value (left k))).sum)|
        ≤ diagonalRadius indices.length M := by
  obtain ⟨r, hr, hf, he⟩ := residual_accuracy indices left left initial M p
  obtain ⟨pivot, hp, hx⟩ := hexec
  have heq : pivot = r := Except.ok.inj (hp.symm.trans hr)
  subst pivot
  obtain ⟨_, _, hpos, hs⟩ := positiveSqrt_success r x hf hx
  refine ⟨hpos, ?_⟩
  have htarget := profile_target_bound _ _ _ _ _ p
  have hmag : value r ≤ M + residualRadius indices.length M := by
    have ht := (abs_le.mp he).2
    have hh := le_abs_self (value initial - (indices.map (fun k => value (left k) * value (left k))).sum)
    linarith
  have hm := mul_le_mul_of_nonneg_left hmag
    (by positivity : 0 ≤ 2 * (2 : ℝ)^(-53 : Int) + ((2 : ℝ)^(-53 : Int))^2)
  have ht := abs_sub_le ((value x)^2) (value r)
    (value initial - (indices.map (fun k => value (left k) * value (left k))).sum)
  unfold diagonalRadius
  linarith

private theorem gram_prefix (n : Nat) (l : Array Float)
    (hz : ∀ i j : Fin n, i < j → matrix n n l i j = 0)
    (i j : Fin n)
    : (matrix n n l * (matrix n n l).transpose) i j
      = value (entry n l i.val j.val) * value (entry n l j.val j.val)
        + ∑ k ∈ Finset.range j.val,
            value (entry n l i.val k) * value (entry n l j.val k) := by
  rw [Matrix.mul_apply]
  have he (k : Fin n) : matrix n n l i k * (matrix n n l).transpose k j =
      (if k = j then value (entry n l i.val j.val) * value (entry n l j.val j.val) else 0) +
      (if k.val < j.val then value (entry n l i.val k.val) * value (entry n l j.val k.val) else 0) := by
    by_cases hkj : k = j
    · subst k
      simp [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry]
    · by_cases hlt : k.val < j.val
      · simp [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry, hkj, hlt]
      · have hjk : j < k := by have := Fin.val_ne_of_ne hkj; exact Fin.lt_def.mpr (by omega)
        simp only [Matrix.transpose_apply, hz j k hjk, mul_zero, hkj, hlt, ↓reduceIte, add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hsum : (∑ k : Fin n, if k.val < j.val then
        value (entry n l i.val k.val) * value (entry n l j.val k.val) else 0) =
      ∑ k ∈ Finset.range j.val, value (entry n l i.val k) * value (entry n l j.val k) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => if k < j.val then
      value (entry n l i.val k) * value (entry n l j.val k) else 0), ← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hsum]
  simp

theorem diagonalRadius_mono {k n : Nat} (M : ℝ) (hM : 0 ≤ M) (hkn : k ≤ n)
    : diagonalRadius k M ≤ diagonalRadius n M := by
  have he := residualRadius_mono M hM hkn
  unfold diagonalRadius
  exact add_le_add he
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl M) he) (by positivity))

/-- Backward error of the entire actual Cholesky factor. Every lower cell is
connected to the native computation by the column-write invariant above.
Symmetry extends the lower-triangle enclosure to the full input matrix. -/
theorem factor_backward_error (n : Nat) (a l : Array Float) (M δ D : ℝ)
    (p : FactorProfile n a l M δ D)
    : EntrywiseWithin (diagonalRadius n M + divisionRadius n M δ D)
        (matrix n n l * (matrix n n l).transpose) (matrix n n a) := by
  have h := cholesky_equations n a l p.execution
  have hz : ∀ i j : Fin n, i < j → matrix n n l i j = 0 := by
    intro i j hij
    change value (entry n l i.val j.val) = 0
    rw [h.2.1 i.val j.val i.isLt j.isLt (Fin.lt_def.mp hij)]
    exact Flare.Binary64.Arithmetic.zero_value
  have hdiag0 : 0 ≤ diagonalRadius n M := by
    unfold diagonalRadius residualRadius
    have hM := p.mass_nonneg
    positivity
  have hdiv0 := divisionRadius_nonneg n M δ D p.mass_nonneg p.diagonal_lower p.bound_nonneg
  have lower (i j : Fin n) (hji : j ≤ i) :
      |(matrix n n l * (matrix n n l).transpose) i j - matrix n n a i j|
      ≤ diagonalRadius n M + divisionRadius n M δ D := by
    have hcell := h.2.2 i.val j.val i.isLt (Fin.le_def.mp hji)
    by_cases heq : i = j
    · subst i
      have hce : ∃ pivot, subtractProducts (List.range j.val) (fun k => entry n l j.val k)
          (fun k => entry n l j.val k) (entry n a j.val j.val) = .ok pivot ∧
          positiveSqrt pivot = .ok (entry n l j.val j.val) := by
        simpa only [CellComputation, ↓reduceIte] using hcell
      have he := (diagonal_backward_error _ _ _ _ M
        (p.rows j.val j.val j.isLt (le_refl _)) hce).2
      simp only [← List.sum_toFinset _ (List.nodup_range (n := j.val)), List.toFinset_range,
        List.length_range] at he
      have hbound := he.trans (diagonalRadius_mono M p.mass_nonneg (Nat.le_of_lt j.isLt))
      have hid : |(matrix n n l * (matrix n n l).transpose) j j - matrix n n a j j| =
        |(value (entry n l j.val j.val))^2 - (value (entry n a j.val j.val) -
          ∑ k ∈ Finset.range j.val, value (entry n l j.val k) * value (entry n l j.val k))| := by
        rw [gram_prefix n l hz j j]
        change |value (entry n l j.val j.val) * value (entry n l j.val j.val) + _ -
          value (entry n a j.val j.val)| = _
        congr 1
        ring
      rw [hid]
      exact hbound.trans (by linarith)
    · have hne : i.val ≠ j.val := fun he => heq (Fin.ext he)
      have hce : divideResidual (List.range j.val) (fun k => entry n l i.val k)
          (fun k => entry n l j.val k) (entry n a i.val j.val) (entry n l j.val j.val) =
          .ok (entry n l i.val j.val) := by
        simpa only [CellComputation, hne, ↓reduceIte] using hcell
      have hq : (M + residualRadius j.val M) / δ ≤ (2 : ℝ)^(1000 : Int) :=
        (div_le_div_of_nonneg_right (add_le_add (le_refl M)
          (residualRadius_mono M p.mass_nonneg (Nat.le_of_lt j.isLt))) p.diagonal_lower.le).trans
          p.quotient_bound
      obtain ⟨r, hr, _, he⟩ := divideResidual_accuracy _ _ _ _ _ M δ D
        (p.rows i.val j.val i.isLt (Fin.le_def.mp hji))
        (Flare.Matrix.Storage.getD_finite _ _ p.finite_lower)
        p.diagonal_lower (p.diagonal_floor j.val j.isLt) (p.diagonal_bound j.val j.isLt)
        (by simpa using hq)
      have hre : r = entry n l i.val j.val := Except.ok.inj (hr.symm.trans hce)
      subst r
      simp only [← List.sum_toFinset _ (List.nodup_range (n := j.val)), List.toFinset_range,
        List.length_range] at he
      have hbound := he.trans (divisionRadius_mono M δ D p.mass_nonneg p.diagonal_lower
        p.bound_nonneg (Nat.le_of_lt j.isLt))
      have hid : |(matrix n n l * (matrix n n l).transpose) i j - matrix n n a i j| =
          |value (entry n l i.val j.val) * value (entry n l j.val j.val) -
            (value (entry n a i.val j.val) - ∑ k ∈ Finset.range j.val,
              value (entry n l i.val k) * value (entry n l j.val k))| := by
        rw [gram_prefix n l hz i j]
        change |value (entry n l i.val j.val) * value (entry n l j.val j.val) + _ -
          value (entry n a i.val j.val)| = _
        congr 1
        ring
      rw [hid]
      exact hbound.trans (by linarith)
  refine ⟨add_nonneg hdiag0 hdiv0, fun i j => ?_⟩
  by_cases hji : j ≤ i
  · exact lower i j hji
  · have hij : i ≤ j := le_of_lt (lt_of_not_ge hji)
    have hsym : (matrix n n l * (matrix n n l).transpose) i j =
        (matrix n n l * (matrix n n l).transpose) j i := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hasym : matrix n n a i j = matrix n n a j i := by
      simpa only [Matrix.conjTranspose_apply, star_trivial]
        using congr_fun (congr_fun p.symmetry.eq j) i
    rw [hsym, hasym]
    exact lower j i hij

end Kalman.Proofs.FloatCholeskyFactor
