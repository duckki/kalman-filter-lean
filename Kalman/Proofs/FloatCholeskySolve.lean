import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.FloatResidualError
import Kalman.Proofs.ErrorPropagation
import Kalman.Proofs.FactorStructure

/-! The stored native substitution results obey their row kernels. This data
flow proof connects arithmetic allowances to the actual two-pass solve. -/

namespace Kalman.Proofs.FloatCholeskySolve

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.FloatResidualError
open Flare.Binary64.Value Std.Do

set_option mvcgen.warning false

private theorem entry_write (n columns : Nat) (r : Array Float) (i j a c : Nat)
    (s : Float) (hr : r.size = n * columns) (hi : i < n) (hj : j < columns)
    (hc : c < columns)
    : entry columns (r.set! (i * columns + j) s) a c
      = if a = i ∧ c = j then s else entry columns r a c :=
  Flare.Matrix.Storage.entry_set columns r i j a c s hr hi hj hc

theorem divideResidual_congr (indices : List Nat) (left right left' right' : Nat → Float)
    (initial diagonal : Float) (hl : ∀ k ∈ indices, left k = left' k)
    (hr : ∀ k ∈ indices, right k = right' k)
    : divideResidual indices left right initial diagonal
      = divideResidual indices left' right' initial diagonal := by
  unfold divideResidual
  simp only [subtractProducts_bridge,
    Flare.Matrix.Substitution.subtractProducts_congr indices left right left' right' initial hl hr]

@[spec]
private theorem divideResidual_result (indices : List Nat) (left right : Nat → Float)
    (initial diagonal : Float)
    : ⦃⌜True⌝
      ⦄ divideResidual indices left right initial diagonal
      ⦃⇓? r => ⌜divideResidual indices left right initial diagonal = .ok r⌝⦄ := by
  generalize he : divideResidual indices left right initial diagonal = result
  cases result <;> mvcgen

private def ForwardEquations (n columns : Nat) (l b : Array Float) (i j : Nat)
    (r : Array Float)
    : Prop :=
  r.size = n * columns
  ∧ ∀ a c,
      a < n
      → c < columns
      → a < i ∨ a = i ∧ c < j
      → divideResidual (List.range a) (fun k => entry n l a k)
          (fun k => entry columns r k c) (entry columns b a c) (entry n l a a)
        = .ok (entry columns r a c)

private theorem forward_write (n columns : Nat) (l b r : Array Float)
    (i j : Nat) (s : Float) (hi : i < n) (hj : j < columns)
    (hr : ForwardEquations n columns l b i j r)
    (hs
      : divideResidual (List.range i) (fun k => entry n l i k)
          (fun k => entry columns r k j) (entry columns b i j) (entry n l i i)
        = .ok s)
    : ForwardEquations n columns l b i (j + 1) (r.set! (i * columns + j) s) := by
  refine ⟨(Array.size_set! ..).trans hr.1, ?_⟩
  intro a c ha hc hac
  have reads (hrow : a ≤ i) :
      divideResidual (List.range a) (fun k => entry n l a k)
        (fun k => entry columns (r.set! (i * columns + j) s) k c)
        (entry columns b a c) (entry n l a a) =
      divideResidual (List.range a) (fun k => entry n l a k)
        (fun k => entry columns r k c) (entry columns b a c) (entry n l a a) := by
    apply divideResidual_congr _ _ _ _ _ _ _ (by intros; rfl)
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [entry_write n columns r i j k c s hr.1 hi hj hc]
    simp [show k ≠ i by omega]
  rw [reads (by omega)]
  rw [entry_write n columns r i j a c s hr.1 hi hj hc]
  split
  · rename_i he
    obtain ⟨rfl, rfl⟩ := he
    exact hs
  · apply hr.2 a c ha hc
    omega

private theorem forward_equations_triple (n columns : Nat) (l b : Array Float)
    : ⦃⌜True⌝
      ⦄ forwardCholesky n columns l b
      ⦃⇓? r => ⌜ForwardEquations n columns l b n 0 r⌝⦄ := by
  unfold forwardCholesky
  mvcgen
    invariants
      | inv1 => ⇓? ⟨xs, r⟩ => ⌜ForwardEquations n columns l b xs.prefix.length 0 r⌝
      | inv2 pref i suff hi initial hs =>
        ⇓? ⟨xs, r⟩ => ⌜ForwardEquations n columns l b i xs.prefix.length r⌝
    with
      | vc1 =>
        rename_i prefI i suffI hi initial hinit prefJ j suffJ hj r hr s hs
        have hj' := Flare.Matrix.Storage.range_current hj
        have hh := forward_write n columns l b r i j s
          (Flare.Matrix.Storage.range_current hi).2 hj'.2
          (by simpa only [hj'.1] using hr) hs
        simpa only [List.length_append, List.length_singleton, ← hj'.1] using hh
      | vc3 =>
        rename_i pref i suff hi r hr
        simpa only [(Flare.Matrix.Storage.range_current hi).1, List.length_nil] using hr
      | vc4 =>
        rename_i pref i suff hi initial hinit r hr
        have hr' : ForwardEquations n columns l b i columns r := by
          simpa [Std.Legacy.Range.toList] using hr
        refine ⟨hr'.1, ?_⟩
        intro a c ha hc hac
        apply hr'.2 a c ha hc
        have hi' := (Flare.Matrix.Storage.range_current hi).1
        simp only [List.length_append, List.length_singleton] at hac
        omega
      | vc6 => simp [ForwardEquations]
      | vc7 =>
        rename_i r hr
        simpa [Std.Legacy.Range.toList] using hr

theorem forward_equations (n columns : Nat) (l b y : Array Float)
    (hy : forwardCholesky n columns l b = .ok y)
    : y.size = n * columns
      ∧ ∀ i j,
          i < n
          → j < columns
          → divideResidual (List.range i) (fun k => entry n l i k)
              (fun k => entry columns y k j) (entry columns b i j) (entry n l i i)
            = .ok (entry columns y i j) := by
  have h := forward_equations_triple n columns l b
  rw [hy] at h
  exact ⟨(h True.intro).1, fun i j hi hj => (h True.intro).2 i j hi hj (Or.inl hi)⟩

private def BackwardEquations (n columns : Nat) (l y : Array Float) (step j : Nat)
    (r : Array Float)
    : Prop :=
  r.size = n * columns
  ∧ ∀ a c,
      a < n
      → c < columns
      → n - 1 - a < step ∨ n - 1 - a = step ∧ c < j
      → divideResidual (List.range' (a + 1) (n - (a + 1))) (fun k => entry n l k a)
          (fun k => entry columns r k c) (entry columns y a c) (entry n l a a)
        = .ok (entry columns r a c)

private theorem backward_write (n columns : Nat) (l y r : Array Float)
    (step j : Nat) (s : Float) (ht : step < n) (hj : j < columns)
    (hr : BackwardEquations n columns l y step j r)
    (hs
      : divideResidual (List.range' (n - 1 - step + 1) (n - (n - 1 - step + 1)))
          (fun k => entry n l k (n - 1 - step)) (fun k => entry columns r k j)
          (entry columns y (n - 1 - step) j) (entry n l (n - 1 - step) (n - 1 - step))
        = .ok s)
    : BackwardEquations n columns l y step (j + 1)
        (r.set! ((n - 1 - step) * columns + j) s) := by
  let i := n - 1 - step
  have hi : i < n := by dsimp [i]; omega
  refine ⟨(Array.size_set! ..).trans hr.1, ?_⟩
  intro a c ha hc hac
  have hai : i ≤ a := by dsimp [i]; omega
  have reads :
      divideResidual (List.range' (a + 1) (n - (a + 1))) (fun k => entry n l k a)
        (fun k => entry columns (r.set! (i * columns + j) s) k c)
        (entry columns y a c) (entry n l a a) =
      divideResidual (List.range' (a + 1) (n - (a + 1))) (fun k => entry n l k a)
        (fun k => entry columns r k c) (entry columns y a c) (entry n l a a) := by
    apply divideResidual_congr _ _ _ _ _ _ _ (by intros; rfl)
    intro k hk
    obtain ⟨t, _, hkt⟩ := List.mem_range'.mp hk
    have hki : k ≠ i := by omega
    rw [entry_write n columns r i j k c s hr.1 hi hj hc]
    simp [hki]
  change divideResidual _ _ (fun k => entry columns (r.set! (i * columns + j) s) k c) _ _ = _
  rw [reads, entry_write n columns r i j a c s hr.1 hi hj hc]
  split
  · rename_i he
    obtain ⟨rfl, rfl⟩ := he
    exact hs
  · apply hr.2 a c ha hc
    dsimp [i] at *
    omega

private theorem backward_equations_triple (n columns : Nat) (l y : Array Float)
    : ⦃⌜True⌝
      ⦄ backwardCholesky n columns l y
      ⦃⇓? r => ⌜BackwardEquations n columns l y n 0 r⌝⦄ := by
  unfold backwardCholesky
  mvcgen
    invariants
      | inv1 => ⇓? ⟨xs, r⟩ => ⌜BackwardEquations n columns l y xs.prefix.length 0 r⌝
      | inv2 pref t suff ht initial i hs =>
        ⇓? ⟨xs, r⟩ => ⌜BackwardEquations n columns l y t xs.prefix.length r⌝
    with
      | vc1 =>
        rename_i prefT t suffT ht initial i hinit prefJ j suffJ hj r hr s hs
        have hj' := Flare.Matrix.Storage.range_current hj
        have hh := backward_write n columns l y r t j s
          (Flare.Matrix.Storage.range_current ht).2 hj'.2
          (by simpa only [hj'.1] using hr) hs
        simpa only [List.length_append, List.length_singleton, ← hj'.1] using hh
      | vc3 =>
        rename_i pref t suff ht r i hr
        simpa only [(Flare.Matrix.Storage.range_current ht).1, List.length_nil] using hr
      | vc4 =>
        rename_i pref t suff ht initial i hinit r hr
        have hr' : BackwardEquations n columns l y t columns r := by
          simpa [Std.Legacy.Range.toList] using hr
        refine ⟨hr'.1, ?_⟩
        intro a c ha hc hac
        apply hr'.2 a c ha hc
        have ht' := (Flare.Matrix.Storage.range_current ht).1
        simp only [List.length_append, List.length_singleton] at hac
        omega
      | vc6 => simp [BackwardEquations]
      | vc7 =>
        rename_i r hr
        simpa [Std.Legacy.Range.toList] using hr

theorem backward_equations (n columns : Nat) (l y x : Array Float)
    (hx : backwardCholesky n columns l y = .ok x)
    : x.size = n * columns
      ∧ ∀ i j,
          i < n
          → j < columns
          → divideResidual (List.range' (i + 1) (n - (i + 1))) (fun k => entry n l k i)
              (fun k => entry columns x k j) (entry columns y i j) (entry n l i i)
            = .ok (entry columns x i j) := by
  have h := backward_equations_triple n columns l y
  rw [hx] at h
  exact ⟨
    (h True.intro).1,
    fun i j hi hj => (h True.intro).2 i j hi hj (Or.inl (by omega))
  ⟩

private theorem lower_sum (n i : Nat) (hi : i ≤ n) (f : Nat → ℝ)
    : (∑ k : Fin n, if k.val < i then f k.val else 0) = ∑ k ∈ Finset.range i, f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < i then f k else 0), ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem upper_sum (n i : Nat) (f : Nat → ℝ)
    : (∑ k : Fin n, if i < k.val then f k.val else 0)
      = ∑ k ∈ Finset.Ico (i + 1) n, f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if i < k then f k else 0), ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private theorem lower_product (n columns : Nat) (l y : Array Float)
    (hz : ∀ i j : Fin n, i < j → matrix n n l i j = 0) (i : Fin n) (j : Fin columns)
    : (matrix n n l * matrix n columns y) i j
      = value (entry n l i.val i.val) * value (entry columns y i.val j.val)
        + ∑ k ∈ Finset.range i.val,
            value (entry n l i.val k) * value (entry columns y k j.val) := by
  rw [Matrix.mul_apply]
  have he (k : Fin n) : matrix n n l i k * matrix n columns y k j =
      (if k = i then value (entry n l i.val i.val) * value (entry columns y i.val j.val) else 0) +
      (if k.val < i.val then value (entry n l i.val k.val) *
        value (entry columns y k.val j.val) else 0) := by
    by_cases hki : k = i
    · subst k; simp [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry]
    · by_cases hlt : k.val < i.val
      · simp [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry, hki, hlt]
      · have hik : i < k := by have := Fin.val_ne_of_ne hki; exact Fin.lt_def.mpr (by omega)
        simp only [hz i k hik, zero_mul, hki, hlt, ↓reduceIte, add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib, lower_sum n i.val (Nat.le_of_lt i.isLt)
    (fun k => value (entry n l i.val k) * value (entry columns y k j.val))]
  simp

private theorem upper_product (n columns : Nat) (l x : Array Float)
    (hz : ∀ i j : Fin n, i < j → matrix n n l i j = 0) (i : Fin n) (j : Fin columns)
    : ((matrix n n l).transpose * matrix n columns x) i j
      = value (entry n l i.val i.val) * value (entry columns x i.val j.val)
        + ∑ k ∈ Finset.Ico (i.val + 1) n,
            value (entry n l k i.val) * value (entry columns x k j.val) := by
  rw [Matrix.mul_apply]
  have he (k : Fin n) : (matrix n n l).transpose i k * matrix n columns x k j =
      (if k = i then value (entry n l i.val i.val) * value (entry columns x i.val j.val) else 0) +
      (if i.val < k.val then value (entry n l k.val i.val) *
        value (entry columns x k.val j.val) else 0) := by
    by_cases hki : k = i
    · subst k; simp [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry]
    · by_cases hlt : i.val < k.val
      · simp [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry, hki, hlt]
      · have hki' : k < i := by have := Fin.val_ne_of_ne hki; exact Fin.lt_def.mpr (by omega)
        simp only [Matrix.transpose_apply, hz k i hki', zero_mul, hki, hlt, ↓reduceIte, add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib, upper_sum n i.val
    (fun k => value (entry n l k i.val) * value (entry columns x k j.val))]
  simp

/-- Actual returned arrays obey both triangular residual enclosures. Profiles
are on their stored term masses, not on an assumed residual or solution error. -/
theorem substitution_residuals (n columns : Nat) (l b y x : Array Float) (M δ D : ℝ)
    (p : SolveProfile n columns l b y x M δ D) (hM : 0 ≤ M)
    : y.size = n * columns
      ∧ x.size = n * columns
      ∧ (∀ i j,
          |(matrix n n l * matrix n columns y - matrix n columns b) i j|
          ≤ divisionRadius n M δ D)
      ∧ (∀ i j,
          |((matrix n n l).transpose * matrix n columns x - matrix n columns y) i j|
          ≤ divisionRadius n M δ D) := by
  have hf := forward_equations n columns l b y p.forward
  have hb := backward_equations n columns l y x p.backward
  have quotient (k : Nat) (hk : k ≤ n) :
      (M + residualRadius k M) / δ ≤ (2 : ℝ) ^ (1000 : Int) :=
    (div_le_div_of_nonneg_right
      (add_le_add (le_refl M) (residualRadius_mono M hM hk)) p.diagonal_lower.le).trans p.quotient_bound
  refine ⟨hf.1, hb.1, ?_, ?_⟩
  · intro i j
    obtain ⟨r, hr, _, he⟩ := divideResidual_accuracy _ _ _ _ _ M δ D
      (p.forward_rows i.val j.val i.isLt j.isLt)
      (Flare.Matrix.Storage.getD_finite _ _ p.finite_lower) p.diagonal_lower
      (p.diagonal_floor i.val i.isLt) (p.lower_bound i i)
      (by simpa using quotient i.val (Nat.le_of_lt i.isLt))
    have hre : r = entry columns y i.val j.val :=
      Except.ok.inj (hr.symm.trans (hf.2 i.val j.val i.isLt j.isLt))
    subst r
    have hlist : (List.range i.val).toFinset = Finset.range i.val := List.toFinset_range _
    simp only [← List.sum_toFinset _ (List.nodup_range (n := i.val)), hlist, List.length_range] at he
    apply (le_trans ?_ (divisionRadius_mono M δ D hM p.diagonal_lower p.bound_nonneg
      (Nat.le_of_lt i.isLt)))
    rw [Matrix.sub_apply, lower_product n columns l y p.lower_positive.1 i j]
    convert he using 1
    simp only [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry]
    congr 1
    ring
  · intro i j
    obtain ⟨r, hr, _, he⟩ := divideResidual_accuracy _ _ _ _ _ M δ D
      (p.backward_rows i.val j.val i.isLt j.isLt)
      (Flare.Matrix.Storage.getD_finite _ _ p.finite_lower) p.diagonal_lower
      (p.diagonal_floor i.val i.isLt) (p.lower_bound i i)
      (by simpa using quotient (n - (i.val + 1)) (by omega))
    have hre : r = entry columns x i.val j.val :=
      Except.ok.inj (hr.symm.trans (hb.2 i.val j.val i.isLt j.isLt))
    subst r
    have hlist : (List.range' (i.val + 1) (n - (i.val + 1))).toFinset = Finset.Ico (i.val + 1) n := by
      rw [List.toFinset_range'_1, Nat.add_sub_of_le (by omega : i.val + 1 ≤ n)]
    simp only [← List.sum_toFinset _ List.nodup_range', hlist, List.length_range'] at he
    apply (le_trans ?_ (divisionRadius_mono M δ D hM p.diagonal_lower p.bound_nonneg
      (show n - (i.val + 1) ≤ n by omega)))
    rw [Matrix.sub_apply, upper_product n columns l x p.lower_positive.1 i j]
    convert he using 1
    simp only [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry]
    congr 1
    ring

/-- A posteriori residual enclosure for the actual two-pass Cholesky solve,
relative to the exact Gram denoted by its supplied stored factor. -/
theorem solve_residual (n columns : Nat) (l b y x : Array Float) (M δ D : ℝ)
    (p : SolveProfile n columns l b y x M δ D) (hM : 0 ≤ M)
    : solveCholesky n columns l b = .ok x
      ∧ x.size = n * columns
      ∧ ∀ i j,
          |((matrix n n l * (matrix n n l).transpose) * matrix n columns x
            - matrix n columns b)
            i j|
          ≤ (1 + n * D) * divisionRadius n M δ D := by
  obtain ⟨_, hs, hf, hb⟩ := substitution_residuals n columns l b y x M δ D p hM
  refine ⟨?_, hs, ?_⟩
  · unfold solveCholesky
    rw [p.forward]
    change backwardCholesky n columns l y = .ok x
    exact p.backward
  · intro i j
    have hid : (matrix n n l * (matrix n n l).transpose) * matrix n columns x - matrix n columns b =
        matrix n n l * ((matrix n n l).transpose * matrix n columns x - matrix n columns y) +
          (matrix n n l * matrix n columns y - matrix n columns b) := by
      rw [Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [hid, Matrix.add_apply]
    have hmul := Kalman.Proofs.ErrorPropagation.product_magnitude (matrix n n l)
      ((matrix n n l).transpose * matrix n columns x - matrix n columns y)
      D (divisionRadius n M δ D) p.lower_bound hb i j
    have ht := (abs_add_le _ _).trans (add_le_add hmul (hf i j))
    nlinarith

/-- Forward error with an explicit positive spectral floor. This compares to
the supplied factor's exact Gram, not yet to the ideal innovation covariance. -/
theorem solve_accuracy (n columns : Nat) (l b y x : Array Float) (M δ D α : ℝ)
    (p : SolveProfile n columns l b y x M δ D) (hM : 0 ≤ M) (hα : 0 < α)
    (hA : (matrix n n l * (matrix n n l).transpose - α • 1).PosSemidef)
    : solveCholesky n columns l b = .ok x
      ∧ Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin
          (n * ((1 + n * D) * divisionRadius n M δ D) / α)
          (matrix n columns x)
          ((matrix n n l * (matrix n n l).transpose)⁻¹ * matrix n columns b) := by
  obtain ⟨hs, _, hr⟩ := solve_residual n columns l b y x M δ D p hM
  let A := matrix n n l * (matrix n n l).transpose
  let ρ := (1 + n * D) * divisionRadius n M δ D
  have hD := p.bound_nonneg
  have hρ : 0 ≤ ρ := mul_nonneg (by positivity)
    (divisionRadius_nonneg n M δ D hM p.diagonal_lower p.bound_nonneg)
  have hpd := Flare.Analysis.NumericalBounds.posDef_of_lower_bound A α hα hA
  have hinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hpd.isUnit)
  refine ⟨hs, by change 0 ≤ n * ρ / α; positivity, ?_⟩
  intro i j
  have hexact : A.mulVec (fun k => (A⁻¹ * matrix n columns b) k j) =
      fun k => matrix n columns b k j := by
    have heq : A * (A⁻¹ * matrix n columns b) = matrix n columns b := by
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    ext k
    exact congr_fun (congr_fun heq k) j
  exact Flare.Analysis.NumericalBounds.residual_entrywise_bound A α ρ hα hρ hA
    (fun k => matrix n columns x k j) (fun k => (A⁻¹ * matrix n columns b) k j)
    (fun k => matrix n columns b k j) hexact (fun k => hr k j) i

end Kalman.Proofs.FloatCholeskySolve
