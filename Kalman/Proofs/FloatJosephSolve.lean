import Kalman.Proofs.FloatDiagonalStorage
import Kalman.Proofs.FloatSolveError
import Kalman.Proofs.RealDiagonalObservation

/-! Two-state diagonal LDLᵀ analysis for the dense Joseph filter. The actual
runtime factorization and solve are unchanged. Diagonal structure removes the
generic LDLᵀ conditioning allowance; every remaining rounding is charged. -/

namespace Kalman.Proofs.FloatJosephSolve

open Matrix hiding transpose
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Flare.Binary64.Value

set_option maxHeartbeats 1600000

private theorem finite_core (x : Float) (h : x.isFinite = true)
    : Flare.Matrix.Dense.finite x = .ok x := by
  simp [Flare.Matrix.Dense.finite, h]

private theorem subtract_zero_error (a z : Float)
    (ha : a.isFinite = true) (hz : z.isFinite = true)
    (hb : |value a| ≤ 5) (hzero : value z = 0)
    : (a - z).isFinite = true ∧ |value (a - z) - value a| ≤ (2 : ℝ) ^ (-49 : Int) := by
  have h := Flare.Binary64.Arithmetic.sub_error a z 3 ha hz
    (by norm_num) (by norm_num) (by rw [hzero, sub_zero]; norm_num; linarith)
  simpa only [hzero, sub_zero, show (3 : Int) - 52 = -49 by norm_num] using h

/-- Original finite diagonal coefficient bounds establish successful pivots,
an exactly diagonal decoded L, and a sharp bound for the second pivot. -/
theorem factor_diagonal (a : Array Float)
    (hf : a.all Float.isFinite = true) (hz : DecodedDiagonal 2 a)
    (hlo : ∀ i, i < 2 → (3 : ℝ) / 2 ≤ value (entry 2 a i i))
    (hhi : ∀ i, i < 2 → value (entry 2 a i i) ≤ 5)
    : ∃ l d,
        Flare.Matrix.Dense.factor 2 a = .ok ⟨#[1.0, 0.0, l, 1.0], #[entry 2 a 0 0, d]⟩
        ∧ l.isFinite = true
        ∧ value l = 0
        ∧ d.isFinite = true
        ∧ 1 ≤ value d
        ∧ value d ≤ 6
        ∧ |value d - value (entry 2 a 1 1)| ≤ (2 : ℝ) ^ (-49 : Int) := by
  have af (i j : Nat) := Flare.Matrix.Storage.getD_finite a (i * 2 + j) hf
  have hp0 : 0.0 < entry 2 a 0 0 := by
    apply (Flare.Binary64.Order.lt_iff _ _ (by decide) (af 0 0)).mpr
    change (0 : ℝ) < value (entry 2 a 0 0)
    linarith [hlo 0 (by decide)]
  have hl := Flare.Binary64.Zero.div_zero (entry 2 a 1 0) (entry 2 a 0 0)
    (af 1 0) (af 0 0) (hz 1 0 (by decide) (by decide) (by decide))
    (by linarith [hlo 0 (by decide)])
  let l := entry 2 a 1 0 / entry 2 a 0 0
  have ht := Flare.Binary64.Zero.mul_zero l (entry 2 a 0 0) hl.1 (af 0 0)
    (by rw [hl.2]; simp)
  have hu := Flare.Binary64.Zero.mul_zero (l * entry 2 a 0 0) l ht.1 hl.1
    (by rw [ht.2]; simp)
  have hd := subtract_zero_error (entry 2 a 1 1) ((l * entry 2 a 0 0) * l)
    (af 1 1) hu.1 (by rw [abs_of_pos (by linarith [hlo 1 (by decide)])]; exact hhi 1 (by decide)) hu.2
  let d := entry 2 a 1 1 - (l * entry 2 a 0 0) * l
  have dlow : 1 ≤ value d := by
    have he := (abs_le.mp hd.2).1
    have ha := hlo 1 (by decide)
    norm_num only at he
    dsimp only [d]
    linarith
  have dhi : value d ≤ 6 := by
    have he := (abs_le.mp hd.2).2
    have ha := hhi 1 (by decide)
    norm_num only at he
    dsimp only [d]
    linarith
  have dp : 0.0 < d := by
    apply (Flare.Binary64.Order.lt_iff _ _ (by decide) hd.1).mpr
    simp only [Flare.Binary64.Arithmetic.zero_value]
    linarith
  refine ⟨l, d, ?_, hl.1, hl.2, hd.1, dlow, dhi, hd.2⟩
  dsimp only [l, d, entry, Flare.Matrix.Dense.entry] at hp0 hl ht hu hd dp ⊢
  simp only [Array.getD_eq_getD_getElem?] at hp0 hl ht hu hd dp
  norm_num only at hp0 hl ht hu hd dp
  simp [Flare.Matrix.Dense.factor, Flare.Matrix.Dense.finite,
    Std.Legacy.Range.forIn_eq_forIn_range', List.range',
    List.forIn_cons, List.forIn_nil, hp0, dp, hl.1, ht.1, hu.1, hd.1,
    Flare.Matrix.Dense.entry, bind, Except.bind, pure, Except.pure,
    -bind_pure_comp]
  constructor <;> apply Array.ext
  all_goals try { simp; done }
  all_goals
    intro i hi hj
    simp only [Array.size_setIfInBounds, Array.size_replicate] at hi
    interval_cases i <;> simp

private theorem quotient_error_from_residual (x y b a d : ℝ)
    (ha : 1 ≤ a) (hd : 1 ≤ d) (hD : d ≤ 6)
    (hx : |x| ≤ 6) (had : |a - d| ≤ (2 : ℝ) ^ (-49 : Int))
    (hxy : |x - y / d| ≤ (2 : ℝ) ^ (-43 : Int))
    (hyb : |y - b| ≤ (2 : ℝ) ^ (-45 : Int))
    : |x - b / a| ≤ (2 : ℝ) ^ (-40 : Int) := by
  have hd0 : d ≠ 0 := by linarith
  have eq : x * a - b = x * (a - d) + (x - y / d) * d + (y - b) := by
    field_simp
    ring
  have hr : |x * a - b| ≤ 6 * (2 : ℝ) ^ (-49 : Int)
      + (2 : ℝ) ^ (-43 : Int) * 6 + (2 : ℝ) ^ (-45 : Int) := by
    rw [eq]
    calc
      _ ≤ |x * (a - d)| + |(x - y / d) * d| + |y - b| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < d)]
        exact add_le_add
          (add_le_add
            (mul_le_mul hx had (abs_nonneg _) (by norm_num))
            (mul_le_mul hxy hD (by linarith) (by positivity)))
          hyb
  have ha0 : 0 < a := by linarith
  rw [show x - b / a = (x * a - b) / a by field_simp,
    abs_div, abs_of_pos ha0]
  apply (div_le_iff₀ ha0).mpr
  apply hr.trans
  have h := mul_le_mul_of_nonneg_left ha
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-40 : Int))
  norm_num at h ⊢
  linarith

private theorem zero_product_sums (s : Finset Nat) (left right : Nat → Float)
    (hz : ∀ k ∈ s, value (left k) = 0)
    : (∑ k ∈ s, value (left k) * value (right k)) = 0
      ∧ (∑ k ∈ s, |value (left k) * value (right k)|) = 0 := by
  constructor <;> apply Finset.sum_eq_zero <;> intro k hk
  · rw [hz k hk, zero_mul]
  · rw [hz k hk, zero_mul, abs_zero]

private theorem residual_zero (indices : List Nat) (left right : Nat → Float) (b : Float)
    (hb : b.isFinite = true) (hb0 : value b = 0)
    (hl : ∀ k ∈ indices, (left k).isFinite = true)
    (hr : ∀ k ∈ indices, (right k).isFinite = true)
    (hz : ∀ k ∈ indices, value (left k) = 0)
    : ∃ r,
        Flare.Matrix.Substitution.subtractProducts indices left right b = .ok r
        ∧ r.isFinite = true
        ∧ value r = 0 := by
  induction indices generalizing b with
  | nil => exact ⟨b, rfl, hb, hb0⟩
  | cons k indices ih =>
      have hp := Flare.Binary64.Zero.mul_zero _ _ (hl k (by simp)) (hr k (by simp))
        (by rw [hz k (by simp), zero_mul])
      have hs := FloatDiagonalStorage.sub_zero b (left k * right k) hb hp.1 hb0 hp.2
      obtain ⟨r, hrun, hf, h0⟩ := ih (b - left k * right k) hs.1 hs.2
        (fun j hj => hl j (by simp [hj])) (fun j hj => hr j (by simp [hj]))
        (fun j hj => hz j (by simp [hj]))
      have hc : Flare.Matrix.Substitution.subtractProducts (k :: indices) left right b = (do
          let product ← Flare.Matrix.Dense.finite (left k * right k)
          let next ← Flare.Matrix.Dense.finite (b - product)
          Flare.Matrix.Substitution.subtractProducts indices left right next) := by
        simp only [Flare.Matrix.Substitution.subtractProducts, List.forIn_cons]
        cases hp : Flare.Matrix.Dense.finite (left k * right k) with
        | error e => simp [bind, Except.bind]
        | ok product =>
            cases hs : Flare.Matrix.Dense.finite (b - product) <;>
              simp [hs, bind, Except.bind, pure, Except.pure]
      refine ⟨r, ?_, hf, h0⟩
      rw [hc, finite_core _ hp.1]
      change (do
        let next ← Flare.Matrix.Dense.finite (b - left k * right k)
        Flare.Matrix.Substitution.subtractProducts indices left right next) = .ok r
      rw [finite_core _ hs.1]
      exact hrun

private theorem substitution_diagonal (f : Flare.Matrix.Dense.Factor)
    (b y x : Array Float) (lf : f.lower.all Float.isFinite = true)
    (df : f.diagonal.all Float.isFinite = true) (bf : b.all Float.isFinite = true)
    (yf : y.all Float.isFinite = true) (xf : x.all Float.isFinite = true)
    (lz : ∀ i k, i < 2 → k < i → value (entry 2 f.lower i k) = 0)
    (dn : ∀ i, i < 2 → value (f.diagonal.getD i 0.0) ≠ 0)
    (hy : Flare.Matrix.LinearSolve.forward 2 2 f b = .ok y)
    (hx : Flare.Matrix.LinearSolve.backward 2 2 f y = .ok x) (bz : DecodedDiagonal 2 b)
    : DecodedDiagonal 2 x := by
  have getfinite (a : Array Float) (hf : a.all Float.isFinite = true) (i j : Nat)
      : (entry 2 a i j).isFinite = true := Flare.Matrix.Storage.getD_finite a _ hf
  have yz : DecodedDiagonal 2 y := by
    intro i j hi hj hij
    obtain ⟨r, hr, _, hz⟩ := residual_zero (List.range i)
      (fun k => entry 2 f.lower i k) (fun k => entry 2 y k j) (entry 2 b i j)
      (getfinite b bf i j) (bz i j hi hj hij)
      (fun k _ => getfinite f.lower lf i k) (fun k _ => getfinite y yf k j)
      (fun k hk => lz i k hi (List.mem_range.mp hk))
    have he := Flare.Matrix.Substitution.forward_equations 2 2 f b y hy i j hi hj
    rw [hr] at he
    exact (congrArg value (Except.ok.inj he)).symm.trans hz
  intro i j hi hj hij
  have hq := Flare.Binary64.Zero.div_zero (entry 2 y i j) (f.diagonal.getD i 0.0)
    (getfinite y yf i j) (Flare.Matrix.Storage.getD_finite _ _ df) (yz i j hi hj hij) (dn i hi)
  obtain ⟨r, hr, _, hz⟩ := residual_zero (List.range' (i + 1) (2 - (i + 1)))
    (fun k => entry 2 f.lower k i) (fun k => entry 2 x k j)
    (entry 2 y i j / f.diagonal.getD i 0.0) hq.1 hq.2
    (fun k _ => getfinite f.lower lf k i) (fun k _ => getfinite x xf k j)
    (by
      intro k hk
      obtain ⟨t, ht, hkt⟩ := List.mem_range'.mp hk
      exact lz k i (by omega) (by omega))
  have he := Flare.Matrix.Substitution.backward_equations 2 2 f y x hx i j hi hj
  unfold Flare.Matrix.Substitution.divideSubtractProducts at he
  rw [finite_core _ hq.1] at he
  change Flare.Matrix.Substitution.subtractProducts _ _ _ _ = .ok (entry 2 x i j) at he
  rw [hr] at he
  exact (congrArg value (Except.ok.inj he)).symm.trans hz

/-- Sharp forward error of the actual two-pass LDLᵀ solve on diagonal
coefficients in [3/2,5] and finite RHS entries bounded by four. The exact
comparator is the original coefficient matrix, not the rounded factor. -/
theorem solve_accuracy (a b : Array Float)
    (af : a.all Float.isFinite = true) (bf : b.all Float.isFinite = true)
    (az : DecodedDiagonal 2 a)
    (alo : ∀ i, i < 2 → (3 : ℝ) / 2 ≤ value (entry 2 a i i))
    (ahi : ∀ i, i < 2 → value (entry 2 a i i) ≤ 5)
    (bb : ∀ i j, i < 2 → j < 2 → |value (entry 2 b i j)| ≤ 4)
    : ∃ x,
        solveSPD 2 2 a b = .ok x
        ∧ x.size = 4
        ∧ x.all Float.isFinite = true
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-40 : Int)) (matrix 2 2 x)
            ((matrix 2 2 a)⁻¹ * matrix 2 2 b)
        ∧ (DecodedDiagonal 2 b → DecodedDiagonal 2 x) := by
  obtain ⟨l, d, hf, lf, lz, df, dlo, dhi, de⟩ := factor_diagonal a af az alo ahi
  let f : Flare.Matrix.Dense.Factor :=
    ⟨#[1.0, 0.0, l, 1.0], #[entry 2 a 0 0, d]⟩
  have flf : f.lower.all Float.isFinite = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 4 := hi
    interval_cases i
    · change (1.0 : Float).isFinite = true
      decide +kernel
    · change (0.0 : Float).isFinite = true
      decide +kernel
    · exact lf
    · change (1.0 : Float).isFinite = true
      decide +kernel
  have fdf : f.diagonal.all Float.isFinite = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 2 := hi
    interval_cases i
    · exact Flare.Matrix.Storage.getD_finite a _ af
    · exact df
  have lower_zero : ∀ i k, i < 2 → k < i → value (entry 2 f.lower i k) = 0 := by
    intro i k hi hk
    have hi1 : i = 1 := by omega
    have hk0 : k = 0 := by omega
    subst i k
    simpa [f, entry, Flare.Matrix.Dense.entry] using lz
  have lower_bound : ∀ i k, i < 2 → k < i → |value (entry 2 f.lower i k)| ≤ 128 := by
    intro i k hi hk
    rw [lower_zero i k hi hk]
    norm_num
  have diag_lower : ∀ i, i < 2 → 1 ≤ value (f.diagonal.getD i 0.0) := by
    intro i hi
    interval_cases i
    · exact (by norm_num : (1 : ℝ) ≤ 3 / 2).trans (alo 0 (by decide))
    · exact dlo
  have diag_upper : ∀ i, i < 2 → value (f.diagonal.getD i 0.0) ≤ 6 := by
    intro i hi
    interval_cases i
    · exact (ahi 0 (by decide)).trans (by norm_num)
    · exact dhi
  have diag_error : ∀ i, i < 2 →
      |value (entry 2 a i i) - value (f.diagonal.getD i 0.0)| ≤ (2 : ℝ) ^ (-49 : Int) := by
    intro i hi
    interval_cases i
    · change |value (entry 2 a 0 0) - value (entry 2 a 0 0)| ≤ _
      simp
    · change |value (entry 2 a 1 1) - value d| ≤ _
      simpa only [abs_sub_comm] using de
  obtain ⟨y, hy, _, yf, ybig, ye⟩ := Flare.Matrix.Substitution.forward_accuracy
    2 2 2 f b (by decide) (by norm_num) (by norm_num) flf bf lower_bound
    (by intro i j hi hj; exact (bb i j hi hj).trans (by norm_num))
  have eta : (2 : ℝ) ^ (-1022 : Int) ≤ 1 := by
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (-1022 : Int) ≤ 0)
  have yerr : ∀ i j, i < 2 → j < 2 →
      |value (entry 2 y i j) - value (entry 2 b i j)| ≤ (2 : ℝ) ^ (-45 : Int) := by
    intro i j hi hj
    have he := ye i j hi hj
    have hz : ∀ k ∈ Finset.range i, value (entry 2 f.lower i k) = 0 := by
      intro k hk
      exact lower_zero i k hi (Finset.mem_range.mp hk)
    have sums := zero_product_sums _
      (fun k => Flare.Matrix.Dense.entry 2 f.lower i k)
      (fun k => Flare.Matrix.Dense.entry 2 y k j) hz
    rw [sums.1, sums.2, sub_zero, add_zero] at he
    have hmass := bb i j hi hj
    have hip : (i : ℝ) ≤ 1 := by exact_mod_cast (show i ≤ 1 by omega)
    apply he.trans
    calc
      _ ≤ 1 * (2 : ℝ) ^ (-48 : Int) * (4 + 1) := by gcongr
      _ ≤ _ := by norm_num
  have ybound : ∀ i j, i < 2 → j < 2 → |value (entry 2 y i j)| ≤ 5 := by
    intro i j hi hj
    have ht := abs_sub_le (value (entry 2 y i j)) (value (entry 2 b i j)) 0
    simp only [sub_zero] at ht
    have he := yerr i j hi hj
    have hb := bb i j hi hj
    norm_num only at he
    linarith
  obtain ⟨x, hx, xs, xf, _, xe⟩ := Flare.Matrix.Substitution.backward_accuracy
    2 2 2 f y (by decide) (by norm_num) (by norm_num) flf fdf yf lower_bound
    (fun i hi => (by norm_num : (1 : ℝ) / 8 ≤ 1).trans (diag_lower i hi)) ybig
  have xerr : ∀ i j, i < 2 → j < 2 →
      |value (entry 2 x i j)
        - value (entry 2 y i j) / value (f.diagonal.getD i 0.0)|
        ≤ (2 : ℝ) ^ (-43 : Int) := by
    intro i j hi hj
    have he := xe i j hi hj
    have hz : ∀ k ∈ Finset.Ico (i + 1) 2, value (entry 2 f.lower k i) = 0 := by
      intro k hk
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
      exact lower_zero k i hhi (by omega)
    have sums := zero_product_sums _
      (fun k => Flare.Matrix.Dense.entry 2 f.lower k i)
      (fun k => Flare.Matrix.Dense.entry 2 x k j) hz
    rw [sums.1, sums.2, sub_zero, add_zero] at he
    have hq : |value (entry 2 y i j) / value (f.diagonal.getD i 0.0)| ≤ 5 := by
      rw [abs_div, abs_of_pos (by linarith [diag_lower i hi] : (0 : ℝ) < value (f.diagonal.getD i 0.0))]
      apply (div_le_iff₀ (by linarith [diag_lower i hi] : (0 : ℝ) < value (f.diagonal.getD i 0.0))).mpr
      linarith [ybound i j hi hj, diag_lower i hi]
    have hi2 : ((2 - i : Nat) : ℝ) ≤ 2 := by exact_mod_cast (show 2 - i ≤ 2 by omega)
    apply he.trans
    calc
      _ ≤ 2 * (2 : ℝ) ^ (-47 : Int) * (5 + 1) := by gcongr
      _ ≤ _ := by norm_num
  have xb : ∀ i j, i < 2 → j < 2 → |value (entry 2 x i j)| ≤ 6 := by
    intro i j hi hj
    have hq : |value (entry 2 y i j) / value (f.diagonal.getD i 0.0)| ≤ 5 := by
      rw [abs_div, abs_of_pos (by linarith [diag_lower i hi] : (0 : ℝ) < value (f.diagonal.getD i 0.0))]
      apply (div_le_iff₀ (by linarith [diag_lower i hi] : (0 : ℝ) < value (f.diagonal.getD i 0.0))).mpr
      linarith [ybound i j hi hj, diag_lower i hi]
    have ht := abs_sub_le (value (entry 2 x i j))
      (value (entry 2 y i j) / value (f.diagonal.getD i 0.0)) 0
    simp only [sub_zero] at ht
    have he := xerr i j hi hj
    norm_num only at he
    linarith
  have hsolve : Flare.Matrix.Dense.solveSPD 2 2 a b = .ok x := by
    simp only [Flare.Matrix.Dense.solveSPD, hf, bind, Except.bind]
    rw [Flare.Matrix.LinearSolve.solve_split, hy]
    exact hx
  refine ⟨
    x,
    by exact (FloatDenseError.adapt_ok _ x).mpr hsolve,
    xs,
    xf,
    ⟨by positivity, ?_⟩,
    substitution_diagonal f b y x flf fdf bf yf xf lower_zero
      (fun i hi => by linarith [diag_lower i hi]) hy hx
  ⟩
  intro i j
  rw [FloatDiagonalStorage.matrix_diagonal 2 a az,
    RealDiagonalObservation.diagonal_inverse _ (fun i => by
      have h := alo i.val i.isLt
      change value (entry 2 a i.val i.val) ≠ 0
      linarith), Matrix.diagonal_mul]
  change |value (entry 2 x i.val j.val)
    - (value (entry 2 a i.val i.val))⁻¹ * value (entry 2 b i.val j.val)| ≤ _
  rw [mul_comm ((value (entry 2 a i.val i.val))⁻¹), ← div_eq_mul_inv]
  exact quotient_error_from_residual _ _ _ _ _
    ((by norm_num : (1 : ℝ) ≤ 3 / 2).trans (alo i.val i.isLt))
    (diag_lower i.val i.isLt) (diag_upper i.val i.isLt)
    (xb i.val j.val i.isLt j.isLt) (diag_error i.val i.isLt)
    (xerr i.val j.val i.isLt j.isLt) (yerr i.val j.val i.isLt j.isLt)

end Kalman.Proofs.FloatJosephSolve
