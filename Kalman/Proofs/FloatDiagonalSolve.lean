import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.FloatCholeskySolveDomain
import Kalman.Proofs.FloatDiagonalStorage

/-! Both actual native substitution passes on a finite diagonal two-state
factor. Larger RHS entries are admitted because residual cross-products vanish.
The numerical reference is the exact Gram of the supplied stored factor. -/

namespace Kalman.Proofs.FloatDiagonalSolve

open Matrix
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.CholeskyProfiles.DiagonalSolve
open Kalman.Proofs.FloatDenseError
open Kalman.Proofs.FloatResidualError
open Flare.Binary64.Value

set_option maxHeartbeats 800000

private theorem denormal_le_one : (2 : ℝ) ^ (-1022 : Int) ≤ 1 := by
  simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)

private theorem mass_upper : (16 : ℝ) ≤ (2 : ℝ) ^ (990 : Int) := by
  simpa only [show (2 : ℝ)^(4 : Int) = 16 by norm_num]
    using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (4 : Int) ≤ 990)

private theorem quotient_bound {k : Nat} (hk : k ≤ 2)
    : (16 + residualRadius k 16) / 1 ≤ (2 : ℝ) ^ (1000 : Int) := by
  have he := residualRadius_mono 16 (by norm_num) hk
  apply le_trans (b := 32)
  · norm_num [residualRadius] at he ⊢
    linarith
  · simpa only [show (2 : ℝ)^(5 : Int) = 32 by norm_num]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (5 : Int) ≤ 1000)

theorem division_radius_cap
    : divisionRadius 2 16 1 (9 / 4) ≤ 11 * (2 : ℝ) ^ (-46 : Int) := by
  have h : divisionRadius 2 16 1 (9 / 4) ≤ residualRadius 2 16
      + (9 / 4) * (2 : ℝ)^(-50 : Int) * (16 + residualRadius 2 16 + 1) := by
    unfold divisionRadius
    norm_num only [div_one]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl denormal_le_one) (by positivity))
  exact h.trans (by norm_num [residualRadius])

private theorem empty_profile (left right : Nat → Float) (b : Float)
    (hf : b.isFinite = true) (hb : |value b| ≤ 5)
    : ResidualProfile [] left right b 16 := by
  refine ⟨by decide, hf, by simp, by simp, mass_upper, ?_⟩
  simp only [List.map_nil, List.sum_nil, add_zero]
  linarith [denormal_le_one]

private theorem single_profile (k : Nat) (left right : Nat → Float) (b : Float)
    (ha : (left k).isFinite = true) (ht : (right k).isFinite = true)
    (hf : b.isFinite = true) (hz : value (left k) = 0) (hb : |value b| ≤ 5)
    : ResidualProfile [k] left right b 16 := by
  refine ⟨by simp, hf, by simpa using ha, by simpa using ht, mass_upper, ?_⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hz, zero_mul,
    abs_zero, add_zero]
  linarith [denormal_le_one]

private theorem divided_row (indices : List Nat) (left right : Nat → Float) (b d : Float)
    (C : ℝ) (p : ResidualProfile indices left right b 16) (hk : indices.length ≤ 2)
    (hd : d.isFinite = true) (hdlo : 1 ≤ value d) (hdhi : |value d| ≤ 9 / 4)
    (hzero : ∀ k ∈ indices, value (left k) = 0)
    (hmargin : |value b| + 11 * (2 : ℝ) ^ (-46 : Int) ≤ C)
    : ∃ r,
        divideResidual indices left right b d = .ok r
        ∧ r.isFinite = true
        ∧ |value r| ≤ C := by
  obtain ⟨r, hr, hf, he⟩ := divideResidual_accuracy indices left right b d 16 1 (9 / 4)
    p hd (by norm_num) hdlo hdhi (quotient_bound hk)
  have he' := he.trans ((divisionRadius_mono 16 1 (9 / 4)
    (by norm_num) (by norm_num) (by norm_num) hk).trans division_radius_cap)
  have hz : (indices.map (fun k => value (left k) * value (right k))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    rw [hzero k hk, zero_mul]
  rw [hz, sub_zero] at he'
  have hm := abs_sub_le (value r * value d) (value b) 0
  simp only [sub_zero, abs_mul, abs_of_pos (by linarith : 0 < value d)] at hm
  have hlo := mul_le_mul_of_nonneg_left hdlo (abs_nonneg (value r))
  simp only [mul_one] at hlo
  exact ⟨r, hr, hf, by linarith⟩

theorem factor_lowerPositive (l : Array Float) (p : FactorDomain l)
    : FactorRecursion.LowerPositive (matrix 2 2 l) := by
  refine ⟨
    ?_,
    fun i => (by norm_num : (0 : ℝ) < 1).trans_le (p.diagonal_floor i.val i.isLt)
  ⟩
  intro i j hij
  exact p.diagonal i.val j.val i.isLt j.isLt (by omega)

theorem factor_gram_floor (l : Array Float) (p : FactorDomain l)
    : (FactorRecursion.gram (matrix 2 2 l) - (1 : ℝ) • 1).PosSemidef := by
  rw [FloatDiagonalStorage.gram_diagonal 2 l p.diagonal, smul_one_eq_diagonal, diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  change 0 ≤ (value (entry 2 l i.val i.val))^2 - 1
  nlinarith [p.diagonal_floor i.val i.isLt]

private theorem column_success (l b : Array Float) (p : FactorDomain l)
    (q : RightHandSideDomain b) (j : Nat) (hj : j < 2)
    : ∃ y0 y1 x0 x1,
        divideResidual [] (fun _ => 0.0) (fun _ => 0.0) (entry 2 b 0 j) (entry 2 l 0 0)
          = .ok y0
        ∧ divideResidual [0] (fun _ => entry 2 l 1 0) (fun _ => y0) (entry 2 b 1 j)
            (entry 2 l 1 1)
          = .ok y1
        ∧ divideResidual [] (fun _ => 0.0) (fun _ => 0.0) y1 (entry 2 l 1 1) = .ok x1
        ∧ divideResidual [1] (fun _ => entry 2 l 1 0) (fun _ => x1) y0 (entry 2 l 0 0)
          = .ok x0
        ∧ y0.isFinite = true
        ∧ y1.isFinite = true
        ∧ x0.isFinite = true
        ∧ x1.isFinite = true
        ∧ |value y0| ≤ 5
        ∧ |value y1| ≤ 5
        ∧ |value x0| ≤ 6
        ∧ |value x1| ≤ 6 := by
  have hlf (i k : Nat) := Flare.Matrix.Storage.getD_finite l (i * 2 + k) p.finite
  have hbf (i k : Nat) := Flare.Matrix.Storage.getD_finite b (i * 2 + k) q.finite
  have hc := p.diagonal 1 0 (by decide) (by decide) (by decide)
  obtain ⟨y0, hy0, fy0, my0⟩ := divided_row [] (fun _ => 0.0) (fun _ => 0.0)
    (entry 2 b 0 j) (entry 2 l 0 0) 5
    (empty_profile _ _ _ (hbf 0 j) ((q.entry_bound 0 j (by decide) hj).trans (by norm_num)))
    (by simp) (hlf 0 0) (p.diagonal_floor 0 (by decide))
    (p.entry_bound 0 0 (by decide) (by decide)) (by simp) (by
      have hb := q.entry_bound 0 j (by decide) hj
      norm_num at ⊢
      linarith)
  obtain ⟨y1, hy1, fy1, my1⟩ := divided_row [0] (fun _ => entry 2 l 1 0) (fun _ => y0)
    (entry 2 b 1 j) (entry 2 l 1 1) 5
    (single_profile 0 _ _ _ (hlf 1 0) fy0 (hbf 1 j) hc
      ((q.entry_bound 1 j (by decide) hj).trans (by norm_num)))
    (by simp) (hlf 1 1) (p.diagonal_floor 1 (by decide))
    (p.entry_bound 1 1 (by decide) (by decide)) (by simpa using hc) (by
      have hb := q.entry_bound 1 j (by decide) hj
      norm_num at ⊢
      linarith)
  obtain ⟨x1, hx1, fx1, mx1⟩ := divided_row [] (fun _ => 0.0) (fun _ => 0.0)
    y1 (entry 2 l 1 1) 6 (empty_profile _ _ _ fy1 my1) (by simp)
    (hlf 1 1) (p.diagonal_floor 1 (by decide)) (p.entry_bound 1 1 (by decide) (by decide))
    (by simp) (by norm_num at ⊢; linarith)
  obtain ⟨x0, hx0, fx0, mx0⟩ := divided_row [1] (fun _ => entry 2 l 1 0) (fun _ => x1)
    y0 (entry 2 l 0 0) 6 (single_profile 1 _ _ _ (hlf 1 0) fx1 fy0 hc my0) (by simp)
    (hlf 0 0) (p.diagonal_floor 0 (by decide)) (p.entry_bound 0 0 (by decide) (by decide))
    (by simpa using hc) (by norm_num at ⊢; linarith)
  exact ⟨y0, y1, x0, x1, hy0, hy1, hx1, hx0, fy0, fy1, fx0, fx1, my0, my1, mx0, mx1⟩

/-- Both passes and all residual profiles are derived with mass 16, diagonal
floor 1 and factor cap 9/4. The RHS cap is four, including correlated RHSs. -/
theorem solve_profile (l b : Array Float) (p : FactorDomain l) (q : RightHandSideDomain b)
    : ∃ y x,
        y.size = 4
        ∧ x.size = 4
        ∧ y.all Float.isFinite = true
        ∧ x.all Float.isFinite = true
        ∧ SolveProfile 2 2 l b y x 16 1 (9 / 4)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 y i j)| ≤ 5)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 x i j)| ≤ 6) := by
  obtain ⟨y00, y10, x00, x10, hy00, hy10, hx10, hx00, fy00, fy10, fx00, fx10,
    my00, my10, mx00, mx10⟩ := column_success l b p q 0 (by decide)
  obtain ⟨y01, y11, x01, x11, hy01, hy11, hx11, hx01, fy01, fy11, fx01, fx11,
    my01, my11, mx01, mx11⟩ := column_success l b p q 1 (by decide)
  let y := #[y00, y01, y10, y11]
  let x := #[x00, x01, x10, x11]
  have hyf : y.all Float.isFinite = true := by simp [y, fy00, fy01, fy10, fy11]
  have hxf : x.all Float.isFinite = true := by simp [x, fx00, fx01, fx10, fx11]
  have hym : ∀ i j, i < 2 → j < 2 → |value (entry 2 y i j)| ≤ 5 := by
    intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      simpa [y, entry, Flare.Matrix.Dense.entry] using (by assumption : _)
  have hxm : ∀ i j, i < 2 → j < 2 → |value (entry 2 x i j)| ≤ 6 := by
    intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      simpa [x, entry, Flare.Matrix.Dense.entry] using (by assumption : _)
  have hforward := FloatCholeskySolveDomain.forward_two_of_rows l b
    y00 y01 y10 y11 hy00 hy01 hy10 hy11
  have hbackward := FloatCholeskySolveDomain.backward_two_of_rows l
    y00 y01 y10 y11 x00 x01 x10 x11 hx10 hx11 hx00 hx01
  have hlf (i j : Nat) := Flare.Matrix.Storage.getD_finite l (i * 2 + j) p.finite
  have hbf (i j : Nat) := Flare.Matrix.Storage.getD_finite b (i * 2 + j) q.finite
  have hyfinite (i j : Nat) := Flare.Matrix.Storage.getD_finite y (i * 2 + j) hyf
  have hxfinite (i j : Nat) := Flare.Matrix.Storage.getD_finite x (i * 2 + j) hxf
  have hc := p.diagonal 1 0 (by decide) (by decide) (by decide)
  refine ⟨y, x, by simp [y], by simp [x], hyf, hxf, ?_, hym, hxm⟩
  refine ⟨
    by decide,
    hforward,
    hbackward,
    p.finite,
    factor_lowerPositive l p,
    by norm_num,
    p.diagonal_floor,
    by norm_num,
    fun i j => p.entry_bound i.val j.val i.isLt j.isLt,
    quotient_bound (by decide),
    ?_,
    ?_
  ⟩
  · intro i j hi hj
    interval_cases i
    · exact empty_profile _ _ _ (hbf 0 j) ((q.entry_bound 0 j (by decide) hj).trans (by norm_num))
    · simpa using single_profile 0 (fun k => entry 2 l 1 k) (fun k => entry 2 y k j)
        (entry 2 b 1 j) (hlf 1 0) (hyfinite 0 j) (hbf 1 j) hc
        ((q.entry_bound 1 j (by decide) hj).trans (by norm_num))
  · intro i j hi hj
    interval_cases i
    · simpa [List.range'] using single_profile 1 (fun k => entry 2 l k 0)
        (fun k => entry 2 x k j) (entry 2 y 0 j) (hlf 1 0) (hxfinite 1 j) (hyfinite 0 j) hc
        (hym 0 j (by decide) hj)
    · exact empty_profile _ _ _ (hyfinite 1 j) (hym 1 j (by decide) hj)

theorem solve_radius_cap
    : 2 * ((1 + 2 * (9 / 4)) * divisionRadius 2 16 1 (9 / 4)) / 1
      ≤ (2 : ℝ) ^ (-39 : Int) := by
  have h := division_radius_cap
  norm_num at h ⊢
  linarith

/-- Larger diagonal factors and RHSs give successful native solves and an
absolute entrywise error ≤2^-39 against the supplied factor's exact Gram. -/
theorem solve_accuracy (l b : Array Float) (p : FactorDomain l)
    (q : RightHandSideDomain b)
    : ∃ y x,
        y.size = 4
        ∧ x.size = 4
        ∧ y.all Float.isFinite = true
        ∧ x.all Float.isFinite = true
        ∧ SolveProfile 2 2 l b y x 16 1 (9 / 4)
        ∧ solveCholesky 2 2 l b = .ok x
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-39 : Int)) (matrix 2 2 x)
            ((FactorRecursion.gram (matrix 2 2 l))⁻¹ * matrix 2 2 b)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 x i j)| ≤ 6) := by
  obtain ⟨y, x, hys, hxs, hyf, hxf, hp, _, hm⟩ := solve_profile l b p q
  obtain ⟨hr, he⟩ := FloatCholeskySolve.solve_accuracy 2 2 l b y x 16 1 (9 / 4) 1
    hp (by norm_num) (by norm_num) (factor_gram_floor l p)
  exact ⟨
    y,
    x,
    hys,
    hxs,
    hyf,
    hxf,
    hp,
    hr,
    ⟨by positivity, fun i j => (he.2 i j).trans solve_radius_cap⟩,
    hm
  ⟩

private theorem subtract_zero_words (a b : Float) (ha : a.isFinite = true)
    (hb : b.isFinite = true) (ha0 : value a = 0) (hb0 : value b = 0)
    : (a - b).isFinite = true ∧ value (a - b) = 0 := by
  have hf := Flare.Binary64.Nearest.sub_error_nearest a b ha hb (by rw [ha0, hb0]; simp)
  refine ⟨hf.1, ?_⟩
  obtain ⟨sa, hsa⟩ := Flare.Binary64.Zero.unpack_zero a ha ha0
  obtain ⟨sb, hsb⟩ := Flare.Binary64.Zero.unpack_zero b hb hb0
  change (Flare.Binary64.Value.modelToReal (Float.Model.pack
    (Float.Model.UnpackedFloat.sub Float.Model.Format.binary64
      a.toModel.unpack b.toModel.unpack))).getD 0 = 0
  rw [hsa, hsb]
  cases sa <;> cases sb <;> rfl

private theorem residual_zero (indices : List Nat) (left right : Nat → Float) (b : Float)
    (hb : b.isFinite = true) (hb0 : value b = 0)
    (hl : ∀ k ∈ indices, (left k).isFinite = true)
    (hr : ∀ k ∈ indices, (right k).isFinite = true)
    (hz : ∀ k ∈ indices, value (left k) * value (right k) = 0)
    : ∃ r,
        subtractProducts indices left right b = .ok r
        ∧ r.isFinite = true
        ∧ value r = 0 := by
  induction indices generalizing b with
  | nil => exact ⟨b, rfl, hb, hb0⟩
  | cons k indices ih =>
      have hp := Flare.Binary64.Zero.mul_zero _ _ (hl k (by simp)) (hr k (by simp)) (hz k (by simp))
      have hs := subtract_zero_words b (left k * right k) hb hp.1 hb0 hp.2
      obtain ⟨r, hrun, hf, h0⟩ := ih (b - left k * right k) hs.1 hs.2
        (fun j hj => hl j (by simp [hj])) (fun j hj => hr j (by simp [hj]))
        (fun j hj => hz j (by simp [hj]))
      have hc : subtractProducts (k :: indices) left right b = (do
          let product ← finite (left k * right k)
          let next ← finite (b - product)
          subtractProducts indices left right next) := by
        simp only [subtractProducts_schedule, List.forIn_cons]
        cases hp : finite (left k * right k) with
        | error e => simp [bind, Except.bind]
        | ok product =>
            cases hs : finite (b - product) <;>
              simp [hs, bind, Except.bind, pure, Except.pure]
      refine ⟨r, ?_, hf, h0⟩
      rw [hc, finite_ok (left k * right k) hp.1]
      change (do
        let next ← finite (b - left k * right k)
        subtractProducts indices left right next) = .ok r
      rw [finite_ok _ hs.1]
      exact hrun

private theorem divide_zero (indices : List Nat) (left right : Nat → Float)
    (b d x : Float) (hb : b.isFinite = true) (hb0 : value b = 0) (hd : d.isFinite = true)
    (hd0 : value d ≠ 0) (hl : ∀ k ∈ indices, (left k).isFinite = true)
    (hr : ∀ k ∈ indices, (right k).isFinite = true)
    (hz : ∀ k ∈ indices, value (left k) * value (right k) = 0)
    (hx : divideResidual indices left right b d = .ok x)
    : value x = 0 := by
  obtain ⟨r, hrun, hf, h0⟩ := residual_zero indices left right b hb hb0 hl hr hz
  have hq := Flare.Binary64.Zero.div_zero r d hf hd h0 hd0
  unfold divideResidual at hx
  rw [hrun] at hx
  change finite (r / d) = .ok x at hx
  rw [finite_ok _ hq.1] at hx
  exact (Except.ok.inj hx) ▸ hq.2

/-- A diagonal RHS gives an exactly decoded diagonal solution through the
actual two-pass schedule, including either signed-zero encoding. -/
theorem solve_diagonal (l b y x : Array Float) (p : FactorDomain l)
    (q : RightHandSideDomain b)
    (db : Kalman.Implementation.Correctness.InputInterpretation.DecodedDiagonal 2 b)
    (hyf : y.all Float.isFinite = true) (hxf : x.all Float.isFinite = true)
    (profile : SolveProfile 2 2 l b y x 16 1 (9 / 4))
    : Kalman.Implementation.Correctness.InputInterpretation.DecodedDiagonal 2 x := by
  have hlf (i j : Nat) := Flare.Matrix.Storage.getD_finite l (i * 2 + j) p.finite
  have hbf (i j : Nat) := Flare.Matrix.Storage.getD_finite b (i * 2 + j) q.finite
  have hyfinite (i j : Nat) := Flare.Matrix.Storage.getD_finite y (i * 2 + j) hyf
  have hxfinite (i j : Nat) := Flare.Matrix.Storage.getD_finite x (i * 2 + j) hxf
  have hn (i : Nat) (hi : i < 2) : value (entry 2 l i i) ≠ 0 := by
    have h := p.diagonal_floor i hi
    linarith
  have hfw := FloatCholeskySolve.forward_equations 2 2 l b y profile.forward
  have hbw := FloatCholeskySolve.backward_equations 2 2 l y x profile.backward
  have hy01 : value (entry 2 y 0 1) = 0 := divide_zero [] _ _ _ _ _ (hbf 0 1)
    (db 0 1 (by decide) (by decide) (by decide)) (hlf 0 0) (hn 0 (by decide))
    (by simp) (by simp) (by simp) (hfw.2 0 1 (by decide) (by decide))
  have hy10 : value (entry 2 y 1 0) = 0 := divide_zero [0] _ _ _ _ _ (hbf 1 0)
    (db 1 0 (by decide) (by decide) (by decide)) (hlf 1 1) (hn 1 (by decide))
    (by intro k hk; have he := List.mem_singleton.mp hk; subst k; exact hlf 1 0)
    (by intro k hk; have he := List.mem_singleton.mp hk; subst k; exact hyfinite 0 0)
    (by simp [p.diagonal 1 0 (by decide) (by decide) (by decide)])
    (hfw.2 1 0 (by decide) (by decide))
  have hx10 : value (entry 2 x 1 0) = 0 := divide_zero [] _ _ _ _ _ (hyfinite 1 0)
    hy10 (hlf 1 1) (hn 1 (by decide)) (by simp) (by simp) (by simp)
    (hbw.2 1 0 (by decide) (by decide))
  have hx01 : value (entry 2 x 0 1) = 0 := divide_zero [1] _ _ _ _ _ (hyfinite 0 1)
    hy01 (hlf 0 0) (hn 0 (by decide))
    (by intro k hk; have he := List.mem_singleton.mp hk; subst k; exact hlf 1 0)
    (by intro k hk; have he := List.mem_singleton.mp hk; subst k; exact hxfinite 1 1)
    (by simp [p.diagonal 1 0 (by decide) (by decide) (by decide)])
    (hbw.2 0 1 (by decide) (by decide))
  intro i j hi hj hij
  interval_cases i <;> interval_cases j <;> simp_all

end Kalman.Proofs.FloatDiagonalSolve
