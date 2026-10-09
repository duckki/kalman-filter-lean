import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.FloatCholeskyDomain

/-! Two-state native triangular solves from the stored factor and RHS alone.
The factor's exact Gram and the original covariance remain distinct references. -/

namespace Kalman.Proofs.FloatCholeskySolveDomain

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.CholeskyProfiles.SolveDomain
open Kalman.Proofs.FloatDenseError
open Kalman.Proofs.FloatResidualError
open Flare.Binary64.Value

set_option maxHeartbeats 800000

private theorem denormal_le_one : (2 : ℝ) ^ (-1022 : Int) ≤ 1 := by
  simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (-1022 : Int) ≤ 0)

private theorem mass_upper : (32 : ℝ) ≤ (2 : ℝ) ^ (990 : Int) := by
  simpa only [show (2 : ℝ)^(5 : Int) = 32 by norm_num]
    using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (5 : Int) ≤ 990)

private theorem quotient_bound {k : Nat} (hk : k ≤ 2)
    : (32 + residualRadius k 32) / (1 / 2) ≤ (2 : ℝ) ^ (1000 : Int) := by
  have he := residualRadius_mono 32 (by norm_num) hk
  calc
    _ ≤ (128 : ℝ) := by norm_num [residualRadius] at he ⊢; linarith
    _ ≤ _ := by
      simpa only [show (2 : ℝ)^(7 : Int) = 128 by norm_num]
        using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (7 : Int) ≤ 1000)

/-- A numerical cap for the existing division allowance on this solve domain. -/
theorem division_radius_cap
    : divisionRadius 2 32 (1 / 2) 2 ≤ 25 * (2 : ℝ) ^ (-46 : Int) := by
  have hd : divisionRadius 2 32 (1 / 2) 2 ≤ residualRadius 2 32
      + 2 * (2 : ℝ)^(-50 : Int) * ((32 + residualRadius 2 32) / (1 / 2) + 1) := by
    unfold divisionRadius
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl denormal_le_one) (by norm_num)
  calc
    _ ≤ _ := hd
    _ ≤ _ := by norm_num [residualRadius]

private theorem empty_profile (left right : Nat → Float) (b : Float)
    (hf : b.isFinite = true) (hb : |value b| ≤ 3)
    : ResidualProfile [] left right b 32 := by
  refine ⟨by decide, hf, by simp, by simp, mass_upper, ?_⟩
  simp only [List.map_nil, List.sum_nil, add_zero]
  linarith [denormal_le_one]

private theorem single_profile (k : Nat) (left right : Nat → Float) (b : Float)
    (ha : (left k).isFinite = true) (ht : (right k).isFinite = true)
    (hb : b.isFinite = true) (ham : |value (left k)| ≤ 2) (htm : |value (right k)| ≤ 7)
    (hbm : |value b| ≤ 3)
    : ResidualProfile [k] left right b 32 := by
  refine ⟨by simp, hb, ?_, ?_, mass_upper, ?_⟩
  · intro t ht; simpa only [List.mem_singleton.mp ht] using ha
  · intro t ht'; simpa only [List.mem_singleton.mp ht'] using ht
  ·
    have hprod := mul_le_mul ham htm (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, abs_mul]
    linarith [denormal_le_one]

private theorem divided_row (indices : List Nat) (left right : Nat → Float)
    (b d : Float) (C : ℝ) (p : ResidualProfile indices left right b 32)
    (hk : indices.length ≤ 2) (hd : d.isFinite = true)
    (hdlo : (1 : ℝ) / 2 ≤ value d) (hdhi : |value d| ≤ 2)
    (hmargin
      : |value b - (indices.map (fun k => value (left k) * value (right k))).sum|
          + 25 * (2 : ℝ) ^ (-46 : Int)
        ≤ C / 2)
    : ∃ r,
        divideResidual indices left right b d = .ok r
        ∧ r.isFinite = true
        ∧ |value r| ≤ C := by
  obtain ⟨r, hr, hf, he⟩ := divideResidual_accuracy indices left right b d 32 (1 / 2) 2
    p hd (by norm_num) hdlo hdhi (quotient_bound hk)
  have he' := he.trans ((divisionRadius_mono 32 (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num) hk).trans
    division_radius_cap)
  have hmag := abs_sub_le (value r * value d)
    (value b - (indices.map (fun k => value (left k) * value (right k))).sum) 0
  simp only [sub_zero, abs_mul, abs_of_pos (by linarith : 0 < value d)] at hmag
  have hm := mul_le_mul_of_nonneg_left hdlo (abs_nonneg (value r))
  have hb : |value r| * (1 / 2) ≤ C / 2 := calc
    _ ≤ |value r| * value d := hm
    _ ≤ _ := hmag
    _ ≤ 25 * (2 : ℝ)^(-46 : Int)
        + |value b - (indices.map (fun k => value (left k) * value (right k))).sum| :=
      add_le_add he' le_rfl
    _ ≤ _ := by simpa only [add_comm] using hmargin
  exact ⟨r, hr, hf, by linarith only [hb]⟩

private theorem divideResidual_empty (left right : Nat → Float) (b d : Float)
    : divideResidual [] left right b d = finite (b / d) :=
  rfl

private theorem divideResidual_single (k : Nat) (left right : Nat → Float) (b d : Float)
    : divideResidual [k] left right b d
      = (do
          let product ← finite (left k * right k)
          let residual ← finite (b - product)
          finite (residual / d)) := by
  unfold divideResidual
  rw [subtractProducts_schedule]
  simp [Bind.bind, Except.bind, pure, Except.pure]
  cases finite (left k * right k) with
  | error e => rfl
  | ok product =>
      dsimp only
      cases finite (b - product) <;> rfl

/-- Assemble the actual forward loop from its four ordered row executions. -/
theorem forward_two_of_rows (l b : Array Float) (y00 y01 y10 y11 : Float)
    (h00
      : divideResidual [] (fun _ => 0.0) (fun _ => 0.0) (entry 2 b 0 0) (entry 2 l 0 0)
        = .ok y00)
    (h01
      : divideResidual [] (fun _ => 0.0) (fun _ => 0.0) (entry 2 b 0 1) (entry 2 l 0 0)
        = .ok y01)
    (h10
      : divideResidual [0] (fun _ => entry 2 l 1 0) (fun _ => y00) (entry 2 b 1 0)
          (entry 2 l 1 1)
        = .ok y10)
    (h11
      : divideResidual [0] (fun _ => entry 2 l 1 0) (fun _ => y01) (entry 2 b 1 1)
          (entry 2 l 1 1)
        = .ok y11)
    : forwardCholesky 2 2 l b = .ok #[y00, y01, y10, y11] := by
  simp [divideResidual_empty, divideResidual_single, entry, Flare.Matrix.Dense.entry,
    Array.getD_eq_getD_getElem?, Bind.bind, Except.bind] at h00 h01 h10 h11
  simp [forwardCholesky, Std.Legacy.Range.forIn_eq_forIn_range', List.range', List.range,
    List.range.loop, divideResidual_empty, divideResidual_single,
    entry, Flare.Matrix.Dense.entry, h00, h01, h10, h11, Bind.bind, Except.bind, pure, Except.pure]
  rfl

/-- Assemble the actual backward loop from its four ordered row executions. -/
theorem backward_two_of_rows (l : Array Float) (y00 y01 y10 y11 x00 x01 x10 x11 : Float)
    (h10 : divideResidual [] (fun _ => 0.0) (fun _ => 0.0) y10 (entry 2 l 1 1) = .ok x10)
    (h11 : divideResidual [] (fun _ => 0.0) (fun _ => 0.0) y11 (entry 2 l 1 1) = .ok x11)
    (h00
      : divideResidual [1] (fun _ => entry 2 l 1 0) (fun _ => x10) y00 (entry 2 l 0 0)
        = .ok x00)
    (h01
      : divideResidual [1] (fun _ => entry 2 l 1 0) (fun _ => x11) y01 (entry 2 l 0 0)
        = .ok x01)
    : backwardCholesky 2 2 l #[y00, y01, y10, y11] = .ok #[x00, x01, x10, x11] := by
  simp [divideResidual_empty, divideResidual_single, entry, Flare.Matrix.Dense.entry,
    Array.getD_eq_getD_getElem?, Bind.bind, Except.bind] at h00 h01 h10 h11
  simp [backwardCholesky, Std.Legacy.Range.forIn_eq_forIn_range', List.range',
    divideResidual_empty, divideResidual_single,
    entry, Flare.Matrix.Dense.entry, h00, h01, h10, h11, Bind.bind, Except.bind, pure, Except.pure]
  rfl

theorem factor_lowerPositive (l : Array Float) (p : FactorDomain l)
    : FactorRecursion.LowerPositive (matrix 2 2 l) := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    exact p.upper_zero
  · intro i
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le (p.diagonal_floor i.val i.isLt)

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
        ∧ |value y0| ≤ 1 / 2
        ∧ |value y1| ≤ 3
        ∧ |value x0| ≤ 30
        ∧ |value x1| ≤ 7 := by
  have hlf (i k : Nat) : (entry 2 l i k).isFinite = true :=
    Flare.Matrix.Storage.getD_finite _ _ p.finite
  have hbf (i k : Nat) : (entry 2 b i k).isFinite = true :=
    Flare.Matrix.Storage.getD_finite _ _ q.finite
  have hc := p.entry_bound 1 0 (by decide) (by decide)
  obtain ⟨y0, hy0, hy0f, hy0m⟩ := divided_row [] (fun _ => 0.0) (fun _ => 0.0)
    (entry 2 b 0 j) (entry 2 l 0 0) (1 / 2)
    (empty_profile _ _ _ (hbf 0 j) ((q.entry_bound 0 j (by decide) hj).trans (by norm_num)))
    (by simp) (hlf 0 0) (p.diagonal_floor 0 (by decide)) (p.entry_bound 0 0 (by decide) (by decide)) (by
      simp only [List.map_nil, List.sum_nil, sub_zero]
      calc
        _ ≤ (1 : ℝ) / 8 + 25 * (2 : ℝ)^(-46 : Int) :=
          add_le_add (q.entry_bound 0 j (by decide) hj) le_rfl
        _ ≤ _ := by norm_num)
  obtain ⟨y1, hy1, hy1f, hy1m⟩ := divided_row [0] (fun _ => entry 2 l 1 0) (fun _ => y0)
    (entry 2 b 1 j) (entry 2 l 1 1) 3
    (single_profile 0 _ _ _ (hlf 1 0) hy0f (hbf 1 j) hc (hy0m.trans (by norm_num))
      ((q.entry_bound 1 j (by decide) hj).trans (by norm_num)))
    (by simp) (hlf 1 1) (p.diagonal_floor 1 (by decide)) (p.entry_bound 1 1 (by decide) (by decide)) (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hprod : |value (entry 2 l 1 0) * value y0| ≤ 2 * (1 / 2) := by
        rw [abs_mul]
        exact mul_le_mul hc hy0m (abs_nonneg _) (by norm_num)
      have ht := (abs_sub (value (entry 2 b 1 j)) (value (entry 2 l 1 0) * value y0)).trans
        (add_le_add (q.entry_bound 1 j (by decide) hj) hprod)
      calc
        _ ≤ (1 / 8 + 2 * (1 / 2) : ℝ) + 25 * (2 : ℝ)^(-46 : Int) := add_le_add ht le_rfl
        _ ≤ _ := by norm_num)
  obtain ⟨x1, hx1, hx1f, hx1m⟩ := divided_row [] (fun _ => 0.0) (fun _ => 0.0)
    y1 (entry 2 l 1 1) 7 (empty_profile _ _ _ hy1f hy1m) (by simp) (hlf 1 1)
    (p.diagonal_floor 1 (by decide)) (p.entry_bound 1 1 (by decide) (by decide)) (by
      simp only [List.map_nil, List.sum_nil, sub_zero]
      calc
        _ ≤ 3 + 25 * (2 : ℝ)^(-46 : Int) := add_le_add hy1m le_rfl
        _ ≤ _ := by norm_num)
  obtain ⟨x0, hx0, hx0f, hx0m⟩ := divided_row [1] (fun _ => entry 2 l 1 0) (fun _ => x1)
    y0 (entry 2 l 0 0) 30 (single_profile 1 _ _ _ (hlf 1 0) hx1f hy0f hc hx1m (hy0m.trans (by norm_num)))
    (by simp) (hlf 0 0) (p.diagonal_floor 0 (by decide)) (p.entry_bound 0 0 (by decide) (by decide)) (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hprod : |value (entry 2 l 1 0) * value x1| ≤ 2 * 7 := by
        rw [abs_mul]
        exact mul_le_mul hc hx1m (abs_nonneg _) (by norm_num)
      have ht := (abs_sub (value y0) (value (entry 2 l 1 0) * value x1)).trans
        (add_le_add hy0m hprod)
      calc
        _ ≤ (1 / 2 + 2 * 7 : ℝ) + 25 * (2 : ℝ)^(-46 : Int) := add_le_add ht le_rfl
        _ ≤ _ := by norm_num)
  exact ⟨
    y0,
    y1,
    x0,
    x1,
    hy0,
    hy1,
    hx1,
    hx0,
    hy0f,
    hy1f,
    hx0f,
    hx1f,
    hy0m,
    hy1m,
    hx0m,
    hx1m
  ⟩

/-- Both passes, every finite guard, and all final row profiles are derived
from the stored factor and RHS. The constants match the uniform solve budget. -/
theorem solve_profile (l b : Array Float) (p : FactorDomain l) (q : RightHandSideDomain b)
    : ∃ y x,
        y.size = 4
        ∧ x.size = 4
        ∧ y.all Float.isFinite = true
        ∧ x.all Float.isFinite = true
        ∧ SolveProfile 2 2 l b y x 32 (1 / 2) 2
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 y i j)| ≤ 3)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 x i j)| ≤ 30) := by
  obtain ⟨y00, y10, x00, x10, hy00, hy10, hx10, hx00, fy00, fy10, fx00, fx10, my00, my10, mx00, mx10⟩ := column_success l b p q 0 (by decide)
  obtain ⟨y01, y11, x01, x11, hy01, hy11, hx11, hx01, fy01, fy11, fx01, fx11, my01, my11, mx01, mx11⟩ := column_success l b p q 1 (by decide)
  let y := #[y00, y01, y10, y11]
  let x := #[x00, x01, x10, x11]
  have hyf : y.all Float.isFinite = true := by simp [y, fy00, fy01, fy10, fy11]
  have hxf : x.all Float.isFinite = true := by simp [x, fx00, fx01, fx10, fx11]
  have hym : ∀ i j, i < 2 → j < 2 → |value (entry 2 y i j)| ≤ 3 := by
    intro i j hi hj
    interval_cases i <;> interval_cases j
    · simpa [y, entry, Flare.Matrix.Dense.entry] using my00.trans (by norm_num : (1 : ℝ) / 2 ≤ 3)
    · simpa [y, entry, Flare.Matrix.Dense.entry] using my01.trans (by norm_num : (1 : ℝ) / 2 ≤ 3)
    · simpa [y, entry, Flare.Matrix.Dense.entry] using my10
    · simpa [y, entry, Flare.Matrix.Dense.entry] using my11
  have hxm : ∀ i j, i < 2 → j < 2 → |value (entry 2 x i j)| ≤ 30 := by
    intro i j hi hj
    interval_cases i <;> interval_cases j
    · simpa [x, entry, Flare.Matrix.Dense.entry] using mx00
    · simpa [x, entry, Flare.Matrix.Dense.entry] using mx01
    · simpa [x, entry, Flare.Matrix.Dense.entry] using mx10.trans (by norm_num : (7 : ℝ) ≤ 30)
    · simpa [x, entry, Flare.Matrix.Dense.entry] using mx11.trans (by norm_num : (7 : ℝ) ≤ 30)
  have hlf (i j : Nat) : (entry 2 l i j).isFinite = true := Flare.Matrix.Storage.getD_finite _ _ p.finite
  have hbf (i j : Nat) : (entry 2 b i j).isFinite = true := Flare.Matrix.Storage.getD_finite _ _ q.finite
  have hyfinite (i j : Nat) : (entry 2 y i j).isFinite = true := Flare.Matrix.Storage.getD_finite _ _ hyf
  have hxfinite (i j : Nat) : (entry 2 x i j).isFinite = true := Flare.Matrix.Storage.getD_finite _ _ hxf
  have hforward : forwardCholesky 2 2 l b = .ok y := forward_two_of_rows l b y00 y01 y10 y11 hy00 hy01 hy10 hy11
  have hbackward : backwardCholesky 2 2 l y = .ok x := backward_two_of_rows l y00 y01 y10 y11 x00 x01 x10 x11 hx10 hx11 hx00 hx01
  have hp : SolveProfile 2 2 l b y x 32 (1 / 2) 2 := by
    refine ⟨by decide, hforward, hbackward, p.finite, factor_lowerPositive l p, by norm_num,
      p.diagonal_floor, by norm_num, fun i j => p.entry_bound i.val j.val i.isLt j.isLt,
      quotient_bound (by decide), ?_, ?_⟩
    · intro i j hi hj
      interval_cases i
      · exact empty_profile _ _ _ (hbf 0 j)
          ((q.entry_bound 0 j (by decide) hj).trans (by norm_num))
      · have hy0 : |value (entry 2 y 0 j)| ≤ 7 := (hym 0 j (by decide) hj).trans (by norm_num)
        simpa using single_profile 0 (fun t => entry 2 l 1 t) (fun t => entry 2 y t j) (entry 2 b 1 j)
          (hlf 1 0) (hyfinite 0 j) (hbf 1 j)
          (p.entry_bound 1 0 (by decide) (by decide)) hy0
          ((q.entry_bound 1 j (by decide) hj).trans (by norm_num))
    · intro i j hi hj
      interval_cases i
      · have hx1 : |value (entry 2 x 1 j)| ≤ 7 := by
          interval_cases j
          · simpa [x, entry, Flare.Matrix.Dense.entry] using mx10
          · simpa [x, entry, Flare.Matrix.Dense.entry] using mx11
        simpa [List.range'] using single_profile 1 (fun t => entry 2 l t 0) (fun t => entry 2 x t j)
          (entry 2 y 0 j) (hlf 1 0) (hxfinite 1 j) (hyfinite 0 j)
          (p.entry_bound 1 0 (by decide) (by decide)) hx1 (hym 0 j (by decide) hj)
      · exact empty_profile _ _ _ (hyfinite 1 j) (hym 1 j (by decide) hj)
  exact ⟨y, x, by simp [y], by simp [x], hyf, hxf, hp, hym, hxm⟩

theorem solve_radius_cap
    : 2 * ((1 + 2 * 2) * divisionRadius 2 32 (1 / 2) 2) / (1 / 2)
      ≤ (2 : ℝ) ^ (-37 : Int) := by
  have h := division_radius_cap
  norm_num at h ⊢
  linarith only [h]

/-- Conditioning is a property of the supplied stored factor's exact Gram.
On floor 1/2, both passes succeed, solution error is at most 2^-37, and every
returned solution entry has magnitude at most one. -/
theorem solve_accuracy (l b : Array Float) (p : FactorDomain l)
    (q : RightHandSideDomain b)
    (hfloor : (matrix 2 2 l * (matrix 2 2 l).transpose - (1 / 2 : ℝ) • 1).PosSemidef)
    : ∃ y x,
        y.size = 4
        ∧ x.size = 4
        ∧ y.all Float.isFinite = true
        ∧ x.all Float.isFinite = true
        ∧ SolveProfile 2 2 l b y x 32 (1 / 2) 2
        ∧ solveCholesky 2 2 l b = .ok x
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-37 : Int)) (matrix 2 2 x)
            ((matrix 2 2 l * (matrix 2 2 l).transpose)⁻¹ * matrix 2 2 b)
        ∧ (∀ i j, |matrix 2 2 x i j| ≤ 1) := by
  obtain ⟨y, x, hys, hxs, hyf, hxf, hp, _, _⟩ := solve_profile l b p q
  obtain ⟨hrun, he⟩ := FloatCholeskySolve.solve_accuracy 2 2 l b y x 32 (1 / 2) 2 (1 / 2)
    hp (by norm_num) (by norm_num) hfloor
  have he' : EntrywiseWithin ((2 : ℝ)^(-37 : Int)) (matrix 2 2 x)
      ((matrix 2 2 l * (matrix 2 2 l).transpose)⁻¹ * matrix 2 2 b) :=
    ⟨by positivity, fun i j => (he.2 i j).trans solve_radius_cap⟩
  have hinv := Flare.Analysis.NumericalBounds.inverse_entry_bound
    (matrix 2 2 l * (matrix 2 2 l).transpose) (1 / 2) (by norm_num) hfloor
  have htarget := ErrorPropagation.product_magnitude
    (matrix 2 2 l * (matrix 2 2 l).transpose)⁻¹ (matrix 2 2 b) 2 (1 / 8)
    (by simpa using hinv) (fun i j => q.entry_bound i.val j.val i.isLt j.isLt)
  refine ⟨y, x, hys, hxs, hyf, hxf, hp, hrun, he', ?_⟩
  intro i j
  have ht := htarget i j
  have herr := he'.2 i j
  have hmag := abs_sub_le (matrix 2 2 x i j)
    (((matrix 2 2 l * (matrix 2 2 l).transpose)⁻¹ * matrix 2 2 b) i j) 0
  simp only [sub_zero] at hmag
  norm_num at ht herr
  linarith only [ht, herr, hmag]

/-- The preceding original-covariance Cholesky domain supplies this solve's
factor conditions, including signed-zero upper storage. -/
theorem factor_domain_of_cholesky (a l : Array Float)
    (p : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain a)
    (hrun : cholesky 2 a = .ok l)
    : FactorDomain l := by
  obtain ⟨l', hls, hp, hlp, _, hc⟩ := FloatCholeskyDomain.cholesky_profile a p
  have heq : l' = l := Except.ok.inj (hp.execution.symm.trans hrun)
  subst l'
  refine ⟨hls, hp.finite_lower, hlp.1 0 1 (by decide), hp.diagonal_floor, ?_⟩
  intro i j hi hj
  interval_cases i <;> interval_cases j
  · exact hp.diagonal_bound 0 (by decide)
  · rw [show value (entry 2 l 0 1) = 0 from hlp.1 0 1 (by decide)]
    norm_num
  · exact hc.trans (by norm_num)
  · exact hp.diagonal_bound 1 (by decide)

theorem original_solve_radius_cap
    : 2
        * ((1 + 2 * 2) * divisionRadius 2 32 (1 / 2) 2 + 2 * (2 : ℝ) ^ (-42 : Int))
        / (3 / 4)
      ≤ (2 : ℝ) ^ (-37 : Int) := by
  have h := division_radius_cap
  norm_num at h ⊢
  linarith only [h]

/-- Original-input Cholesky followed by the native two-pass solve. Both runs
and all operand profiles are conclusions. The reference is A^-1 B for the
original decoded covariance A, so factorization error is included. -/
theorem factor_and_solve_accuracy (a b : Array Float)
    (p : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain a)
    (q : RightHandSideDomain b)
    : ∃ l x,
        cholesky 2 a = .ok l
        ∧ solveCholesky 2 2 l b = .ok x
        ∧ x.size = 4
        ∧ x.all Float.isFinite = true
        ∧ (matrix 2 2 a).PosDef
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-37 : Int)) (matrix 2 2 x)
            ((matrix 2 2 a)⁻¹ * matrix 2 2 b)
        ∧ (∀ i j, |matrix 2 2 x i j| ≤ 1) := by
  obtain ⟨l, _, hl, _, _, hpd, _, hfloor, he⟩ := FloatCholeskyDomain.cholesky_accuracy a p
  obtain ⟨y, x, _, hxs, _, hxf, hp, hx, _, hm⟩ :=
    solve_accuracy l b (factor_domain_of_cholesky a l p hl) q hfloor
  obtain ⟨_, _, hres⟩ := FloatCholeskySolve.solve_residual 2 2 l b y x 32 (1 / 2) 2 hp (by norm_num)
  have hperturb := ErrorPropagation.within_mul_right (ErrorPropagation.within_sym he)
    (matrix 2 2 x) (by norm_num : (0 : ℝ) ≤ 1) hm
  let ρ := (1 + 2 * 2) * divisionRadius 2 32 (1 / 2) 2 + 2 * (2 : ℝ)^(-42 : Int)
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    have hd := divisionRadius_nonneg 2 32 (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num)
    positivity
  have href : ∀ i j, |(matrix 2 2 a * matrix 2 2 x - matrix 2 2 b) i j| ≤ ρ := by
    intro i j
    have ht := abs_sub_le ((matrix 2 2 a * matrix 2 2 x) i j)
      (((matrix 2 2 l * (matrix 2 2 l).transpose) * matrix 2 2 x) i j)
      (matrix 2 2 b i j)
    have hg := hres i j
    have hd := hperturb.2 i j
    change |(matrix 2 2 l * (matrix 2 2 l).transpose * matrix 2 2 x) i j - matrix 2 2 b i j| ≤ _ at hg
    change |(matrix 2 2 a * matrix 2 2 x) i j - matrix 2 2 b i j| ≤ _
    dsimp [ρ]
    simpa only [Nat.cast_ofNat, mul_one, add_comm] using ht.trans (add_le_add hd hg)
  have hid : matrix 2 2 a * (matrix 2 2 a)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hpd.isUnit)
  refine ⟨l, x, hl, hx, hxs, hxf, hpd, ⟨by positivity, ?_⟩, hm⟩
  intro i j
  have hexact : (matrix 2 2 a).mulVec (fun k => ((matrix 2 2 a)⁻¹ * matrix 2 2 b) k j)
      = fun k => matrix 2 2 b k j := by
    have hex : matrix 2 2 a * ((matrix 2 2 a)⁻¹ * matrix 2 2 b) = matrix 2 2 b := by
      rw [← Matrix.mul_assoc, hid, Matrix.one_mul]
    ext k
    exact congr_fun (congr_fun hex k) j
  have herr := Flare.Analysis.NumericalBounds.residual_entrywise_bound (matrix 2 2 a)
    (3 / 4) ρ (by norm_num) hρ (FloatCholeskyDomain.input_lower_bound a p)
    (fun k => matrix 2 2 x k j) (fun k => ((matrix 2 2 a)⁻¹ * matrix 2 2 b) k j)
    (fun k => matrix 2 2 b k j) hexact (fun k => href k j) i
  exact herr.trans original_solve_radius_cap

/-- Nonzero RHS columns at both signs of the admitted magnitude boundary. -/
theorem rightHandSide_domain_nonempty
    : RightHandSideDomain #[0.125, -0.125, -0.125, 0.125] := by
  have hp : value (0.125 : Float) = (1 : ℝ) / 8 := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-55 : Int) = _
    norm_num
  have hn : value (-0.125 : Float) = -(1 : ℝ) / 8 := by
    rw [(Flare.Binary64.Order.neg_value (0.125 : Float) (by decide +kernel)).2]
    rw [hp]
    ring
  refine ⟨by decide, by decide +kernel, ?_⟩
  intro i j hi hj
  interval_cases i <;> interval_cases j <;> norm_num [entry, Flare.Matrix.Dense.entry, hp, hn]

end Kalman.Proofs.FloatCholeskySolveDomain
