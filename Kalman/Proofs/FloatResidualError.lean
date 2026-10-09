import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.FloatDenseError
import Flare.Matrix.Substitution
import Flare.Binary64.Sqrt
import Flare.Binary64.Order

/-! Native residual, final division, and Cholesky square-root bounds.
The subtraction bridge is definitional equality with FLARE's proved schedule.
All bounds compare exact decoding of the same stored operands. -/

namespace Kalman.Proofs.FloatResidualError

open Kalman.Implementation.LinearAlgebra
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.FloatDenseError
open Flare.Binary64.Value

private theorem adapt_bind {α β : Type} (p : Except Flare.Matrix.DenseError α)
    (f : α → Except Flare.Matrix.DenseError β)
    : adapt (p >>= f)
      = (do
          let x ← adapt p; adapt (f x)) := by
  cases p with
  | ok x => rfl
  | error e => cases e <;> rfl

private def residualSchedule (indices : List Nat) (left right : Nat → Float)
    (initial : Float)
    : Except Kalman.Definitions.Input.Error Float := do
  let mut s := initial
  for k in indices do
    let term ← finite (left k * right k)
    s ← finite (s - term)
  return s

/-- Mapping the error type preserves the original native finite checks and
arithmetic order, for every list and every operand, including rejected runs. -/
theorem subtractProducts_schedule (indices : List Nat) (left right : Nat → Float)
    (initial : Float)
    : subtractProducts indices left right initial
      = (do
          let mut s := initial
          for k in indices do
            let term ← finite (left k * right k)
            s ← finite (s - term)
          return s) := by
  change subtractProducts indices left right initial = residualSchedule indices left right initial
  induction indices generalizing initial with
  | nil => rfl
  | cons k ks ih =>
      unfold subtractProducts subtractProductsCore residualSchedule
      simp only [List.forIn_cons, bind_assoc, pure_bind]
      rw [adapt_bind]
      apply congrArg (fun f : Float → Except Kalman.Definitions.Input.Error Float =>
        finite (left k * right k) >>= f)
      funext term
      rw [adapt_bind]
      apply congrArg (fun f : Float → Except Kalman.Definitions.Input.Error Float =>
        finite (initial - term) >>= f)
      funext s
      exact ih s

theorem subtractProducts_bridge (indices : List Nat) (left right : Nat → Float)
    (initial : Float)
    : subtractProducts indices left right initial
      = adapt (Flare.Matrix.Substitution.subtractProducts indices left right initial) :=
  rfl

theorem residual_accuracy (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (M : ℝ) (p : ResidualProfile indices left right initial M)
    : ∃ r,
        subtractProducts indices left right initial = .ok r
        ∧ r.isFinite = true
        ∧ |value r
            - (value initial
                - (indices.map (fun k => value (left k) * value (right k))).sum)|
          ≤ residualRadius indices.length M := by
  obtain ⟨r, hr, hf, he⟩ := Flare.Matrix.Substitution.subtractProducts_accuracy
    indices left right initial M p.length_le p.finite_initial p.finite_left p.finite_right
    p.upper p.mass
  exact ⟨r, by rw [subtractProducts_bridge, hr]; rfl, hf, he⟩

theorem profile_mass_nonneg (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (M : ℝ) (p : ResidualProfile indices left right initial M)
    : 0 ≤ M := by
  have hs : 0 ≤ (indices.map (fun k => |value (left k) * value (right k)|)).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
    exact abs_nonneg _
  have hη : 0 ≤ (2 : ℝ) ^ (-1022 : Int) := by positivity
  linarith [p.mass, abs_nonneg (value initial)]

theorem residualRadius_mono {k n : Nat} (M : ℝ) (hM : 0 ≤ M) (hkn : k ≤ n)
    : residualRadius k M ≤ residualRadius n M := by
  unfold residualRadius
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) (by positivity)) hM

theorem divisionRadius_mono {k n : Nat} (M δ D : ℝ) (hM : 0 ≤ M)
    (hδ : 0 < δ) (hD : 0 ≤ D) (hkn : k ≤ n)
    : divisionRadius k M δ D ≤ divisionRadius n M δ D := by
  have he := residualRadius_mono M hM hkn
  unfold divisionRadius
  exact add_le_add he
    (mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_right (add_le_add (le_refl M) he) hδ.le)
        (le_refl _))
      (by positivity))

theorem divisionRadius_nonneg (k : Nat) (M δ D : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hD : 0 ≤ D)
    : 0 ≤ divisionRadius k M δ D := by
  unfold divisionRadius residualRadius
  positivity

theorem profile_target_bound (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (M : ℝ) (p : ResidualProfile indices left right initial M)
    : |value initial - (indices.map (fun k => value (left k) * value (right k))).sum|
      ≤ M := by
  have hs : |(indices.map (fun k => value (left k) * value (right k))).sum| ≤
      (indices.map (fun k => |value (left k) * value (right k)|)).sum := by
    clear p
    induction indices with
    | nil => simp
    | cons k ks ih =>
        simpa only [List.map_cons, List.sum_cons]
          using (abs_add_le (value (left k) * value (right k)) _).trans
            (add_le_add le_rfl ih)
  have hη : 0 ≤ (2 : ℝ) ^ (-1022 : Int) := by positivity
  exact ((abs_sub _ _).trans (add_le_add le_rfl hs)).trans (by linarith [p.mass])

/-- The row residual after its rounded diagonal division. The quotient domain
is derived from a term-mass budget and a strictly positive diagonal floor. -/
theorem divideResidual_accuracy (indices : List Nat) (left right : Nat → Float)
    (initial diagonal : Float) (M δ D : ℝ)
    (p : ResidualProfile indices left right initial M) (hd : diagonal.isFinite = true)
    (hδ : 0 < δ) (hfloor : δ ≤ value diagonal) (hD : |value diagonal| ≤ D)
    (hquotient : (M + residualRadius indices.length M) / δ ≤ (2 : ℝ) ^ (1000 : Int))
    : ∃ r,
        divideResidual indices left right initial diagonal = .ok r
        ∧ r.isFinite = true
        ∧ |value r * value diagonal
            - (value initial
                - (indices.map (fun k => value (left k) * value (right k))).sum)|
          ≤ divisionRadius indices.length M δ D := by
  obtain ⟨s, hs, hsf, he⟩ := residual_accuracy indices left right initial M p
  have hM := profile_mass_nonneg _ _ _ _ _ p
  have htarget := profile_target_bound _ _ _ _ _ p
  have hε : 0 ≤ residualRadius indices.length M := by unfold residualRadius; positivity
  have hd0 : 0 < value diagonal := hδ.trans_le hfloor
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have hmag : |value s| ≤ M + residualRadius indices.length M := by
    have ht := abs_sub_le (value s)
      (value initial - (indices.map (fun k => value (left k) * value (right k))).sum) 0
    simp only [sub_zero] at ht
    linarith
  have hq : |value s / value diagonal| ≤ (M + residualRadius indices.length M) / δ := by
    rw [abs_div, abs_of_pos hd0]
    exact div_le_div₀ (by positivity) hmag hδ hfloor
  have herr := Flare.Binary64.Division.div_error_relative s diagonal hsf hd hd0.ne'
    (hq.trans hquotient)
  refine ⟨s / diagonal, ?_, herr.1, ?_⟩
  · unfold divideResidual
    rw [hs]
    change finite (s / diagonal) = .ok (s / diagonal)
    exact finite_ok _ herr.1
  have hqerr : |value (s / diagonal) - value s / value diagonal| ≤
      (2 : ℝ) ^ (-50 : Int) *
        ((M + residualRadius indices.length M) / δ + (2 : ℝ) ^ (-1022 : Int)) :=
    herr.2.trans (mul_le_mul_of_nonneg_left
      (add_le_add hq (le_refl _)) (by positivity))
  have hid : value (s / diagonal) * value diagonal -
      (value initial - (indices.map (fun k => value (left k) * value (right k))).sum) =
      (value (s / diagonal) - value s / value diagonal) * value diagonal +
        (value s - (value initial - (indices.map (fun k => value (left k) * value (right k))).sum)) := by
    field_simp
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have hmul := mul_le_mul hqerr hD (abs_nonneg _) (by positivity)
  unfold divisionRadius
  nlinarith

theorem positiveSqrt_accuracy (pivot : Float) (hf : pivot.isFinite = true)
    (hp : 0 < value pivot)
    : positiveSqrt pivot = .ok pivot.sqrt
      ∧ pivot.sqrt.isFinite = true
      ∧ 0 < value pivot.sqrt
      ∧ |(value pivot.sqrt) ^ 2 - value pivot|
        ≤ (2 * (2 : ℝ) ^ (-53 : Int) + ((2 : ℝ) ^ (-53 : Int)) ^ 2) * value pivot := by
  have h := Flare.Binary64.Sqrt.positive_sqrt_squared_error pivot hf hp
  have hg : 0.0 < pivot := (Flare.Binary64.Order.lt_iff _ _ (by decide) hf).mpr
    (by simpa only [Flare.Binary64.Arithmetic.zero_value] using hp)
  have hg' : 0.0 < pivot.sqrt := (Flare.Binary64.Order.lt_iff _ _ (by decide) h.1).mpr
    (by simpa only [Flare.Binary64.Arithmetic.zero_value] using h.2.1)
  refine ⟨?_, h.1, h.2.1, h.2.2⟩
  simp only [positiveSqrt, hg, ↓reduceIte, finite_ok _ h.1]
  change (if 0.0 < pivot.sqrt then Except.ok pivot.sqrt else _) =
    (Except.ok pivot.sqrt : Except Kalman.Definitions.Input.Error Float)
  simp only [hg', ↓reduceIte]

/-- A strict exact residual margin proves that the native pivot checks succeed.
The bound is on the square of the returned diagonal, suitable for a Gram error. -/
theorem choleskyDiagonal_accuracy (indices : List Nat) (left : Nat → Float)
    (initial : Float) (M : ℝ) (p : ResidualProfile indices left left initial M)
    (hmargin
      : residualRadius indices.length M
        < value initial - (indices.map (fun k => value (left k) * value (left k))).sum)
    : ∃ pivot,
        subtractProducts indices left left initial = .ok pivot
        ∧ positiveSqrt pivot = .ok pivot.sqrt
        ∧ pivot.sqrt.isFinite = true
        ∧ 0 < value pivot.sqrt
        ∧ |(value pivot.sqrt) ^ 2
            - (value initial
                - (indices.map (fun k => value (left k) * value (left k))).sum)|
          ≤ diagonalRadius indices.length M := by
  obtain ⟨r, hr, hf, he⟩ := residual_accuracy indices left left initial M p
  have hp : 0 < value r := by have := (abs_le.mp he).1; linarith
  obtain ⟨hs, hsf, hsp, hse⟩ := positiveSqrt_accuracy r hf hp
  refine ⟨r, hr, hs, hsf, hsp, ?_⟩
  have htarget := profile_target_bound _ _ _ _ _ p
  have hmag : value r ≤ M + residualRadius indices.length M := by
    have ht := (abs_le.mp he).2
    have hx := le_abs_self
      (value initial - (indices.map (fun k => value (left k) * value (left k))).sum)
    linarith
  have hm := mul_le_mul_of_nonneg_left hmag
    (by positivity : 0 ≤ 2 * (2 : ℝ)^(-53 : Int) + ((2 : ℝ)^(-53 : Int))^2)
  have htri := abs_sub_le ((value r.sqrt)^2) (value r)
    (value initial - (indices.map (fun k => value (left k) * value (left k))).sum)
  unfold diagonalRadius
  linarith

end Kalman.Proofs.FloatResidualError
