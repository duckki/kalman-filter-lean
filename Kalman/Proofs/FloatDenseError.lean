import Kalman.Implementation.LinearAlgebra
import Kalman.Implementation.Correctness.InputInterpretation
import Flare.Matrix.Multiplication
import Flare.Binary64.Nearest

/-! Forward error for the native kernels actually used by the filter.
The dot-product bound includes gradual underflow and establishes finite
successful execution. It is relative to the stored operands, not an ideal
Kalman trajectory; composed comparisons require propagation of upstream error. -/

namespace Kalman.Proofs.FloatDenseError

open Kalman.Definitions.Input
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Flare.Binary64.Value

theorem adapt_ok {α : Type} (p : Except Flare.Matrix.DenseError α) (r : α)
    : adapt p = .ok r ↔ p = .ok r := by
  cases p with
  | ok a => simp [adapt]
  | error e => cases e <;> simp [adapt]

theorem operations_multiply_ok (rows inner columns : Nat) (a b r : Array Float)
    (h : Flare.Matrix.Operations.multiply rows inner columns a b = .ok r)
    : multiply rows inner columns a b = .ok r := by
  unfold Flare.Matrix.Operations.multiply at h
  cases he : Flare.Matrix.Dense.multiply rows inner columns a b with
  | error e => cases e <;> simp [he, Flare.Matrix.Operations.adapt] at h
  | ok result =>
      have hh : result = r := by simpa [he, Flare.Matrix.Operations.adapt] using h
      simp [multiply, he, hh, adapt]

/-- Absolute mass can differ for every output entry. Constants are those of
FLARE's separately rounded, ascending dot-product loop (at most 32 terms). -/
theorem multiply_entrywise_accuracy (rows inner columns : Nat) (a b : Array Float)
    (M : Nat → Nat → ℝ) (hinner : inner ≤ 32) (ha : a.all Float.isFinite = true)
    (hb : b.all Float.isFinite = true)
    (hM : ∀ i j, i < rows → j < columns → M i j ≤ (2 : ℝ) ^ (990 : Int))
    (hη : ∀ i j, i < rows → j < columns → (2 : ℝ) ^ (-1022 : Int) ≤ M i j)
    (hmass
      : ∀ i j,
          i < rows
          → j < columns
          → (∑ k ∈ Finset.range inner,
              |value (entry inner a i k) * value (entry columns b k j)|)
            ≤ M i j)
    : ∃ r,
        multiply rows inner columns a b = .ok r
        ∧ r.size = rows * columns
        ∧ r.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix rows columns r i j
              - (matrix rows inner a * matrix inner columns b) i j|
            ≤ inner * (2 : ℝ) ^ (-50 : Int) * M i.val j.val := by
  obtain ⟨r, hr, hs, hf, he⟩ := Flare.Matrix.Multiplication.multiply_entrywise_accuracy
    rows inner columns a b M hinner ha hb hM hη hmass
  exact ⟨r, operations_multiply_ok _ _ _ _ _ _ hr, hs, hf, he⟩

theorem finite_ok (x : Float) (h : x.isFinite = true) : finite x = .ok x := by
  simp [finite, Flare.Matrix.Dense.finite, h, adapt]

/-- Actual native subtraction, including cancellation; its bound is absolute.
The magnitude premise is on the exact difference of stored finite operands. -/
theorem sub_accuracy (a b : Array Float) (E : Int)
    (hE : -1022 ≤ E) (hE' : E ≤ 1022)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hmag : ∀ i, i < a.size → |value (a.getD i 0.0) - value (b.getD i 0.0)| ≤ (2 : ℝ) ^ E)
    : ∃ r,
        sub a b = .ok r
        ∧ r.size = a.size
        ∧ r.all Float.isFinite = true
        ∧ ∀ i,
            i < a.size
            → |value (r.getD i 0.0) - (value (a.getD i 0.0) - value (b.getD i 0.0))|
              ≤ (2 : ℝ) ^ (E - 52) := by
  have he (i : Nat) (hi : i < a.size) := Flare.Binary64.Arithmetic.sub_error
    (a.getD i 0.0) (b.getD i 0.0) E
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ hb)
    hE hE' (hmag i hi)
  have hm : sub a b = .ok ((Array.range a.size).map (fun i => a.getD i 0.0 - b.getD i 0.0)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro i hi
    apply finite_ok
    exact (he i (by simpa using hi)).1
  refine ⟨_, hm, by simp, ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    simpa only [Array.getElem_map, Array.getElem_range] using (he i (by simpa using hi)).1
  · intro i hi
    simpa [hi] using (he i hi).2

theorem add_accuracy (a b : Array Float) (E : Int)
    (hE : -1022 ≤ E) (hE' : E ≤ 1022)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hmag : ∀ i, i < a.size → |value (a.getD i 0.0) + value (b.getD i 0.0)| ≤ (2 : ℝ) ^ E)
    : ∃ r,
        add a b = .ok r
        ∧ r.size = a.size
        ∧ r.all Float.isFinite = true
        ∧ ∀ i,
            i < a.size
            → |value (r.getD i 0.0) - (value (a.getD i 0.0) + value (b.getD i 0.0))|
              ≤ (2 : ℝ) ^ (E - 52) := by
  have he (i : Nat) (hi : i < a.size) := Flare.Binary64.Arithmetic.add_error
    (a.getD i 0.0) (b.getD i 0.0) E
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ hb)
    hE hE' (hmag i hi)
  have hm : add a b = .ok ((Array.range a.size).map (fun i => a.getD i 0.0 + b.getD i 0.0)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro i hi
    apply finite_ok
    exact (he i (by simpa using hi)).1
  refine ⟨_, hm, by simp, ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    simpa only [Array.getElem_map, Array.getElem_range] using (he i (by simpa using hi)).1
  · intro i hi
    simpa [hi] using (he i hi).2

end Kalman.Proofs.FloatDenseError
