import Kalman.Proofs.FloatDenseError
import Flare.Matrix.SolveAccuracy

/-! The LDLᵀ solve used by the dense filter inherits FLARE's native residual
and forward-error enclosure through the error adapter. Its conditioning and
dimension profile are narrower than the filter's accepted input domain. -/

namespace Kalman.Proofs.FloatSolveError

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Flare.Binary64.Value

theorem operations_solve_ok (n columns : Nat) (a b r : Array Float)
    (h : Flare.Matrix.Operations.solveSPD n columns a b = .ok r)
    : solveSPD n columns a b = .ok r := by
  unfold Flare.Matrix.Operations.solveSPD at h
  cases he : Flare.Matrix.Dense.solveSPD n columns a b with
  | error e => cases e <;> simp [he, Flare.Matrix.Operations.adapt] at h
  | ok result =>
      have hh : result = r := by simpa [he, Flare.Matrix.Operations.adapt] using h
      simp [solveSPD, he, hh, adapt]

/-- A posteriori native solve enclosure under a proved 3/16 eigenvalue floor.
The actual rounded coefficient matrix must satisfy this floor and symmetry.
This is not a hypothesis on the desired solution error. -/
theorem solve_accuracy (n columns : Nat) (B : Int) (a b : Array Float)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : ∃ f y x,
        Flare.Matrix.Dense.factor n a = .ok f
        ∧ Flare.Matrix.LinearSolve.forward n columns f b = .ok y
        ∧ Flare.Matrix.LinearSolve.backward n columns f y = .ok x
        ∧ solveSPD n columns a b = .ok x
        ∧ x.size = n * columns
        ∧ x.all Float.isFinite = true
        ∧ ∀ i j,
            |matrix n columns x i j - ((matrix n n a)⁻¹ * matrix n columns b) i j|
            ≤ n
              * (∑ k : Fin n,
                  Flare.Matrix.SolveAccuracy.residualBound n columns f b y x k j)
              / (3 / 16 : ℝ) := by
  obtain ⟨f, y, x, hf, hy, hx, hs, hsize, hfinite, he⟩ :=
    Flare.Matrix.SolveAccuracy.solveSPD_accuracy n columns B a b hn hB hB' haf hbf hA ha hb
  exact ⟨f, y, x, hf, hy, hx, operations_solve_ok _ _ _ _ _ hs, hsize, hfinite, he⟩

end Kalman.Proofs.FloatSolveError
