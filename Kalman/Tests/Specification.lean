import Kalman.Definitions.FactorRecursion
import Mathlib.Tactic.NormNum
import Kalman.Proofs.RealObservableInvariant

/-! Closed exact-arithmetic checks of source equations, independent of Float.
These local examples check transcription on simple inputs; general theorems
and completed full-recursion witnesses belong to Proofs. -/

namespace Kalman.Tests.Specification

open Matrix
open Kalman.Definitions.LinearModel
open Kalman.Definitions.CovarianceRecursion
open Kalman.Definitions.FactorRecursion

noncomputable def scalarModel : Model 1 1 := ⟨1, 1, 1, 1⟩
noncomputable def scalarState : State 1 := ⟨0, 1⟩

example : (predict scalarModel scalarState).covariance 0 0 = 2 := by
  simp only [predict, scalarModel, scalarState]
  norm_num [Matrix.mul_apply, Matrix.one_apply, Matrix.ofNat_apply, Fin.sum_univ_one]

example : innovationCovariance scalarModel scalarState 0 0 = 2 := by
  norm_num [innovationCovariance, scalarModel, scalarState, Matrix.mul_apply, Fin.sum_univ_one]

example : compact scalarModel scalarState (Matrix.of fun _ _ => 1 / 2) 0 0 = 1 / 2 := by
  simp only [compact, scalarModel, scalarState]
  norm_num [Matrix.mul_apply, Matrix.one_apply, Matrix.ofNat_apply, Fin.sum_univ_one]

example
    : subtractive scalarModel scalarState (Matrix.of fun _ _ => 1 / 2) 0 0 = 1 / 2 := by
  simp only [subtractive, scalarModel, scalarState]
  norm_num [Matrix.mul_apply, Matrix.one_apply, Matrix.ofNat_apply, Fin.sum_univ_one]

example : joseph scalarModel scalarState (Matrix.of fun _ _ => 1 / 2) 0 0 = 1 / 2 := by
  simp only [joseph, scalarModel, scalarState]
  norm_num [Matrix.mul_apply, Matrix.one_apply, Matrix.ofNat_apply,
    Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_one]

example : (trajectory (m := 1) .joseph scalarState []).length = 1 := by
  rfl

example : gram (Matrix.of fun _ _ : Fin 1 => (3 : ℝ)) 0 0 = 9 := by
  simp only [gram]
  norm_num [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_one]

/-- The positive scalar Real reference behind the cancellation regression. -/
example : 0 < (1 : ℝ) / ((2 : ℝ) ^ 54 + 1) := by positivity

/-- Full observation with identity/sign-reversing dynamics and unequal process
noise. Every covariance formulation has the same analytic two-state output. -/
example (form : Form)
    : step form
        (Kalman.Definitions.DiagonalObservation.model ![1, -1] ![1, 3 / 2] ![1, 1])
        (Kalman.Definitions.DiagonalObservation.state ![1, -1 / 2] ![1, 3 / 2]) ![-1, -1]
      = Kalman.Definitions.DiagonalObservation.state ![-1 / 3, -5 / 8]
          ![2 / 3, 3 / 4] := by
  rw [Kalman.Proofs.RealDiagonalObservation.step_eq form _ _ _ _ _ _
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)]
  apply congrArg₂ State.mk
  · funext i
    fin_cases i <;> norm_num [Kalman.Definitions.DiagonalObservation.step,
      Kalman.Definitions.DiagonalObservation.state, Kalman.Definitions.DiagonalObservation.priorVariance,
      Kalman.Definitions.DiagonalObservation.posteriorMean, Kalman.Definitions.DiagonalObservation.optimalGain]
  · apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;> norm_num [Kalman.Definitions.DiagonalObservation.priorVariance,
      Kalman.Definitions.DiagonalObservation.posteriorVariance]

end Kalman.Tests.Specification
