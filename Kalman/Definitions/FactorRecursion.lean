import Kalman.Definitions.CovarianceRecursion
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Real square-root and U-D interpretations

Tracy (2022), arXiv:2208.06452v1: QR factorizations for prediction,
innovation, and the factored Joseph correction. Lower factors are used here,
so the source's upper-factor operations are transposed explicitly.
Bierman (1976), Automatica 12(4), pp. 375–382: P = U D Uᵀ storage.
QR is specified by an orthogonal triangularization relation, without selecting
a noncomputable canonical QR implementation. The native algorithm selects one.
-/

namespace Kalman.Definitions.FactorRecursion

open Matrix
open Kalman.Definitions.LinearModel

noncomputable section

def gram {n : Nat} {ι : Type} [Fintype ι] (a : Matrix (Fin n) ι ℝ) : Square n :=
  a * a.transpose

def LowerPositive {n : Nat} (l : Square n) : Prop :=
  (∀ i j, i < j → l i j = 0) ∧ ∀ i, 0 < l i i

def CovarianceFactor {n : Nat} (p l : Square n) : Prop :=
  LowerPositive l ∧ gram l = p

/-- A right orthogonal transformation of [A B] to [L 0]. This is the
transpose of thin QR on [A B]ᵀ, with a positive diagonal sign convention. -/
def QRGramFactor {n p : Nat} (a : Matrix (Fin n) (Fin n ⊕ Fin p) ℝ) (l : Square n)
    : Prop :=
  LowerPositive l
  ∧ ∃ u : Matrix (Fin n ⊕ Fin p) (Fin n ⊕ Fin p) ℝ,
      u * u.transpose = 1 ∧ a * u = Matrix.fromCols l 0

def predictionPrearray {n m : Nat} (model : Model n m) (l tq : Square n)
    : Matrix (Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromCols (model.transition * l) tq

def innovationPrearray {n m : Nat} (model : Model n m) (l : Square n) (tr : Square m)
    : Matrix (Fin m) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromCols tr (model.observation * l)

def posteriorPrearray {n m : Nat} (model : Model n m)
    (k : Matrix (Fin n) (Fin m) ℝ) (l : Square n) (tr : Square m)
    : Matrix (Fin n) (Fin n ⊕ Fin m) ℝ :=
  Matrix.fromCols ((1 - k * model.observation) * l) (k * tr)

/-- Active source relation for Tracy's three QR stages, with exact noise factors.
It specifies factors, gain, and represented covariances, rather than a choice oracle. -/
def SquareRootStages {n m : Nat} (model : Model n m) (l tq : Square n) (tr : Square m)
    (predicted : Square n) (innovationFactor : Square m) (posterior : Square n)
    (k : Matrix (Fin n) (Fin m) ℝ)
    : Prop :=
  CovarianceFactor model.processNoise tq
  ∧ CovarianceFactor model.measurementNoise tr
  ∧ QRGramFactor (predictionPrearray model l tq) predicted
  ∧ QRGramFactor (innovationPrearray model predicted tr) innovationFactor
  ∧ k = gram predicted * model.observation.transpose * (gram innovationFactor)⁻¹
  ∧ QRGramFactor (posteriorPrearray model k predicted tr) posterior

/-- Bierman U-D representation; this is storage semantics, not a U-D update algorithm. -/
def UDFactor {n : Nat} (p u : Square n) (d : Vector n) : Prop :=
  (∀ i j, j < i → u i j = 0)
  ∧ (∀ i, u i i = 1)
  ∧ (∀ i, 0 < d i)
  ∧ p = u * Matrix.diagonal d * u.transpose

end
end Kalman.Definitions.FactorRecursion
