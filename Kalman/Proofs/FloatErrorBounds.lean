import Kalman.Implementation.Correctness.SquareRootFilterProperties
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Implementation.Correctness.JosephCovarianceEvaluation
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatCholeskyFactor
import Kalman.Proofs.FloatJosephError
import Kalman.Proofs.FloatSolveError
import Kalman.Proofs.FloatMaterialization
import Kalman.Proofs.FloatQRGram
import Kalman.Proofs.FloatQRComposition
import Kalman.Proofs.FloatQRInitialDomain

/-!
# Component bounds and their proof witnesses

This module packages auxiliary component statements with their completed proofs.
It introduces no stronger numerical claim. Read every profile and range premise:
Cholesky/Joseph profiles include actual successful intermediate computations;
the product, array sum, residual, LDLᵀ and materialization bounds prove success
from their operand hypotheses. Full QR Gram error is available under explicit
prefix profiles and under a supported initial-input domain that derives them.
Neither witness assumes final success or the desired error.
See `docs/results.md` for the claim ledger.
-/

namespace Kalman.Proofs.FloatErrorBounds

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Implementation.Correctness.JosephCovarianceEvaluation
open Kalman.Proofs.SquareRootProfiles
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.QRProfiles
open Flare.Binary64.Value

/-! ----------------------------------------------------------------------
## Auxiliary component statements
-------------------------------------------------------------------------- -/

/-! These predicates package intermediate arithmetic and factorization bounds.
They live with their proof witnesses, rather than in the main result interfaces. -/

noncomputable section

/-- Absolute entry error k·2⁻⁵⁰·M for the actual matrix product, with correct
input/output shapes and successful finite execution. M bounds dot-product mass.
The bound is `productRadius inner M = inner * 2⁻⁵⁰ * M`.
The witness requires the shape assumptions and `Kalman.Proofs.ArithmeticProfiles.ProductProfile`.
Proof witness: `Kalman.Proofs.FloatErrorBounds.matrixProductAccuracy`. -/
def MatrixProductAccuracy (rows inner columns : Nat) (a b : Array Float) (M : ℝ) : Prop :=
  a.size = rows * inner
  ∧ b.size = inner * columns
  ∧ ∃ r,
      multiply rows inner columns a b = .ok r
      ∧ r.size = rows * columns
      ∧ r.all Float.isFinite = true
      ∧ EntrywiseWithin (productRadius inner M)
          (matrix rows columns r) (matrix rows inner a * matrix inner columns b)

/-- Absolute entry error 2^(E-52) for checked array addition or subtraction.
The exact stored-operand sum/difference is bounded by 2^E.
Proof witness: `Kalman.Proofs.FloatErrorBounds.arraySumAccuracy`. -/
def ArraySumAccuracy (subtract : Bool) (a b : Array Float) (E : Int) : Prop :=
  a.size = b.size
  ∧ ∃ r,
      (if subtract then sub a b else add a b) = .ok r
      ∧ r.size = a.size
      ∧ r.all Float.isFinite = true
      ∧ ∀ i,
          i < a.size
          → |value (r.getD i 0.0)
              - (value (a.getD i 0.0)
                  + (if subtract then -value (b.getD i 0.0) else value (b.getD i 0.0)))|
            ≤ sumRadius E

/-- Ordered native subtraction of k separately rounded products has absolute
error k·2⁻⁴⁸·M and succeeds under a ResidualProfile.
Proof witness: `Kalman.Proofs.FloatErrorBounds.residualAccuracy`. -/
def ResidualAccuracy (indices : List Nat) (left right : Nat → Float) (initial : Float)
    (M : ℝ)
    : Prop :=
  ∃ r,
    subtractProducts indices left right initial = .ok r
    ∧ r.isFinite = true
    ∧ |value r
        - (value initial - (indices.map (fun k => value (left k) * value (right k))).sum)|
      ≤ residualRadius indices.length M

/-- Rounded division after the residual loop has an explicit equation-residual
allowance; this bound is on x·d-(b-Σac), not on an unscaled quotient error.
Proof witness: `Kalman.Proofs.FloatErrorBounds.residualDivisionAccuracy`. -/
def ResidualDivisionAccuracy (indices : List Nat) (left right : Nat → Float)
    (initial diagonal : Float) (M δ D : ℝ)
    : Prop :=
  ∃ r,
    divideResidual indices left right initial diagonal = .ok r
    ∧ r.isFinite = true
    ∧ |value r * value diagonal
        - (value initial - (indices.map (fun k => value (left k) * value (right k))).sum)|
      ≤ divisionRadius indices.length M δ D

/-- A strict exact residual margin ensures the native Cholesky diagonal checks
succeed. The error compares the squared returned diagonal with that residual.
Proof witness: `Kalman.Proofs.FloatErrorBounds.choleskyDiagonalAccuracy`. -/
def CholeskyDiagonalAccuracy (indices : List Nat) (left : Nat → Float) (initial : Float)
    (M : ℝ)
    : Prop :=
  ∃ pivot,
    subtractProducts indices left left initial = .ok pivot
    ∧ positiveSqrt pivot = .ok pivot.sqrt
    ∧ pivot.sqrt.isFinite = true
    ∧ 0 < value pivot.sqrt
    ∧ |(value pivot.sqrt) ^ 2
        - (value initial - (indices.map (fun k => value (left k) * value (left k))).sum)|
      ≤ diagonalRadius indices.length M

/-- Shared radius used by the completed Cholesky error statements below. -/
def choleskyGramRadius (n : Nat) (M δ D : ℝ) : ℝ :=
  diagonalRadius n M + divisionRadius n M δ D

/-- Shared radius used by the completed Cholesky error statements below. -/
def choleskySolutionRadius (n : Nat) (M δ D α : ℝ) : ℝ :=
  n * ((1 + n * D) * divisionRadius n M δ D) / α

/-- Whole-factor backward error: the exact Gram of the actual returned native
factor is within c_n+r_n of the same stored covariance input.
Proof witness: `Kalman.Proofs.FloatErrorBounds.choleskyGramAccuracy`. -/
def CholeskyGramAccuracy (n : Nat) (a l : Array Float) (M δ D : ℝ) : Prop :=
  a.size = n * n
  ∧ a.all Float.isFinite = true
  ∧ l.size = n * n
  ∧ l.all Float.isFinite = true
  ∧ cholesky n a = .ok l
  ∧ EntrywiseWithin (choleskyGramRadius n M δ D)
      (matrix n n l * (matrix n n l).transpose) (matrix n n a)

/-- Solution error for the actual two-pass solve, relative to the supplied
stored factor's exact Gram. α is its proved positive spectral floor.
Proof witness: `Kalman.Proofs.FloatErrorBounds.choleskySolveAccuracy`. -/
def CholeskySolveAccuracy (n columns : Nat) (l b x : Array Float) (M δ D α : ℝ) : Prop :=
  l.size = n * n
  ∧ l.all Float.isFinite = true
  ∧ b.size = n * columns
  ∧ b.all Float.isFinite = true
  ∧ solveCholesky n columns l b = .ok x
  ∧ x.size = n * columns
  ∧ EntrywiseWithin (choleskySolutionRadius n M δ D α)
      (matrix n columns x)
      ((matrix n n l * (matrix n n l).transpose)⁻¹ * matrix n columns b)

/-- The dense filter's actual LDLᵀ solver has finite successful execution and
an explicit FLARE residual-based solution-error allowance. Its success domain
is n≤12 and A≽(3/16)I with the magnitude restrictions in the witness theorem.
Proof witness: `Kalman.Proofs.FloatErrorBounds.ldlSolveAccuracy`. -/
def LDLSolveAccuracy (n columns : Nat) (a b : Array Float) : Prop :=
  a.size = n * n
  ∧ b.size = n * columns
  ∧ ∃ f y x,
      Flare.Matrix.Dense.factor n a = .ok f
      ∧ Flare.Matrix.LinearSolve.forward n columns f b = .ok y
      ∧ Flare.Matrix.LinearSolve.backward n columns f y = .ok x
      ∧ solveSPD n columns a b = .ok x
      ∧ x.size = n * columns
      ∧ x.all Float.isFinite = true
      ∧ ∀ i j,
          |matrix n columns x i j - ((matrix n n a)⁻¹ * matrix n columns b) i j|
          ≤ n
            * (∑ t : Fin n,
                Flare.Matrix.SolveAccuracy.residualBound n columns f b y x t j)
            / (3 / 16 : ℝ)

/-- One native QR iteration's exact column-Gram change. The proof witness
requires its incoming panel profile and prior triangular zeros, not assumed
success or error. This is a local bound, not a whole-QR backward-error claim.
Proof witness: `Kalman.Proofs.FloatErrorBounds.qrIterationGramAccuracy`. -/
def QRIterationGramAccuracy (height width pivot : Nat) (a : Array Float) (M : ℝ) : Prop :=
  Kalman.Proofs.QRProfiles.IterationGramAccuracy height width pivot a M

/-- Complete native QR factor error against the exact Gram of the same original
stored prearray, with successful execution and strictly PD exact output Gram.
Witnesses use either explicit prefix profiles or the supported initial-input
domain from which all those profiles are derived.
Proof witness: `Kalman.Proofs.FloatErrorBounds.qrGramFactorAccuracy`. -/
def QRGramFactorAccuracy (rows columns : Nat) (a : Array Float) (budget : Nat → ℝ)
    : Prop :=
  Kalman.Proofs.QRProfiles.GramFactorAccuracy rows columns a budget

/-- Native factor success, quantitative exact-Gram floor and original-prearray
error, including the conservative M²/128 cap. The proof witness takes only
the initial finite prearray's eight-row energy/rank/scale domain.
Proof witness: `Kalman.Proofs.FloatErrorBounds.qrGramFactorInitialAccuracy`. -/
def QRInitialGramFactorAccuracy (rows columns : Nat) (a : Array Float) (M : ℝ) : Prop :=
  Kalman.Proofs.QRProfiles.InitialGramFactorAccuracy rows columns a M

end

/-- Completed native matrix-product bound, including successful finite execution. -/
theorem matrixProductAccuracy (rows inner columns : Nat) (a b : Array Float) (M : ℝ)
    (ha : a.size = rows * inner) (hb : b.size = inner * columns)
    (p : ProductProfile rows inner columns a b M)
    : MatrixProductAccuracy rows inner columns a b M := by
  obtain ⟨r, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy
    rows inner columns a b (fun _ _ => M) p.inner_le p.finite_left p.finite_right
    (fun _ _ _ _ => p.upper) (fun _ _ _ _ => p.lower) p.mass
  have hM : 0 ≤ M := (zpow_pos (by norm_num : (0 : ℝ) < 2) (-1022 : Int)).le.trans p.lower
  exact ⟨ha, hb, r, hr, hs, hf, by unfold productRadius; positivity, he⟩

/-- Completed addition/subtraction bound; cancellation and underflow are included. -/
theorem arraySumAccuracy (subtract : Bool) (a b : Array Float) (E : Int)
    (hs : a.size = b.size) (p : SumProfile a b E subtract)
    : ArraySumAccuracy subtract a b E := by
  cases subtract with
  | false =>
      obtain ⟨r, hr, hsize, hf, he⟩ := FloatDenseError.add_accuracy a b E
        p.exponent_lower p.exponent_upper p.finite_left p.finite_right
        (by simpa only [Bool.false_eq_true, ↓reduceIte] using p.magnitude)
      exact ⟨hs, r, hr, hsize, hf, he⟩
  | true =>
      obtain ⟨r, hr, hsize, hf, he⟩ := FloatDenseError.sub_accuracy a b E
        p.exponent_lower p.exponent_upper p.finite_left p.finite_right
        (by simpa only [Bool.true_eq_false, ↓reduceIte, sub_eq_add_neg] using p.magnitude)
      refine ⟨hs, r, hr, hsize, hf, ?_⟩
      simpa only [Bool.true_eq_false, ↓reduceIte, ← sub_eq_add_neg, sumRadius] using he

/-- Completed ordered residual bound, with successful finite execution. -/
theorem residualAccuracy (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (M : ℝ) (p : ResidualProfile indices left right initial M)
    : ResidualAccuracy indices left right initial M :=
  FloatResidualError.residual_accuracy indices left right initial M p

/-- Completed residual/division allowance, including successful finite execution. -/
theorem residualDivisionAccuracy (indices : List Nat) (left right : Nat → Float)
    (initial diagonal : Float) (M δ D : ℝ)
    (p : ResidualProfile indices left right initial M) (hd : diagonal.isFinite = true)
    (hδ : 0 < δ) (hfloor : δ ≤ value diagonal) (hD : |value diagonal| ≤ D)
    (hquotient : (M + residualRadius indices.length M) / δ ≤ (2 : ℝ) ^ (1000 : Int))
    : ResidualDivisionAccuracy indices left right initial diagonal M δ D :=
  FloatResidualError.divideResidual_accuracy indices left right initial diagonal M δ D
    p hd hδ hfloor hD hquotient

/-- Completed local Cholesky diagonal bound; the supplied residual margin
establishes success of both positive-pivot checks rather than assuming success. -/
theorem choleskyDiagonalAccuracy (indices : List Nat) (left : Nat → Float)
    (initial : Float) (M : ℝ) (p : ResidualProfile indices left left initial M)
    (hmargin
      : residualRadius indices.length M
        < value initial - (indices.map (fun k => value (left k) * value (left k))).sum)
    : CholeskyDiagonalAccuracy indices left initial M :=
  FloatResidualError.choleskyDiagonal_accuracy indices left initial M p hmargin

/-- Completed whole-Cholesky backward error under a posteriori operand budgets.
FactorProfile includes successful execution; this does not prove an input success domain. -/
theorem choleskyGramAccuracy (n : Nat) (a l : Array Float) (M δ D : ℝ)
    (ha : a.size = n * n) (haf : a.all Float.isFinite = true)
    (p : FactorProfile n a l M δ D)
    : CholeskyGramAccuracy n a l M δ D :=
  ⟨
    ha,
    haf,
    (FloatCholeskyFactor.cholesky_equations n a l p.execution).1,
    p.finite_lower,
    p.execution,
    FloatCholeskyFactor.factor_backward_error n a l M δ D p
  ⟩

/-- Completed native solve error against LLᵀ, with explicit conditioning.
SolveProfile includes both successful passes and their stored operand budgets. -/
theorem choleskySolveAccuracy (n columns : Nat) (l b y x : Array Float) (M δ D α : ℝ)
    (hl : l.size = n * n) (hb : b.size = n * columns) (hbf : b.all Float.isFinite = true)
    (p : SolveProfile n columns l b y x M δ D) (hM : 0 ≤ M) (hα : 0 < α)
    (hA : (matrix n n l * (matrix n n l).transpose - α • 1).PosSemidef)
    : CholeskySolveAccuracy n columns l b x M δ D α := by
  obtain ⟨hs, he⟩ := FloatCholeskySolve.solve_accuracy n columns l b y x M δ D α p hM hα hA
  exact ⟨hl, p.finite_lower, hb, hbf, hs,
    (FloatCholeskySolve.backward_equations n columns l y x p.backward).1, he⟩

/-- Completed native LDLᵀ solve bound. Unlike the a posteriori Cholesky profiles,
these original stored-matrix hypotheses establish successful finite execution. -/
theorem ldlSolveAccuracy (n columns : Nat) (B : Int) (a b : Array Float)
    (has : a.size = n * n) (hbs : b.size = n * columns)
    (hn : n ≤ 12) (hB : 0 ≤ B) (hB' : B ≤ 512)
    (haf : a.all Float.isFinite = true) (hbf : b.all Float.isFinite = true)
    (hA : (matrix n n a - (3 / 16 : ℝ) • 1).PosSemidef)
    (ha : ∀ i j : Fin n, |value (entry n a i.val j.val)| ≤ 1024)
    (hb : ∀ i j, i < n → j < columns → |value (entry columns b i j)| ≤ (2 : ℝ) ^ B)
    : LDLSolveAccuracy n columns a b :=
  ⟨has, hbs, FloatSolveError.solve_accuracy n columns B a b hn hB hB' haf hbf hA ha hb⟩

/-- Completed Joseph evaluation bound at the supplied stored gain, covering
all five products and both sums. This does not include gain/prediction error. -/
theorem josephCovarianceAccuracy {input : Input.Model} {prior : Input.State}
    {k output : Array Float} (p : JosephProfile input prior k output) (P W K : ℝ)
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hK : 0 ≤ K)
    (hp
      : ∀ i j,
          |matrix input.stateDimension input.stateDimension prior.covariance i j| ≤ P)
    (hw
      : ∀ i j,
          |((1 : Matrix (Fin input.stateDimension) (Fin input.stateDimension) ℝ)
            - matrix input.stateDimension input.measurementDimension k
              * matrix input.measurementDimension input.stateDimension input.observation)
            i j|
          ≤ W)
    (hk : ∀ i j, |matrix input.stateDimension input.measurementDimension k i j| ≤ K)
    : JosephCovarianceAccuracy (josephRadius p P W K) input prior k output :=
  FloatJosephError.joseph_evaluation_error p P W K hP hW hK hp hw hk

/-- Completed dense materialization bound, including checked valid output. -/
theorem factorMaterializationAccuracy (n : Nat) (factor : Input.FactorState) (M : ℝ)
    (hn : 0 < n) (hn' : n ≤ 32)
    (hv
      : Kalman.Implementation.Correctness.SquareRootFilterProperties.ValidFactor n factor)
    (hM : M ≤ (2 : ℝ) ^ (990 : Int)) (hη : (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hmass
      : ∀ i j,
          i < n
          → j < n
          → (∑ k ∈ Finset.range n,
              |value (entry n factor.lower i k) * value (entry n factor.lower j k)|)
            ≤ M)
    : FactorMaterializationAccuracy n factor M :=
  FloatMaterialization.materialization_accuracy n factor M hn hn' hv hM hη hmass

/-- A proved error enclosure implies strict dense PD when symmetry and the
reference eigenvalue margin are also supplied. It does not infer those premises. -/
theorem denseCovariancePositiveDefinite {n : Nat}
    (reference output : Matrix (Fin n) (Fin n) ℝ) (α ε : ℝ)
    (hmargin : n * ε < α) (href : (reference - α • 1).PosSemidef)
    (hout : output.IsHermitian) (he : EntrywiseWithin ε output reference)
    : output.PosDef :=
  ErrorPropagation.posDef_of_error_margin reference output α ε hmargin href hout he

/-- Completed local native QR Gram bound. At pivot zero the prior-zero premise
is vacuous; at later pivots it is the proved ascending-loop structural invariant.
The incoming numerical profile still needs justification at each later pivot. -/
theorem qrIterationGramAccuracy (height width pivot : Nat) (a : Array Float) (M : ℝ)
    (p : Kalman.Proofs.QRProfiles.IterationProfile height width pivot a M)
    (hz : Kalman.Proofs.QRProfiles.ProcessedColumns height width pivot a)
    : QRIterationGramAccuracy height width pivot a M :=
  FloatQRGram.qrIteration_gram_accuracy height width pivot a M p hz

/-- Completed full native QR factor Gram bound under explicit prefix operand
profiles. Success, retained diagonal positivity and error are conclusions.
The initial-domain witness below discharges profiles for up to eight tall rows. -/
theorem qrGramFactorAccuracy (rows columns : Nat) (a : Array Float) (budget : Nat → ℝ)
    (hs : a.size = rows * columns) (hf : a.all Float.isFinite = true)
    (p
      : Kalman.Proofs.QRProfiles.TriangularizationProfile
          columns rows (transpose rows columns a) budget)
    : QRGramFactorAccuracy rows columns a budget :=
  FloatQRComposition.gramFactor_accuracy rows columns a budget hs hf p

/-- Completed initial-input factor theorem. For rows≤columns≤8, scale in
[2⁻⁸⁹⁶,2⁹⁰⁰], row energies ≤M²/2 and initial row Gram ≽(M²/8)I, native
factorization succeeds with positive diagonal, strict-PD exact Gram floor
M²/16 and absolute Gram error ≤M²/128. No prefix profile or success is assumed. -/
theorem qrGramFactorInitialAccuracy (rows columns : Nat) (a : Array Float) (M : ℝ)
    (d : Kalman.Proofs.QRProfiles.GramFactorInputDomain rows columns a M)
    : QRInitialGramFactorAccuracy rows columns a M :=
  FloatQRInitialDomain.gramFactor_initial_accuracy rows columns a M d

end Kalman.Proofs.FloatErrorBounds
