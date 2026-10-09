import Flare.Matrix.SolveAccuracy
import Kalman.Implementation.LinearAlgebra
import Kalman.Implementation.Correctness.InputInterpretation

/-!
# Cholesky operand profiles and input domains

Related interpretation relations, operand domains, and error contracts are
grouped below. These definitions state propositions; proof witnesses
live in `Kalman/Proofs/`.
-/

/-! ----------------------------------------------------------------------
## Factorization and triangular solve profiles
-------------------------------------------------------------------------- -/

/-! Operand profiles for Cholesky and its substitution passes. These bound
stored values and term masses; no accuracy conclusion is a premise. -/

namespace Kalman.Proofs.CholeskyProfiles

open Kalman.Implementation.LinearAlgebra
open Flare.Binary64.Value

noncomputable section

structure ResidualProfile (indices : List Nat) (left right : Nat → Float)
    (initial : Float) (M : ℝ)
    : Prop where
  length_le : indices.length ≤ 32
  finite_initial : initial.isFinite = true
  finite_left : ∀ k ∈ indices, (left k).isFinite = true
  finite_right : ∀ k ∈ indices, (right k).isFinite = true
  upper : M ≤ (2 : ℝ) ^ (990 : Int)
  mass
    : |value initial|
        + (indices.map (fun k => |value (left k) * value (right k)|)).sum
        + (2 : ℝ) ^ (-1022 : Int)
      ≤ M

def residualRadius (terms : Nat) (M : ℝ) : ℝ := terms * (2 : ℝ) ^ (-48 : Int) * M

def divisionRadius (terms : Nat) (M δ D : ℝ) : ℝ :=
  residualRadius terms M
  + D * (2 : ℝ) ^ (-50 : Int)
    * ((M + residualRadius terms M) / δ + (2 : ℝ) ^ (-1022 : Int))

def diagonalRadius (terms : Nat) (M : ℝ) : ℝ :=
  residualRadius terms M
  + (2 * (2 : ℝ) ^ (-53 : Int) + ((2 : ℝ) ^ (-53 : Int)) ^ 2)
    * (M + residualRadius terms M)

/-- Native operation equation for one Cholesky cell, using final stored prefixes.
It records execution, not a Real error conclusion. -/
def CellComputation (n : Nat) (a l : Array Float) (i j : Nat) (x : Float) : Prop :=
  if i = j then
    ∃ pivot,
      subtractProducts (List.range j) (fun k => entry n l j k)
          (fun k => entry n l j k) (entry n a j j)
        = .ok pivot
      ∧ positiveSqrt pivot = .ok x
  else
    divideResidual (List.range j) (fun k => entry n l i k)
      (fun k => entry n l j k) (entry n a i j) (entry n l j j)
    = .ok x

structure FactorProfile (n : Nat) (a l : Array Float) (M δ D : ℝ) : Prop where
  dimension_le : n ≤ 32
  execution : cholesky n a = .ok l
  symmetry
    : (Kalman.Implementation.Correctness.InputInterpretation.matrix n n a).IsHermitian
  finite_lower : l.all Float.isFinite = true
  mass_nonneg : 0 ≤ M
  diagonal_lower : 0 < δ
  diagonal_floor : ∀ i, i < n → δ ≤ value (entry n l i i)
  bound_nonneg : 0 ≤ D
  diagonal_bound : ∀ i, i < n → |value (entry n l i i)| ≤ D
  quotient_bound : (M + residualRadius n M) / δ ≤ (2 : ℝ) ^ (1000 : Int)
  rows
    : ∀ i j,
        i < n
        → j ≤ i
        → ResidualProfile (List.range j) (fun k => entry n l i k)
            (fun k => entry n l j k) (entry n a i j) M

/-- The two native passes are explicit, enabling a posteriori bounds on the
actual intermediate values. A successful run alone is not an accuracy theorem. -/
structure SolveProfile (n columns : Nat) (l b y x : Array Float) (M δ D : ℝ) : Prop where
  dimension_le : n ≤ 32
  forward : forwardCholesky n columns l b = .ok y
  backward : backwardCholesky n columns l y = .ok x
  finite_lower : l.all Float.isFinite = true
  lower_positive
    : Kalman.Definitions.FactorRecursion.LowerPositive
        (Kalman.Implementation.Correctness.InputInterpretation.matrix n n l)
  diagonal_lower : 0 < δ
  diagonal_floor : ∀ i, i < n → δ ≤ value (entry n l i i)
  bound_nonneg : 0 ≤ D
  lower_bound
    : ∀ i j : Fin n,
        |Kalman.Implementation.Correctness.InputInterpretation.matrix n n l i j| ≤ D
  quotient_bound : (M + residualRadius n M) / δ ≤ (2 : ℝ) ^ (1000 : Int)
  forward_rows
    : ∀ i j,
        i < n
        → j < columns
        → ResidualProfile (List.range i) (fun k => entry n l i k)
            (fun k => entry columns y k j) (entry columns b i j) M
  backward_rows
    : ∀ i j,
        i < n
        → j < columns
        → ResidualProfile (List.range' (i + 1) (n - (i + 1)))
            (fun k => entry n l k i) (fun k => entry columns x k j)
            (entry columns y i j) M

end
end Kalman.Proofs.CholeskyProfiles

/-! ----------------------------------------------------------------------
## Stored factor and right-hand-side domain
-------------------------------------------------------------------------- -/

/-! Conditions on the stored inputs of the two-state triangular solve.
No execution equation, intermediate array or error conclusion is assumed. -/

namespace Kalman.Proofs.CholeskyProfiles.SolveDomain

open Kalman.Implementation.LinearAlgebra
open Flare.Binary64.Value

noncomputable section

/-- A finite stored lower factor, with quantitative diagonal and entry bounds.
The upper entry may be either signed zero. -/
structure FactorDomain (l : Array Float) : Prop where
  size : l.size = 4
  finite : l.all Float.isFinite = true
  upper_zero : value (entry 2 l 0 1) = 0
  diagonal_floor : ∀ i, i < 2 → (1 : ℝ) / 2 ≤ value (entry 2 l i i)
  entry_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 l i j)| ≤ 2

/-- A sufficient project operating cap for two finite RHS columns. -/
structure RightHandSideDomain (b : Array Float) : Prop where
  size : b.size = 4
  finite : b.all Float.isFinite = true
  entry_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 b i j)| ≤ 1 / 8

end
end Kalman.Proofs.CholeskyProfiles.SolveDomain

/-! ----------------------------------------------------------------------
## Diagonal solve domain
-------------------------------------------------------------------------- -/

/-! Stored-input conditions for the larger diagonal two-state solve. No run,
intermediate profile or numerical accuracy conclusion is assumed. -/

namespace Kalman.Proofs.CholeskyProfiles.DiagonalSolve

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Flare.Binary64.Value

noncomputable section

structure FactorDomain (l : Array Float) : Prop where
  size : l.size = 4
  finite : l.all Float.isFinite = true
  diagonal : DecodedDiagonal 2 l
  diagonal_floor : ∀ i, i < 2 → 1 ≤ value (entry 2 l i i)
  entry_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 l i j)| ≤ 9 / 4

structure RightHandSideDomain (b : Array Float) : Prop where
  size : b.size = 4
  finite : b.all Float.isFinite = true
  entry_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 b i j)| ≤ 4

end
end Kalman.Proofs.CholeskyProfiles.DiagonalSolve
