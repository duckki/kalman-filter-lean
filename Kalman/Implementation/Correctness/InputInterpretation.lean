import Kalman.Implementation.SquareRootFilter
import Kalman.Definitions.Theorems.RecursionSensitivity
import Kalman.Definitions.FactorRecursion
import Kalman.Definitions.Input
import Flare.Matrix.Value
import Kalman.Implementation.LinearAlgebra

/-!
# Shared decoded-input interpretation

Shared definitions used by multiple result files. These relations and operating
conditions are not themselves universal success or accuracy theorems.
-/

namespace Kalman.Implementation.Correctness.InputInterpretation

open Kalman.Definitions Kalman.Implementation
open Kalman.Implementation.LinearAlgebra
open Flare.Binary64.Value

noncomputable section

/-! ----------------------------------------------------------------------
## Exact decoding and comparison relations
-------------------------------------------------------------------------- -/

/-!
# Exact interpretation of the decoded native input

FLARE supplies the native Float → logical binary64 model → Real interpretation.
Missing entries and exceptional values are totalized to zero by this ghost layer;
every meaningful contract separately requires valid shapes and finite storage.
Runtime kernels never execute this interpretation or rational/model arithmetic.
-/

abbrev matrix := Flare.Matrix.Value.matrix

def vector (n : Nat) (a : Array Float) : LinearModel.Vector n :=
  fun i => Flare.Binary64.Value.value (a.getD i.val 0.0)

def model (input : Input.Model)
    : LinearModel.Model input.stateDimension input.measurementDimension :=
  ⟨
    matrix input.stateDimension input.stateDimension input.transition,
    matrix input.measurementDimension input.stateDimension input.observation,
    matrix input.stateDimension input.stateDimension input.processNoise,
    matrix input.measurementDimension input.measurementDimension input.measurementNoise
  ⟩

def state (n : Nat) (input : Input.State) : LinearModel.State n :=
  ⟨vector n input.mean, matrix n n input.covariance⟩

/-- The covariance denoted by stored factor entries, using exact real multiplication. -/
def factorState (n : Nat) (input : Input.FactorState) : LinearModel.State n :=
  ⟨vector n input.mean, FactorRecursion.gram (matrix n n input.lower)⟩

/-! ----------------------------------------------------------------------
## Decoded diagonal storage
-------------------------------------------------------------------------- -/

/-! Exact decoded diagonal storage. Shape and finiteness are separate premises;
either signed-zero word is allowed outside the diagonal. This relation does
not assert diagonal preservation by any native operation. -/

def DecodedDiagonal (n : Nat) (a : Array Float) : Prop :=
  ∀ i j, i < n → j < n → i ≠ j → value (entry n a i j) = 0

/-! ----------------------------------------------------------------------
## Original covariance input domain
-------------------------------------------------------------------------- -/

/-- A sufficient correlated two-state covariance/noise domain.
The constants are project operating choices, not universal Cholesky requirements. -/
structure TwoStateCovarianceDomain (a : Array Float) : Prop where
  size : a.size = 4
  finite : a.all Float.isFinite = true
  symmetry : value (entry 2 a 0 1) = value (entry 2 a 1 0)
  diagonal_lower : ∀ i, i < 2 → 1 ≤ value (entry 2 a i i)
  diagonal_upper : ∀ i, i < 2 → value (entry 2 a i i) ≤ 2
  off_diagonal_bound : |value (entry 2 a 1 0)| ≤ 1 / 4

/-! ----------------------------------------------------------------------
## Independent ideal trace and native execution
-------------------------------------------------------------------------- -/

/-- Only dimension metadata is fixed; every stored input word is retained.
Horizon input domains require agreement with the native dimension metadata. -/
def atDimensions (n m : Nat) (input : Input.Model) : Input.Model :=
  ⟨
    n,
    m,
    input.transition,
    input.observation,
    input.processNoise,
    input.measurementNoise,
    input.measurement
  ⟩

def exactRun (n m : Nat) (inputs : Nat → Input.Model) (initial : LinearModel.State n)
    : Nat → LinearModel.State n
  | 0 => initial
  | t + 1 =>
      CovarianceRecursion.step .joseph (model (atDimensions n m (inputs t)))
        (exactRun n m inputs initial t) (vector m (inputs t).measurement)

/-- The actual executable driver, imported from the runtime-only module. -/
abbrev nativeRun := SquareRootFilter.run

end
end Kalman.Implementation.Correctness.InputInterpretation
