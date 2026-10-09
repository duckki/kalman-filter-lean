import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact linear Gaussian model

Särkkä and Svensson (2023), §6.3, Theorem 6.6, pp. 96–98.
Notation is adapted to F, H, Q, R; a deterministic control offset is omitted.
All scalar arithmetic is exact in ℝ. Finite dimensions are type indices.
These source semantics are independent of native storage and validation policies.
-/

namespace Kalman.Definitions.LinearModel

abbrev Vector (n : Nat) := Fin n → ℝ
abbrev Square (n : Nat) := Matrix (Fin n) (Fin n) ℝ

/-- Source transition and observation model, with independent additive noises. -/
structure Model (n m : Nat) where
  transition : Square n
  observation : Matrix (Fin m) (Fin n) ℝ
  processNoise : Square n
  measurementNoise : Square m

/-- Mean and state-error covariance; covariance validity is a separate premise. -/
structure State (n : Nat) where
  mean : Vector n
  covariance : Square n

end Kalman.Definitions.LinearModel
