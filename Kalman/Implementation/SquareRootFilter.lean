import Kalman.Implementation.OrthogonalFactorization

/-!
# Native QR square-root Kalman filter

Tracy (2022), arXiv:2208.06452v1: prediction, innovation, and factored
Joseph QR. Lower factors transpose the source's upper-factor convention.
Noise covariances use checked Cholesky; covariance state uses a retained factor.
This is a project implementation of the algorithm, not a verbatim Julia port.
-/

namespace Kalman.Implementation.SquareRootFilter

open Kalman.Definitions.Input
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization

def fromCovariance (input : Model) (state : State) : Except Error FactorState := do
  input.validate
  state.validate input.stateDimension
  unless symmetric input.stateDimension state.covariance do
    throw .invalidFactor
  return ⟨state.mean, ← cholesky input.stateDimension state.covariance⟩

/-- An optional rounded dense output. Its positivity is a separate obligation. -/
def materialize (n : Nat) (state : FactorState) : Except Error State := do
  unless 0 < n && n ≤ 32 do
    throw .unsupportedDimension
  state.validate n
  return ⟨state.mean, ← multiply n n n state.lower (transpose n n state.lower)⟩

def predictUnchecked (input : Model) (state : FactorState)
    : Except Error FactorState := do
  let n := input.stateDimension
  let tq ← cholesky n input.processNoise
  let fl ← multiply n n n input.transition state.lower
  let prearray := fromCols n n n fl tq
  let lower ← gramFactor n (n + n) prearray
  let mean ← multiply n n 1 input.transition state.mean
  return ⟨mean, lower⟩

def updateUnchecked (input : Model) (prior : FactorState) : Except Error FactorState := do
  let n := input.stateDimension
  let m := input.measurementDimension
  let tr ← cholesky m input.measurementNoise
  let hl ← multiply m n n input.observation prior.lower
  let innovationFactor ← gramFactor m (m + n) (fromCols m m n tr hl)
  let pht ← multiply n n m prior.lower (transpose m n hl)
  let kt ← solveCholesky m n innovationFactor (transpose n m pht)
  let k := transpose m n kt
  let projected ← multiply m n 1 input.observation prior.mean
  let residual ← sub input.measurement projected
  let increment ← multiply n m 1 k residual
  let mean ← add prior.mean increment
  let kh ← multiply n m n k input.observation
  let w ← sub (identity n) kh
  let wl ← multiply n n n w prior.lower
  let ktr ← multiply n m m k tr
  let lower ← gramFactor n (n + m) (fromCols n n m wl ktr)
  return ⟨mean, lower⟩

def predict (input : Model) (state : FactorState) : Except Error FactorState := do
  input.validate
  state.validate input.stateDimension
  predictUnchecked input state

def update (input : Model) (prior : FactorState) : Except Error FactorState := do
  input.validate
  prior.validate input.stateDimension
  updateUnchecked input prior

def step (input : Model) (state : FactorState) : Except Error FactorState := do
  input.validate
  state.validate input.stateDimension
  let output ← updateUnchecked input (← predictUnchecked input state)
  output.validate input.stateDimension
  return output

/-! ----------------------------------------------------------------------
## Finite trajectories
-------------------------------------------------------------------------- -/

/-- Repeated checked steps on time-varying native inputs. The first failed
prefix propagates its error. No covariance is materialized. -/
def run (inputs : Nat → Kalman.Definitions.Input.Model)
    (initial : Kalman.Definitions.Input.FactorState)
    : Nat → Except Kalman.Definitions.Input.Error Kalman.Definitions.Input.FactorState
  | 0 => .ok initial
  | t + 1 => do
      Kalman.Implementation.SquareRootFilter.step (inputs t) (← run inputs initial t)

end Kalman.Implementation.SquareRootFilter
