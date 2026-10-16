import Kalman.Implementation.CovarianceFilter

/-! Optional lower-triangle storage repair after the checked Joseph correction.
This copies words, performs no floating-point arithmetic, and propagates every
error from the underlying checked update unchanged. -/

namespace Kalman.Implementation.SymmetricJosephFilter

open Kalman.Definitions.Input

/-- Keep the mean and lower covariance triangle; copy lower entries to upper
entries. Public callers should supply a validated, finite `n`-state result. -/
def mirrorCovariance (n : Nat) (state : State) : State :=
  ⟨state.mean, Flare.Matrix.Dense.mirrorLower n state.covariance⟩

/-- Opt-in symmetry repair. The original Joseph implementation is unchanged. -/
def update (input : Model) (prior : State) : Except Error State := do
  let output ← CovarianceFilter.update .joseph input prior
  return mirrorCovariance input.stateDimension output

/-- Checked covariance prediction followed by the same explicit storage repair. -/
def predict (input : Model) (state : State) : Except Error State := do
  let output ← CovarianceFilter.predict input state
  return mirrorCovariance input.stateDimension output

/-- Prediction and position correction each repair their resulting covariance. -/
def step (input : Model) (state : State) : Except Error State := do
  update input (← predict input state)

/-- Retain the original input sequence and fail at the first rejected step. -/
def run (inputs : Nat → Model) (initial : State) : Nat → Except Error State
  | 0 => .ok initial
  | t + 1 => do step (inputs t) (← run inputs initial t)

end Kalman.Implementation.SymmetricJosephFilter
