import Init.Data.Float.Float

/-!
# Authoritative decoded binary64 input

Project choices, not paper requirements: row-major arrays; dimensions 1–32;
finite entries; symmetric Q and R; checked arithmetic. Runtime dimension bounds
keep storage and loop index expressions below 2^16. Real covariance assumptions
remain explicit mathematical premises, not assertions made by these checks.
-/

namespace Kalman.Definitions.Input

inductive Error where
  | unsupportedDimension
  | invalidShape
  | nonfiniteInput
  | nonsymmetricNoise
  | nonfiniteComputation
  | nonpositivePivot
  | invalidFactor
deriving DecidableEq, Repr

/-- One decoded model/observation input shared by all native formulations. -/
structure Model where
  stateDimension : Nat
  measurementDimension : Nat
  transition : Array Float
  observation : Array Float
  processNoise : Array Float
  measurementNoise : Array Float
  measurement : Array Float
deriving Repr

structure State where
  mean : Array Float
  covariance : Array Float
deriving Repr

/-- A different working representation of the same state covariance. -/
structure FactorState where
  mean : Array Float
  lower : Array Float
deriving Repr

def symmetric (n : Nat) (a : Array Float) : Bool :=
  Id.run do
    for i in [:n] do
      for j in [:i] do
        if a.getD (i * n + j) 0.0 != a.getD (j * n + i) 0.0 then
          return false
    return true

/-- Validation precedence: dimensions, shapes, finite inputs, noise symmetry.
It checks storage, not mathematical positive definiteness. -/
def Model.validate (input : Model) : Except Error Unit := do
  let n := input.stateDimension
  let m := input.measurementDimension
  unless 0 < n && n ≤ 32 && 0 < m && m ≤ 32 do
    throw .unsupportedDimension
  unless input.transition.size == n * n
          && input.observation.size == m * n
          && input.processNoise.size == n * n
          && input.measurementNoise.size == m * m
          && input.measurement.size == m do
    throw .invalidShape
  unless #[
            input.transition,
            input.observation,
            input.processNoise,
            input.measurementNoise,
            input.measurement
          ].all
          (fun a => a.all Float.isFinite) do
    throw .nonfiniteInput
  unless symmetric n input.processNoise && symmetric m input.measurementNoise do
    throw .nonsymmetricNoise

def State.validate (state : State) (n : Nat) : Except Error Unit := do
  unless state.mean.size == n && state.covariance.size == n * n do
    throw .invalidShape
  unless state.mean.all Float.isFinite && state.covariance.all Float.isFinite do
    throw .nonfiniteInput

def FactorState.validate (state : FactorState) (n : Nat) : Except Error Unit :=
  if state.mean.size == n && state.lower.size == n * n then
    if state.mean.all Float.isFinite && state.lower.all Float.isFinite then
      if (Array.range n).all
          (fun i => decide (0.0 < state.lower.getD (i * n + i) 0.0)) then
        if (Array.range n).all
            (fun i =>
              (Array.range n).all
                (fun j =>
                  if i < j then state.lower.getD (i * n + j) 0.0 == 0.0 else true)) then
          .ok ()
        else
          .error .invalidFactor
      else
        .error .invalidFactor
    else
      .error .nonfiniteInput
  else
    .error .invalidShape

end Kalman.Definitions.Input
