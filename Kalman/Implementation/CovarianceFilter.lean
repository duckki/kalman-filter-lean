import Kalman.Implementation.LinearAlgebra

/-!
# Three native covariance filters

The standard prediction and correction follow Särkkä and Svensson (2023),
Theorem 6.6. Direct Joseph evaluation follows Thornton and Bierman (1976),
Eq. (8), with vector measurements. Project adaptation: an LDLᵀ innovation
solve replaces explicit inversion. Each formulation has its own operation order.
The conventional forms deliberately allow an invalid posterior to be returned.
-/

namespace Kalman.Implementation.CovarianceFilter

open Kalman.Definitions.Input
open Kalman.Implementation.LinearAlgebra

inductive Form where
  | compact
  | subtractive
  | joseph
deriving DecidableEq, Repr

/-- Common gain calculation, exposing the rounded innovation for inspection. -/
structure Correction where
  gain : Array Float
  innovationCovariance : Array Float
  residual : Array Float
deriving Repr

def predictUnchecked (input : Model) (state : State) : Except Error State := do
  let n := input.stateDimension
  let mean ← multiply n n 1 input.transition state.mean
  let fp ← multiply n n n input.transition state.covariance
  let propagated ← multiply n n n fp (transpose n n input.transition)
  let covariance ← add propagated input.processNoise
  return ⟨mean, covariance⟩

def correctionUnchecked (input : Model) (prior : State) : Except Error Correction := do
  let n := input.stateDimension
  let m := input.measurementDimension
  let hp ← multiply m n n input.observation prior.covariance
  let hph ← multiply m n m hp (transpose m n input.observation)
  let s ← add hph input.measurementNoise
  let pht ← multiply n n m prior.covariance (transpose m n input.observation)
  let kt ← solveSPD m n s (transpose n m pht)
  let projected ← multiply m n 1 input.observation prior.mean
  let residual ← sub input.measurement projected
  return ⟨transpose m n kt, s, residual⟩

def covarianceUnchecked (form : Form) (input : Model) (prior : State) (k : Array Float)
    : Except Error (Array Float) := do
  let n := input.stateDimension
  let m := input.measurementDimension
  match form with
  | .compact =>
      let kh ← multiply n m n k input.observation
      let w ← sub (identity n) kh
      multiply n n n w prior.covariance
  | .subtractive =>
      let hp ← multiply m n n input.observation prior.covariance
      let correction ← multiply n m n k hp
      sub prior.covariance correction
  | .joseph =>
      let kh ← multiply n m n k input.observation
      let w ← sub (identity n) kh
      let wp ← multiply n n n w prior.covariance
      let first ← multiply n n n wp (transpose n n w)
      let kr ← multiply n m m k input.measurementNoise
      let second ← multiply n m n kr (transpose n m k)
      add first second

def updateUnchecked (form : Form) (input : Model) (prior : State)
    : Except Error State := do
  let c ← correctionUnchecked input prior
  let increment ←
    multiply input.stateDimension input.measurementDimension 1 c.gain c.residual
  let mean ← add prior.mean increment
  let covariance ← covarianceUnchecked form input prior c.gain
  return ⟨mean, covariance⟩

def predict (input : Model) (state : State) : Except Error State := do
  input.validate
  state.validate input.stateDimension
  predictUnchecked input state

def update (form : Form) (input : Model) (prior : State) : Except Error State := do
  input.validate
  prior.validate input.stateDimension
  updateUnchecked form input prior

def step (form : Form) (input : Model) (state : State) : Except Error State := do
  input.validate
  state.validate input.stateDimension
  updateUnchecked form input (← predictUnchecked input state)

end Kalman.Implementation.CovarianceFilter
