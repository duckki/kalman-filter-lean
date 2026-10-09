import Kalman.Definitions.LinearModel

/-!
# Real Kalman recursion and covariance formulations

Särkkä and Svensson (2023), Theorem 6.6, pp. 96–98: prediction,
innovation, gain, and conventional correction. Joseph congruence form is
Thornton and Bierman (1976), Eq. (8), p. 10, with vector measurements.
The information formulation is the algebraic precision-matrix interpretation
of the same Gaussian update, valid for invertible prior and noise covariances.
Matrix inverse is total in Mathlib; its intended use requires invertibility.
-/

namespace Kalman.Definitions.CovarianceRecursion

open Kalman.Definitions.LinearModel
open Matrix

noncomputable section

/-- Exact prediction from the posterior of the preceding time step. -/
def predict {n m : Nat} (model : Model n m) (state : State n) : State n :=
  ⟨
    model.transition *ᵥ state.mean,
    model.transition * state.covariance * model.transition.transpose + model.processNoise
  ⟩

def innovation {n m : Nat} (model : Model n m) (prior : State n) (measurement : Vector m)
    : Vector m :=
  measurement - model.observation *ᵥ prior.mean

def innovationCovariance {n m : Nat} (model : Model n m) (prior : State n) : Square m :=
  model.observation * prior.covariance * model.observation.transpose
  + model.measurementNoise

def gain {n m : Nat} (model : Model n m) (prior : State n) : Matrix (Fin n) (Fin m) ℝ :=
  prior.covariance * model.observation.transpose * (innovationCovariance model prior)⁻¹

/-- Compact conventional covariance evaluation: (I - K H) P. -/
def compact {n m : Nat} (model : Model n m) (prior : State n)
    (k : Matrix (Fin n) (Fin m) ℝ)
    : Square n :=
  (1 - k * model.observation) * prior.covariance

/-- Subtractive conventional evaluation: P - K (H P). Association is explicit. -/
def subtractive {n m : Nat} (model : Model n m) (prior : State n)
    (k : Matrix (Fin n) (Fin m) ℝ)
    : Square n :=
  prior.covariance - k * (model.observation * prior.covariance)

/-- Direct Joseph congruence, with no subtractive expansion or symmetry repair.
This definition also makes sense for a gain other than the optimal gain. -/
def joseph {n m : Nat} (model : Model n m) (prior : State n)
    (k : Matrix (Fin n) (Fin m) ℝ)
    : Square n :=
  let w := 1 - k * model.observation
  w * prior.covariance * w.transpose + k * model.measurementNoise * k.transpose

inductive Form where
  | compact
  | subtractive
  | joseph
deriving DecidableEq, Repr

def correctedCovariance {n m : Nat} (form : Form) (model : Model n m)
    (prior : State n) (k : Matrix (Fin n) (Fin m) ℝ)
    : Square n :=
  match form with
  | .compact => compact model prior k
  | .subtractive => subtractive model prior k
  | .joseph => joseph model prior k

/-- Measurement correction using the exact optimal gain. -/
def update {n m : Nat} (form : Form) (model : Model n m) (prior : State n)
    (measurement : Vector m)
    : State n :=
  let k := gain model prior
  ⟨
    prior.mean + k *ᵥ innovation model prior measurement,
    correctedCovariance form model prior k
  ⟩

/-- One full time step, with prediction preceding measurement correction. -/
def step {n m : Nat} (form : Form) (model : Model n m) (state : State n)
    (measurement : Vector m)
    : State n :=
  update form model (predict model state) measurement

/-- Project finite-horizon composition of the source recursion. The trace starts
with the initial state and permits time-varying models at fixed dimensions. -/
def trajectory {n m : Nat} (form : Form) (initial : State n)
    (observations : List (Model n m × Vector m))
    : List (State n) :=
  observations.scanl
    (fun state observation => step form observation.1 state observation.2) initial

/-- Precision of the corrected Gaussian. Intended domain: P and R invertible. -/
def posteriorPrecision {n m : Nat} (model : Model n m) (prior : State n) : Square n :=
  prior.covariance⁻¹
  + model.observation.transpose * model.measurementNoise⁻¹ * model.observation

/-- Exact information-form measurement correction. No Float implementation yet. -/
def informationUpdate {n m : Nat} (model : Model n m) (prior : State n)
    (measurement : Vector m)
    : State n :=
  let p := (posteriorPrecision model prior)⁻¹
  let information :=
    prior.covariance⁻¹ *ᵥ prior.mean
    + model.observation.transpose *ᵥ (model.measurementNoise⁻¹ *ᵥ measurement)
  ⟨p *ᵥ information, p⟩

end
end Kalman.Definitions.CovarianceRecursion
