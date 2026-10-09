import Kalman.Definitions.CovarianceRecursion

/-! Exact fully observed diagonal specialization of Särkkä and Svensson
(2023), Theorem 6.6, Eqs. (6.20)–(6.29), pp. 96–98. The scalar rational
formulas below are project algebraic specializations, with their equality to
the existing matrix recursion proved in Proofs/RealDiagonalObservation.
These are Real specifications, not a second native input format. -/

namespace Kalman.Definitions.DiagonalObservation

open Kalman.Definitions.LinearModel

noncomputable section

def model {n : Nat} (f q r : Vector n) : Model n n :=
  ⟨Matrix.diagonal f, 1, Matrix.diagonal q, Matrix.diagonal r⟩

def state {n : Nat} (x p : Vector n) : State n := ⟨x, Matrix.diagonal p⟩

def priorVariance (f q p : ℝ) : ℝ := f ^ 2 * p + q

def optimalGain (p r : ℝ) : ℝ := p / (p + r)

def posteriorVariance (p r : ℝ) : ℝ := p * r / (p + r)

/-- Scalar Joseph covariance at a supplied gain, specializing the matrix
Joseph equation to full diagonal observation. -/
def josephVariance (p r k : ℝ) : ℝ := (1 - k) ^ 2 * p + k ^ 2 * r

def posteriorMean (p r x z : ℝ) : ℝ := r / (p + r) * x + optimalGain p r * z

/-- Exact componentwise specialization; the matrix step is the authoritative
comparison target, and equality is proved rather than assumed. -/
def step {n : Nat} (f q r z x p : Vector n) : State n :=
  state (fun i => posteriorMean (priorVariance (f i) (q i) (p i)) (r i) (f i * x i) (z i))
    (fun i => posteriorVariance (priorVariance (f i) (q i) (p i)) (r i))

/-- Project prefix recursion for time-varying diagonal models and measurements. -/
def run {n : Nat} (f q r z : Nat → Vector n) (x p : Vector n) : Nat → State n
  | 0 => state x p
  | t + 1 =>
      CovarianceRecursion.step .joseph (model (f t) (q t) (r t)) (run f q r z x p t) (z t)

end
end Kalman.Definitions.DiagonalObservation
