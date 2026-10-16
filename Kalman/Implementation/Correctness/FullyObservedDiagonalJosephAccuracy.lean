import Kalman.Implementation.CovarianceFilter
import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy

/-! Dense-state invariants and completed native direct-Joseph guarantees.
The exact reference always interprets the original finite input words. -/

namespace Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Flare.Binary64.Value

noncomputable section

/-! ----------------------------------------------------------------------
## Dense native operating invariant
-------------------------------------------------------------------------- -/

/-- Storage bounds propagated by native direct-Joseph filtering. Positivity
concerns the returned dense array itself, with no symmetry repair or Gram
reinterpretation. Proof witness for positivity:
`Kalman.Proofs.FloatJosephUpdate.invariant_positive`. -/
structure StateInvariant (current : Input.State) : Prop where
  mean_size : current.mean.size = 2
  covariance_size : current.covariance.size = 4
  mean_finite : current.mean.all Float.isFinite = true
  covariance_finite : current.covariance.all Float.isFinite = true
  diagonal : DecodedDiagonal 2 current.covariance
  covariance_floor : ∀ i, (7 : ℝ) / 16 ≤ matrix 2 2 current.covariance i i
  covariance_cap : ∀ i, matrix 2 2 current.covariance i i ≤ (13 : ℝ) / 8
  mean_bound : ∀ i, i < 2 → |value (current.mean.getD i 0.0)| ≤ (9 : ℝ) / 8

/-! ----------------------------------------------------------------------
## Completed correction guarantee
-------------------------------------------------------------------------- -/

/-- Successful complete native Joseph correction, invariant output, and local
covariance/mean errors at most 2^-33 against the optimal-gain Real update of
the same original decoded prior and original model words. The witness derives
gain formation, residual/mean arithmetic, and covariance evaluation from its
original stored-input domain; no intermediate execution is a domain premise.
This is a local correction result, separately from prediction and horizons.
Proof witness: `Kalman.Proofs.FloatJosephUpdate.update_accuracy`. -/
def CorrectionAccuracy (input : Input.Model) (prior output : Input.State) : Prop :=
  CovarianceFilter.updateUnchecked .joseph input prior = .ok output
  ∧ StateInvariant output
  ∧ StateWithin ((2 : ℝ) ^ (-33 : Int)) ((2 : ℝ) ^ (-33 : Int)) (state 2 output)
      (CovarianceRecursion.update .joseph (model (atDimensions 2 2 input)) (state 2 prior)
        (vector 2 input.measurement))

/-! ----------------------------------------------------------------------
## Completed checked full-step guarantee
-------------------------------------------------------------------------- -/

/-- Complete checked native direct-Joseph step, invariant output, and local
covariance/mean errors at most 2^-32 against the exact full step of the same
incoming stored state. This includes prediction rounding propagated through
the changed gain. Original model and incoming invariant conditions are
sufficient; no intermediate success or desired output error is assumed.
Proof witness: `Kalman.Proofs.FloatJosephFilter.step_accuracy`. -/
def StepAccuracy (input : Input.Model) (current output : Input.State) : Prop :=
  Kalman.Implementation.CovarianceFilter.step .joseph input current = .ok output
  ∧ StateInvariant output
  ∧ StateWithin ((2 : ℝ) ^ (-32 : Int)) ((2 : ℝ) ^ (-32 : Int)) (state 2 output)
      (CovarianceRecursion.step .joseph (model (atDimensions 2 2 input)) (state 2 current)
        (vector 2 input.measurement))

/-! ----------------------------------------------------------------------
## Original-input horizons and uniform accumulated accuracy
-------------------------------------------------------------------------- -/

/-- The original model domain is shared with the QR certificate; only the
native working state and arithmetic path differ. -/
abbrev ModelDomain := FullyObservedDiagonalFilterAccuracy.ModelDomain

/-- The same original dense initial words are used by both implementations. -/
abbrev InitializationDomain := FullyObservedDiagonalFilterAccuracy.InitializationDomain

/-- Uniform covariance-entry error allowance at every native prefix. -/
def covarianceBudget : ℝ := (2 : ℝ) ^ (-30 : Int)

/-- Uniform mean-component error allowance, including covariance/gain coupling. -/
def meanBudget : ℝ := (2 : ℝ) ^ (-29 : Int)

/-- Original dense initialization and time-varying original model bounds only.
No reached profile, successful trace, or desired output error is assumed. -/
structure HorizonDomain (initial : Input.State) (inputs : Nat → Input.Model)
    (horizon : Nat)
    : Prop where
  initial_state : InitializationDomain initial
  models : ∀ t, t < horizon → ModelDomain (inputs t)

/-- Correctness-side composition of the existing checked native step. This
definition specifies the repeated executable calls without duplicating or
altering their arithmetic kernels. -/
def josephRun (inputs : Nat → Input.Model) (initial : Input.State)
    : Nat → Except Input.Error Input.State
  | 0 => .ok initial
  | t + 1 => do
      let current ← josephRun inputs initial t
      Kalman.Implementation.CovarianceFilter.step .joseph (inputs t) current

/-- Every finite prefix of checked direct-Joseph filtering succeeds with
uniform covariance/mean errors 2^-30/2^-29 against one independent Real trace
from the original dense words. Both actual dense and ideal covariances are
strictly positive definite. All stage profiles and native invariants follow
from the original input domain, including unit/sign-reversing dynamics.
Proof witness: `Kalman.Proofs.FloatJosephHorizon.initializedHorizonAccuracy`. -/
def HorizonAccuracy : Prop :=
  ∀ (initial : Input.State) (inputs : Nat → Input.Model) (horizon : Nat),
    HorizonDomain initial inputs horizon
    → ∀ t,
        t ≤ horizon
        → ∃ output,
            josephRun inputs initial t = .ok output
            ∧ StateInvariant output
            ∧ StateWithin covarianceBudget meanBudget (state 2 output)
                (exactRun 2 2 inputs (state 2 initial) t)
            ∧ (matrix 2 2 output.covariance).PosDef
            ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef

end
end Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
