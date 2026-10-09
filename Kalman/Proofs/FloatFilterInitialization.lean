import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FloatSquareRootError

/-! Native covariance-to-factor initialization, including its discrepancy from
the original decoded covariance. This error can seed the full-horizon theorem. -/

namespace Kalman.Proofs.FloatFilterInitialization

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Flare.Binary64.Value

theorem state_storage (n : Nat) (initial : Input.State) (h : initial.validate n = .ok ())
    : initial.mean.size = n
      ∧ initial.covariance.size = n * n
      ∧ initial.mean.all Float.isFinite = true
      ∧ initial.covariance.all Float.isFinite = true := by
  cases hs : (initial.mean.size == n && initial.covariance.size == n * n) with
  | false => simp [Input.State.validate, hs, bind, Except.bind] at h
  | true =>
      cases hf
            : (initial.mean.all Float.isFinite
                && initial.covariance.all Float.isFinite) with
      | false => simp [Input.State.validate, hs, hf] at h
      | true =>
          obtain ⟨hm, hp⟩ := Bool.and_eq_true_iff.mp hs
          obtain ⟨hmf, hpf⟩ := Bool.and_eq_true_iff.mp hf
          exact ⟨of_decide_eq_true hm, of_decide_eq_true hp, hmf, hpf⟩

/-- The checked initializer contributes a covariance radius and zero mean
error. A successful Cholesky operand profile is explicit; model-only Cholesky
success on every PD covariance is not asserted. -/
theorem fromCovariance_accuracy (input : Input.Model) (initial : Input.State)
    (lower : Array Float) (M δ D : ℝ)
    (p : FactorProfile input.stateDimension initial.covariance lower M δ D)
    (hinput : input.validate = .ok ())
    (hstate : initial.validate input.stateDimension = .ok ())
    (hsym : Input.symmetric input.stateDimension initial.covariance = true)
    : Kalman.Implementation.SquareRootFilter.fromCovariance input initial
        = .ok ⟨initial.mean, lower⟩
      ∧ FactorAccuracy
          (diagonalRadius input.stateDimension M
            + divisionRadius input.stateDimension M δ D)
          0 input.stateDimension ⟨initial.mean, lower⟩
          (state input.stateDimension initial) := by
  obtain ⟨hm, _, hmf, _⟩ := state_storage input.stateDimension initial hstate
  obtain ⟨hl, ht, _⟩ := FloatCholeskyFactor.cholesky_equations input.stateDimension
    initial.covariance lower p.execution
  have hp : FactorRecursion.LowerPositive (matrix input.stateDimension input.stateDimension lower) := by
    constructor
    · intro i j hij
      change value (entry input.stateDimension lower i.val j.val) = 0
      rw [ht i.val j.val i.isLt j.isLt hij]
      exact Flare.Binary64.Arithmetic.zero_value
    · intro i
      exact p.diagonal_lower.trans_le (p.diagonal_floor i.val i.isLt)
  refine ⟨
    ?_,
    FloatFactorValidity.factor_validate_complete input.stateDimension _ hm hl hmf
      p.finite_lower hp,
    FloatCholeskyFactor.factor_backward_error _ _ _ _ _ _ p,
    le_rfl,
    ?_
  ⟩
  · simp [Kalman.Implementation.SquareRootFilter.fromCovariance, hinput, hstate, hsym,
      p.execution, bind, Except.bind, pure, Except.pure]
  · intro i
    simp [state]

end Kalman.Proofs.FloatFilterInitialization
