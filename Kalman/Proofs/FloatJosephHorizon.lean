import Kalman.Proofs.FloatJosephFilter
import Kalman.Proofs.FloatObservableHorizon

/-! Complete original-input accuracy for repeated checked direct-Joseph steps.
Native storage invariance and the independent ideal invariant are established
separately; covariance/mean error recurrences then close uniform budgets. -/

namespace Kalman.Proofs.FloatJosephHorizon

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
open Kalman.Proofs.DiagonalStages.Horizon (transition processVariance measurementVariance)
open Kalman.Definitions.Theorems.RecursionSensitivity

/-! ----------------------------------------------------------------------
## Original initialization and independent reference
-------------------------------------------------------------------------- -/

/-- Dense initialization preserves the original words exactly. -/
theorem initial_invariant (initial : Input.State) (d : InitializationDomain initial)
    : StateInvariant initial := by
  exact ⟨
    d.mean_size,
    d.covariance.covariance.size,
    d.mean_finite,
    d.covariance.covariance.finite,
    d.covariance.diagonal,
    fun i =>
      (by norm_num : (7 : ℝ) / 16 ≤ 1).trans
        (d.covariance.covariance.diagonal_lower i.val i.isLt),
    fun i => (d.covariance.diagonal_cap i.val i.isLt).trans (by norm_num),
    fun i hi => (d.mean_bound i hi).trans (by norm_num)
  ⟩

/-- Independent ideal invariance uses original inputs, without a native trace. -/
theorem exact_run_invariant (initial : Input.State) (inputs : Nat → Input.Model)
    (horizon : Nat) (d : HorizonDomain initial inputs horizon)
    : ∀ t,
        t ≤ horizon
        → DiagonalStateInvariant (exactRun 2 2 inputs (state 2 initial) t) := by
  intro t ht
  induction t with
  | zero =>
      exact FloatObservableInitialization.exact_initial_invariant initial d.initial_state
  | succ t ih =>
      rw [exactRun, RealObservableHorizon.model_diagonal (inputs t) (d.models t (by omega))]
      exact (RealObservableInvariant.step_invariant .joseph _ _ _ _ _
              (RealObservableHorizon.model_domain (inputs t)
                (d.models t (by omega))) (ih (by omega))).1

/-! ----------------------------------------------------------------------
## Coupled one-step error propagation
-------------------------------------------------------------------------- -/

/-- Both complete scalar recurrences fit the public uniform budgets. -/
theorem uniform_budget_caps
    : (2 : ℝ) ^ (-32 : Int) + 9 / 25 * covarianceBudget ≤ covarianceBudget
      ∧ (2 : ℝ) ^ (-32 : Int) + (3 / 5 * meanBudget + 1 / 2 * covarianceBudget)
        ≤ meanBudget := by
  norm_num [covarianceBudget, meanBudget]

/-- Accumulate one checked native step against the independent exact state,
including the covariance-dependent gain change in the mean recurrence. -/
theorem step_accumulated_accuracy (input : Input.Model) (current : Input.State)
    (reference : LinearModel.State 2) (p : ModelDomain input) (s : StateInvariant current)
    (r : DiagonalStateInvariant reference)
    (he : StateWithin covarianceBudget meanBudget (state 2 current) reference)
    : ∃ output,
        Kalman.Implementation.CovarianceFilter.step .joseph input current = .ok output
        ∧ StateInvariant output
        ∧ StateWithin covarianceBudget meanBudget (state 2 output)
            (CovarianceRecursion.step .joseph (model (atDimensions 2 2 input)) reference
              (vector 2 input.measurement))
        ∧ (matrix 2 2 output.covariance).PosDef := by
  obtain ⟨output, ho, so, hl⟩ := FloatJosephFilter.step_accuracy input current p s
  have da : (state 2 current).covariance = diagonal (fun i => (state 2 current).covariance i i) :=
    FloatDiagonalStorage.matrix_diagonal 2 current.covariance s.diagonal
  have hp : ∀ i, 0 ≤ (state 2 current).covariance i i :=
    fun i => (by norm_num : (0 : ℝ) ≤ 7 / 16).trans (s.covariance_floor i)
  have propagated := RealObservableSensitivity.step_sensitivity .joseph (transition input)
    (processVariance input) (measurementVariance input) (vector 2 input.measurement)
    (state 2 current) reference covarianceBudget meanBudget
    (RealObservableHorizon.model_domain input p) da hp r he
  rw [← RealObservableHorizon.model_diagonal input p] at propagated
  have joined := FloatFullFilter.stateWithin_trans hl propagated
  refine ⟨
    output,
    ho,
    so,
    ⟨
      ⟨
        by unfold covarianceBudget; positivity,
        fun i j => (joined.1.2 i j).trans uniform_budget_caps.1
      ⟩,
      by unfold meanBudget; positivity,
      fun i => (joined.2.2 i).trans uniform_budget_caps.2
    ⟩,
    FloatJosephUpdate.invariant_positive output so
  ⟩

/-! ----------------------------------------------------------------------
## Complete original-input native horizon
-------------------------------------------------------------------------- -/

/-- Every finite prefix of repeated checked direct-Joseph steps succeeds and
has uniform original-input covariance/mean errors 2^-30/2^-29, with positive
native and exact covariances, including identity and sign-reversing dynamics. -/
theorem initialized_horizon_accuracy (initial : Input.State) (inputs : Nat → Input.Model)
    (horizon : Nat) (d : HorizonDomain initial inputs horizon)
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            josephRun inputs initial t = .ok output
            ∧ StateInvariant output
            ∧ StateWithin covarianceBudget meanBudget (state 2 output)
                (exactRun 2 2 inputs (state 2 initial) t)
            ∧ (matrix 2 2 output.covariance).PosDef
            ∧ (exactRun 2 2 inputs (state 2 initial) t).covariance.PosDef := by
  intro t ht
  induction t with
  | zero =>
      have si := initial_invariant initial d.initial_state
      refine ⟨
        initial,
        rfl,
        si,
        ?_,
        FloatJosephUpdate.invariant_positive initial si,
        RealObservableInvariant.covariance_positive _
          (exact_run_invariant initial inputs horizon d 0 (by omega))
      ⟩
      refine ⟨
        ⟨by unfold covarianceBudget; positivity, ?_⟩,
        by unfold meanBudget; positivity,
        ?_
      ⟩
      · intro i j
        simp only [exactRun, sub_self, abs_zero]
        unfold covarianceBudget
        positivity
      · intro i
        simp only [exactRun, sub_self, abs_zero]
        unfold meanBudget
        positivity
  | succ t ih =>
      obtain ⟨current, hc, sc, ac, _, _⟩ := ih (by omega)
      have rc := exact_run_invariant initial inputs horizon d t (by omega)
      obtain ⟨output, ho, so, ao, hp⟩ := step_accumulated_accuracy (inputs t) current _
        (d.models t (by omega)) sc rc ac
      refine ⟨
        output,
        ?_,
        so,
        ao,
        hp,
        RealObservableInvariant.covariance_positive _
          (exact_run_invariant initial inputs horizon d (t + 1) ht)
      ⟩
      simp [josephRun, hc, ho, bind, Except.bind]

/-! ----------------------------------------------------------------------
## Nontrivial original-input witnesses
-------------------------------------------------------------------------- -/

/-- Identity dynamics with nonzero means/measurements inhabit every horizon. -/
theorem identity_domain_nonempty (horizon : Nat)
    : ∃ input : Input.Model,
      ∃ initial : Input.State,
        HorizonDomain initial (fun _ => input) horizon
        ∧ input.transition = identity 2
        ∧ initial.covariance = identity 2
        ∧ initial.mean = #[1.0, -1.0] := by
  obtain ⟨input, initial, d, hF, hP, hx⟩ := FloatObservableHorizon.identity_domain_nonempty horizon
  exact ⟨input, initial, ⟨d.initial_state, d.models⟩, hF, hP, hx⟩

/-- Near-unit and sign-reversing original transition words also qualify. -/
theorem near_identity_domain_nonempty (horizon : Nat)
    : ∃ input : Input.Model,
      ∃ initial : Input.State,
        HorizonDomain initial (fun _ => input) horizon
        ∧ input.transition = #[0.9990234375, -0.0, 0.0, -1.0]
        ∧ initial.covariance = identity 2
        ∧ initial.mean = #[1.0, -1.0] := by
  obtain ⟨input, initial, d, hF, hP, hx⟩ := FloatObservableHorizon.near_identity_domain_nonempty horizon
  exact ⟨input, initial, ⟨d.initial_state, d.models⟩, hF, hP, hx⟩

/-- Proof witness for the public completed horizon statement. -/
theorem initializedHorizonAccuracy : HorizonAccuracy := by
  intro initial inputs horizon d
  exact initialized_horizon_accuracy initial inputs horizon d

end Kalman.Proofs.FloatJosephHorizon
