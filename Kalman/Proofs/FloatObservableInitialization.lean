import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.SquareRootProfiles
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Proofs.FloatObservableFilter
import Kalman.Proofs.FloatCholeskySolveDomain

/-! Checked initialization from the original finite dense covariance and mean.
Every validator, Cholesky run, returned invariant and initial error is derived. -/

namespace Kalman.Proofs.FloatObservableInitialization

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.DiagonalStages
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Flare.Binary64.Value

/-- The independent ideal initial state uses the original covariance, not the
Gram of the rounded Cholesky factor. -/
theorem exact_initial_invariant (initial : Input.State) (d : InitializationDomain initial)
    : Kalman.Definitions.Theorems.RecursionSensitivity.DiagonalStateInvariant
        (state 2 initial) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change matrix 2 2 initial.covariance = diagonal (fun i => matrix 2 2 initial.covariance i i)
    exact FloatDiagonalStorage.matrix_diagonal 2 initial.covariance d.covariance.diagonal
  · intro i
    exact (by norm_num : (1 : ℝ) / 2 ≤ 1).trans (d.covariance.covariance.diagonal_lower i.val i.isLt)
  · intro i
    exact d.covariance.diagonal_cap i.val i.isLt
  · intro i
    exact d.mean_bound i.val i.isLt

/-- Original dense initialization derives the complete native invariant,
strict positivity and covariance/mean errors 2^-42 / zero. -/
theorem initialize_invariant (input : Input.Model) (initial : Input.State)
    (p : ModelDomain input) (d : InitializationDomain initial)
    : ∃ retained,
        Kalman.Implementation.SquareRootFilter.fromCovariance input initial = .ok retained
        ∧ StateInvariant retained
        ∧ FactorAccuracy ((2 : ℝ) ^ (-42 : Int)) 0 2 retained (state 2 initial)
        ∧ (state 2 initial).covariance.PosDef := by
  obtain ⟨l, hls, hl, hlf, hlp, hpd, _, hf, he⟩ :=
    FloatCholeskyDomain.cholesky_accuracy initial.covariance d.covariance.covariance
  have hv := FloatFactorValidity.factor_validate_complete 2 ⟨initial.mean, l⟩
    d.mean_size hls d.mean_finite hlf hlp
  have hs : initial.validate 2 = .ok () := by
    have hshape : (initial.mean.size == 2 && initial.covariance.size == 2 * 2) = true := by
      simp [d.mean_size, d.covariance.covariance.size]
    have hfinite : (initial.mean.all Float.isFinite && initial.covariance.all Float.isFinite) = true := by
      simp [d.mean_finite, d.covariance.covariance.finite]
    simp [Input.State.validate, hshape, hfinite, pure, Except.pure]
  have hs' : initial.validate input.stateDimension = .ok () := by
    simpa only [p.state_dimension] using hs
  have hln : cholesky input.stateDimension initial.covariance = .ok l := by
    simpa only [p.state_dimension] using hl
  have hsym : Input.symmetric input.stateDimension initial.covariance = true := by
    simpa only [p.state_dimension]
      using FloatCholeskyDomain.input_symmetric initial.covariance d.covariance.covariance
  have hr : Kalman.Implementation.SquareRootFilter.fromCovariance input initial = .ok ⟨initial.mean, l⟩ := by
    simp [Kalman.Implementation.SquareRootFilter.fromCovariance,
      FloatObservableFilter.input_validate input p, hs', hsym, hln,
      bind, Except.bind, pure, Except.pure]
  have hd := FloatDiagonalStorage.cholesky_diagonal_two initial.covariance
    d.covariance.covariance d.covariance.diagonal l hl
  have hb := FloatCholeskySolveDomain.factor_domain_of_cholesky initial.covariance l
    d.covariance.covariance hl
  have hcap : ∀ i, FactorRecursion.gram (matrix 2 2 l) i i ≤ 13 / 8 := by
    intro i
    have h := (abs_le.mp (he.2 i i)).2
    have hi := d.covariance.diagonal_cap i.val i.isLt
    change matrix 2 2 initial.covariance i i ≤ 3 / 2 at hi
    change FactorRecursion.gram (matrix 2 2 l) i i - matrix 2 2 initial.covariance i i
      ≤ (2 : ℝ)^(-42 : Int) at h
    norm_num at h
    linarith
  have hfloor : (FactorRecursion.gram (matrix 2 2 l) - (7 / 16 : ℝ) • 1).PosSemidef := by
    convert hf.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 16)) using 1
    unfold FactorRecursion.gram
    module
  have ha : FactorAccuracy ((2 : ℝ)^(-42 : Int)) 0 2 ⟨initial.mean, l⟩ (state 2 initial) := by
    refine ⟨hv, he, le_rfl, ?_⟩
    intro i
    simp [state]
  exact ⟨
    _,
    hr,
    ⟨
      d.mean_size,
      hls,
      d.mean_finite,
      hlf,
      hlp,
      hd,
      hb.entry_bound,
      hfloor,
      hcap,
      fun i hi => (d.mean_bound i hi).trans (by norm_num)
    ⟩,
    ha,
    hpd
  ⟩

/-- Identity covariance and signed nonzero means inhabit dense initialization. -/
theorem identity_domain_nonempty
    : InitializationDomain (⟨#[1.0, -1.0], identity 2⟩ : Input.State) := by
  have hn := (Flare.Binary64.Order.neg_value (1.0 : Float) (by decide +kernel)).2
  refine ⟨FloatObservablePrediction.identity_noise, by decide, by decide +kernel, ?_⟩
  intro i hi
  interval_cases i <;> norm_num [Flare.Binary64.Arithmetic.one_value, hn]

end Kalman.Proofs.FloatObservableInitialization
