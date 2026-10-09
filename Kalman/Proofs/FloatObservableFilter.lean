import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Proofs.RealObservableCorrection
import Kalman.Proofs.FloatObservablePosterior
import Kalman.Proofs.FloatFilterHorizon

/-! Complete checked native filtering at full observation and diagonal dynamics
up to magnitude one. Original inputs derive validation, every stage, accuracy
against the ideal step of the same incoming state, and the retained invariant.
No independently accumulated trajectory error is claimed by the local theorem. -/

namespace Kalman.Proofs.FloatObservableFilter

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.DiagonalStages
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Implementation.Correctness.InputInterpretation (atDimensions)
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1000000

/-- All public model checks follow from the original stored domain. -/
theorem input_validate (input : Input.Model) (p : ModelDomain input)
    : input.validate = .ok () := by
  have hq := FloatCholeskyDomain.input_symmetric input.processNoise p.process_noise.covariance
  have hr := FloatCholeskyDomain.input_symmetric input.measurementNoise p.noise.covariance
  have hd : (0 < input.stateDimension && input.stateDimension ≤ 32
      && 0 < input.measurementDimension && input.measurementDimension ≤ 32) = true := by
    simp [p.state_dimension, p.measurement_dimension]
  have hs : (input.transition.size == input.stateDimension * input.stateDimension
      && input.observation.size == input.measurementDimension * input.stateDimension
      && input.processNoise.size == input.stateDimension * input.stateDimension
      && input.measurementNoise.size == input.measurementDimension * input.measurementDimension
      && input.measurement.size == input.measurementDimension) = true := by
    simp [p.state_dimension, p.measurement_dimension, p.transition_size, p.observation_size,
      p.process_noise.covariance.size, p.noise.covariance.size, p.measurement_size]
  have hsym : (Input.symmetric input.stateDimension input.processNoise
      && Input.symmetric input.measurementDimension input.measurementNoise) = true := by
    simp [p.state_dimension, p.measurement_dimension, hq, hr]
  have hf : #[input.transition, input.observation, input.processNoise,
      input.measurementNoise, input.measurement].all (fun a => a.all Float.isFinite) = true := by
    rw [Array.all_eq_true]
    intro i hi
    change i < 5 at hi
    interval_cases i
    · exact p.transition_finite
    · exact p.observation_finite
    · exact p.process_noise.covariance.finite
    · exact p.noise.covariance.finite
    · exact p.measurement_finite
  simp only [Input.Model.validate, hd, hs, hf, hsym, ↓reduceIte, pure, Except.pure]

theorem factor_validate (initial : Input.FactorState) (s : StateInvariant initial)
    : initial.validate 2 = .ok () :=
  (FloatFactorValidity.factor_validate_complete 2 initial s.mean_size s.factor_size
    s.mean_finite s.factor_finite s.lower_positive).1

theorem prediction_domain (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : Kalman.Proofs.DiagonalStages.Prediction.TwoStateDomain input initial :=
  ⟨
    p.state_dimension,
    p.transition_size,
    p.transition_finite,
    p.transition_diagonal,
    p.transition_bound,
    s.factor_size,
    s.factor_finite,
    s.factor_bound,
    s.covariance_diagonal_cap,
    p.process_noise,
    s.mean_size,
    s.mean_finite,
    s.mean_bound
  ⟩

/-- The original inputs derive the reached correction domain and retain the
sharp prediction allowance. Fixed dimension metadata does not alter any word. -/
theorem reached_correction_domain (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : ∃ prior,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok prior
        ∧ FactorAccuracy (7 * (2 : ℝ) ^ (-32 : Int)) ((2 : ℝ) ^ (-46 : Int)) 2 prior
            (CovarianceRecursion.predict (model (atDimensions 2 2 input))
              (factorState 2 initial))
        ∧ Kalman.Proofs.DiagonalStages.Mean.TwoStateDomain input prior := by
  let a := atDimensions 2 2 input
  have had : a = input := FloatFilterHorizon.atDimensions_eq 2 2 input p.state_dimension p.measurement_dimension
  have pa : ModelDomain a := had.symm ▸ p
  have pd := prediction_domain a initial pa s
  obtain ⟨prior, hr, _, dc⟩ := FloatObservableMean.prediction_correction_domain a initial pd
    pa.toObservationInputs s.diagonal pa.measurement_size pa.measurement_finite pa.measurement_bound
  obtain ⟨prior', hr', ha, _, _, _, _⟩ := FloatObservablePrediction.prediction_accuracy_sharp a initial pd
  have eq : prior' = prior := Except.ok.inj (hr'.symm.trans hr)
  subst prior'
  exact ⟨prior, by simpa only [had] using hr, ha, had ▸ dc⟩

/-- Exact prediction from the same stored state remains diagonal, has floor
one and mean cap 9/8. No independently bounded reference state is assumed. -/
theorem exact_prediction_bounds (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : let prior :=
        CovarianceRecursion.predict (model (atDimensions 2 2 input))
          (factorState 2 initial)
      prior.covariance = diagonal (fun i => prior.covariance i i)
      ∧ (∀ i, 1 ≤ prior.covariance i i)
      ∧ (∀ i, |prior.mean i| ≤ 9 / 8) := by
  have hF := FloatDiagonalStorage.matrix_diagonal 2 input.transition p.transition_diagonal
  have hQ := FloatDiagonalStorage.matrix_diagonal 2 input.processNoise p.process_noise.diagonal
  have hP : FactorRecursion.gram (matrix 2 2 initial.lower)
      = diagonal (fun i => FactorRecursion.gram (matrix 2 2 initial.lower) i i) := by
    rw [FloatDiagonalStorage.gram_diagonal 2 initial.lower s.diagonal]
    simp only [diagonal_apply_eq]
  have he := RealObservableCorrection.predict_eq_diagonal (model (atDimensions 2 2 input))
    (factorState 2 initial) _ _ _ hF hQ hP
  dsimp only
  rw [he]
  refine ⟨by simp only [DiagonalObservation.state, diagonal_apply_eq], ?_, ?_⟩
  · intro i
    simp only [DiagonalObservation.state, diagonal_apply_eq, DiagonalObservation.priorVariance]
    have hp := (CovarianceStructure.gram_posSemidef (matrix 2 2 initial.lower)).diag_nonneg (i := i)
    have hq := p.process_noise.covariance.diagonal_lower i.val i.isLt
    change 1 ≤ matrix 2 2 input.processNoise i i at hq
    linarith [mul_nonneg (sq_nonneg (matrix 2 2 input.transition i i)) hp]
  · intro i
    change |matrix 2 2 input.transition i i * vector 2 initial.mean i| ≤ 9 / 8
    rw [abs_mul]
    have hf : |matrix 2 2 input.transition i i| ≤ 1 := p.transition_bound i.val i.val i.isLt i.isLt
    have hx : |vector 2 initial.mean i| ≤ 9 / 8 := s.mean_bound i.val i.isLt
    exact (mul_le_mul hf hx (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans (by norm_num)

theorem local_radius_caps
    : localCovarianceRadius ≤ 3 * (2 : ℝ) ^ (-30 : Int)
      ∧ localMeanRadius ≤ localJointRadius
      ∧ 2 * (3 * (2 : ℝ) ^ (-30 : Int)) ≤ localJointRadius := by
  norm_num [localCovarianceRadius, localMeanRadius, localJointRadius]

/-- Complete checked step and invariant preservation from original inputs.
The accuracy comparator is the exact full step of the same incoming stored
factor/mean, and includes prediction error propagated through the changed gain.
Covariance error is at most 3·2^-30 and mean/joint error at most 5·2^-28. -/
theorem step_accuracy_and_invariant (input : Input.Model) (initial : Input.FactorState)
    (p : ModelDomain input) (s : StateInvariant initial)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.step input initial = .ok output
        ∧ StateInvariant output
        ∧ FactorAccuracy (3 * (2 : ℝ) ^ (-30 : Int)) localJointRadius 2 output
            (exactStep input initial)
        ∧ (factorState 2 output).covariance.PosDef
        ∧ Kalman.Definitions.Theorems.RecursionSensitivity.DiagonalJointWithin
            localJointRadius (factorState 2 output) (exactStep input initial) := by
  let a := atDimensions 2 2 input
  have had : a = input := FloatFilterHorizon.atDimensions_eq 2 2 input p.state_dimension p.measurement_dimension
  have pa : ModelDomain a := had.symm ▸ p
  obtain ⟨prior, hpred, ep, dc⟩ := reached_correction_domain a initial pa s
  obtain ⟨output, hcorr, ec, dd, hpd, hfloor, hcap, hfactor, hmean⟩ :=
    FloatObservablePosterior.correction_accuracy_and_bounds_sharp a prior dc
  let ideal := CovarianceRecursion.predict (model a) (factorState 2 initial)
  have hb := exact_prediction_bounds a initial pa s
  change ideal.covariance = diagonal (fun i => ideal.covariance i i)
    ∧ (∀ i, 1 ≤ ideal.covariance i i) ∧ (∀ i, |ideal.mean i| ≤ 9 / 8) at hb
  have da : (factorState 2 prior).covariance
      = diagonal (fun i => (factorState 2 prior).covariance i i) := by
    change FactorRecursion.gram (matrix 2 2 prior.lower)
      = diagonal (fun i => FactorRecursion.gram (matrix 2 2 prior.lower) i i)
    rw [FloatDiagonalStorage.gram_diagonal 2 prior.lower dc.diagonal]
    simp only [diagonal_apply_eq]
  have ha : ∀ i, 15 / 16 ≤ (factorState 2 prior).covariance i i := by
    intro i
    change 15 / 16 ≤ FactorRecursion.gram (matrix 2 2 prior.lower) i i
    have hf := dc.covariance_floor.diag_nonneg (i := i)
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one, sub_nonneg] using hf
  have hR : (model a).measurementNoise = diagonal (fun i => matrix 2 2 a.measurementNoise i i) :=
    FloatDiagonalStorage.matrix_diagonal 2 a.measurementNoise pa.noise.diagonal
  have er := RealObservableCorrection.update_sensitivity (model a) (factorState 2 prior) ideal
    (vector 2 a.measurement) (fun i => matrix 2 2 a.measurementNoise i i)
    (7 * (2 : ℝ)^(-32 : Int)) ((2 : ℝ)^(-46 : Int)) pa.observation_identity hR da hb.1 ha
    (fun i => (by norm_num : (15 : ℝ) / 16 ≤ 1).trans (hb.2.1 i))
    (fun i => pa.noise.covariance.diagonal_lower i.val i.isLt)
    (fun i => pa.noise.diagonal_cap i.val i.isLt) hb.2.2
    (fun i => pa.measurement_bound i.val i.isLt)
    (FloatFullFilter.factorAccuracy_stateWithin ep)
  have eo := FloatFullFilter.stateWithin_trans (FloatFullFilter.factorAccuracy_stateWithin ec) er
  have eo' : StateWithin localCovarianceRadius localMeanRadius
      (factorState 2 output) (exactStep input initial) := by
    simpa only [localCovarianceRadius, localMeanRadius, exactStep,
      CovarianceRecursion.step, add_assoc, a, atDimensions, ideal]
      using eo
  have acc : FactorAccuracy (3 * (2 : ℝ)^(-30 : Int)) localJointRadius 2 output (exactStep input initial) :=
    ⟨ec.1, ⟨by positivity, fun i j => (eo'.1.2 i j).trans local_radius_caps.1⟩,
      by unfold localJointRadius; positivity, fun i => (eo'.2.2 i).trans local_radius_caps.2.1⟩
  obtain ⟨hms, hls, hmf, hlf⟩ := FloatObservablePrediction.factor_storage output ec.1.1
  have sout : StateInvariant output := ⟨hms, hls, hmf, hlf, ec.1.2, dd,
    fun i j hi hj => (hfactor i j hi hj).trans (by norm_num), hfloor,
    fun i => (hcap i).trans (by norm_num), hmean⟩
  have hin : initial.validate a.stateDimension = .ok () := factor_validate initial s
  have hr : Kalman.Implementation.SquareRootFilter.step a initial = .ok output := by
    simp [Kalman.Implementation.SquareRootFilter.step, input_validate a pa, hin,
      hpred, hcorr, ec.1.1, bind, Except.bind, pure, Except.pure]
  refine ⟨output, by simpa only [had] using hr, sout, acc, hpd, ?_⟩
  refine ⟨⟨by unfold localJointRadius; positivity, ?_⟩, acc.2.2⟩
  intro i j
  exact (acc.2.1.2 i j).trans (by norm_num [localJointRadius])

/-- Every finite native prefix succeeds and retains the same stored invariant
and strict-PD exact covariance. This is execution/invariance, separately from
accumulated accuracy against an independent ideal trajectory. -/
theorem run_invariant (inputs : Nat → Input.Model) (initial : Input.FactorState)
    (horizon : Nat) (p : ∀ t, t < horizon → ModelDomain (inputs t))
    (s : StateInvariant initial)
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            Kalman.Implementation.SquareRootFilter.run inputs initial t = .ok output
            ∧ StateInvariant output
            ∧ (factorState 2 output).covariance.PosDef := by
  intro t ht
  induction t with
  | zero =>
      exact ⟨initial, rfl, s, FactorStructure.lowerPositive_gram_posDef _ s.lower_positive⟩
  | succ t ih =>
      obtain ⟨current, hr, sc, _⟩ := ih (by omega)
      obtain ⟨output, hs, so, _, hp, _⟩ := step_accuracy_and_invariant (inputs t) current (p t (by omega)) sc
      exact ⟨
        output,
        by simp [Kalman.Implementation.SquareRootFilter.run, hr, hs,
          bind, Except.bind],
        so,
        hp
      ⟩

/-- Nonzero identity dynamics and signed, nonzero mean/measurement words
inhabit the complete original-input domain. -/
theorem identity_domain_nonempty
    : ∃ input : Input.Model,
      ∃ initial : Input.FactorState,
        ModelDomain input
        ∧ StateInvariant initial
        ∧ input.transition = identity 2
        ∧ initial.mean = #[1.0, -1.0]
        ∧ input.measurement = #[-1.0, 1.0] := by
  let input : Input.Model := ⟨2, 2, identity 2, identity 2, identity 2, identity 2, #[-1.0, 1.0]⟩
  let initial : Input.FactorState := ⟨#[1.0, -1.0], identity 2⟩
  have hi : matrix 2 2 (identity 2) = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
    Flare.Matrix.JacobiInitialization.identity_matrix 2
  have hn := (Flare.Binary64.Order.neg_value (1.0 : Float) (by decide +kernel)).2
  have hd : Kalman.Implementation.Correctness.InputInterpretation.DecodedDiagonal 2 (identity 2) := by
    intro i j hi' hj hij
    change matrix 2 2 (identity 2) ⟨i, hi'⟩ ⟨j, hj⟩ = 0
    rw [hi]
    exact Matrix.one_apply_ne (fun h => hij (congrArg Fin.val h))
  have hid : ∀ i j, i < 2 → j < 2 → |value (entry 2 (identity 2) i j)| ≤ 1 := by
    intro i j hi' hj
    change |matrix 2 2 (identity 2) ⟨i, hi'⟩ ⟨j, hj⟩| ≤ 1
    rw [hi]
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have ho : Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.ObservationInputs input :=
    ⟨rfl, Flare.Matrix.JacobiInitialization.identity_size 2,
      Flare.Matrix.JacobiInitialization.identity_finite 2, hi, FloatObservablePrediction.identity_noise⟩
  refine ⟨input, initial, ?_, ?_, rfl, rfl, rfl⟩
  · refine ⟨ho, rfl, Flare.Matrix.JacobiInitialization.identity_size 2,
      Flare.Matrix.JacobiInitialization.identity_finite 2, hd, hid,
      FloatObservablePrediction.identity_noise, by decide, by decide +kernel, ?_⟩
    intro i hlt
    interval_cases i <;> norm_num [input, Flare.Binary64.Arithmetic.one_value, hn]
  · refine ⟨by decide, Flare.Matrix.JacobiInitialization.identity_size 2, by decide +kernel,
      Flare.Matrix.JacobiInitialization.identity_finite 2, ?_, hd,
      fun i j hi' hj => (hid i j hi' hj).trans (by norm_num), ?_, ?_, ?_⟩
    · change FactorRecursion.LowerPositive (matrix 2 2 (identity 2))
      rw [hi]
      constructor
      · intro i j hij
        exact Matrix.one_apply_ne (fun h => by subst j; simp at hij)
      · intro i
        simp
    · have he : FactorRecursion.gram (matrix 2 2 initial.lower) = 1 := by
        simp [initial, FactorRecursion.gram, hi]
      rw [he]
      convert (Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul (by norm_num : 0 ≤ (9 : ℝ) / 16) using 1
      norm_num
      module
    · intro i
      norm_num [initial, FactorRecursion.gram, hi]
    · intro i hlt
      interval_cases i <;> norm_num [initial, Flare.Binary64.Arithmetic.one_value, hn]

end Kalman.Proofs.FloatObservableFilter
