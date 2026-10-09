import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Proofs.FloatSquareRootUpdate
import Kalman.Proofs.RecursionSensitivity

/-! Native full-step accuracy against a single independently supplied exact
state. Incoming error, prediction, imperfect gain, mean and Joseph QR compose. -/

namespace Kalman.Proofs.FloatFullFilter

open Matrix
open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.FilterComposition
open Kalman.Proofs.ErrorPropagation

theorem stateWithin_trans {n : Nat} {a b c : LinearModel.State n} {eP eX fP fX : ℝ}
    (hab : StateWithin eP eX a b) (hbc : StateWithin fP fX b c)
    : StateWithin (eP + fP) (eX + fX) a c :=
  ⟨
    within_trans hab.1 hbc.1,
    add_nonneg hab.2.1 hbc.2.1,
    fun i => (abs_sub_le _ _ _).trans (add_le_add (hab.2.2 i) (hbc.2.2 i))
  ⟩

theorem factorAccuracy_stateWithin {n : Nat} {output : Input.FactorState}
    {reference : LinearModel.State n} {eP eX : ℝ}
    (h : FactorAccuracy eP eX n output reference)
    : StateWithin eP eX (factorState n output) reference :=
  ⟨h.2.1, h.2.2⟩

/-- Complete checked step succeeds on its operand domain, and propagates both
incoming errors to the exact step from the reference. No gain error, covariance
error or mean error of the returned state is a premise. -/
theorem step_accuracy (input : Input.Model) (initial : Input.FactorState)
    (reference : LinearModel.State input.stateDimension)
    (p : StepProfile input initial) (d : StepEnvironment input reference) (eP eX : ℝ)
    (hinput : input.validate = .ok ())
    (hinitial
      : Kalman.Implementation.Correctness.SquareRootFilterProperties.ValidFactor
          input.stateDimension initial)
    (href : reference.covariance.PosSemidef)
    (he : StateWithin eP eX (factorState input.stateDimension initial) reference)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.step input initial = .ok output
        ∧ FactorAccuracy (stepCovarianceRadius p d eP) (stepMeanRadius p d eP eX)
            input.stateDimension output
            (CovarianceRecursion.step .joseph (model input) reference
              (vector input.measurementDimension input.measurement)) := by
  let n := input.stateDimension
  let m := input.measurementDimension
  let refPrior := CovarianceRecursion.predict (model input) reference
  obtain ⟨prior, hprior, ep⟩ := FloatSquareRootError.prediction_accuracy input initial p.prediction
  have hstored : Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok (predicted p) := by
    simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, predicted,
      p.prediction.noise.execution, p.prediction.computeProduct, p.computeQR,
      p.prediction.computeMean, bind, Except.bind, pure, Except.pure]
  have heq : prior = predicted p := Except.ok.inj (hprior.symm.trans hstored)
  subst prior
  have es := RecursionSensitivity.predict_sensitivity (model input)
    (factorState n initial) reference p.prediction.transitionBound eP eX
    p.prediction.transition_nonneg p.prediction.transition_magnitude he
  have eprior : StateWithin (predictedCovarianceRadius p eP) (predictedMeanRadius p eX)
      (factorState n (predicted p)) refPrior := stateWithin_trans (factorAccuracy_stateWithin ep) es
  have hpr : refPrior.covariance.PosSemidef := by
    have h := href.mul_mul_conjTranspose_same (model input).transition
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h.add d.process_psd
  have hpa := CovarianceStructure.gram_posSemidef (matrix n n (predicted p).lower)
  have hP := d.covariance_nonneg
  have hH := p.innovation.observation_nonneg
  have hep := eprior.1.1
  have hex := eprior.2.1
  let P := d.covarianceBound + predictedCovarianceRadius p eP
  let K := gainMagnitude n m d.noiseFloor P p.innovation.observationBound
  let Z := d.innovationBound + n * p.innovation.observationBound * predictedMeanRadius p eX
  have hP' : 0 ≤ P := add_nonneg hP hep
  have hα := d.floor_positive
  have hK : 0 ≤ K := by dsimp [K, gainMagnitude]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; exact add_nonneg d.innovation_nonneg (by positivity)
  have hb : ∀ i j, |(factorState n (predicted p)).covariance i j| ≤ P := by
    intro i j
    calc
      _ = |((factorState n (predicted p)).covariance i j - refPrior.covariance i j)
            + refPrior.covariance i j| := by
        congr 1; ring
      _ ≤ |(factorState n (predicted p)).covariance i j - refPrior.covariance i j|
          + |refPrior.covariance i j| :=
        abs_add_le _ _
      _ ≤ predictedCovarianceRadius p eP + d.covarianceBound :=
        add_le_add (eprior.1.2 i j) (d.covariance_magnitude i j)
      _ = _ := add_comm _ _
  have hk := RecursionSensitivity.gain_magnitude (model input) (factorState n (predicted p))
    d.noiseFloor P p.innovation.observationBound d.floor_positive hP' hH hpa d.noise_lower
    hb p.innovation.observation_magnitude
  have ez := within_mul_left (model input).observation
    (show EntrywiseWithin (predictedMeanRadius p eX)
      (fun i (_ : Fin 1) => (factorState n (predicted p)).mean i)
      (fun i (_ : Fin 1) => refPrior.mean i) from ⟨hex, fun i _ => eprior.2.2 i⟩)
    hH p.innovation.observation_magnitude
  have hz : ∀ i, |CovarianceRecursion.innovation (model input) (factorState n (predicted p))
      (vector m input.measurement) i| ≤ Z := by
    intro i
    have ed := ez.2 i 0
    change |((model input).observation *ᵥ (factorState n (predicted p)).mean) i
      - ((model input).observation *ᵥ refPrior.mean) i| ≤ _ at ed
    have er := d.innovation_magnitude i
    dsimp only [CovarianceRecursion.innovation] at er ⊢
    change _ ≤ d.innovationBound + n * p.innovation.observationBound * predictedMeanRadius p eX
    calc
      _ = |((vector m input.measurement - (model input).observation *ᵥ refPrior.mean) i)
            - (((model input).observation *ᵥ (factorState n (predicted p)).mean) i
                - ((model input).observation *ᵥ refPrior.mean) i)| := by
        congr 1; simp only [Pi.sub_apply]; ring
      _ ≤ _ := (abs_sub _ _).trans (add_le_add er ed)
  obtain ⟨output, houtput, ea⟩ := FloatSquareRootUpdate.update_accuracy input (predicted p)
    p.innovation p.gain p.mean p.posterior d.noiseFloor P d.noiseBound K Z
    d.floor_positive hP' d.noise_nonneg hK hZ d.noise_lower hb d.noise_magnitude hk hz
  have ec := RecursionSensitivity.update_sensitivity (model input) (factorState n (predicted p))
    refPrior (vector m input.measurement) d.noiseFloor d.covarianceBound d.noiseBound
    p.innovation.observationBound d.innovationBound _ _ d.floor_positive d.covariance_nonneg
    d.noise_nonneg hH d.innovation_nonneg hpa hpr d.noise_lower d.covariance_magnitude
    d.noise_magnitude p.innovation.observation_magnitude d.innovation_magnitude eprior
  have eo := stateWithin_trans (factorAccuracy_stateWithin ea) ec
  refine ⟨output, ?_, ea.1, eo.1, eo.2⟩
  simp [Kalman.Implementation.SquareRootFilter.step, hinput, hinitial.1,
    hstored, houtput, ea.1.1, bind, Except.bind, pure, Except.pure]

/-- The original public full-step covariance contract, now with a completed
implementation witness. The stronger theorem above also covers mean and prior error. -/
theorem stepWithin (input : Input.Model) (initial : Input.FactorState)
    (p : StepProfile input initial)
    (d : StepEnvironment input (factorState input.stateDimension initial))
    (hinput : input.validate = .ok ())
    (hinitial
      : Kalman.Implementation.Correctness.SquareRootFilterProperties.ValidFactor
          input.stateDimension initial)
    : ∃ output,
        Kalman.Proofs.SquareRootProfiles.StepWithin
          (stepCovarianceRadius p d 0) input initial output := by
  obtain ⟨output, hrun, ha⟩ := step_accuracy input initial _ p d 0 0 hinput hinitial
    (CovarianceStructure.gram_posSemidef _)
    ⟨within_refl _, le_rfl, fun i => by simp⟩
  exact ⟨output, hinput, hinitial, hrun, ha.1, ha.2.1⟩

/-- Proof witness for the result catalogue statement. -/
theorem stepAccuracy : Kalman.Proofs.FilterComposition.StepAccuracy :=
  step_accuracy

end Kalman.Proofs.FloatFullFilter
