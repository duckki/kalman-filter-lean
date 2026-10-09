import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Definitions.Theorems.RecursionSensitivity
import Kalman.Implementation.SquareRootFilter

/-!
# Full-filter profiles and error budgets

Related interpretation relations, operand domains, and error contracts are
grouped below. These definitions state propositions; proof witnesses
live in `Kalman/Proofs/`.
-/

/-! ----------------------------------------------------------------------
## Full-step profiles and propagated errors
-------------------------------------------------------------------------- -/

/-! Complete-filter operand witnesses and explicit propagated error radii.
These are contracts, not proofs. QR domains concern original assembled arrays;
Cholesky/solve profiles still expose successful intermediate operations. -/

namespace Kalman.Proofs.FilterComposition

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Definitions.Theorems.RecursionSensitivity

noncomputable section

structure StepProfile (input : Input.Model) (initial : Input.FactorState) where
  prediction : PredictionProfile input initial
  lower : Array Float
  computeQR
    : Kalman.Implementation.OrthogonalFactorization.gramFactor input.stateDimension
        (input.stateDimension + input.stateDimension)
        (fromCols input.stateDimension input.stateDimension input.stateDimension
          prediction.fl prediction.tq)
      = .ok lower
  innovation : InnovationProfile input ⟨prediction.mean, lower⟩
  gain : GainProfile innovation
  mean : MeanProfile gain
  posterior : PosteriorProfile gain

def predicted {input : Input.Model} {initial : Input.FactorState}
    (p : StepProfile input initial)
    : Input.FactorState :=
  ⟨p.prediction.mean, p.lower⟩

/-- Reference magnitudes and conditioning are independent of native accuracy.
P and Z bound the ideal predicted covariance and innovation. -/
structure StepEnvironment (input : Input.Model)
    (reference : LinearModel.State input.stateDimension) where
  (noiseFloor covarianceBound noiseBound innovationBound : ℝ)
  floor_positive : 0 < noiseFloor
  covariance_nonneg : 0 ≤ covarianceBound
  noise_nonneg : 0 ≤ noiseBound
  innovation_nonneg : 0 ≤ innovationBound
  process_psd : (model input).processNoise.PosSemidef
  noise_lower : ((model input).measurementNoise - noiseFloor • 1).PosSemidef
  covariance_magnitude
    : ∀ i j,
        |(CovarianceRecursion.predict (model input) reference).covariance i j|
        ≤ covarianceBound
  noise_magnitude : ∀ i j, |(model input).measurementNoise i j| ≤ noiseBound
  innovation_magnitude
    : ∀ i,
        |CovarianceRecursion.innovation (model input)
          (CovarianceRecursion.predict (model input) reference)
          (vector input.measurementDimension input.measurement) i|
        ≤ innovationBound

def predictedCovarianceRadius {input : Input.Model} {initial : Input.FactorState}
    (p : StepProfile input initial) (eP : ℝ)
    : ℝ :=
  predictionCovarianceRadius p.prediction
  + input.stateDimension ^ 2 * p.prediction.transitionBound ^ 2 * eP

def predictedMeanRadius {input : Input.Model} {initial : Input.FactorState}
    (p : StepProfile input initial) (eX : ℝ)
    : ℝ :=
  predictionMeanRadius p.prediction
  + input.stateDimension * p.prediction.transitionBound * eX

def stepCovarianceRadius {input : Input.Model} {initial : Input.FactorState}
    {reference : LinearModel.State input.stateDimension} (p : StepProfile input initial)
    (d : StepEnvironment input reference) (eP : ℝ)
    : ℝ :=
  let n := input.stateDimension
  let m := input.measurementDimension
  let e := predictedCovarianceRadius p eP
  let K :=
    gainMagnitude n m d.noiseFloor (d.covarianceBound + e) p.innovation.observationBound
  posteriorRadius p.posterior d.noiseFloor (d.covarianceBound + e) d.noiseBound K
  + correctionCovarianceRadius n m d.noiseFloor d.covarianceBound d.noiseBound
      p.innovation.observationBound e

def stepMeanRadius {input : Input.Model} {initial : Input.FactorState}
    {reference : LinearModel.State input.stateDimension} (p : StepProfile input initial)
    (d : StepEnvironment input reference) (eP eX : ℝ)
    : ℝ :=
  let n := input.stateDimension
  let m := input.measurementDimension
  let e := predictedCovarianceRadius p eP
  let x := predictedMeanRadius p eX
  let K :=
    gainMagnitude n m d.noiseFloor (d.covarianceBound + e) p.innovation.observationBound
  let Z := d.innovationBound + n * p.innovation.observationBound * x
  meanRadius p.mean d.noiseFloor K Z
  + correctionMeanRadius n m d.noiseFloor d.covarianceBound p.innovation.observationBound
      d.innovationBound e x

end
end Kalman.Proofs.FilterComposition

/-! ----------------------------------------------------------------------
## Finite-horizon composition
-------------------------------------------------------------------------- -/

/-! Time-varying native filter traces at fixed dimensions, and numerical
admissibility of every reached prefix. No successful final trace or trajectory
accuracy is a domain premise. Stored inputs remain the authoritative values. -/

namespace Kalman.Proofs.FilterComposition.Horizon

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.FilterComposition

noncomputable section

/-- A reached-prefix operand domain. Radius caps compare explicit arithmetic
expressions with the chosen budget, not the unknown error of the actual output.
Profiles are needed only at reached prefixes, never at nonexistent future runs. -/
structure HorizonOperands (n m horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State n) where
  initial_positive : reference.covariance.PosDef
  dimensions
    : ∀ t,
        t < horizon → (inputs t).stateDimension = n ∧ (inputs t).measurementDimension = m
  input_valid : ∀ t, t < horizon → (inputs t).validate = .ok ()
  process_positive
    : ∀ t, t < horizon → (model (atDimensions n m (inputs t))).processNoise.PosDef
  environment
    : ∀ t,
        t < horizon
        → StepEnvironment (atDimensions n m (inputs t)) (exactRun n m inputs reference t)
  profile
    : ∀ t,
        t < horizon
        → ∀ current,
            nativeRun inputs initial t = .ok current
            → StepProfile (atDimensions n m (inputs t)) current

structure HorizonDomain (n m horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State n) (eP eX : Nat → ℝ)
    extends HorizonOperands n m horizon inputs initial reference where
  initial_accuracy : FactorAccuracy (eP 0) (eX 0) n initial reference
  covariance_cap
    : ∀ t (ht : t < horizon) current (hrun : nativeRun inputs initial t = .ok current),
        stepCovarianceRadius (profile t ht current hrun) (environment t ht) (eP t)
        ≤ eP (t + 1)
  mean_cap
    : ∀ t (ht : t < horizon) current (hrun : nativeRun inputs initial t = .ok current),
        stepMeanRadius (profile t ht current hrun) (environment t ht) (eP t) (eX t)
        ≤ eX (t + 1)

end
end Kalman.Proofs.FilterComposition.Horizon

/-! ----------------------------------------------------------------------
## Uniform two-state budgets
-------------------------------------------------------------------------- -/

/-! A conservative two-state operating budget. Equality fields fix numerical
allowances, not operand values: any witnesses meeting these allowances qualify.
Admissibility of a whole trace is separate from this coefficient calculation. -/

namespace Kalman.Proofs.FilterComposition.Budget

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.FilterComposition

noncomputable section

structure UniformStepParameters {input : Input.Model} {initial : Input.FactorState}
    {reference : LinearModel.State input.stateDimension} (p : StepProfile input initial)
    (d : StepEnvironment input reference)
    : Prop where
  state_dimension : input.stateDimension = 2
  measurement_dimension : input.measurementDimension = 2
  prediction_noiseMass : p.prediction.noiseMass = 8
  prediction_noiseFloor : p.prediction.noiseFloor = 1 / 2
  prediction_noiseBound : p.prediction.noiseBound = 2
  prediction_productMass : p.prediction.productMass = 8
  prediction_meanMass : p.prediction.meanMass = 8
  prediction_qrBudget : p.prediction.qrBudget = 2
  prediction_transitionBound : p.prediction.transitionBound = 1 / 32
  prediction_factorBound : p.prediction.factorBound = 2
  innovation_noiseMass : p.innovation.noiseMass = 8
  innovation_noiseFloor : p.innovation.noiseFloor = 1 / 2
  innovation_noiseBound : p.innovation.noiseBound = 2
  innovation_productMass : p.innovation.productMass = 8
  innovation_qrBudget : p.innovation.qrBudget = 2
  innovation_observationBound : p.innovation.observationBound = 1 / 32
  innovation_factorBound : p.innovation.factorBound = 2
  gain_productMass : p.gain.productMass = 8
  gain_solveMass : p.gain.solveMass = 32
  gain_solveFloor : p.gain.solveFloor = 1 / 2
  gain_solveBound : p.gain.solveBound = 2
  gain_gainBound : p.gain.gainBound = 1
  mean_projectedMass : p.mean.projectedMass = 8
  mean_incrementMass : p.mean.incrementMass = 8
  mean_residualExponent : p.mean.residualExponent = 2
  mean_meanExponent : p.mean.meanExponent = 2
  posterior_khMass : p.posterior.khMass = 8
  posterior_wlMass : p.posterior.wlMass = 8
  posterior_ktrMass : p.posterior.ktrMass = 8
  posterior_qrBudget : p.posterior.qrBudget = 2
  posterior_noiseFactorBound : p.posterior.noiseFactorBound = 2
  posterior_wExponent : p.posterior.wExponent = 2
  environment_noiseFloor : d.noiseFloor = 1
  environment_covarianceBound : d.covarianceBound = 2
  environment_noiseBound : d.noiseBound = 1
  environment_innovationBound : d.innovationBound = 2

/-- Uniform allowances require the numerical profiles and reference bounds
listed above at every reached prefix. Final success and accuracy are not assumed. -/
structure UniformHorizonDomain (horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State 2)
    (budget : ℝ := 1 / 128) where
  operands
    : Kalman.Proofs.FilterComposition.Horizon.HorizonOperands 2 2 horizon inputs initial
        reference
  initial_accuracy
    : Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
        budget budget 2 initial reference
  parameters
    : ∀ t (ht : t < horizon) current
        (hrun
          : Kalman.Implementation.Correctness.InputInterpretation.nativeRun inputs initial
              t
            = .ok current),
        UniformStepParameters (operands.profile t ht current hrun)
          (operands.environment t ht)

def localPrediction : ℝ :=
  let e := productRadius 2 8
  qrGramRadius 4 2 (fun _ => 2)
  + 2 * (2 * e * (2 * (1 / 32) * 2) + e ^ 2)
  + (diagonalRadius 2 8 + divisionRadius 2 8 (1 / 2) 2)

def propagatedCovariance (eP : ℝ) : ℝ := localPrediction + 2 ^ 2 * (1 / 32) ^ 2 * eP

def propagatedMean (eX : ℝ) : ℝ := productRadius 2 8 + 2 * (1 / 32) * eX

def localGain : ℝ :=
  2
  * ((1 + 2 * 2) * divisionRadius 2 32 (1 / 2) 2
      + productRadius 2 8
      + 2 * 2 * productRadius 2 8
      + 2 * localPrediction)

def localPosterior : ℝ :=
  let ew := sumRadius 2 + productRadius 2 8
  let ewl := productRadius 2 8 + 2 * ew * 2
  let ekt := productRadius 2 8
  let W : ℝ := 1 + 2 * 1 * (1 / 32)
  qrGramRadius 4 2 (fun _ => 2)
  + 2 * (2 * ewl * (2 * W * 2) + ewl ^ 2)
  + 2 * (2 * ekt * (2 * 1 * 2) + ekt ^ 2)
  + 2 ^ 2 * 1 ^ 2 * (diagonalRadius 2 8 + divisionRadius 2 8 (1 / 2) 2)

def uniformCovarianceRadius (eP : ℝ) : ℝ :=
  let e := propagatedCovariance eP
  let K := gainMagnitude 2 2 1 (2 + e) (1 / 32)
  localPosterior
  + (2 ^ 2 * (2 + e)
        * (2 * (2 * localGain * (1 / 32)) * (1 + 2 * K * (1 / 32))
            + (2 * localGain * (1 / 32)) ^ 2)
      + 2 ^ 2 * 1 * (2 * localGain * K + localGain ^ 2))
  + correctionCovarianceRadius 2 2 1 2 1 (1 / 32) e

def uniformMeanRadius (eP eX : ℝ) : ℝ :=
  let e := propagatedCovariance eP
  let x := propagatedMean eX
  let K := gainMagnitude 2 2 1 (2 + e) (1 / 32)
  let Z := 2 + 2 * (1 / 32) * x
  let ez := sumRadius 2 + productRadius 2 8
  sumRadius 2
  + productRadius 2 8
  + 2 * (localGain * Z + K * ez + localGain * ez)
  + correctionMeanRadius 2 2 1 2 (1 / 32) 2 e x

end
end Kalman.Proofs.FilterComposition.Budget

/-! ----------------------------------------------------------------------
## Reset-model operating domain
-------------------------------------------------------------------------- -/

/-! An original-input nonvacuity witness for the two-state horizon domain.
Reset dynamics and zero observation deliberately make this a simple domain
inhabitant; it is not evidence of a sharp tolerance for a navigation model. -/

namespace Kalman.Proofs.FilterComposition.Reset

open Kalman.Definitions

def identity : Array Float := #[1.0, 0.0, 0.0, 1.0]
def signedIdentity : Array Float := #[1.0, 0.0, -0.0, 1.0]
def zeros : Array Float := #[0.0, 0.0, 0.0, 0.0]
def zeroMean : Array Float := #[0.0, 0.0]
def measurement : Array Float := #[1.0, 0.0]
def input : Input.Model := ⟨2, 2, zeros, zeros, identity, identity, measurement⟩
def initial : Input.FactorState := ⟨zeroMean, signedIdentity⟩

end Kalman.Proofs.FilterComposition.Reset

/-! Conditional composition contracts, with proof-witness references.
Supporting domains and budgets live in `Kalman.Proofs.FilterComposition`. -/

/-! ----------------------------------------------------------------------
## Step accuracy
-------------------------------------------------------------------------- -/

namespace Kalman.Proofs.FilterComposition

open Matrix
open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Definitions.Theorems.RecursionSensitivity

noncomputable section

/-- Conditional full-step covariance and mean error propagation from the supplied
reference state, with successful checked native execution.
Proof witness: `Kalman.Proofs.FloatFullFilter.stepAccuracy`
(the existing `FloatFullFilter.step_accuracy` proof). -/
def StepAccuracy : Prop :=
  ∀ (input : Input.Model) (initial : Input.FactorState)
    (reference : LinearModel.State input.stateDimension)
    (p : StepProfile input initial) (d : StepEnvironment input reference) (eP eX : ℝ)
    (_ : input.validate = .ok ())
    (_
      : Kalman.Implementation.Correctness.SquareRootFilterProperties.ValidFactor
          input.stateDimension initial)
    (_ : reference.covariance.PosSemidef)
    (_ : StateWithin eP eX (factorState input.stateDimension initial) reference),
    ∃ output,
      Kalman.Implementation.SquareRootFilter.step input initial = .ok output
      ∧ FactorAccuracy (stepCovarianceRadius p d eP) (stepMeanRadius p d eP eX)
          input.stateDimension output
          (CovarianceRecursion.step .joseph (model input) reference
            (vector input.measurementDimension input.measurement))

end
end Kalman.Proofs.FilterComposition

/-! ----------------------------------------------------------------------
## Finite-horizon accuracy
-------------------------------------------------------------------------- -/

namespace Kalman.Proofs.FilterComposition.Horizon

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties

noncomputable section

/-- Conditional success, covariance/mean accuracy, and strict positivity at every
prefix of a finite time-varying horizon under HorizonDomain.
Proof witness: `Kalman.Proofs.FloatFilterHorizon.finiteHorizonAccuracy`
(the existing `FloatFilterHorizon.finite_horizon_accuracy` proof). -/
def FiniteHorizonAccuracy : Prop :=
  ∀ (n m horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State n) (eP eX : Nat → ℝ)
    (_ : HorizonDomain n m horizon inputs initial reference eP eX),
  ∀ t,
    t ≤ horizon
    → ∃ output,
        nativeRun inputs initial t = .ok output
        ∧ FactorAccuracy (eP t) (eX t) n output (exactRun n m inputs reference t)
        ∧ (factorState n output).covariance.PosDef
        ∧ (exactRun n m inputs reference t).covariance.PosDef

end
end Kalman.Proofs.FilterComposition.Horizon
