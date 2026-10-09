import Kalman.Implementation.Correctness.SquareRootFilterProperties
import Kalman.Implementation.SquareRootFilter
import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles

open Kalman.Implementation.Correctness.SquareRootFilterProperties

/-!
# Square-root working relations and operand profiles

Related interpretation relations, operand domains, and error contracts are
grouped below. These definitions state propositions; proof witnesses
live in `Kalman/Proofs/`.
-/

/-! ----------------------------------------------------------------------
## Factor validity and dense materialization
-------------------------------------------------------------------------- -/

/-!
# Square-root implementation contracts

These state comparison relations. The successful-step PD contract and
full-step accuracy under explicit operand profiles are proved. Successful factor storage, exact-real
Gram positivity, approximation to the ideal filter, and a rounded materialized
covariance are four distinct obligations. Rank rejection is part of the API.
-/

namespace Kalman.Proofs.SquareRootProfiles

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity

noncomputable section

/-- Error relative to the exact recursion starting from the covariance denoted
by the initial factor. Initial Cholesky error is a separate comparison. -/
def StepWithin (ε : ℝ) (input : Input.Model) (initial output : Input.FactorState)
    : Prop :=
  input.validate = .ok ()
  ∧ ValidFactor input.stateDimension initial
  ∧ Kalman.Implementation.SquareRootFilter.step input initial = .ok output
  ∧ ValidFactor input.stateDimension output
  ∧ let reference :=
      CovarianceRecursion.step .joseph (model input)
        (factorState input.stateDimension initial)
        (vector input.measurementDimension input.measurement)
    EntrywiseWithin ε (factorState input.stateDimension output).covariance
      reference.covariance

end
end Kalman.Proofs.SquareRootProfiles

/-! ----------------------------------------------------------------------
## Prediction profiles and error relations
-------------------------------------------------------------------------- -/

/-! Stage operand domains and explicit errors for the existing three-QR filter.
These profiles describe stored operations and magnitudes, never desired errors.
The stage theorems live in Kalman.Proofs.FloatSquareRootError. -/

namespace Kalman.Proofs.SquareRootProfiles.Error

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles

noncomputable section

structure PredictionProfile (input : Input.Model) (initial : Input.FactorState) where
  (tq fl mean : Array Float)
  (noiseMass noiseFloor noiseBound productMass meanMass qrBudget transitionBound factorBound
      : ℝ)
  noise_shape : input.processNoise.size = input.stateDimension * input.stateDimension
  noise_finite : input.processNoise.all Float.isFinite = true
  noise
    : FactorProfile input.stateDimension input.processNoise tq noiseMass noiseFloor
        noiseBound
  product
    : ProductProfile input.stateDimension input.stateDimension input.stateDimension
        input.transition initial.lower productMass
  computeProduct
    : multiply input.stateDimension input.stateDimension input.stateDimension
        input.transition initial.lower
      = .ok fl
  meanProduct
    : ProductProfile input.stateDimension input.stateDimension 1
        input.transition initial.mean meanMass
  computeMean
    : multiply input.stateDimension input.stateDimension 1 input.transition initial.mean
      = .ok mean
  qr
    : GramFactorInputDomain input.stateDimension
        (input.stateDimension + input.stateDimension)
        (fromCols input.stateDimension input.stateDimension input.stateDimension fl tq)
        qrBudget
  transition_nonneg : 0 ≤ transitionBound
  factor_nonneg : 0 ≤ factorBound
  transition_magnitude
    : ∀ i j,
        |matrix input.stateDimension input.stateDimension input.transition i j|
        ≤ transitionBound
  factor_magnitude
    : ∀ i j,
        |matrix input.stateDimension input.stateDimension initial.lower i j| ≤ factorBound

def predictionCovarianceRadius {input : Input.Model} {initial : Input.FactorState}
    (p : PredictionProfile input initial)
    : ℝ :=
  let n := input.stateDimension
  let e := productRadius n p.productMass
  qrGramRadius (n + n) n (fun _ => p.qrBudget)
  + n * (2 * e * (n * p.transitionBound * p.factorBound) + e ^ 2)
  + (diagonalRadius n p.noiseMass
      + divisionRadius n p.noiseMass p.noiseFloor p.noiseBound)

def predictionMeanRadius {input : Input.Model} {initial : Input.FactorState}
    (p : PredictionProfile input initial)
    : ℝ :=
  productRadius input.stateDimension p.meanMass

end
end Kalman.Proofs.SquareRootProfiles.Error

/-! ----------------------------------------------------------------------
## Innovation, gain, mean, and posterior profiles
-------------------------------------------------------------------------- -/

/-! Stored-operand domains for innovation, gain, mean and Joseph factor update.
Operation equations expose the existing schedule. Desired errors are not premises. -/

namespace Kalman.Proofs.SquareRootProfiles.Update

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles

noncomputable section

structure InnovationProfile (input : Input.Model) (prior : Input.FactorState) where
  (tr hl lower : Array Float)
  (noiseMass noiseFloor noiseBound productMass qrBudget observationBound factorBound : ℝ)
  noise
    : FactorProfile input.measurementDimension input.measurementNoise tr noiseMass
        noiseFloor noiseBound
  product
    : ProductProfile input.measurementDimension input.stateDimension input.stateDimension
        input.observation prior.lower productMass
  computeProduct
    : multiply input.measurementDimension input.stateDimension input.stateDimension
        input.observation prior.lower
      = .ok hl
  qr
    : GramFactorInputDomain input.measurementDimension
        (input.measurementDimension + input.stateDimension)
        (fromCols input.measurementDimension input.measurementDimension
          input.stateDimension tr hl)
        qrBudget
  computeQR
    : Kalman.Implementation.OrthogonalFactorization.gramFactor input.measurementDimension
        (input.measurementDimension + input.stateDimension)
        (fromCols input.measurementDimension input.measurementDimension
          input.stateDimension tr hl)
      = .ok lower
  observation_nonneg : 0 ≤ observationBound
  factor_nonneg : 0 ≤ factorBound
  observation_magnitude
    : ∀ i j,
        |matrix input.measurementDimension input.stateDimension input.observation i j|
        ≤ observationBound
  factor_magnitude
    : ∀ i j,
        |matrix input.stateDimension input.stateDimension prior.lower i j| ≤ factorBound

def innovationRadius {input : Input.Model} {prior : Input.FactorState}
    (p : InnovationProfile input prior)
    : ℝ :=
  let n := input.stateDimension
  let m := input.measurementDimension
  let e := productRadius n p.productMass
  qrGramRadius (m + n) m (fun _ => p.qrBudget)
  + (diagonalRadius m p.noiseMass
      + divisionRadius m p.noiseMass p.noiseFloor p.noiseBound)
  + n * (2 * e * (n * p.observationBound * p.factorBound) + e ^ 2)

structure GainProfile {input : Input.Model} {prior : Input.FactorState}
    (innovation : InnovationProfile input prior) where
  (pht forward solution : Array Float)
  (productMass solveMass solveFloor solveBound gainBound : ℝ)
  product
    : ProductProfile input.stateDimension input.stateDimension input.measurementDimension
        prior.lower
        (transpose input.measurementDimension input.stateDimension innovation.hl)
        productMass
  computeProduct
    : multiply input.stateDimension input.stateDimension input.measurementDimension
        prior.lower
        (transpose input.measurementDimension input.stateDimension innovation.hl)
      = .ok pht
  solve
    : SolveProfile input.measurementDimension input.stateDimension innovation.lower
        (transpose input.stateDimension input.measurementDimension pht) forward solution
        solveMass solveFloor solveBound
  finite_solution : solution.all Float.isFinite = true
  mass_nonneg : 0 ≤ solveMass
  gain_nonneg : 0 ≤ gainBound
  gain_magnitude
    : ∀ i j,
        |matrix input.stateDimension input.measurementDimension
          (transpose input.measurementDimension input.stateDimension solution) i j|
        ≤ gainBound

def gainArray {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} (p : GainProfile innovation)
    : Array Float :=
  transpose input.measurementDimension input.stateDimension p.solution

def gainResidualRadius {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} (p : GainProfile innovation)
    : ℝ :=
  let n := input.stateDimension
  let m := input.measurementDimension
  (1 + m * p.solveBound) * divisionRadius m p.solveMass p.solveFloor p.solveBound
  + productRadius n p.productMass
  + n * innovation.factorBound * productRadius n innovation.productMass
  + m * p.gainBound * innovationRadius innovation

def gainRadius {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} (p : GainProfile innovation) (α : ℝ)
    : ℝ :=
  input.measurementDimension * gainResidualRadius p / α

structure MeanProfile {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior}
    (gain : GainProfile innovation) where
  (projected residual increment mean : Array Float)
  (projectedMass incrementMass : ℝ)
  (residualExponent meanExponent : Int)
  measurement_shape : input.measurement.size = input.measurementDimension
  prior_shape : prior.mean.size = input.stateDimension
  projectedProduct
    : ProductProfile input.measurementDimension input.stateDimension 1
        input.observation prior.mean projectedMass
  computeProjected
    : multiply input.measurementDimension input.stateDimension 1 input.observation
        prior.mean
      = .ok projected
  residualSum : SumProfile input.measurement projected residualExponent true
  computeResidual : sub input.measurement projected = .ok residual
  incrementProduct
    : ProductProfile input.stateDimension input.measurementDimension 1
        (gainArray gain) residual incrementMass
  computeIncrement
    : multiply input.stateDimension input.measurementDimension 1 (gainArray gain) residual
      = .ok increment
  meanSum : SumProfile prior.mean increment meanExponent false
  computeMean : add prior.mean increment = .ok mean

def meanRadius {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} {gain : GainProfile innovation}
    (p : MeanProfile gain) (α K Z : ℝ)
    : ℝ :=
  let e :=
    sumRadius p.residualExponent + productRadius input.stateDimension p.projectedMass
  sumRadius p.meanExponent
  + productRadius input.measurementDimension p.incrementMass
  + input.measurementDimension * (gainRadius gain α * Z + K * e + gainRadius gain α * e)

structure PosteriorProfile {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} (gain : GainProfile innovation) where
  (kh w wl ktr : Array Float)
  (khMass wlMass ktrMass qrBudget noiseFactorBound : ℝ)
  (wExponent : Int)
  khProduct
    : ProductProfile input.stateDimension input.measurementDimension input.stateDimension
        (gainArray gain) input.observation khMass
  computeKH
    : multiply input.stateDimension input.measurementDimension input.stateDimension
        (gainArray gain) input.observation
      = .ok kh
  wSum : SumProfile (identity input.stateDimension) kh wExponent true
  computeW : sub (identity input.stateDimension) kh = .ok w
  wlProduct
    : ProductProfile input.stateDimension input.stateDimension input.stateDimension w
        prior.lower wlMass
  computeWL
    : multiply input.stateDimension input.stateDimension input.stateDimension w
        prior.lower
      = .ok wl
  ktrProduct
    : ProductProfile input.stateDimension input.measurementDimension
        input.measurementDimension (gainArray gain) innovation.tr ktrMass
  computeKTR
    : multiply input.stateDimension input.measurementDimension input.measurementDimension
        (gainArray gain) innovation.tr
      = .ok ktr
  qr
    : GramFactorInputDomain input.stateDimension
        (input.stateDimension + input.measurementDimension)
        (fromCols input.stateDimension input.stateDimension input.measurementDimension wl
          ktr)
        qrBudget
  noise_nonneg : 0 ≤ noiseFactorBound
  noise_magnitude
    : ∀ i j,
        |matrix input.measurementDimension input.measurementDimension innovation.tr i j|
        ≤ noiseFactorBound

def posteriorEvaluationRadius {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} {gain : GainProfile innovation}
    (p : PosteriorProfile gain)
    : ℝ :=
  let n := input.stateDimension
  let m := input.measurementDimension
  let W := 1 + m * gain.gainBound * innovation.observationBound
  let ew := sumRadius p.wExponent + productRadius m p.khMass
  let ewl := productRadius n p.wlMass + n * ew * innovation.factorBound
  let ekt := productRadius m p.ktrMass
  qrGramRadius (n + m) n (fun _ => p.qrBudget)
  + n * (2 * ewl * (n * W * innovation.factorBound) + ewl ^ 2)
  + m * (2 * ekt * (m * gain.gainBound * p.noiseFactorBound) + ekt ^ 2)
  + m ^ 2 * gain.gainBound ^ 2
    * (diagonalRadius m innovation.noiseMass
        + divisionRadius m innovation.noiseMass innovation.noiseFloor
            innovation.noiseBound)

def posteriorRadius {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} {gain : GainProfile innovation}
    (p : PosteriorProfile gain) (α P R K : ℝ)
    : ℝ :=
  let n := input.stateDimension
  let m := input.measurementDimension
  let e := gainRadius gain α
  posteriorEvaluationRadius p
  + (n ^ 2 * P
        * (2 * (m * e * innovation.observationBound)
              * (1 + m * K * innovation.observationBound)
            + (m * e * innovation.observationBound) ^ 2)
      + m ^ 2 * R * (2 * e * K + e ^ 2))

end
end Kalman.Proofs.SquareRootProfiles.Update
