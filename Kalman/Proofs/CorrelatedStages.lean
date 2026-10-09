import Kalman.Proofs.QRProfiles
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition

/-!
# Correlated filter operating domains

Related interpretation relations, operand domains, and error contracts are
grouped below. These definitions state propositions; proof witnesses
live in `Kalman/Proofs/`.
-/

/-! ----------------------------------------------------------------------
## Gain operand domain
-------------------------------------------------------------------------- -/

/-! A sufficient stored-input domain for forming a two-state gain RHS.
The covariance bound concerns the exact Gram of the stored prior factor. -/

namespace Kalman.Proofs.CorrelatedStages.Gain

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Flare.Binary64.Value

noncomputable section

/-- Original stored observation/prior-factor conditions. The stricter
observation cap leaves rounding headroom inside the solve's RHS cap. -/
structure TwoStateDomain (h l : Array Float) : Prop where
  observation_size : h.size = 4
  factor_size : l.size = 4
  observation_finite : h.all Float.isFinite = true
  factor_finite : l.all Float.isFinite = true
  observation_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 h i j)| ≤ 1 / 64
  factor_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 l i j)| ≤ 2
  covariance_bound : ∀ i j, |(matrix 2 2 l * (matrix 2 2 l).transpose) i j| ≤ 2

end
end Kalman.Proofs.CorrelatedStages.Gain

/-! ----------------------------------------------------------------------
## Innovation operand domain
-------------------------------------------------------------------------- -/

/-! Stored model/prior conditions sufficient for two-state innovation and gain.
The noise diagonal cap leaves room for the observation block's row energy. -/

namespace Kalman.Proofs.CorrelatedStages.Innovation

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Flare.Binary64.Value

noncomputable section

/-- A local stage domain, still requiring preservation of the reached prior
factor bounds for a full input-derived filter trajectory. -/
structure TwoStateDomain (input : Input.Model) (prior : Input.FactorState) : Prop where
  state_dimension : input.stateDimension = 2
  measurement_dimension : input.measurementDimension = 2
  gain_inputs
    : Kalman.Proofs.CorrelatedStages.Gain.TwoStateDomain input.observation prior.lower
  noise
    : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain
        input.measurementNoise
  noise_diagonal_cap : ∀ i, i < 2 → value (entry 2 input.measurementNoise i i) ≤ 3 / 2

end
end Kalman.Proofs.CorrelatedStages.Innovation

/-! ----------------------------------------------------------------------
## Mean correction domain
-------------------------------------------------------------------------- -/

/-! Stored mean/measurement headroom for the two-state correction stage.
No arithmetic execution or desired output/error is assumed in this domain. -/

namespace Kalman.Proofs.CorrelatedStages.Mean

open Kalman.Definitions
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Flare.Binary64.Value

noncomputable section

/-- A small predicted mean and bounded measurement leave correction headroom. -/
structure VectorDomain (mean measurement : Array Float) : Prop where
  mean_size : mean.size = 2
  measurement_size : measurement.size = 2
  mean_finite : mean.all Float.isFinite = true
  measurement_finite : measurement.all Float.isFinite = true
  mean_bound : ∀ i, i < 2 → |value (mean.getD i 0.0)| ≤ 9 / 32
  measurement_bound : ∀ i, i < 2 → |value (measurement.getD i 0.0)| ≤ 1

/-- Combined original local correction inputs. The reached prior-factor and
predicted-mean bounds still need preservation in a full-filter invariant. -/
structure TwoStateDomain (input : Input.Model) (prior : Input.FactorState) : Prop
    extends Kalman.Proofs.CorrelatedStages.Innovation.TwoStateDomain input prior where
  vectors : VectorDomain prior.mean input.measurement

/-- Closed allowance for the local domain, including original-noise and gain
error. It specializes the existing innovation, gain and mean stage radii. -/
noncomputable def localMeanRadius : ℝ :=
  let e := productRadius 2 8
  let eI :=
    qrGramRadius 4 2 (fun _ => 2)
    + (diagonalRadius 2 8 + divisionRadius 2 8 (1 / 2) 2)
    + 2 * (2 * e * (2 * (1 / 64) * 2) + e ^ 2)
  let eK :=
    2 * ((1 + 2 * 2) * divisionRadius 2 32 (1 / 2) 2 + e + 2 * 2 * e + 2 * eI) / (3 / 4)
  let eZ := sumRadius 2 + e
  sumRadius 2 + e + 2 * (eK * 2 + (1 / 6) * eZ + eK * eZ)

end
end Kalman.Proofs.CorrelatedStages.Mean

/-! ----------------------------------------------------------------------
## Prediction and correction inputs
-------------------------------------------------------------------------- -/

/-! Original stored transition/state/process-noise bounds for prediction.
Transition bounds are independent of the smaller observation/gain RHS domain.
The stored covariance cap supplies row-energy headroom for the rounded FL Gram. -/

namespace Kalman.Proofs.CorrelatedStages.Prediction

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Flare.Binary64.Value

noncomputable section

/-- Prediction permits stronger transitions than the observation/gain domain.
The covariance bound concerns the exact Gram of the original stored factor. -/
structure TransitionInputs (transition factor : Array Float) : Prop where
  transition_size : transition.size = 4
  factor_size : factor.size = 4
  transition_finite : transition.all Float.isFinite = true
  factor_finite : factor.all Float.isFinite = true
  transition_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 transition i j)| ≤ 1 / 8
  factor_bound : ∀ i j, i < 2 → j < 2 → |value (entry 2 factor i j)| ≤ 2
  covariance_bound : ∀ i j, |FactorRecursion.gram (matrix 2 2 factor) i j| ≤ 2

/-- A sufficient two-state prediction domain. The exact stored incoming Gram
entry cap is useful for later invariant closure; no native run is assumed. -/
structure TwoStateDomain (input : Input.Model) (initial : Input.FactorState) : Prop where
  state_dimension : input.stateDimension = 2
  transition_inputs : TransitionInputs input.transition initial.lower
  noise
    : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain
        input.processNoise
  noise_diagonal_cap : ∀ i, i < 2 → value (entry 2 input.processNoise i i) ≤ 3 / 2
  mean_size : initial.mean.size = 2
  mean_finite : initial.mean.all Float.isFinite = true
  mean_bound : ∀ i, i < 2 → |value (initial.mean.getD i 0.0)| ≤ 1

/-- The existing prediction radius at the derived uniform profile constants.
It includes original process-noise factorization and rounded prearray error. -/
noncomputable def localCovarianceRadius : ℝ :=
  let e := productRadius 2 8
  qrGramRadius 4 2 (fun _ => 2)
  + 2 * (2 * e * (2 * (1 / 8) * 2) + e ^ 2)
  + (diagonalRadius 2 8 + divisionRadius 2 8 (1 / 2) 2)

end
end Kalman.Proofs.CorrelatedStages.Prediction

/-! ----------------------------------------------------------------------
## Posterior correction domain
-------------------------------------------------------------------------- -/

/-! Reached prediction margins needed for the posterior QR domain.
These are input conditions; no posterior execution or error is assumed. -/

namespace Kalman.Proofs.CorrelatedStages.Posterior

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Implementation.LinearAlgebra
open Kalman.Proofs.ArithmeticProfiles

noncomputable section

/-- Prediction provides these stronger covariance margins in addition to the
local mean-correction domain. -/
structure TwoStateDomain (input : Input.Model) (prior : Input.FactorState) : Prop
    extends toMeanDomain :
              Kalman.Proofs.CorrelatedStages.Mean.TwoStateDomain input prior where
  covariance_floor
    : (FactorRecursion.gram (matrix 2 2 prior.lower) - (2 / 3 : ℝ) • 1).PosSemidef
  covariance_bound : ∀ i j, |FactorRecursion.gram (matrix 2 2 prior.lower) i j| ≤ 7 / 4

/-- Fixed constants derived by the completed innovation/gain input theorem.
This parameter relation is distinct from the theorem deriving it. -/
structure GainParameters {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} (gain : GainProfile innovation)
    : Prop where
  noise_mass : innovation.noiseMass = 8
  noise_floor : innovation.noiseFloor = 1 / 2
  noise_bound : innovation.noiseBound = 2
  innovation_product_mass : innovation.productMass = 8
  innovation_qr_budget : innovation.qrBudget = 2
  observation_bound : innovation.observationBound = 1 / 64
  factor_bound : innovation.factorBound = 2
  gain_product_mass : gain.productMass = 8
  solve_mass : gain.solveMass = 32
  solve_floor : gain.solveFloor = 1 / 2
  solve_bound : gain.solveBound = 2
  gain_bound : gain.gainBound = 1

/-- Actual posterior arithmetic before QR, with fixed derived mass/exponent
choices. No desired numerical discrepancy is a field of this profile. -/
structure TwoStateStages (k h l tr : Array Float) where
  (kh w wl ktr : Array Float)
  kh_product : ProductProfile 2 2 2 k h 8
  compute_kh : multiply 2 2 2 k h = .ok kh
  w_sum : SumProfile (identity 2) kh 2 true
  compute_w : sub (identity 2) kh = .ok w
  wl_product : ProductProfile 2 2 2 w l 8
  compute_wl : multiply 2 2 2 w l = .ok wl
  ktr_product : ProductProfile 2 2 2 k tr 8
  compute_ktr : multiply 2 2 2 k tr = .ok ktr

/-- Fixed posterior parameters derived below from the local inputs. -/
structure PosteriorParameters {input : Input.Model} {prior : Input.FactorState}
    {innovation : InnovationProfile input prior} {gain : GainProfile innovation}
    (posterior : PosteriorProfile gain)
    : Prop where
  kh_mass : posterior.khMass = 8
  wl_mass : posterior.wlMass = 8
  ktr_mass : posterior.ktrMass = 8
  qr_budget : posterior.qrBudget = 2
  noise_factor_bound : posterior.noiseFactorBound = 2
  w_exponent : posterior.wExponent = 2

end
end Kalman.Proofs.CorrelatedStages.Posterior

/-! ----------------------------------------------------------------------
## Independent reference bounds and derived step parameters
-------------------------------------------------------------------------- -/

namespace Kalman.Proofs.CorrelatedStages

open Kalman.Definitions
open Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.FilterComposition

noncomputable section

/-- Independent ideal trajectory bounds, with no native state or error premise.
The reference starts at the exact original dense covariance and mean. -/
structure ReferenceInvariant (reference : LinearModel.State 2) : Prop where
  covariance_positive : reference.covariance.PosDef
  covariance_bound : ∀ i j, |reference.covariance i j| ≤ 2
  mean_bound : ∀ i, |reference.mean i| ≤ 1

/-- Fixed arithmetic constants derived from the original operating domain.
This relation permits reuse of the full-step/horizon error composition. -/
structure StepParameters {input : Input.Model} {initial : Input.FactorState}
    (p : StepProfile input initial)
    : Prop where
  prediction_noise_mass : p.prediction.noiseMass = 8
  prediction_noise_floor : p.prediction.noiseFloor = 1 / 2
  prediction_noise_bound : p.prediction.noiseBound = 2
  prediction_product_mass : p.prediction.productMass = 8
  prediction_mean_mass : p.prediction.meanMass = 8
  prediction_qr_budget : p.prediction.qrBudget = 2
  transition_bound : p.prediction.transitionBound = 1 / 8
  factor_bound : p.prediction.factorBound = 2
  gain : Kalman.Proofs.CorrelatedStages.Posterior.GainParameters p.gain
  mean_projected_mass : p.mean.projectedMass = 8
  mean_increment_mass : p.mean.incrementMass = 8
  mean_residual_exponent : p.mean.residualExponent = 2
  mean_exponent : p.mean.meanExponent = 2
  posterior : Kalman.Proofs.CorrelatedStages.Posterior.PosteriorParameters p.posterior

end
end Kalman.Proofs.CorrelatedStages
