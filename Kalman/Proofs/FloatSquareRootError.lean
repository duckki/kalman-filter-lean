import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FloatPrearray
import Kalman.Proofs.FloatCholeskyFactor
import Kalman.Proofs.FloatFactorValidity

/-! Native stage errors for the actual Tracy three-QR implementation.
The same stored inputs are decoded exactly; every upstream error is propagated. -/

namespace Kalman.Proofs.FloatSquareRootError

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.ErrorPropagation

/-- Prediction includes rounded noise Cholesky, transition-factor product,
copied prearray, native QR, and mean product. No desired error is assumed. -/
theorem prediction_accuracy (input : Input.Model) (initial : Input.FactorState)
    (p : PredictionProfile input initial)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok output
        ∧ FactorAccuracy (predictionCovarianceRadius p) (predictionMeanRadius p)
            input.stateDimension output
            (CovarianceRecursion.predict (model input)
              (factorState input.stateDimension initial)) := by
  let n := input.stateDimension
  have ef := FloatJosephError.product_within p.product p.computeProduct
  have em := FloatJosephError.product_within p.meanProduct p.computeMean
  have eq := FloatCholeskyFactor.factor_backward_error n input.processNoise p.tq
    p.noiseMass p.noiseFloor p.noiseBound p.noise
  obtain ⟨_, _, l, hrun, hls, hlf, hlp, _, eg⟩ :=
    FloatQRInitialDomain.gramFactor_accuracy_initial n (n + n) _ p.qrBudget p.qr
  have hT := p.transition_nonneg
  have hL := p.factor_nonneg
  have efl := FloatPrearray.gram_within ef.2.2
    (by positivity : 0 ≤ (n : ℝ) * p.transitionBound * p.factorBound)
    (product_magnitude _ _ _ _ p.transition_magnitude p.factor_magnitude)
  have epre := within_add efl eq
  rw [FloatPrearray.fromCols_gram] at eg
  have ec := within_trans eg epre
  refine ⟨⟨p.mean, l⟩, ?_, ?_, ?_, em.2.2.1, ?_⟩
  · simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, p.noise.execution,
      p.computeProduct, hrun, p.computeMean, n, bind, Except.bind, pure, Except.pure]
  · exact FloatFactorValidity.factor_validate_complete n _ (by simpa using em.1)
      hls em.2.1 hlf hlp
  · convert ec using 1
    · unfold predictionCovarianceRadius
      dsimp only [n]
      ring
    · rfl
    · simp only [CovarianceRecursion.predict, model, factorState,
        FactorStructure.gram_mul, n]
  · intro i
    simpa [predictionMeanRadius, CovarianceRecursion.predict, model, factorState, vector,
      matrix, Flare.Matrix.Value.matrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      using em.2.2.2 i 0

end Kalman.Proofs.FloatSquareRootError
