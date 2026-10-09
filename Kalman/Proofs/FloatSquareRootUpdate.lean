import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FloatSquareRootError
import Kalman.Proofs.RealErrorBounds

/-! Innovation and gain errors against the same decoded prior and ideal noise.
The posterior and mean stages compose these errors, rather than assuming an exact gain. -/

namespace Kalman.Proofs.FloatSquareRootUpdate

open Matrix
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.ErrorPropagation

theorem innovation_accuracy (input : Input.Model) (prior : Input.FactorState)
    (p : InnovationProfile input prior)
    : p.lower.size = input.measurementDimension * input.measurementDimension
      ∧ p.lower.all Float.isFinite = true
      ∧ FactorRecursion.LowerPositive
          (matrix input.measurementDimension input.measurementDimension p.lower)
      ∧ EntrywiseWithin (innovationRadius p)
          (FactorRecursion.gram
            (matrix input.measurementDimension input.measurementDimension p.lower))
          (CovarianceRecursion.innovationCovariance (model input)
            (factorState input.stateDimension prior)) := by
  let n := input.stateDimension
  let m := input.measurementDimension
  obtain ⟨_, _, l, hl, hs, hf, hp, _, eg⟩ :=
    FloatQRInitialDomain.gramFactor_accuracy_initial m (m + n) _ p.qrBudget p.qr
  have he : l = p.lower := Except.ok.inj (hl.symm.trans p.computeQR)
  subst l
  have eh := FloatJosephError.product_within p.product p.computeProduct
  have er := FloatCholeskyFactor.factor_backward_error m input.measurementNoise p.tr
    p.noiseMass p.noiseFloor p.noiseBound p.noise
  have hH := p.observation_nonneg
  have hL := p.factor_nonneg
  have ehl := FloatPrearray.gram_within eh.2.2 (by positivity)
    (product_magnitude _ _ _ _ p.observation_magnitude p.factor_magnitude)
  rw [FloatPrearray.fromCols_gram] at eg
  have et := within_trans eg (within_add er ehl)
  refine ⟨hs, hf, hp, ?_⟩
  convert et using 1
  · unfold innovationRadius
    dsimp only [n, m]
    ring
  · simp only [CovarianceRecursion.innovationCovariance, model, factorState,
      FactorStructure.gram_mul, m]
    abel

theorem innovation_lower (input : Input.Model) (prior : Input.FactorState) (α : ℝ)
    (hr
      : (matrix input.measurementDimension input.measurementDimension
            input.measurementNoise
          - α • 1).PosSemidef)
    : (CovarianceRecursion.innovationCovariance (model input)
          (factorState input.stateDimension prior)
        - α • 1).PosSemidef := by
  have hp := (CovarianceStructure.gram_posSemidef
    (matrix input.stateDimension input.stateDimension prior.lower)).mul_mul_conjTranspose_same
      (matrix input.measurementDimension input.stateDimension input.observation)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
  convert hp.add hr using 1
  dsimp only [CovarianceRecursion.innovationCovariance, model, factorState]
  abel

theorem gain_accuracy (input : Input.Model) (prior : Input.FactorState)
    (innovation : InnovationProfile input prior) (p : GainProfile innovation) (α : ℝ)
    (hα : 0 < α)
    (hr
      : (matrix input.measurementDimension input.measurementDimension
            input.measurementNoise
          - α • 1).PosSemidef)
    : solveCholesky input.measurementDimension input.stateDimension innovation.lower
          (transpose input.stateDimension input.measurementDimension p.pht)
        = .ok p.solution
      ∧ EntrywiseWithin (gainRadius p α)
          (matrix input.stateDimension input.measurementDimension (gainArray p))
          (CovarianceRecursion.gain (model input)
            (factorState input.stateDimension prior)) := by
  let n := input.stateDimension
  let m := input.measurementDimension
  let k := matrix n m (gainArray p)
  let sh := FactorRecursion.gram (matrix m m innovation.lower)
  let s := CovarianceRecursion.innovationCovariance (model input) (factorState n prior)
  let c := FactorRecursion.gram (matrix n n prior.lower)
    * (matrix m n input.observation).transpose
  have eh := FloatJosephError.product_within innovation.product innovation.computeProduct
  have ep := FloatJosephError.product_within p.product p.computeProduct
  have es := (innovation_accuracy input prior innovation).2.2.2
  obtain ⟨hexe, _, eres⟩ := FloatCholeskySolve.solve_residual m n innovation.lower
    (transpose n m p.pht) p.forward p.solution p.solveMass p.solveFloor p.solveBound p.solve p.mass_nonneg
  have hD := p.solve.bound_nonneg
  have hdiv := FloatResidualError.divisionRadius_nonneg m p.solveMass p.solveFloor p.solveBound
    p.mass_nonneg p.solve.diagonal_lower hD
  have hρ : 0 ≤ (1 + (m : ℝ) * p.solveBound) * divisionRadius m p.solveMass p.solveFloor p.solveBound := by positivity
  have ek := within_transpose (show EntrywiseWithin
      ((1 + (m : ℝ) * p.solveBound) * divisionRadius m p.solveMass p.solveFloor p.solveBound)
      (sh * matrix m n p.solution) (matrix m n (transpose n m p.pht)) from ⟨hρ, eres⟩)
  have hkmat := Flare.Matrix.Multiplication.transpose_matrix m n p.solution p.finite_solution
  have hc := Flare.Matrix.Multiplication.transpose_matrix n m p.pht ep.2.1
  simp only [Matrix.transpose_mul, hc, Matrix.transpose_transpose] at ek
  have hs : sh.transpose = sh := by simp [sh, FactorRecursion.gram]
  rw [hs, ← hkmat] at ek
  have ehT : matrix input.stateDimension input.measurementDimension
      (transpose input.measurementDimension input.stateDimension innovation.hl) =
      (matrix input.measurementDimension input.stateDimension innovation.hl).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix _ _ innovation.hl eh.2.1
  rw [ehT] at ep
  have ec := within_trans ep.2.2 (within_mul_left (matrix n n prior.lower)
    (within_transpose eh.2.2) innovation.factor_nonneg innovation.factor_magnitude)
  have ec' : EntrywiseWithin (productRadius n p.productMass
      + n * innovation.factorBound * productRadius n innovation.productMass) (matrix n m p.pht) c := by
    convert ec using 1
    · simp only [Matrix.transpose_mul, Matrix.mul_assoc, c, FactorRecursion.gram, n, m]
  have eright := within_trans (within_sym (within_mul_left k es p.gain_nonneg p.gain_magnitude))
    (within_trans ek ec')
  have eg := RealErrorBounds.gain_residual_accuracy s c k α (gainResidualRadius p) hα
    (innovation_lower input prior α hr) (by
      convert eright using 1
      unfold gainResidualRadius
      dsimp only [n, m]
      ring)
  exact ⟨hexe, eg⟩

/-- The final QR represents a rounded evaluation of Joseph at the actual
stored gain. Rounded KH, subtraction, both products and noise factors are covered. -/
theorem posterior_evaluation_accuracy (input : Input.Model) (prior : Input.FactorState)
    (innovation : InnovationProfile input prior) (gain : GainProfile innovation)
    (p : PosteriorProfile gain)
    : ∃ lower,
        Kalman.Implementation.OrthogonalFactorization.gramFactor input.stateDimension
            (input.stateDimension + input.measurementDimension)
            (fromCols input.stateDimension input.stateDimension input.measurementDimension
              p.wl p.ktr)
          = .ok lower
        ∧ lower.size = input.stateDimension * input.stateDimension
        ∧ lower.all Float.isFinite = true
        ∧ FactorRecursion.LowerPositive
            (matrix input.stateDimension input.stateDimension lower)
        ∧ EntrywiseWithin (posteriorEvaluationRadius p)
            (FactorRecursion.gram
              (matrix input.stateDimension input.stateDimension lower))
            (CovarianceRecursion.joseph (model input)
              (factorState input.stateDimension prior)
              (matrix input.stateDimension input.measurementDimension
                (gainArray gain))) := by
  let n := input.stateDimension
  let m := input.measurementDimension
  let k := matrix n m (gainArray gain)
  let w := (1 : LinearModel.Square n) - k * matrix m n input.observation
  let W : ℝ := 1 + m * gain.gainBound * innovation.observationBound
  have hK := gain.gain_nonneg
  have hH := innovation.observation_nonneg
  have hL := innovation.factor_nonneg
  have hT := p.noise_nonneg
  have hw : ∀ i j, |w i j| ≤ W := by
    intro i j
    have hm := product_magnitude k (matrix m n input.observation) _ _
      gain.gain_magnitude innovation.observation_magnitude i j
    have hi : |(1 : LinearModel.Square n) i j| ≤ 1 := by
      simp [Matrix.one_apply]; split_ifs <;> norm_num
    exact (abs_sub _ _).trans (add_le_add hi hm)
  have ekh := (FloatJosephError.product_within p.khProduct p.computeKH).2.2
  have ew := FloatJosephError.subtract_within (n := n) (m := n) p.wSum
    (by simp [identity, Flare.Matrix.Dense.identity, n]) p.computeW
  rw [FloatJosephError.identity_matrix] at ew
  have ewideal := within_trans ew (within_sub (within_refl (1 : LinearModel.Square n)) ekh)
  simp only [zero_add] at ewideal
  have ewl := within_trans (FloatJosephError.product_within p.wlProduct p.computeWL).2.2
    (within_mul_right ewideal (matrix n n prior.lower) hL innovation.factor_magnitude)
  have egl := FloatPrearray.gram_within ewl (by positivity : 0 ≤ (n : ℝ) * W * innovation.factorBound)
    (product_magnitude w (matrix n n prior.lower) W innovation.factorBound hw innovation.factor_magnitude)
  have ekt := (FloatJosephError.product_within p.ktrProduct p.computeKTR).2.2
  have egt := FloatPrearray.gram_within ekt (by positivity : 0 ≤ (m : ℝ) * gain.gainBound * p.noiseFactorBound)
    (product_magnitude k (matrix m m innovation.tr) _ _ gain.gain_magnitude p.noise_magnitude)
  have er := FloatCholeskyFactor.factor_backward_error m input.measurementNoise innovation.tr
    innovation.noiseMass innovation.noiseFloor innovation.noiseBound innovation.noise
  have etnoise := within_mul_right (within_mul_left k er hK gain.gain_magnitude) k.transpose hK
    (fun i j => gain.gain_magnitude j i)
  rw [FactorStructure.gram_mul] at egt
  have egtnoise := within_trans egt etnoise
  have epre := within_add egl egtnoise
  obtain ⟨_, _, l, hl, hs, hf, hp, _, eg⟩ :=
    FloatQRInitialDomain.gramFactor_accuracy_initial n (n + m) _ p.qrBudget p.qr
  rw [FloatPrearray.fromCols_gram] at eg
  have ec := within_trans eg epre
  refine ⟨l, hl, hs, hf, hp, ?_⟩
  convert ec using 1
  · unfold posteriorEvaluationRadius
    dsimp only [n, m, W]
    ring
  · simp only [CovarianceRecursion.joseph, model, factorState, FactorStructure.gram_mul, n, m, k]

/-- All four mean-update operations, including the imperfect computed gain. -/
theorem mean_accuracy (input : Input.Model) (prior : Input.FactorState)
    (innovation : InnovationProfile input prior) (gain : GainProfile innovation)
    (p : MeanProfile gain) (α K Z : ℝ) (hα : 0 < α) (hK : 0 ≤ K) (hZ : 0 ≤ Z)
    (hr
      : (matrix input.measurementDimension input.measurementDimension
            input.measurementNoise
          - α • 1).PosSemidef)
    (hk
      : ∀ i j,
          |CovarianceRecursion.gain (model input) (factorState input.stateDimension prior)
            i j|
          ≤ K)
    (hz
      : ∀ i,
          |CovarianceRecursion.innovation (model input)
            (factorState input.stateDimension prior)
            (vector input.measurementDimension input.measurement) i|
          ≤ Z)
    : p.mean.size = input.stateDimension
      ∧ p.mean.all Float.isFinite = true
      ∧ 0 ≤ meanRadius p α K Z
      ∧ ∀ i,
          |vector input.stateDimension p.mean i
            - (CovarianceRecursion.update .joseph (model input)
                (factorState input.stateDimension prior)
                (vector input.measurementDimension input.measurement)).mean
                i|
          ≤ meanRadius p α K Z := by
  let n := input.stateDimension
  let m := input.measurementDimension
  have eg := (gain_accuracy input prior innovation gain α hα hr).2
  have ep := (FloatJosephError.product_within p.projectedProduct p.computeProjected).2.2
  have er := FloatJosephError.subtract_within (n := m) (m := 1) p.residualSum
    (by simpa using p.measurement_shape) p.computeResidual
  have erz := within_trans er (within_sub (within_refl (matrix m 1 input.measurement)) ep)
  simp only [zero_add] at erz
  have hz' : ∀ (i : Fin m) (j : Fin 1), |(matrix m 1 input.measurement
      - matrix m n input.observation * matrix n 1 prior.mean) i j| ≤ Z := by
    intro i j
    fin_cases j
    simpa [CovarianceRecursion.innovation, model, factorState, vector, matrix,
      Flare.Matrix.Value.matrix, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hz i
  have einc := within_trans (FloatJosephError.product_within p.incrementProduct p.computeIncrement).2.2
    (within_mul eg erz hK hZ hk hz')
  have em := FloatJosephError.add_within (n := n) (m := 1) p.meanSum
    (by simpa using p.prior_shape) p.computeMean
  have eout := within_trans em (within_add (within_refl (matrix n 1 prior.mean)) einc)
  have eout' : EntrywiseWithin (meanRadius p α K Z) (matrix n 1 p.mean)
      (matrix n 1 prior.mean + CovarianceRecursion.gain (model input) (factorState n prior)
        * (matrix m 1 input.measurement - matrix m n input.observation * matrix n 1 prior.mean)) := by
    convert eout using 1
    unfold meanRadius
    dsimp only [n, m]
    ring
  obtain ⟨a, ha, hs, hf, _⟩ := FloatDenseError.add_accuracy prior.mean p.increment p.meanExponent
    p.meanSum.exponent_lower p.meanSum.exponent_upper p.meanSum.finite_left p.meanSum.finite_right
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using p.meanSum.magnitude)
  have he : a = p.mean := Except.ok.inj (ha.symm.trans p.computeMean)
  subst a
  refine ⟨hs.trans p.prior_shape, hf, eout'.1, ?_⟩
  intro i
  simpa [CovarianceRecursion.update, CovarianceRecursion.innovation, model, factorState,
    vector, matrix, Flare.Matrix.Value.matrix, Matrix.mul_apply, Matrix.mulVec,
    dotProduct]
    using eout'.2 i 0

/-- Complete native measurement update, with gain, noise, mean and posterior
factor errors composed against the ideal update from the same decoded prior.
All success and final validation assertions are proved from the stage profiles. -/
theorem update_accuracy (input : Input.Model) (prior : Input.FactorState)
    (innovation : InnovationProfile input prior) (gain : GainProfile innovation)
    (mean : MeanProfile gain) (posterior : PosteriorProfile gain)
    (α P R K Z : ℝ) (hα : 0 < α) (hP : 0 ≤ P) (hR : 0 ≤ R) (hK : 0 ≤ K) (hZ : 0 ≤ Z)
    (hr
      : (matrix input.measurementDimension input.measurementDimension
            input.measurementNoise
          - α • 1).PosSemidef)
    (hp : ∀ i j, |(factorState input.stateDimension prior).covariance i j| ≤ P)
    (hnoise : ∀ i j, |(model input).measurementNoise i j| ≤ R)
    (hk
      : ∀ i j,
          |CovarianceRecursion.gain (model input) (factorState input.stateDimension prior)
            i j|
          ≤ K)
    (hz
      : ∀ i,
          |CovarianceRecursion.innovation (model input)
            (factorState input.stateDimension prior)
            (vector input.measurementDimension input.measurement) i|
          ≤ Z)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.updateUnchecked input prior = .ok output
        ∧ Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
            (posteriorRadius posterior α P R K) (meanRadius mean α K Z)
            input.stateDimension output
            (CovarianceRecursion.update .joseph (model input)
              (factorState input.stateDimension prior)
              (vector input.measurementDimension input.measurement)) := by
  obtain ⟨hexe, eg⟩ := gain_accuracy input prior innovation gain α hα hr
  obtain ⟨l, hl, hs, hf, hlp, ec⟩ := posterior_evaluation_accuracy input prior innovation gain posterior
  obtain ⟨hms, hmf, hem, hm⟩ := mean_accuracy input prior innovation gain mean α K Z hα hK hZ hr hk hz
  have ej := RealErrorBounds.joseph_gain_accuracy (model input) (factorState input.stateDimension prior)
    (matrix input.stateDimension input.measurementDimension (gainArray gain))
    (CovarianceRecursion.gain (model input) (factorState input.stateDimension prior))
    (gainRadius gain α) P R innovation.observationBound K eg hP hR innovation.observation_nonneg hK
    hp hnoise innovation.observation_magnitude hk
  have eout := within_trans ec ej
  have hinc : multiply input.stateDimension input.measurementDimension 1
      (transpose input.measurementDimension input.stateDimension gain.solution) mean.residual
      = .ok mean.increment := mean.computeIncrement
  have hkh : multiply input.stateDimension input.measurementDimension input.stateDimension
      (transpose input.measurementDimension input.stateDimension gain.solution) input.observation
      = .ok posterior.kh := posterior.computeKH
  have hktr : multiply input.stateDimension input.measurementDimension input.measurementDimension
      (transpose input.measurementDimension input.stateDimension gain.solution) innovation.tr
      = .ok posterior.ktr := posterior.computeKTR
  refine ⟨⟨mean.mean, l⟩, ?_, ?_, eout, hem, hm⟩
  · simp [Kalman.Implementation.SquareRootFilter.updateUnchecked, innovation.noise.execution,
      innovation.computeProduct, innovation.computeQR, gain.computeProduct, hexe,
      mean.computeProjected, mean.computeResidual, hinc, mean.computeMean,
      hkh, posterior.computeW, posterior.computeWL, hktr, hl,
      bind, Except.bind, pure, Except.pure]
  · exact FloatFactorValidity.factor_validate_complete input.stateDimension _ hms hs hmf hf hlp

end Kalman.Proofs.FloatSquareRootUpdate
