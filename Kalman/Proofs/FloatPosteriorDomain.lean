import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.FloatPredictionDomain
import Kalman.Proofs.FloatPosteriorPrearray

/-! Native posterior profile discharge and returned-state bounds on the
two-state prediction/correction family. The gain is the computed native gain. -/

namespace Kalman.Proofs.FloatPosteriorDomain

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.CorrelatedStages.Posterior
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1200000

/-- Prediction establishes the posterior domain, including the stronger
covariance margins, from the original stored prediction and correction inputs. -/
theorem prediction_posterior_domain (input : Input.Model) (initial : Input.FactorState)
    (p : Kalman.Proofs.CorrelatedStages.Prediction.TwoStateDomain input initial)
    (q
      : Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.CorrectionInputs
          input)
    : ∃ prior,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok prior
        ∧ TwoStateDomain input prior := by
  obtain ⟨prior, hr, _, _, _, hc, hf⟩ := FloatPredictionDomain.prediction_accuracy input initial p
  obtain ⟨prior', hr', _, hm⟩ := FloatPredictionDomain.prediction_correction_domain input initial p q
  have eq : prior' = prior := Except.ok.inj (hr'.symm.trans hr)
  subst prior'
  exact ⟨prior, hr, hm, hf, hc⟩

/-- A nonzero original transition/observation and correlated initial factor
reach this local posterior domain. Its input margins are not assumed afterward. -/
theorem input_domain_nonempty
    : ∃ input : Input.Model,
      ∃ initial prior : Input.FactorState,
        Kalman.Proofs.CorrelatedStages.Prediction.TwoStateDomain input initial
        ∧ Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.CorrectionInputs
            input
        ∧ input.transition = #[0.015625, 0.0, 0.0, 0.015625]
        ∧ initial.lower = #[1.0, 0.0, 0.125, 1.0]
        ∧ Kalman.Implementation.SquareRootFilter.predictUnchecked input initial
          = .ok prior
        ∧ TwoStateDomain input prior := by
  obtain ⟨input, initial, p, q, hF, _, hL⟩ := FloatPredictionDomain.input_domain_nonempty
  obtain ⟨prior, hr, hd⟩ := prediction_posterior_domain input initial p q
  exact ⟨input, initial, prior, p, q, hF, hL, hr, hd⟩

/-- The derived innovation/gain constants give a small original-model gain
error even using the coarser public QR cap. -/
theorem gain_radius_cap (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior) (innovation : InnovationProfile input prior)
    (gain : GainProfile innovation) (g : GainParameters gain)
    : gainRadius gain (3 / 4) ≤ (2 : ℝ) ^ (-20 : Int) := by
  have hqr := FloatQRDomain.qrGramRadius_le_eight_refined 4 2 2 (by decide) (by decide) (by norm_num)
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hη : (2 : ℝ)^(-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)
  simp only [gainRadius, gainResidualRadius, innovationRadius,
    p.state_dimension, p.measurement_dimension, g.noise_mass, g.noise_floor, g.noise_bound,
    g.innovation_product_mass, g.innovation_qr_budget, g.observation_bound, g.factor_bound,
    g.gain_product_mass, g.solve_mass, g.solve_floor, g.solve_bound, g.gain_bound,
    productRadius, diagonalRadius, divisionRadius, residualRadius, hη]
  norm_num at hqr ⊢
  linarith

/-- The stronger reached covariance cap sharpens the ideal gain to 7/48. -/
theorem ideal_gain_magnitude (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∀ i j,
        |CovarianceRecursion.gain (model input) (factorState input.stateDimension prior) i
          j|
        ≤ 7 / 48 := by
  have hr := (FloatMeanDomain.ideal_mean_operand_bounds input prior p.toMeanDomain).1
  have hpn : ∀ n : Nat, n = 2 → ∀ i j,
      |FactorRecursion.gram (matrix n n prior.lower) i j| ≤ 7 / 4 := by
    intro n hn
    subst n
    exact p.covariance_bound
  have hH : ∀ i j, |matrix input.measurementDimension input.stateDimension input.observation i j| ≤ 1 / 64 := by
    intro i j
    have hi : i.val < 2 := by simpa only [p.measurement_dimension] using i.isLt
    have hj : j.val < 2 := by simpa only [p.state_dimension] using j.isLt
    simpa only [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry,
      p.state_dimension]
      using p.gain_inputs.observation_bound i.val j.val hi hj
  have hg := RecursionSensitivity.gain_magnitude (model input) (factorState input.stateDimension prior)
    (3 / 4) (7 / 4) (1 / 64) (by norm_num) (by norm_num) (by norm_num)
    (CovarianceStructure.gram_posSemidef (matrix input.stateDimension input.stateDimension prior.lower))
    hr (hpn _ p.state_dimension) hH
  have hcap : Kalman.Definitions.Theorems.RecursionSensitivity.gainMagnitude
      input.stateDimension input.measurementDimension (3 / 4) (7 / 4) (1 / 64) ≤ 7 / 48 := by
    norm_num [Kalman.Definitions.Theorems.RecursionSensitivity.gainMagnitude, p.state_dimension, p.measurement_dimension]
  exact fun i j => (hg i j).trans hcap

/-- Original-model gain error leaves native gain magnitude at most 1/6.
The gain is still the result of rounded products and both substitution passes. -/
theorem stored_gain_magnitude (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior) (innovation : InnovationProfile input prior)
    (gain : GainProfile innovation) (g : GainParameters gain)
    : ∀ i j, i < 2 → j < 2 → |value (entry 2 (gainArray gain) i j)| ≤ 1 / 6 := by
  have hr := (FloatMeanDomain.ideal_mean_operand_bounds input prior p.toMeanDomain).1
  have he := (FloatSquareRootUpdate.gain_accuracy input prior innovation gain (3 / 4) (by norm_num) hr).2
  have hcap := gain_radius_cap input prior p innovation gain g
  have hideal := ideal_gain_magnitude input prior p
  intro i j hi hj
  have hi' : i < input.stateDimension := by simpa only [p.state_dimension] using hi
  have hj' : j < input.measurementDimension := by simpa only [p.measurement_dimension] using hj
  have hm := abs_sub_le (matrix input.stateDimension input.measurementDimension (gainArray gain) ⟨i, hi'⟩ ⟨j, hj'⟩)
    (CovarianceRecursion.gain (model input) (factorState input.stateDimension prior) ⟨i, hi'⟩ ⟨j, hj'⟩) 0
  simp only [sub_zero] at hm
  have hh := hm.trans (add_le_add ((he.2 ⟨i, hi'⟩ ⟨j, hj'⟩).trans hcap) (hideal ⟨i, hi'⟩ ⟨j, hj'⟩))
  have hb := hh.trans (by norm_num : (2 : ℝ)^(-20 : Int) + 7 / 48 ≤ 1 / 6)
  simpa only [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry,
    p.measurement_dimension]
    using hb

/-- Native measurement-noise factor entry bounds and its exact Gram cap.
The original noise factorization error is included in the latter. -/
theorem noise_factor_bounds (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior) (innovation : InnovationProfile input prior)
    : Kalman.Proofs.CholeskyProfiles.SolveDomain.FactorDomain innovation.tr
      ∧ (∀ i j, |FactorRecursion.gram (matrix 2 2 innovation.tr) i j| ≤ 25 / 16) := by
  have hrun : cholesky 2 input.measurementNoise = .ok innovation.tr := by
    simpa only [p.measurement_dimension] using innovation.noise.execution
  have d := FloatCholeskySolveDomain.factor_domain_of_cholesky input.measurementNoise innovation.tr p.noise hrun
  obtain ⟨tr, _, hr, _, _, _, _, _, he⟩ := FloatCholeskyDomain.cholesky_accuracy input.measurementNoise p.noise
  have eq : tr = innovation.tr := Except.ok.inj (hr.symm.trans hrun)
  subst tr
  have hd : ∀ i, FactorRecursion.gram (matrix 2 2 innovation.tr) i i ≤ 25 / 16 := by
    intro i
    have hdiag := p.noise_diagonal_cap i.val i.isLt
    have herr := (abs_le.mp (he.2 i i)).2
    change FactorRecursion.gram (matrix 2 2 innovation.tr) i i - matrix 2 2 input.measurementNoise i i ≤ _ at herr
    change matrix 2 2 input.measurementNoise i i ≤ _ at hdiag
    exact ((sub_le_iff_le_add).mp herr).trans ((add_le_add le_rfl hdiag).trans (by norm_num))
  have hp := CovarianceStructure.gram_posSemidef (matrix 2 2 innovation.tr)
  refine ⟨d, ?_⟩
  intro i j
  have hs := Flare.Analysis.NumericalBounds.entry_sq_le_diagonal_product _ hp i j
  have hm : FactorRecursion.gram (matrix 2 2 innovation.tr) i i * FactorRecursion.gram (matrix 2 2 innovation.tr) j j
      ≤ (25 / 16 : ℝ)^2 := by nlinarith [hd i, hd j, hp.diag_nonneg (i := i), hp.diag_nonneg (i := j)]
  nlinarith [sq_abs (FactorRecursion.gram (matrix 2 2 innovation.tr) i j),
    abs_nonneg (FactorRecursion.gram (matrix 2 2 innovation.tr) i j)]

/-- Every posterior profile field and its additional energy margin are derived
from reached stored-input bounds and the derived innovation/gain parameters. -/
theorem posterior_profile (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior) (innovation : InnovationProfile input prior)
    (gain : GainProfile innovation) (g : GainParameters gain)
    : ∃ posterior : PosteriorProfile gain,
        PosteriorParameters posterior
        ∧ (∀ i,
            FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 posterior.wl posterior.ktr))
              i i
            ≤ 63 / 32) := by
  have hk := stored_gain_magnitude input prior p innovation gain g
  have hkf : (gainArray gain).all Float.isFinite = true :=
    (Flare.Matrix.Multiplication.transpose_storage input.measurementDimension input.stateDimension
      gain.solution gain.finite_solution).2.1
  obtain ⟨dt, ht⟩ := noise_factor_bounds input prior p innovation
  obtain ⟨s, he⟩ := FloatPosteriorPrearray.arithmetic_stages (gainArray gain) input.observation prior.lower innovation.tr
    hkf p.gain_inputs.observation_finite p.gain_inputs.factor_finite dt.finite
    hk p.gain_inputs.observation_bound p.gain_inputs.factor_bound dt.entry_bound
  obtain ⟨d, hd⟩ := FloatPosteriorPrearray.prearray_domain (gainArray gain) input.observation prior.lower innovation.tr s he
    (fun i j => p.gain_inputs.observation_bound i.val j.val i.isLt j.isLt)
    (fun i j => hk i.val j.val i.isLt j.isLt) p.covariance_bound p.covariance_floor ht
  have htr : ∀ n : Nat, n = 2 → ∀ i j : Nat, i < n → j < n →
      |value (entry n innovation.tr i j)| ≤ 2 := by
    intro n hn
    subst n
    exact dt.entry_bound
  let posterior : PosteriorProfile gain := {
    kh := s.kh, w := s.w, wl := s.wl, ktr := s.ktr
    khMass := 8, wlMass := 8, ktrMass := 8, qrBudget := 2, noiseFactorBound := 2, wExponent := 2
    khProduct := by simpa only [p.state_dimension, p.measurement_dimension] using s.kh_product
    computeKH := by simpa only [p.state_dimension, p.measurement_dimension] using s.compute_kh
    wSum := by simpa only [p.state_dimension] using s.w_sum
    computeW := by simpa only [p.state_dimension] using s.compute_w
    wlProduct := by simpa only [p.state_dimension] using s.wl_product
    computeWL := by simpa only [p.state_dimension] using s.compute_wl
    ktrProduct := by simpa only [p.state_dimension, p.measurement_dimension] using s.ktr_product
    computeKTR := by simpa only [p.state_dimension, p.measurement_dimension] using s.compute_ktr
    qr := by simpa only [p.state_dimension, p.measurement_dimension] using d
    noise_nonneg := by norm_num
    noise_magnitude := fun i j => htr _ p.measurement_dimension i.val j.val i.isLt j.isLt
  }
  exact ⟨posterior, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hd⟩

/-- Innovation, gain, mean and posterior profiles are all conclusions of the
local correction input domain. No intermediate successful run is a premise. -/
theorem correction_profiles (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∃ innovation : InnovationProfile input prior,
      ∃ gain : GainProfile innovation,
        GainParameters gain
        ∧ ∃ mean : MeanProfile gain,
            mean.projectedMass = 8
            ∧ mean.incrementMass = 8
            ∧ mean.residualExponent = 2
            ∧ mean.meanExponent = 2
            ∧ (∀ i, i < 2 → |value (mean.mean.getD i 0.0)| ≤ 1)
            ∧ ∃ posterior : PosteriorProfile gain,
                PosteriorParameters posterior
                ∧ (∀ i,
                    FactorRecursion.gram
                      (matrix 2 4 (fromCols 2 2 2 posterior.wl posterior.ktr)) i i
                    ≤ 63 / 32) := by
  obtain ⟨innovation, gain, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    mean, hm1, hm2, hm3, hm4, _, _, hm, _⟩ := FloatMeanDomain.correction_profiles input prior p.toMeanDomain
  have g : GainParameters gain := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  obtain ⟨posterior, pp, hd⟩ := posterior_profile input prior p innovation gain g
  exact ⟨innovation, gain, g, mean, hm1, hm2, hm3, hm4, hm, posterior, pp, hd⟩

/-- QR rounding preserves covariance-entry cap two, and derives factor bounds
for the next prediction. This concerns the exact Gram of retained words. -/
theorem posterior_output_bounds (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior) (innovation : InnovationProfile input prior)
    (gain : GainProfile innovation) (posterior : PosteriorProfile gain)
    (q : PosteriorParameters posterior)
    (hd
      : ∀ i,
          FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 posterior.wl posterior.ktr)) i
            i
          ≤ 63 / 32)
    (l : Array Float)
    (hl
      : Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
          (fromCols 2 2 2 posterior.wl posterior.ktr)
        = .ok l)
    : Kalman.Proofs.CholeskyProfiles.SolveDomain.FactorDomain l
      ∧ (∀ i j, |FactorRecursion.gram (matrix 2 2 l) i j| ≤ 2) := by
  have d : GramFactorInputDomain 2 4 (fromCols 2 2 2 posterior.wl posterior.ktr) 2 := by
    simpa only [p.state_dimension, p.measurement_dimension, q.qr_budget]
      using posterior.qr
  obtain ⟨l', hr, _, _, _, hp, _, he⟩ := FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 4 _ 2 d
  have eq : l' = l := Except.ok.inj (hr.symm.trans hl)
  subst l'
  have hdiag : ∀ i, FactorRecursion.gram (matrix 2 2 l) i i ≤ 2 := by
    intro i
    have herr := (abs_le.mp (he.2 i i)).2
    change FactorRecursion.gram (matrix 2 2 l) i i
      - FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 posterior.wl posterior.ktr)) i i ≤ _ at herr
    exact ((sub_le_iff_le_add).mp herr).trans ((add_le_add le_rfl (hd i)).trans (by norm_num))
  refine ⟨FloatQRFactorDomain.factor_domain_of_qr 4 _ l d hl, ?_⟩
  intro i j
  have hs := Flare.Analysis.NumericalBounds.entry_sq_le_diagonal_product _ hp.posSemidef i j
  have hm : FactorRecursion.gram (matrix 2 2 l) i i * FactorRecursion.gram (matrix 2 2 l) j j ≤ 2^2 := by
    nlinarith [hdiag i, hdiag j, hp.posSemidef.diag_nonneg (i := i), hp.posSemidef.diag_nonneg (i := j)]
  nlinarith [sq_abs (FactorRecursion.gram (matrix 2 2 l) i j), abs_nonneg (FactorRecursion.gram (matrix 2 2 l) i j)]

/-- Original measurement-noise entry bound, including correlated inputs. -/
theorem original_noise_magnitude (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∀ i j, |(model input).measurementNoise i j| ≤ 3 / 2 := by
  have hp := (FloatCholeskyDomain.input_positive input.measurementNoise p.noise).posSemidef
  have hd : ∀ i : Fin 2, matrix 2 2 input.measurementNoise i i ≤ 3 / 2 :=
    fun i => p.noise_diagonal_cap i.val i.isLt
  have hm : ∀ i j : Fin 2, |matrix 2 2 input.measurementNoise i j| ≤ 3 / 2 := by
    intro i j
    have hs := Flare.Analysis.NumericalBounds.entry_sq_le_diagonal_product _ hp i j
    have hh : matrix 2 2 input.measurementNoise i i * matrix 2 2 input.measurementNoise j j ≤ (3 / 2 : ℝ)^2 := by
      nlinarith [hd i, hd j, hp.diag_nonneg (i := i), hp.diag_nonneg (i := j)]
    nlinarith [sq_abs (matrix 2 2 input.measurementNoise i j), abs_nonneg (matrix 2 2 input.measurementNoise i j)]
  have hmn : ∀ m : Nat, m = 2 → ∀ i j : Fin m, |matrix m m input.measurementNoise i j| ≤ 3 / 2 := by
    intro m hdim
    subst m
    exact hm
  exact hmn _ p.measurement_dimension

/-- The derived local posterior parameters retain the refined covariance
tolerance, including computed-gain and original-noise factorization error. -/
theorem posterior_radius_cap (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior) (innovation : InnovationProfile input prior)
    (gain : GainProfile innovation) (g : GainParameters gain)
    (posterior : PosteriorProfile gain) (q : PosteriorParameters posterior)
    : posteriorRadius posterior (3 / 4) (7 / 4) (3 / 2) (1 / 6)
      ≤ (2 : ℝ) ^ (-25 : Int) := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hη : (2 : ℝ)^(-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  have hη3 := pow_le_one₀ hη0 hη1 (n := 3)
  have hη4 := pow_le_one₀ hη0 hη1 (n := 4)
  simp only [posteriorRadius, posteriorEvaluationRadius, gainRadius, gainResidualRadius, innovationRadius,
    p.state_dimension, p.measurement_dimension, g.noise_mass, g.noise_floor, g.noise_bound,
    g.innovation_product_mass, g.innovation_qr_budget, g.observation_bound, g.factor_bound,
    g.gain_product_mass, g.solve_mass, g.solve_floor, g.solve_bound, g.gain_bound,
    q.kh_mass, q.wl_mass, q.ktr_mass, q.qr_budget, q.noise_factor_bound, q.w_exponent,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius,
    columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius,
    Finset.sum_range_succ, Finset.sum_range_zero, productRadius, diagonalRadius, divisionRadius,
    residualRadius, sumRadius, hη]
  norm_num
  ring_nf
  linarith

/-- Complete native correction from reached stored input margins: successful
execution, both local accuracy budgets, PD stored-factor covariance, and the
mean/factor/covariance caps required by the next prediction. -/
theorem correction_accuracy_and_bounds (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.updateUnchecked input prior = .ok output
        ∧ Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
            ((2 : ℝ) ^ (-25 : Int)) ((2 : ℝ) ^ (-25 : Int)) input.stateDimension output
            (CovarianceRecursion.update .joseph (model input)
              (factorState input.stateDimension prior)
              (vector input.measurementDimension input.measurement))
        ∧ (factorState input.stateDimension output).covariance.PosDef
        ∧ (∀ i, i < 2 → |value (output.mean.getD i 0.0)| ≤ 1)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 output.lower i j)| ≤ 2)
        ∧ (∀ i j, |FactorRecursion.gram (matrix 2 2 output.lower) i j| ≤ 2) := by
  obtain ⟨innovation, gain, g, mean, hm1, hm2, hm3, hm4, hm, posterior, q, hd⟩ := correction_profiles input prior p
  obtain ⟨hr, hk, hz⟩ := FloatMeanDomain.ideal_mean_operand_bounds input prior p.toMeanDomain
  have hp : ∀ i j, |(factorState input.stateDimension prior).covariance i j| ≤ 7 / 4 := by
    have hpn : ∀ n : Nat, n = 2 → ∀ i j,
        |FactorRecursion.gram (matrix n n prior.lower) i j| ≤ 7 / 4 := by
      intro n hn
      subst n
      exact p.covariance_bound
    exact hpn _ p.state_dimension
  obtain ⟨output, hu, ha⟩ := FloatSquareRootUpdate.update_accuracy input prior innovation gain mean posterior
    (3 / 4) (7 / 4) (3 / 2) (1 / 6) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hr hp (original_noise_magnitude input prior p) hk hz
  obtain ⟨l, hl, _, _, _, _⟩ := FloatSquareRootUpdate.posterior_evaluation_accuracy input prior innovation gain posterior
  have hl2 : Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
      (fromCols 2 2 2 posterior.wl posterior.ktr) = .ok l := by
    simpa only [p.state_dimension, p.measurement_dimension] using hl
  have hgain := (FloatSquareRootUpdate.gain_accuracy input prior innovation gain (3 / 4) (by norm_num) hr).1
  have hinc : multiply input.stateDimension input.measurementDimension 1
      (transpose input.measurementDimension input.stateDimension gain.solution) mean.residual = .ok mean.increment := mean.computeIncrement
  have hkh : multiply input.stateDimension input.measurementDimension input.stateDimension
      (transpose input.measurementDimension input.stateDimension gain.solution) input.observation = .ok posterior.kh := posterior.computeKH
  have hktr : multiply input.stateDimension input.measurementDimension input.measurementDimension
      (transpose input.measurementDimension input.stateDimension gain.solution) innovation.tr = .ok posterior.ktr := posterior.computeKTR
  have hrun : Kalman.Implementation.SquareRootFilter.updateUnchecked input prior = .ok ⟨mean.mean, l⟩ := by
    simp [Kalman.Implementation.SquareRootFilter.updateUnchecked, innovation.noise.execution,
      innovation.computeProduct, innovation.computeQR, gain.computeProduct, hgain,
      mean.computeProjected, mean.computeResidual, hinc, mean.computeMean, hkh,
      posterior.computeW, posterior.computeWL, hktr, hl, bind, Except.bind, pure, Except.pure]
  have eq : output = ⟨mean.mean, l⟩ := Except.ok.inj (hu.symm.trans hrun)
  subst output
  obtain ⟨dl, hc⟩ := posterior_output_bounds input prior p innovation gain posterior q hd l hl2
  have hmean : meanRadius mean (3 / 4) (1 / 6) 2 = Kalman.Proofs.CorrelatedStages.Mean.localMeanRadius := by
    simp only [meanRadius, gainRadius, gainResidualRadius, innovationRadius,
      Kalman.Proofs.CorrelatedStages.Mean.localMeanRadius,
      p.state_dimension, p.measurement_dimension, g.noise_mass, g.noise_floor, g.noise_bound,
      g.innovation_product_mass, g.innovation_qr_budget, g.observation_bound, g.factor_bound,
      g.gain_product_mass, g.solve_mass, g.solve_floor, g.solve_bound, g.gain_bound, hm1, hm2, hm3, hm4]
    norm_num
  have hmc : meanRadius mean (3 / 4) (1 / 6) 2 ≤ (2 : ℝ)^(-25 : Int) := by
    rw [hmean]
    exact FloatMeanDomain.local_mean_radius_cap
  have hpc := posterior_radius_cap input prior p innovation gain g posterior q
  have ha' : Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
      ((2 : ℝ)^(-25 : Int)) ((2 : ℝ)^(-25 : Int)) input.stateDimension ⟨mean.mean, l⟩
      (CovarianceRecursion.update .joseph (model input) (factorState input.stateDimension prior)
        (vector input.measurementDimension input.measurement)) :=
    ⟨ha.1, ⟨by positivity, fun i j => (ha.2.1.2 i j).trans hpc⟩,
      by positivity, fun i => (ha.2.2.2 i).trans hmc⟩
  exact ⟨
    _,
    hrun,
    ha',
    FloatFactorValidity.validFactor_posDef _ _ ha'.1,
    hm,
    dl.entry_bound,
    hc
  ⟩

end Kalman.Proofs.FloatPosteriorDomain
