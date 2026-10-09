import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.FloatMeanDomain

/-! Native prediction profiles and returned correction headroom from local
stored inputs. The prediction prearray keeps its actual [FL, T_Q] column order. -/

namespace Kalman.Proofs.FloatPredictionDomain

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.CorrelatedStages.Prediction
open Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-- Equal-width block exchange preserves the exact Gram and row energy.
It transfers an input domain, not a native QR output or operation schedule. -/
theorem prearray_swap_domain (a b : Array Float)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (d : GramFactorInputDomain 2 4 (fromCols 2 2 2 a b) 2)
    : GramFactorInputDomain 2 4 (fromCols 2 2 2 b a) 2 := by
  have hg : FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 b a))
      = FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 a b)) := by
    rw [FloatPrearray.fromCols_gram 2 2 2 b a, FloatPrearray.fromCols_gram 2 2 2 a b, add_comm]
  refine ⟨d.rows_le_columns, d.columns_le_eight, FloatPrearray.fromCols_size 2 2 2 b a,
    FloatPrearray.fromCols_finite 2 2 2 b a hb ha, d.budget_lower, d.budget_upper, ?_, ?_⟩
  · intro i
    have he : FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 a b)) i i ≤ (2 : ℝ)^2 / 2 := by
      simpa only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
        using d.row_energy i
    rw [← hg] at he
    simpa only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
      using he
  · simpa only [hg] using d.gram_lower

/-- The transition block needs only its own mass-eight product, not the
observation domain or a formed gain RHS. -/
theorem transition_product (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial)
    : ∃ fl,
        ProductProfile 2 2 2 input.transition initial.lower 8
        ∧ multiply 2 2 2 input.transition initial.lower = .ok fl
        ∧ fl.size = 4
        ∧ fl.all Float.isFinite = true
        ∧ EntrywiseWithin (productRadius 2 8) (matrix 2 2 fl)
            (matrix 2 2 input.transition * matrix 2 2 initial.lower) := by
  have pp := FloatGainDomain.product_profile_two input.transition initial.lower (1 / 8) 2
    p.transition_inputs.transition_finite p.transition_inputs.factor_finite
    (by norm_num) (by norm_num) (by norm_num)
    p.transition_inputs.transition_bound p.transition_inputs.factor_bound
  obtain ⟨fl, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy 2 2 2
    input.transition initial.lower (fun _ _ => (8 : ℝ))
    pp.inner_le pp.finite_left pp.finite_right
    (fun _ _ _ _ => pp.upper) (fun _ _ _ _ => pp.lower) pp.mass
  exact ⟨fl, pp, hr, hs, hf, ⟨by norm_num [productRadius], he⟩⟩

/-- Covariance structure supplies the rounded transition-block Gram bound.
Bounding individual FL entries would give insufficient QR energy headroom. -/
theorem transition_gram_bound (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial) (fl : Array Float)
    (hf : multiply 2 2 2 input.transition initial.lower = .ok fl)
    : ∀ i j,
        |FactorRecursion.gram (matrix 2 2 fl) i j|
        ≤ 1 / 8 + 2 * (2 * productRadius 2 8 * (1 / 2) + (productRadius 2 8) ^ 2) := by
  obtain ⟨fl', _, hr, _, _, he⟩ := transition_product input initial p
  have eq : fl' = fl := Except.ok.inj (hr.symm.trans hf)
  subst fl'
  have hF : ∀ i j, |matrix 2 2 input.transition i j| ≤ 1 / 8 :=
    fun i j => p.transition_inputs.transition_bound i.val j.val i.isLt j.isLt
  have hL : ∀ i j, |matrix 2 2 initial.lower i j| ≤ 2 :=
    fun i j => p.transition_inputs.factor_bound i.val j.val i.isLt j.isLt
  have hfl := product_magnitude (matrix 2 2 input.transition) (matrix 2 2 initial.lower)
    (1 / 8) 2 hF hL
  have htarget : ∀ i j,
      |(matrix 2 2 input.transition * matrix 2 2 initial.lower) i j| ≤ 1 / 2 :=
    fun i j => (hfl i j).trans (by norm_num)
  have hgram := FloatPrearray.gram_within he (by norm_num : (0 : ℝ) ≤ 1 / 2) htarget
  have hc := product_magnitude _ _ _ (1 / 8)
    (product_magnitude (matrix 2 2 input.transition)
      (FactorRecursion.gram (matrix 2 2 initial.lower)) (1 / 8) 2
      hF p.transition_inputs.covariance_bound) (fun i j => hF j i)
  have hc' : ∀ i j,
      |FactorRecursion.gram (matrix 2 2 input.transition * matrix 2 2 initial.lower) i j|
        ≤ 1 / 8 := by
    intro i j
    have ht := hc i j
    change |(matrix 2 2 input.transition * FactorRecursion.gram (matrix 2 2 initial.lower)
      * (matrix 2 2 input.transition).transpose) i j| ≤ _ at ht
    convert ht using 1
    · simp only [FactorRecursion.gram, Matrix.transpose_mul, Matrix.mul_assoc]
    · norm_num
  intro i j
  have hm := abs_sub_le (FactorRecursion.gram (matrix 2 2 fl) i j)
    (FactorRecursion.gram (matrix 2 2 input.transition * matrix 2 2 initial.lower) i j) 0
  simp only [sub_zero] at hm
  have herr := hgram.2 i j
  have ht := hc' i j
  norm_num only [Nat.cast_ofNat] at herr
  linarith only [hm, herr, ht]

/-- Stronger energy/rank margins remain available after assembling the actual
prediction prearray; they will bound the returned stored covariance. -/
theorem prearray_margins (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial) (tq fl : Array Float)
    (hq : cholesky 2 input.processNoise = .ok tq)
    (hf : multiply 2 2 2 input.transition initial.lower = .ok fl)
    : (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 fl tq))
        - (11 / 16 : ℝ) • 1).PosSemidef
      ∧ (∀ i,
          FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 fl tq)) i i ≤ 27 / 16) := by
  obtain ⟨tq', _, hq', _, _, _, _, _, he⟩ := FloatCholeskyDomain.cholesky_accuracy input.processNoise p.noise
  have eq : tq' = tq := Except.ok.inj (hq'.symm.trans hq)
  subst tq'
  have hfl := transition_gram_bound input initial p fl hf
  have hnoiseFloor := ErrorPropagation.lower_bound_of_error _ _ (3 / 4)
    ((2 : ℝ)^(-42 : Int)) (FloatCholeskyDomain.input_lower_bound input.processNoise p.noise)
    (CovarianceStructure.gram_posSemidef (matrix 2 2 tq)).isHermitian he
  have hpad : 0 ≤ (3 / 4 : ℝ) - 2 * (2 : ℝ)^(-42 : Int) - 11 / 16 := by norm_num
  have hnoisePadded := hnoiseFloor.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad)
  refine ⟨?_, ?_⟩
  · rw [FloatPrearray.fromCols_gram 2 2 2 fl tq]
    convert (CovarianceStructure.gram_posSemidef (matrix 2 2 fl)).add hnoisePadded using 1
    simp only [FactorRecursion.gram, Nat.cast_ofNat, sub_smul]
    module
  intro i
  have hnoiseDiag : FactorRecursion.gram (matrix 2 2 tq) i i ≤ 3 / 2 + (2 : ℝ)^(-42 : Int) := by
    have herr := (abs_le.mp (he.2 i i)).2
    have hd := p.noise_diagonal_cap i.val i.isLt
    change matrix 2 2 input.processNoise i i ≤ _ at hd
    change FactorRecursion.gram (matrix 2 2 tq) i i - matrix 2 2 input.processNoise i i ≤ _ at herr
    calc
      _ ≤ (2 : ℝ) ^ (-42 : Int) + matrix 2 2 input.processNoise i i :=
        (sub_le_iff_le_add).mp herr
      _ ≤ (2 : ℝ) ^ (-42 : Int) + 3 / 2 := add_le_add le_rfl hd
      _ = _ := add_comm _ _
  have hflDiag : FactorRecursion.gram (matrix 2 2 fl) i i
      ≤ 1 / 8 + 2 * (2 * productRadius 2 8 * (1 / 2) + (productRadius 2 8)^2) :=
    (le_abs_self _).trans (hfl i i)
  rw [FloatPrearray.fromCols_gram 2 2 2 fl tq, Matrix.add_apply]
  exact (add_le_add hflDiag hnoiseDiag).trans (by norm_num [productRadius])

/-- Original noise and covariance-aware FL energy derive the full QR input
domain in the actual [FL,T_Q] order. No rounded product energy is assumed. -/
theorem prearray_domain (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial) (tq fl : Array Float)
    (hq : cholesky 2 input.processNoise = .ok tq)
    (hf : multiply 2 2 2 input.transition initial.lower = .ok fl)
    : GramFactorInputDomain 2 4 (fromCols 2 2 2 fl tq) 2 := by
  obtain ⟨tq', _, hr, hqf, _, _, _, _, _⟩ :=
    FloatCholeskyDomain.cholesky_accuracy input.processNoise p.noise
  have eq : tq' = tq := Except.ok.inj (hr.symm.trans hq)
  subst tq'
  obtain ⟨fl', _, hr', _, hff, _⟩ := transition_product input initial p
  have eq' : fl' = fl := Except.ok.inj (hr'.symm.trans hf)
  subst fl'
  obtain ⟨hfloor, henergy⟩ := prearray_margins input initial p tq fl hq hf
  have hid := FloatQRInitialDomain.identity_input_domain 2 (by decide)
  refine ⟨
    by decide,
    by decide,
    FloatPrearray.fromCols_size 2 2 2 fl tq,
    FloatPrearray.fromCols_finite 2 2 2 fl tq hff hqf,
    hid.budget_lower,
    hid.budget_upper,
    ?_,
    ?_
  ⟩
  · intro i
    have hb := (henergy i).trans (by norm_num : (27 / 16 : ℝ) ≤ 2^2 / 2)
    simpa only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hb
  · convert hfloor.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : 0 ≤ (11 / 16 : ℝ) - 1 / 2)) using 1
    norm_num
    module

/-- Prediction mean uses a mass-eight product and leaves strict correction
headroom: its stored magnitude is at most 9/32. -/
theorem mean_stage (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial)
    : ∃ mean,
        ProductProfile 2 2 1 input.transition initial.mean 8
        ∧ multiply 2 2 1 input.transition initial.mean = .ok mean
        ∧ mean.size = 2
        ∧ mean.all Float.isFinite = true
        ∧ (∀ i, i < 2 → |value (mean.getD i 0.0)| ≤ 9 / 32) := by
  obtain ⟨mean, pp, hr, hs, hf, _, hm⟩ := FloatMeanDomain.vector_product
    input.transition initial.mean (1 / 8) 1 p.transition_inputs.transition_finite p.mean_finite
    (by norm_num) (by norm_num) p.transition_inputs.transition_bound p.mean_bound
  refine ⟨mean, pp, hr, hs, hf, ?_⟩
  intro i hi
  exact (hm i hi).trans (by norm_num [productRadius])

/-- All existing prediction profile fields follow from original local stored
inputs, without a Cholesky/product/QR execution or arithmetic profile premise. -/
theorem prediction_profile (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial)
    : ∃ prediction : PredictionProfile input initial,
        prediction.noiseMass = 8
        ∧ prediction.noiseFloor = 1 / 2
        ∧ prediction.noiseBound = 2
        ∧ prediction.productMass = 8
        ∧ prediction.meanMass = 8
        ∧ prediction.qrBudget = 2
        ∧ prediction.transitionBound = 1 / 8
        ∧ prediction.factorBound = 2
        ∧ (∀ i, i < 2 → |value (prediction.mean.getD i 0.0)| ≤ 9 / 32) := by
  obtain ⟨tq, _, pq, _, _, _⟩ := FloatCholeskyDomain.cholesky_profile input.processNoise p.noise
  obtain ⟨fl, pp, hp, _, _, _⟩ := transition_product input initial p
  obtain ⟨mean, pm, hmean, _, _, hm⟩ := mean_stage input initial p
  have d := prearray_domain input initial p tq fl pq.execution hp
  have htransition : ∀ n : Nat, n = 2 → ∀ i j : Nat, i < n → j < n →
      |value (entry n input.transition i j)| ≤ 1 / 8 := by
    intro n hn
    subst n
    intro i j hi hj
    exact (p.transition_inputs.transition_bound i j hi hj).trans (by norm_num)
  have hfactor : ∀ n : Nat, n = 2 → ∀ i j : Nat, i < n → j < n →
      |value (entry n initial.lower i j)| ≤ 2 := by
    intro n hn
    subst n
    exact p.transition_inputs.factor_bound
  let prediction : PredictionProfile input initial := {
    tq := tq, fl := fl, mean := mean
    noiseMass := 8, noiseFloor := 1 / 2, noiseBound := 2
    productMass := 8, meanMass := 8, qrBudget := 2, transitionBound := 1 / 8, factorBound := 2
    noise_shape := by simpa only [p.state_dimension] using p.noise.size
    noise_finite := p.noise.finite
    noise := by simpa only [p.state_dimension] using pq
    product := by simpa only [p.state_dimension] using pp
    computeProduct := by simpa only [p.state_dimension] using hp
    meanProduct := by simpa only [p.state_dimension] using pm
    computeMean := by simpa only [p.state_dimension] using hmean
    qr := by simpa only [p.state_dimension] using d
    transition_nonneg := by norm_num
    factor_nonneg := by norm_num
    transition_magnitude := fun i j => htransition _ p.state_dimension i.val j.val i.isLt j.isLt
    factor_magnitude := fun i j => hfactor _ p.state_dimension i.val j.val i.isLt j.isLt
  }
  exact ⟨prediction, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩

/-- Native prediction QR gives both a covariance floor and a covariance entry
cap, with enough slack for the next local innovation/gain domain. -/
theorem factor_output_bounds (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial) (tq fl l : Array Float)
    (hq : cholesky 2 input.processNoise = .ok tq)
    (hf : multiply 2 2 2 input.transition initial.lower = .ok fl)
    (hl
      : Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
          (fromCols 2 2 2 fl tq)
        = .ok l)
    : Kalman.Proofs.CholeskyProfiles.SolveDomain.FactorDomain l
      ∧ (FactorRecursion.gram (matrix 2 2 l) - (2 / 3 : ℝ) • 1).PosSemidef
      ∧ (∀ i j, |FactorRecursion.gram (matrix 2 2 l) i j| ≤ 7 / 4) := by
  have d := prearray_domain input initial p tq fl hq hf
  obtain ⟨hfloor, henergy⟩ := prearray_margins input initial p tq fl hq hf
  obtain ⟨l', hr, _, _, _, hp, _, he⟩ :=
    FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 4 _ 2 d
  have eq : l' = l := Except.ok.inj (hr.symm.trans hl)
  subst l'
  have hdiag : ∀ i, FactorRecursion.gram (matrix 2 2 l) i i ≤ 7 / 4 := by
    intro i
    have herr := (abs_le.mp (he.2 i i)).2
    have hen := henergy i
    change FactorRecursion.gram (matrix 2 2 l) i i
      - FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 fl tq)) i i ≤ _ at herr
    calc
      _ ≤ (2 : ℝ) ^ 2 / 33554432
          + FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 fl tq)) i i :=
        (sub_le_iff_le_add).mp herr
      _ ≤ (2 : ℝ) ^ 2 / 33554432 + 27 / 16 := add_le_add le_rfl hen
      _ ≤ _ := by norm_num
  have hreturnedFloor := ErrorPropagation.lower_bound_of_error _ _ (11 / 16)
    ((2 : ℝ)^2 / 33554432) hfloor hp.isHermitian he
  have hpad : 0 ≤ (11 / 16 : ℝ) - 2 * (2 : ℝ)^2 / 33554432 - 2 / 3 := by norm_num
  have hreturnedPadded := hreturnedFloor.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad)
  refine ⟨FloatQRFactorDomain.factor_domain_of_qr 4 _ l d hl, ?_, ?_⟩
  · convert hreturnedPadded using 1
    norm_num
    module
  intro i j
  have hs := Flare.Analysis.NumericalBounds.entry_sq_le_diagonal_product _ hp.posSemidef i j
  have hm : FactorRecursion.gram (matrix 2 2 l) i i * FactorRecursion.gram (matrix 2 2 l) j j
      ≤ (7 / 4 : ℝ)^2 := by
    have hi := hp.posSemidef.diag_nonneg (i := i)
    have hj := hp.posSemidef.diag_nonneg (i := j)
    nlinarith [hdiag i, hdiag j]
  nlinarith [sq_abs (FactorRecursion.gram (matrix 2 2 l) i j),
    abs_nonneg (FactorRecursion.gram (matrix 2 2 l) i j)]

/-- The closed local covariance allowance fits the refined absolute tolerance. -/
theorem local_covariance_radius_cap : localCovarianceRadius ≤ (2 : ℝ) ^ (-25 : Int) := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hη : (2 : ℝ)^(-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  simp only [localCovarianceRadius, qrGramRadius, iterationGramRadius, iterationRadius,
    sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius,
    reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
    productRadius, diagonalRadius, divisionRadius, residualRadius, hη]
  norm_num
  ring_nf
  linarith

/-- Actual prediction success, accuracy against original process noise, and
returned correction headroom, all derived from original local stored inputs. -/
theorem prediction_accuracy (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok output
        ∧ FactorAccuracy localCovarianceRadius ((2 : ℝ) ^ (-46 : Int))
            input.stateDimension output
            (CovarianceRecursion.predict (model input)
              (factorState input.stateDimension initial))
        ∧ (∀ i, i < 2 → |value (output.mean.getD i 0.0)| ≤ 9 / 32)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 output.lower i j)| ≤ 2)
        ∧ (∀ i j, |FactorRecursion.gram (matrix 2 2 output.lower) i j| ≤ 7 / 4)
        ∧ (FactorRecursion.gram (matrix 2 2 output.lower)
            - (2 / 3 : ℝ) • 1).PosSemidef := by
  obtain ⟨prediction, hqM, hqF, hqB, hP, hM, hQR, hF, hL, hm⟩ := prediction_profile input initial p
  obtain ⟨output, hr, ha⟩ := FloatSquareRootError.prediction_accuracy input initial prediction
  have d : GramFactorInputDomain 2 4 (fromCols 2 2 2 prediction.fl prediction.tq) 2 := by
    simpa only [p.state_dimension, hQR] using prediction.qr
  obtain ⟨l, hl, _, _, _, _, _, _⟩ :=
    FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 4 _ 2 d
  have hq : cholesky 2 input.processNoise = .ok prediction.tq := by
    simpa only [p.state_dimension] using prediction.noise.execution
  have hf : multiply 2 2 2 input.transition initial.lower = .ok prediction.fl := by
    simpa only [p.state_dimension] using prediction.computeProduct
  have hmean : multiply 2 2 1 input.transition initial.mean = .ok prediction.mean := by
    simpa only [p.state_dimension] using prediction.computeMean
  have hrun : Kalman.Implementation.SquareRootFilter.predictUnchecked input initial
      = .ok ⟨prediction.mean, l⟩ := by
    simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, hq, hf, hmean, p.state_dimension, hl,
      bind, Except.bind, pure, Except.pure]
  have eq : output = ⟨prediction.mean, l⟩ := Except.ok.inj (hr.symm.trans hrun)
  subst output
  obtain ⟨hd, hfloor, hcov⟩ := factor_output_bounds input initial p prediction.tq prediction.fl l hq hf hl
  have hcovRadius : predictionCovarianceRadius prediction = localCovarianceRadius := by
    simp only [predictionCovarianceRadius, localCovarianceRadius,
      p.state_dimension, hqM, hqF, hqB, hP, hQR, hF, hL]
    norm_num
  have hmeanRadius : predictionMeanRadius prediction = (2 : ℝ)^(-46 : Int) := by
    norm_num [predictionMeanRadius, productRadius, p.state_dimension, hM]
  exact ⟨_, hrun, hcovRadius ▸ hmeanRadius ▸ ha, hm, hd.entry_bound, hcov, hfloor⟩

private theorem factor_storage (output : Input.FactorState)
    (hv : output.validate 2 = .ok ())
    : output.mean.size = 2
      ∧ output.lower.size = 4
      ∧ output.mean.all Float.isFinite = true
      ∧ output.lower.all Float.isFinite = true := by
  cases hs : (output.mean.size == 2 && output.lower.size == 2 * 2) with
  | false => simp [Input.FactorState.validate, hs] at hv
  | true =>
      cases hf : (output.mean.all Float.isFinite && output.lower.all Float.isFinite) with
      | false => simp [Input.FactorState.validate, hs, hf] at hv
      | true =>
          obtain ⟨hm, hl⟩ := Bool.and_eq_true_iff.mp hs
          obtain ⟨hmf, hlf⟩ := Bool.and_eq_true_iff.mp hf
          exact ⟨of_decide_eq_true hm, of_decide_eq_true hl, hmf, hlf⟩

/-- Prediction establishes the entire reached local correction input domain
from stored initial/model bounds. Correction-stage profiles can then be derived
without assuming any predicted factor or predicted mean bound. -/
theorem prediction_correction_domain (input : Input.Model) (initial : Input.FactorState)
    (p : TwoStateDomain input initial) (q : CorrectionInputs input)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok output
        ∧ FactorAccuracy localCovarianceRadius ((2 : ℝ) ^ (-46 : Int))
            input.stateDimension output
            (CovarianceRecursion.predict (model input)
              (factorState input.stateDimension initial))
        ∧ Kalman.Proofs.CorrelatedStages.Mean.TwoStateDomain input output := by
  obtain ⟨output, hr, ha, hm, hl, hc, _⟩ := prediction_accuracy input initial p
  have hv : output.validate 2 = .ok () := by simpa only [p.state_dimension] using ha.1.1
  obtain ⟨hms, hls, hmf, hlf⟩ := factor_storage output hv
  have hg : Kalman.Proofs.CorrelatedStages.Gain.TwoStateDomain input.observation output.lower :=
    ⟨q.observation_size, hls, q.observation_finite, hlf, q.observation_bound, hl,
      fun i j => (hc i j).trans (by norm_num)⟩
  exact ⟨
    output,
    hr,
    ha,
    ⟨
      ⟨p.state_dimension, q.measurement_dimension, hg, q.noise, q.noise_diagonal_cap⟩,
      ⟨
        hms,
        q.measurement_size,
        hmf,
        q.measurement_finite,
        fun i hi => (hm i hi).trans (by norm_num),
        q.measurement_bound
      ⟩
    ⟩
  ⟩

/-- Nonzero transition/observation and correlated state with endpoint mean
and measurements witness the original local prediction/correction family. -/
theorem input_domain_nonempty
    : ∃ input : Input.Model,
      ∃ initial : Input.FactorState,
        TwoStateDomain input initial
        ∧ CorrectionInputs input
        ∧ input.transition = #[0.015625, 0.0, 0.0, 0.015625]
        ∧ initial.mean = #[1.0, -1.0]
        ∧ initial.lower = #[1.0, 0.0, 0.125, 1.0] := by
  obtain ⟨input, initial, d, _, _, hh, hl⟩ := FloatMeanDomain.input_domain_nonempty
  let input' := {input with transition := input.observation, processNoise := input.measurementNoise}
  let initial' := {initial with mean := #[1.0, -1.0]}
  have hneg := (Flare.Binary64.Order.neg_value (1.0 : Float) (by decide +kernel)).2
  have p : TwoStateDomain input' initial' := by
    refine ⟨d.state_dimension,
      ⟨d.gain_inputs.observation_size, d.gain_inputs.factor_size,
        d.gain_inputs.observation_finite, d.gain_inputs.factor_finite,
        fun i j hi hj => (d.gain_inputs.observation_bound i j hi hj).trans (by norm_num),
        d.gain_inputs.factor_bound, d.gain_inputs.covariance_bound⟩,
      d.noise, d.noise_diagonal_cap,
      by change (#[1.0, -1.0] : Array Float).size = 2; decide,
      by change (#[1.0, -1.0] : Array Float).all Float.isFinite = true; decide +kernel, ?_⟩
    intro i hi
    interval_cases i <;> norm_num [initial', Flare.Binary64.Arithmetic.one_value, hneg]
  have q : CorrectionInputs input' :=
    ⟨d.measurement_dimension, d.gain_inputs.observation_size, d.gain_inputs.observation_finite,
      d.gain_inputs.observation_bound, d.noise, d.noise_diagonal_cap, d.vectors.measurement_size,
      d.vectors.measurement_finite, d.vectors.measurement_bound⟩
  exact ⟨input', initial', p, q, hh, rfl, hl⟩

end Kalman.Proofs.FloatPredictionDomain
