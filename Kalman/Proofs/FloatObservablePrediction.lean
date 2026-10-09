import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Proofs.FloatDiagonalStorage
import Kalman.Proofs.FloatPredictionDomain

/-! Local native prediction at diagonal transition magnitude one. Original
stored noise and covariance energy derive every stage profile, success, error
and innovation headroom. FloatObservableDiagonal adds returned diagonality;
FloatObservableFilter composes complete steps; accumulated observable
trajectory accuracy remains separate work. -/

namespace Kalman.Proofs.FloatObservablePrediction

open Matrix
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.DiagonalStages.Prediction
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

theorem noise_input_floor (a : Array Float) (d : NoiseDomain a)
    : (matrix 2 2 a - (1 : ℝ) • 1).PosSemidef := by
  rw [FloatDiagonalStorage.matrix_diagonal 2 a d.diagonal, smul_one_eq_diagonal, diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  change 0 ≤ value (entry 2 a i.val i.val) - 1
  linarith [d.covariance.diagonal_lower i.val i.isLt]

theorem noise_margins (a l : Array Float) (d : NoiseDomain a) (hl : cholesky 2 a = .ok l)
    : (FactorRecursion.gram (matrix 2 2 l) - (63 / 64 : ℝ) • 1).PosSemidef
      ∧ (∀ i,
          FactorRecursion.gram (matrix 2 2 l) i i ≤ 3 / 2 + (2 : ℝ) ^ (-42 : Int)) := by
  obtain ⟨l', _, hr, _, _, _, hp, _, he⟩ := FloatCholeskyDomain.cholesky_accuracy a d.covariance
  have eq : l' = l := Except.ok.inj (hr.symm.trans hl)
  subst l'
  have hf := lower_bound_of_error _ _ 1 ((2 : ℝ)^(-42 : Int))
    (noise_input_floor a d) hp.isHermitian he
  have hpad : 0 ≤ (1 : ℝ) - 2 * (2 : ℝ)^(-42 : Int) - 63 / 64 := by norm_num
  refine ⟨?_, ?_⟩
  · convert hf.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad) using 1
    norm_num [FactorRecursion.gram]
    module
  · intro i
    have herr := (abs_le.mp (he.2 i i)).2
    have hb := d.diagonal_cap i.val i.isLt
    change FactorRecursion.gram (matrix 2 2 l) i i - value (entry 2 a i.val i.val) ≤ _ at herr
    norm_num at herr ⊢
    linarith only [herr, hb]

theorem transition_product (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial)
    : ∃ fl,
        ProductProfile 2 2 2 input.transition initial.lower 8
        ∧ multiply 2 2 2 input.transition initial.lower = .ok fl
        ∧ fl.size = 4
        ∧ fl.all Float.isFinite = true
        ∧ EntrywiseWithin (productRadius 2 8) (matrix 2 2 fl)
            (matrix 2 2 input.transition * matrix 2 2 initial.lower) := by
  have pp := FloatGainDomain.product_profile_two input.transition initial.lower 1 2
    d.transition_finite d.factor_finite (by norm_num) (by norm_num) (by norm_num)
    d.transition_bound d.factor_bound
  obtain ⟨fl, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy 2 2 2
    input.transition initial.lower (fun _ _ => (8 : ℝ)) pp.inner_le pp.finite_left pp.finite_right
    (fun _ _ _ _ => pp.upper) (fun _ _ _ _ => pp.lower) pp.mass
  exact ⟨fl, pp, hr, hs, hf, ⟨by norm_num [productRadius], he⟩⟩

theorem transition_gram_diagonal_bound (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial) (fl : Array Float)
    (hl : multiply 2 2 2 input.transition initial.lower = .ok fl)
    : ∀ i,
        FactorRecursion.gram (matrix 2 2 fl) i i
        ≤ 13 / 8 + 2 * (2 * productRadius 2 8 * 4 + (productRadius 2 8) ^ 2) := by
  obtain ⟨fl', _, hr, _, _, he⟩ := transition_product input initial d
  have eq : fl' = fl := Except.ok.inj (hr.symm.trans hl)
  subst fl'
  have htarget := product_magnitude (matrix 2 2 input.transition) (matrix 2 2 initial.lower) 1 2
    (fun i j => d.transition_bound i.val j.val i.isLt j.isLt)
    (fun i j => d.factor_bound i.val j.val i.isLt j.isLt)
  have hgram := FloatPrearray.gram_within he (by norm_num : (0 : ℝ) ≤ 4)
    (fun i j => (htarget i j).trans (by norm_num))
  have hdiag := FloatDiagonalStorage.matrix_diagonal 2 input.transition d.transition_diagonal
  intro i
  have hb : FactorRecursion.gram (matrix 2 2 input.transition * matrix 2 2 initial.lower) i i
      ≤ 13 / 8 := by
    rw [FactorStructure.gram_mul, hdiag]
    simp only [diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hf := d.transition_bound i.val i.val i.isLt i.isLt
    change |matrix 2 2 input.transition i i| ≤ 1 at hf
    have hp := (CovarianceStructure.gram_posSemidef (matrix 2 2 initial.lower)).diag_nonneg (i := i)
    have hf2 : (matrix 2 2 input.transition i i)^2 ≤ 1 := by
      nlinarith [(abs_le.mp hf).1, (abs_le.mp hf).2]
    have hm := mul_le_mul_of_nonneg_right hf2 hp
    nlinarith [d.covariance_diagonal_cap i]
  have herr := (abs_le.mp (hgram.2 i i)).2
  norm_num only [Nat.cast_ofNat] at herr
  linarith

theorem prearray_margins (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial) (tq fl : Array Float)
    (hq : cholesky 2 input.processNoise = .ok tq)
    (hf : multiply 2 2 2 input.transition initial.lower = .ok fl)
    : (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 fl tq))
        - (63 / 64 : ℝ) • 1).PosSemidef
      ∧ (∀ i,
          FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 fl tq)) i i ≤ 51 / 16) := by
  obtain ⟨hn, he⟩ := noise_margins input.processNoise tq d.noise hq
  rw [FloatPrearray.fromCols_gram 2 2 2 fl tq]
  refine ⟨?_, ?_⟩
  · convert (CovarianceStructure.gram_posSemidef (matrix 2 2 fl)).add hn using 1
    module
  · intro i
    have ht := transition_gram_diagonal_bound input initial d fl hf i
    have hnoise := he i
    simp only [Matrix.add_apply]
    exact (add_le_add ht hnoise).trans (by norm_num [productRadius])

theorem prearray_domain (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial) (tq fl : Array Float)
    (hq : cholesky 2 input.processNoise = .ok tq)
    (hf : multiply 2 2 2 input.transition initial.lower = .ok fl)
    : GramFactorInputDomain 2 4 (fromCols 2 2 2 fl tq) (21 / 8) := by
  obtain ⟨tq', _, hr, hqf, _, _, _, _, _⟩ :=
    FloatCholeskyDomain.cholesky_accuracy input.processNoise d.noise.covariance
  have eq : tq' = tq := Except.ok.inj (hr.symm.trans hq)
  subst tq'
  obtain ⟨fl', _, hr', _, hff, _⟩ := transition_product input initial d
  have eq' : fl' = fl := Except.ok.inj (hr'.symm.trans hf)
  subst fl'
  obtain ⟨hfloor, henergy⟩ := prearray_margins input initial d tq fl hq hf
  have hid := FloatQRInitialDomain.identity_input_domain 2 (by decide)
  refine ⟨
    by decide,
    by decide,
    FloatPrearray.fromCols_size 2 2 2 fl tq,
    FloatPrearray.fromCols_finite 2 2 2 fl tq hff hqf,
    hid.budget_lower.trans (by norm_num),
    ?_,
    ?_,
    ?_
  ⟩
  · exact (by norm_num : (21 / 8 : ℝ) ≤ 4).trans (by
      simpa only [show (2 : ℝ)^(2 : Int) = 4 by norm_num] using
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 : Int) ≤ 900))
  · intro i
    have hb := (henergy i).trans (by norm_num : (51 / 16 : ℝ) ≤ (21 / 8)^2 / 2)
    simpa only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hb
  · convert hfloor.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : 0 ≤ (63 / 64 : ℝ) - (21 / 8)^2 / 8)) using 1
    norm_num
    module

theorem mean_stage (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial)
    : ∃ mean,
        ProductProfile 2 2 1 input.transition initial.mean 8
        ∧ multiply 2 2 1 input.transition initial.mean = .ok mean
        ∧ mean.size = 2
        ∧ mean.all Float.isFinite = true
        ∧ (∀ i, i < 2 → |value (mean.getD i 0.0)| ≤ 19 / 16) := by
  obtain ⟨mean, pp, hr, hs, hf, he, _⟩ := FloatMeanDomain.vector_product
    input.transition initial.mean 1 (9 / 8) d.transition_finite d.mean_finite
    (by norm_num) (by norm_num) d.transition_bound d.mean_bound
  have hdiag := FloatDiagonalStorage.matrix_diagonal 2 input.transition d.transition_diagonal
  refine ⟨mean, pp, hr, hs, hf, ?_⟩
  intro i hi
  have herr := he.2 ⟨i, hi⟩ 0
  have ht : |(matrix 2 2 input.transition * matrix 2 1 initial.mean) ⟨i, hi⟩ 0| ≤ 9 / 8 := by
    rw [hdiag, Matrix.diagonal_mul, abs_mul]
    have hb : |matrix 2 1 initial.mean ⟨i, hi⟩ 0| ≤ 9 / 8 := by
      simpa [matrix, Flare.Matrix.Value.matrix] using d.mean_bound i hi
    exact (mul_le_mul (d.transition_bound i i hi hi) hb (abs_nonneg _)
            (by norm_num)).trans
      (by norm_num)
  have hm := (abs_sub_le (matrix 2 1 mean ⟨i, hi⟩ 0)
    ((matrix 2 2 input.transition * matrix 2 1 initial.mean) ⟨i, hi⟩ 0) 0)
  simp only [sub_zero] at hm
  change |value (mean.getD i 0.0)| ≤ _
  simp [matrix, Flare.Matrix.Value.matrix] at herr hm
  calc
    _ ≤ productRadius 2 8 + 9 / 8 := by
      simpa only [Array.getD_eq_getD_getElem?] using hm.trans (add_le_add herr ht)
    _ ≤ 19 / 16 := by norm_num [productRadius]

theorem prediction_profile (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial)
    : ∃ p : PredictionProfile input initial,
        p.noiseMass = 8
        ∧ p.noiseFloor = 1 / 2
        ∧ p.noiseBound = 2
        ∧ p.productMass = 8
        ∧ p.meanMass = 8
        ∧ p.qrBudget = 21 / 8
        ∧ p.transitionBound = 1
        ∧ p.factorBound = 2
        ∧ (∀ i, i < 2 → |value (p.mean.getD i 0.0)| ≤ 19 / 16) := by
  obtain ⟨tq, _, pq, _, _, _⟩ := FloatCholeskyDomain.cholesky_profile input.processNoise d.noise.covariance
  obtain ⟨fl, pp, hfl, _, _, _⟩ := transition_product input initial d
  obtain ⟨mean, pm, hm, _, _, hmean⟩ := mean_stage input initial d
  let p : PredictionProfile input initial :=
    {
      tq := tq,
      fl := fl,
      mean := mean,
      noiseMass := 8,
      noiseFloor := 1 / 2,
      noiseBound := 2,
      productMass := 8,
      meanMass := 8,
      qrBudget := 21 / 8,
      transitionBound := 1,
      factorBound := 2,
      noise_shape := by simpa only [d.state_dimension] using d.noise.covariance.size,
      noise_finite := d.noise.covariance.finite,
      noise := by simpa only [d.state_dimension] using pq,
      product := by simpa only [d.state_dimension] using pp,
      computeProduct := by simpa only [d.state_dimension] using hfl,
      meanProduct := by simpa only [d.state_dimension] using pm,
      computeMean := by simpa only [d.state_dimension] using hm,
      qr := by
        simpa only [d.state_dimension]
          using prearray_domain input initial d tq fl pq.execution hfl,
      transition_nonneg := by norm_num,
      factor_nonneg := by norm_num,
      transition_magnitude := by
        intro i j
        have hi : i.val < 2 := by simpa only [d.state_dimension] using i.isLt
        have hj : j.val < 2 := by simpa only [d.state_dimension] using j.isLt
        simpa only [matrix, Flare.Matrix.Value.matrix, d.state_dimension, entry,
          Flare.Matrix.Dense.entry]
          using d.transition_bound i.val j.val hi hj,
      factor_magnitude := by
        intro i j
        have hi : i.val < 2 := by simpa only [d.state_dimension] using i.isLt
        have hj : j.val < 2 := by simpa only [d.state_dimension] using j.isLt
        simpa only [matrix, Flare.Matrix.Value.matrix, d.state_dimension, entry,
          Flare.Matrix.Dense.entry]
          using d.factor_bound i.val j.val hi hj
    }
  exact ⟨p, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmean⟩

/-- Keep the actual four/three-row QR constants and the original-noise
backward error rather than the older convenience cap. -/
theorem local_covariance_radius_sharp_cap
    : localCovarianceRadius ≤ 7 * (2 : ℝ) ^ (-32 : Int) := by
  have hc := FloatCholeskyDomain.backward_radius_cap
  simp only [localCovarianceRadius]
  apply le_trans (add_le_add le_rfl hc)
  simp only [qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius,
    sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius,
    Finset.sum_range_succ, Finset.sum_range_zero, productRadius]
  norm_num

theorem local_covariance_radius_cap : localCovarianceRadius ≤ (2 : ℝ) ^ (-24 : Int) :=
  local_covariance_radius_sharp_cap.trans (by norm_num)

/-- The actual prediction QR output retains a near-unit covariance floor and
bounded entries. This does not yet assert that the returned factor is diagonal. -/
theorem factor_output_bounds (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial) (tq fl l : Array Float)
    (hq : cholesky 2 input.processNoise = .ok tq)
    (hf : multiply 2 2 2 input.transition initial.lower = .ok fl)
    (hl
      : Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
          (fromCols 2 2 2 fl tq)
        = .ok l)
    : (FactorRecursion.gram (matrix 2 2 l) - (15 / 16 : ℝ) • 1).PosSemidef
      ∧ (∀ i, FactorRecursion.gram (matrix 2 2 l) i i ≤ 13 / 4)
      ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 l i j)| ≤ 2) := by
  have pd := prearray_domain input initial d tq fl hq hf
  obtain ⟨hfloor, henergy⟩ := prearray_margins input initial d tq fl hq hf
  obtain ⟨l', hr, _, _, _, hp, _, he⟩ :=
    FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 4 _ (21 / 8) pd
  have eq : l' = l := Except.ok.inj (hr.symm.trans hl)
  subst l'
  have hdiag : ∀ i, FactorRecursion.gram (matrix 2 2 l) i i ≤ 13 / 4 := by
    intro i
    have herr := (abs_le.mp (he.2 i i)).2
    change FactorRecursion.gram (matrix 2 2 l) i i
      - FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 fl tq)) i i ≤ _ at herr
    norm_num at herr
    linarith [henergy i]
  have hs := lower_bound_of_error _ _ (63 / 64) ((21 / 8 : ℝ)^2 / 33554432)
    hfloor hp.isHermitian he
  have hpad : 0 ≤ (63 / 64 : ℝ) - 2 * (21 / 8 : ℝ)^2 / 33554432 - 15 / 16 := by norm_num
  refine ⟨?_, hdiag, ?_⟩
  · convert hs.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad) using 1
    norm_num [FactorRecursion.gram]
    module
  · intro i j hi hj
    have hsq := FloatQRDomain.columnGram_entry_sq_le (matrix 2 2 l).transpose ⟨j, hj⟩ ⟨i, hi⟩
    change (value (entry 2 l i j))^2 ≤ FactorRecursion.gram (matrix 2 2 l) ⟨i, hi⟩ ⟨i, hi⟩ at hsq
    nlinarith [hdiag ⟨i, hi⟩, sq_abs (value (entry 2 l i j)), abs_nonneg (value (entry 2 l i j))]

/-- Prediction at |f|≤1 succeeds and includes noise Cholesky, rounded FL,
actual QR and mean rounding relative to the same original stored operands. -/
theorem prediction_accuracy_sharp (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok output
        ∧ FactorAccuracy (7 * (2 : ℝ) ^ (-32 : Int)) ((2 : ℝ) ^ (-46 : Int))
            input.stateDimension output
            (CovarianceRecursion.predict (model input)
              (factorState input.stateDimension initial))
        ∧ (∀ i, i < 2 → |value (output.mean.getD i 0.0)| ≤ 19 / 16)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 output.lower i j)| ≤ 2)
        ∧ (∀ i, FactorRecursion.gram (matrix 2 2 output.lower) i i ≤ 13 / 4)
        ∧ (FactorRecursion.gram (matrix 2 2 output.lower)
            - (15 / 16 : ℝ) • 1).PosSemidef := by
  obtain ⟨p, hqM, hqF, hqB, hP, hM, hQR, hF, hL, hm⟩ := prediction_profile input initial d
  obtain ⟨output, hr, ha⟩ := FloatSquareRootError.prediction_accuracy input initial p
  have pd : GramFactorInputDomain 2 4 (fromCols 2 2 2 p.fl p.tq) (21 / 8) := by
    simpa only [d.state_dimension, hQR] using p.qr
  obtain ⟨l, hl, _, _, _, _, _, _⟩ :=
    FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 4 _ (21 / 8) pd
  have hq : cholesky 2 input.processNoise = .ok p.tq := by
    simpa only [d.state_dimension] using p.noise.execution
  have hf : multiply 2 2 2 input.transition initial.lower = .ok p.fl := by
    simpa only [d.state_dimension] using p.computeProduct
  have hmean : multiply 2 2 1 input.transition initial.mean = .ok p.mean := by
    simpa only [d.state_dimension] using p.computeMean
  have hrun : Kalman.Implementation.SquareRootFilter.predictUnchecked input initial
      = .ok ⟨p.mean, l⟩ := by
    simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, hq, hf, hmean, d.state_dimension, hl,
      bind, Except.bind, pure, Except.pure]
  have eq : output = ⟨p.mean, l⟩ := Except.ok.inj (hr.symm.trans hrun)
  subst output
  obtain ⟨hfloor, hcap, hb⟩ := factor_output_bounds input initial d p.tq p.fl l hq hf hl
  have hcovRadius : predictionCovarianceRadius p = localCovarianceRadius := by
    simp only [predictionCovarianceRadius, localCovarianceRadius,
      d.state_dimension, hqM, hqF, hqB, hP, hQR, hF, hL]
    norm_num
  have hmeanRadius : predictionMeanRadius p = (2 : ℝ)^(-46 : Int) := by
    norm_num [predictionMeanRadius, productRadius, d.state_dimension, hM]
  rw [hcovRadius, hmeanRadius] at ha
  exact ⟨
    _,
    hrun,
    ⟨
      ha.1,
      ⟨by positivity, fun i j => (ha.2.1.2 i j).trans local_covariance_radius_sharp_cap⟩,
      ha.2.2
    ⟩,
    hm,
    hb,
    hcap,
    hfloor
  ⟩

/-- Compatibility allowance for the same successful prediction. -/
theorem prediction_accuracy (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok output
        ∧ FactorAccuracy ((2 : ℝ) ^ (-24 : Int)) ((2 : ℝ) ^ (-46 : Int))
            input.stateDimension output
            (CovarianceRecursion.predict (model input)
              (factorState input.stateDimension initial))
        ∧ (∀ i, i < 2 → |value (output.mean.getD i 0.0)| ≤ 19 / 16)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 output.lower i j)| ≤ 2)
        ∧ (∀ i, FactorRecursion.gram (matrix 2 2 output.lower) i i ≤ 13 / 4)
        ∧ (FactorRecursion.gram (matrix 2 2 output.lower)
            - (15 / 16 : ℝ) • 1).PosSemidef := by
  obtain ⟨output, hr, ha, hm, hb, hc, hf⟩ := prediction_accuracy_sharp input initial d
  exact ⟨
    output,
    hr,
    ⟨ha.1, ⟨by positivity, fun i j => (ha.2.1.2 i j).trans (by norm_num)⟩, ha.2.2⟩,
    hm,
    hb,
    hc,
    hf
  ⟩

/-- Validation recovers the finite two-state storage fields. -/
theorem factor_storage (output : Input.FactorState) (hv : output.validate 2 = .ok ())
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

/-- Original observation/noise conditions transfer the actual prediction to
the larger innovation domain, with all prior factor bounds derived. -/
theorem prediction_innovation_domain (input : Input.Model) (initial : Input.FactorState)
    (d : TwoStateDomain input initial) (o : ObservationInputs input)
    : ∃ output,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok output
        ∧ FactorAccuracy ((2 : ℝ) ^ (-24 : Int)) ((2 : ℝ) ^ (-46 : Int))
            input.stateDimension output
            (CovarianceRecursion.predict (model input)
              (factorState input.stateDimension initial))
        ∧ InnovationDomain input output := by
  obtain ⟨output, hr, ha, _, hb, hc, hf⟩ := prediction_accuracy input initial d
  have hv : output.validate 2 = .ok () := by simpa only [d.state_dimension] using ha.1.1
  have storage := factor_storage output hv
  exact ⟨output, hr, ha, ⟨o, storage.2.1, storage.2.2.2, hb, hc, hf⟩⟩

private theorem identity_entry (i j : Nat) (hi : i < 2) (hj : j < 2)
    : entry 2 (identity 2) i j = if i = j then 1.0 else 0.0 :=
  Flare.Matrix.JacobiInitialization.identity_entry 2 i j hi hj

private theorem identity_diagonal
    : Kalman.Implementation.Correctness.InputInterpretation.DecodedDiagonal 2
        (identity 2) := by
  intro i j hi hj hij
  rw [identity_entry i j hi hj]
  simp only [ite_eq_right hij]
  rfl

/-- Native identity noise is an original-domain inhabitant. -/
theorem identity_noise : NoiseDomain (identity 2) := by
  refine ⟨
    ⟨
      Flare.Matrix.JacobiInitialization.identity_size 2,
      Flare.Matrix.JacobiInitialization.identity_finite 2,
      ?_,
      ?_,
      ?_,
      ?_
    ⟩,
    identity_diagonal,
    ?_
  ⟩
  · rw [identity_diagonal 0 1 (by decide) (by decide) (by decide),
      identity_diagonal 1 0 (by decide) (by decide) (by decide)]
  · intro i hi
    rw [identity_entry i i hi hi]
    norm_num [Flare.Binary64.Arithmetic.one_value]
  · intro i hi
    rw [identity_entry i i hi hi]
    norm_num [Flare.Binary64.Arithmetic.one_value]
  · rw [identity_diagonal 1 0 (by decide) (by decide) (by decide)]
    norm_num
  · intro i hi
    rw [identity_entry i i hi hi]
    norm_num [Flare.Binary64.Arithmetic.one_value]

/-- Native identity dynamics inhabit both original local input domains.
This is not an assumed execution or a full observable-horizon certificate. -/
theorem identity_domain_nonempty
    : ∃ input : Input.Model,
      ∃ initial : Input.FactorState,
        TwoStateDomain input initial
        ∧ ObservationInputs input
        ∧ input.transition = identity 2 := by
  let input : Input.Model := ⟨2, 2, identity 2, identity 2, identity 2, identity 2, #[-1.0, 1.0]⟩
  let initial : Input.FactorState := ⟨#[1.0, -1.0], identity 2⟩
  have hn := (Flare.Binary64.Order.neg_value (1.0 : Float) (by decide +kernel)).2
  have hid : ∀ i j, i < 2 → j < 2 → |value (entry 2 (identity 2) i j)| ≤ 1 := by
    intro i j hi hj
    rw [identity_entry i j hi hj]
    split_ifs <;> norm_num [Flare.Binary64.Arithmetic.one_value,
      show value (0.0 : Float) = 0 from rfl]
  refine ⟨input, initial, ?_, ?_, rfl⟩
  · refine ⟨rfl, Flare.Matrix.JacobiInitialization.identity_size 2,
      Flare.Matrix.JacobiInitialization.identity_finite 2, identity_diagonal, hid,
      Flare.Matrix.JacobiInitialization.identity_size 2,
      Flare.Matrix.JacobiInitialization.identity_finite 2,
      fun i j hi hj => (hid i j hi hj).trans (by norm_num), ?_, identity_noise,
      by decide, by decide +kernel, ?_⟩
    · intro i
      norm_num [initial, FactorRecursion.gram, Flare.Matrix.JacobiInitialization.identity_matrix]
    · intro i hi
      interval_cases i <;> norm_num [initial, Flare.Binary64.Arithmetic.one_value, hn]
  · exact ⟨rfl, Flare.Matrix.JacobiInitialization.identity_size 2,
      Flare.Matrix.JacobiInitialization.identity_finite 2,
      Flare.Matrix.JacobiInitialization.identity_matrix 2, identity_noise⟩

end Kalman.Proofs.FloatObservablePrediction
