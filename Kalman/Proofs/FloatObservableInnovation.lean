import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatObservablePrediction

/-! Full-observation innovation at the actual reached prediction scale. The
original H=I/R conditions and stored prior derive HL, Cholesky, prearray and QR
success/error. FloatObservableDiagonal adds returned diagonality. Gain solves
and posterior correction remain unfinished. -/

namespace Kalman.Proofs.FloatObservableInnovation

open Matrix
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.DiagonalStages.Prediction
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

theorem observation_product (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior)
    : ∃ hl,
        ProductProfile 2 2 2 input.observation prior.lower 8
        ∧ multiply 2 2 2 input.observation prior.lower = .ok hl
        ∧ hl.size = 4
        ∧ hl.all Float.isFinite = true
        ∧ EntrywiseWithin (productRadius 2 8) (matrix 2 2 hl)
            (matrix 2 2 prior.lower) := by
  have hH : ∀ i j, i < 2 → j < 2 → |value (entry 2 input.observation i j)| ≤ 1 := by
    intro i j hi hj
    change |matrix 2 2 input.observation ⟨i, hi⟩ ⟨j, hj⟩| ≤ _
    rw [d.observation.observation_identity]
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have pp := FloatGainDomain.product_profile_two input.observation prior.lower 1 2
    d.observation.observation_finite d.factor_finite (by norm_num) (by norm_num) (by norm_num)
    hH d.factor_bound
  obtain ⟨hl, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy 2 2 2
    input.observation prior.lower (fun _ _ => (8 : ℝ)) pp.inner_le pp.finite_left pp.finite_right
    (fun _ _ _ _ => pp.upper) (fun _ _ _ _ => pp.lower) pp.mass
  rw [d.observation.observation_identity, Matrix.one_mul] at he
  exact ⟨hl, pp, hr, hs, hf, ⟨by norm_num [productRadius], he⟩⟩

theorem prearray_margins (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (tr hl : Array Float)
    (hr : cholesky 2 input.measurementNoise = .ok tr)
    (hh : multiply 2 2 2 input.observation prior.lower = .ok hl)
    : (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 tr hl))
        - (15 / 8 : ℝ) • 1).PosSemidef
      ∧ (∀ i,
          FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 tr hl)) i i ≤ 77 / 16) := by
  obtain ⟨hl', _, hh', _, _, he⟩ := observation_product input prior d
  have eq : hl' = hl := Except.ok.inj (hh'.symm.trans hh)
  subst hl'
  have hg := FloatPrearray.gram_within he (by norm_num : (0 : ℝ) ≤ 2)
    (fun i j => d.factor_bound i.val j.val i.isLt j.isLt)
  have hp := lower_bound_of_error _ _ (15 / 16)
    (2 * (2 * productRadius 2 8 * 2 + (productRadius 2 8)^2))
    d.covariance_floor (CovarianceStructure.gram_posSemidef (matrix 2 2 hl)).isHermitian hg
  obtain ⟨hn, hc⟩ := FloatObservablePrediction.noise_margins input.measurementNoise tr d.observation.noise hr
  rw [FloatPrearray.fromCols_gram 2 2 2 tr hl]
  refine ⟨?_, ?_⟩
  · have hpad : 0 ≤ (63 / 64 : ℝ) + (15 / 16 - 2 * (2 *
        (2 * productRadius 2 8 * 2 + (productRadius 2 8)^2))) - 15 / 8 := by norm_num [productRadius]
    convert (hn.add hp).add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad) using 1
    norm_num [FactorRecursion.gram]
    module
  · intro i
    have herr := (abs_le.mp (hg.2 i i)).2
    norm_num only [Nat.cast_ofNat] at herr
    have hi := d.covariance_diagonal_cap i
    have ht : FactorRecursion.gram (matrix 2 2 hl) i i
      ≤ 13 / 4 + 2 * (2 * productRadius 2 8 * 2 + (productRadius 2 8)^2) := by linarith
    change FactorRecursion.gram (matrix 2 2 tr) i i + FactorRecursion.gram (matrix 2 2 hl) i i ≤ _
    exact (add_le_add (hc i) ht).trans (by norm_num [productRadius])

theorem prearray_domain (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (tr hl : Array Float)
    (hr : cholesky 2 input.measurementNoise = .ok tr)
    (hh : multiply 2 2 2 input.observation prior.lower = .ok hl)
    : GramFactorInputDomain 2 4 (fromCols 2 2 2 tr hl) (25 / 8) := by
  obtain ⟨tr', _, hr', hrf, _, _, _, _, _⟩ :=
    FloatCholeskyDomain.cholesky_accuracy input.measurementNoise d.observation.noise.covariance
  have eq : tr' = tr := Except.ok.inj (hr'.symm.trans hr)
  subst tr'
  obtain ⟨hl', _, hh', _, hhf, _⟩ := observation_product input prior d
  have eq' : hl' = hl := Except.ok.inj (hh'.symm.trans hh)
  subst hl'
  obtain ⟨hf, he⟩ := prearray_margins input prior d tr hl hr hh
  have hid := FloatQRInitialDomain.identity_input_domain 2 (by decide)
  refine ⟨
    by decide,
    by decide,
    FloatPrearray.fromCols_size 2 2 2 tr hl,
    FloatPrearray.fromCols_finite 2 2 2 tr hl hrf hhf,
    hid.budget_lower.trans (by norm_num),
    ?_,
    ?_,
    ?_
  ⟩
  · exact (by norm_num : (25 / 8 : ℝ) ≤ 4).trans (by
      simpa only [show (2 : ℝ)^(2 : Int) = 4 by norm_num] using
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 : Int) ≤ 900))
  · intro i
    have hb := (he i).trans (by norm_num : (77 / 16 : ℝ) ≤ (25 / 8)^2 / 2)
    simpa only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hb
  · convert hf.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : 0 ≤ (15 / 8 : ℝ) - (25 / 8)^2 / 8)) using 1
    norm_num
    module

theorem local_innovation_radius_cap : localInnovationRadius ≤ (2 : ℝ) ^ (-23 : Int) := by
  simp only [localInnovationRadius, qrGramRadius, iterationGramRadius, iterationRadius,
    sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius,
    reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero, productRadius]
  norm_num

/-- Actual noise factorization, HL product and innovation QR all succeed.
The Gram comparison includes original R factorization and HL rounding. -/
theorem factor_accuracy (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior)
    : ∃ tr hl s,
        cholesky 2 input.measurementNoise = .ok tr
        ∧ multiply 2 2 2 input.observation prior.lower = .ok hl
        ∧ Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
            (fromCols 2 2 2 tr hl)
          = .ok s
        ∧ s.size = 4
        ∧ s.all Float.isFinite = true
        ∧ FactorRecursion.LowerPositive (matrix 2 2 s)
        ∧ (FactorRecursion.gram (matrix 2 2 s)).PosDef
        ∧ (FactorRecursion.gram (matrix 2 2 s) - (29 / 16 : ℝ) • 1).PosSemidef
        ∧ (∀ i, FactorRecursion.gram (matrix 2 2 s) i i ≤ 39 / 8)
        ∧ (∀ i j, i < 2 → j < 2 → |value (entry 2 s i j)| ≤ 9 / 4)
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-23 : Int)) (FactorRecursion.gram (matrix 2 2 s))
            (FactorRecursion.gram (matrix 2 2 prior.lower)
              + matrix 2 2 input.measurementNoise) := by
  obtain ⟨tr, _, hr, _, _, _, _, _, er⟩ :=
    FloatCholeskyDomain.cholesky_accuracy input.measurementNoise d.observation.noise.covariance
  obtain ⟨hl, _, hh, _, _, eh⟩ := observation_product input prior d
  have pd := prearray_domain input prior d tr hl hr hh
  obtain ⟨_, _, s, hs, hss, hsf, hsl, hsp, es⟩ :=
    FloatQRInitialDomain.gramFactor_accuracy_initial 2 4 _ (25 / 8) pd
  have ehg := FloatPrearray.gram_within eh (by norm_num : (0 : ℝ) ≤ 2)
    (fun i j => d.factor_bound i.val j.val i.isLt j.isLt)
  have ep := within_add er ehg
  have ep' : EntrywiseWithin ((2 : ℝ)^(-42 : Int) +
      2 * (2 * productRadius 2 8 * 2 + (productRadius 2 8)^2))
      (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 tr hl)))
      (matrix 2 2 input.measurementNoise + FactorRecursion.gram (matrix 2 2 prior.lower)) := by
    rw [FloatPrearray.fromCols_gram 2 2 2 tr hl]
    exact ep
  have ec := within_trans es ep'
  have ec' : EntrywiseWithin localInnovationRadius (FactorRecursion.gram (matrix 2 2 s))
      (FactorRecursion.gram (matrix 2 2 prior.lower) + matrix 2 2 input.measurementNoise) := by
    convert ec using 1
    · dsimp [localInnovationRadius]
      norm_num
      ring
    · exact add_comm _ _
  have eQR : EntrywiseWithin ((2 : ℝ)^(-23 : Int)) (FactorRecursion.gram (matrix 2 2 s))
      (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 tr hl))) := by
    refine ⟨by positivity, fun i j => (es.2 i j).trans ?_⟩
    apply le_trans _ local_innovation_radius_cap
    dsimp [localInnovationRadius]
    have h : 0 ≤ 2 * (2 * productRadius 2 8 * 2 + (productRadius 2 8)^2) + (2 : ℝ)^(-42 : Int) := by
      norm_num [productRadius]
    rw [add_assoc]
    exact le_add_of_nonneg_right h
  obtain ⟨hfloor, henergy⟩ := prearray_margins input prior d tr hl hr hh
  have hf := lower_bound_of_error _ _ (15 / 8) ((2 : ℝ)^(-23 : Int)) hfloor hsp.isHermitian eQR
  have hpad : 0 ≤ (15 / 8 : ℝ) - 2 * (2 : ℝ)^(-23 : Int) - 29 / 16 := by norm_num
  have hcov : ∀ i, FactorRecursion.gram (matrix 2 2 s) i i ≤ 39 / 8 := by
    intro i
    have herr := (abs_le.mp (eQR.2 i i)).2
    norm_num at herr
    linarith [henergy i]
  refine ⟨
    tr,
    hl,
    s,
    hr,
    hh,
    hs,
    hss,
    hsf,
    hsl,
    hsp,
    ?_,
    hcov,
    ?_,
    ⟨by positivity, fun i j => (ec'.2 i j).trans local_innovation_radius_cap⟩
  ⟩
  · convert hf.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad) using 1
    norm_num
    module
  · intro i j hi hj
    have hsq := FloatQRDomain.columnGram_entry_sq_le (matrix 2 2 s).transpose ⟨j, hj⟩ ⟨i, hi⟩
    change (value (entry 2 s i j))^2 ≤ FactorRecursion.gram (matrix 2 2 s) ⟨i, hi⟩ ⟨i, hi⟩ at hsq
    nlinarith [hcov ⟨i, hi⟩, sq_abs (value (entry 2 s i j)), abs_nonneg (value (entry 2 s i j))]

end Kalman.Proofs.FloatObservableInnovation
