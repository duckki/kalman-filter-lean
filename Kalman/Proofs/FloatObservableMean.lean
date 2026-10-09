import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
import Kalman.Proofs.FloatObservableGain
import Kalman.Proofs.FloatMeanDomain

/-! Full-observation diagonal mean correction from local stored inputs.
Convex gain headroom derives a returned mean cap. Evaluation at the stored gain
and comparison with the ideal gain of the same stored prior are separate. -/

namespace Kalman.Proofs.FloatObservableMean

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.DiagonalStages.Mean
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

private theorem vector_entry (a : Array Float) (i : Fin 2)
    : matrix 2 1 a i 0 = value (a.getD i.val 0.0) := by
  simp [matrix, Flare.Matrix.Value.matrix]

/-- The stored gain range gives strict headroom below the returned 9/8 cap. -/
theorem convex_mean_bound (x z k : ℝ) (hx : |x| ≤ 19 / 16) (hz : |z| ≤ 1)
    (hklo : 3 / 8 ≤ k) (hkhi : k ≤ 13 / 16)
    : |x + k * (z - x)| ≤ 143 / 128 := by
  have hk : 0 ≤ k := by linarith
  have hw : 0 ≤ 1 - k := by linarith
  rw [show x + k * (z - x) = (1 - k) * x + k * z by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hk]
  apply (add_le_add (mul_le_mul_of_nonneg_left hx hw)
    (mul_le_mul_of_nonneg_left hz hk)).trans
  nlinarith

theorem stored_gain_mean_radius_cap
    : sumRadius 2 + productRadius 2 8 + 2 * (13 / 16) * (sumRadius 2 + productRadius 2 8)
      ≤ (2 : ℝ) ^ (-44 : Int) := by norm_num [sumRadius, productRadius]

private theorem gain_magnitude (k : Array Float) (dk : DecodedDiagonal 2 k)
    (hk
      : ∀ i,
          i < 2 → (3 : ℝ) / 8 ≤ value (entry 2 k i i) ∧ value (entry 2 k i i) ≤ 13 / 16)
    : ∀ i j, i < 2 → j < 2 → |value (entry 2 k i j)| ≤ 13 / 16 := by
  intro i j hi hj
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (by linarith [(hk i hi).1])]
    exact (hk i hi).2
  · rw [dk i j hi hj hij, abs_zero]
    norm_num

/-- Every actual projected/residual/increment/add operation and profile is
derived. The stored gain blends bounded vectors and returns magnitude ≤9/8. -/
theorem mean_stages (h mean measurement k : Array Float)
    (p : VectorDomain mean measurement)
    (hh : h.all Float.isFinite = true) (hkf : k.all Float.isFinite = true)
    (hH : matrix 2 2 h = 1) (dk : DecodedDiagonal 2 k)
    (hk
      : ∀ i,
          i < 2 → (3 : ℝ) / 8 ≤ value (entry 2 k i i) ∧ value (entry 2 k i i) ≤ 13 / 16)
    : ∃ projected residual increment output,
        ProductProfile 2 2 1 h mean 8
        ∧ multiply 2 2 1 h mean = .ok projected
        ∧ SumProfile measurement projected 2 true
        ∧ sub measurement projected = .ok residual
        ∧ ProductProfile 2 2 1 k residual 8
        ∧ multiply 2 2 1 k residual = .ok increment
        ∧ SumProfile mean increment 2 false
        ∧ add mean increment = .ok output
        ∧ output.size = 2
        ∧ output.all Float.isFinite = true
        ∧ (∀ i, i < 2 → |value (output.getD i 0.0)| ≤ 9 / 8)
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-44 : Int)) (matrix 2 1 output)
            (matrix 2 1 mean
              + matrix 2 2 k * (matrix 2 1 measurement - matrix 2 1 mean)) := by
  have hHb : ∀ i j, i < 2 → j < 2 → |value (entry 2 h i j)| ≤ 1 := by
    intro i j hi hj
    change |matrix 2 2 h ⟨i, hi⟩ ⟨j, hj⟩| ≤ 1
    rw [hH]
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hKb := gain_magnitude k dk hk
  have hdiag := FloatDiagonalStorage.matrix_diagonal 2 k dk
  obtain ⟨projected, pp, hp, _, hpf, ep, _⟩ := FloatMeanDomain.vector_product h mean 1 (19 / 16)
    hh p.mean_finite (by norm_num) (by norm_num) hHb p.mean_bound
  rw [hH, Matrix.one_mul] at ep
  have hpm : ∀ i, i < 2 → |value (projected.getD i 0.0)| ≤ 5 / 4 := by
    intro i hi
    have he := ep.2 ⟨i, hi⟩ 0
    have ht := abs_sub_le (matrix 2 1 projected ⟨i, hi⟩ 0) (matrix 2 1 mean ⟨i, hi⟩ 0) 0
    simp only [vector_entry] at he
    simp only [sub_zero, vector_entry] at ht
    change |value (projected.getD i 0.0) - value (mean.getD i 0.0)| ≤ productRadius 2 8 at he
    change |value (projected.getD i 0.0)| ≤
      |value (projected.getD i 0.0) - value (mean.getD i 0.0)| + |value (mean.getD i 0.0)| at ht
    have hb := p.mean_bound i hi
    norm_num [productRadius] at he
    simp only [Array.getD_eq_getD_getElem?] at hb ht ⊢
    linarith
  obtain ⟨residual, ps, hs, _, hsf, es, hsm⟩ := FloatMeanDomain.sub_vector measurement projected 1 (5 / 4)
    p.measurement_size p.measurement_finite hpf (by norm_num) p.measurement_bound hpm
  have hsbound : ∀ i, i < 2 → |value (residual.getD i 0.0)| ≤ 19 / 8 := by
    intro i hi
    exact (hsm i hi).trans (by norm_num [sumRadius])
  obtain ⟨increment, pi, hi, _, hif, ei, _⟩ := FloatMeanDomain.vector_product k residual (13 / 16) (19 / 8)
    hkf hsf (by norm_num) (by norm_num) hKb hsbound
  have him : ∀ i, i < 2 → |value (increment.getD i 0.0)| ≤ 2 := by
    intro i hilt
    have he := ei.2 ⟨i, hilt⟩ 0
    have ht : |(matrix 2 2 k * matrix 2 1 residual) ⟨i, hilt⟩ 0| ≤ (13 / 16 : ℝ) * (19 / 8) := by
      rw [hdiag, diagonal_mul, abs_mul]
      exact mul_le_mul (hKb i i hilt hilt)
        (by simpa only [vector_entry] using hsbound i hilt) (abs_nonneg _) (by norm_num)
    have hb := abs_sub_le (matrix 2 1 increment ⟨i, hilt⟩ 0)
      ((matrix 2 2 k * matrix 2 1 residual) ⟨i, hilt⟩ 0) 0
    simp only [vector_entry] at he
    simp only [sub_zero, vector_entry] at hb
    change |value (increment.getD i 0.0)| ≤ _
    change |value (increment.getD i 0.0)| ≤ _ at hb
    norm_num [productRadius] at he ht
    simp only [Array.getD_eq_getD_getElem?] at hb ⊢
    linarith
  obtain ⟨output, po, ho, hos, hof, eo, _⟩ := FloatMeanDomain.add_vector mean increment (19 / 16) 2
    p.mean_size p.mean_finite hif (by norm_num) p.mean_bound him
  have eres := within_trans es (within_sub (within_refl (matrix 2 1 measurement)) ep)
  have einc := within_trans ei (within_mul_left (matrix 2 2 k) eres
    (by norm_num : (0 : ℝ) ≤ 13 / 16) (fun i j => hKb i.val j.val i.isLt j.isLt))
  have eout := within_trans eo (within_add (within_refl (matrix 2 1 mean)) einc)
  have eval : EntrywiseWithin ((2 : ℝ)^(-44 : Int)) (matrix 2 1 output)
      (matrix 2 1 mean + matrix 2 2 k * (matrix 2 1 measurement - matrix 2 1 mean)) := by
    refine ⟨by positivity, fun i j => ?_⟩
    have he := eout.2 i j
    simp only [zero_add, Nat.cast_ofNat] at he
    exact he.trans (by simpa only [add_assoc] using stored_gain_mean_radius_cap)
  refine ⟨
    projected,
    residual,
    increment,
    output,
    pp,
    hp,
    ps,
    hs,
    pi,
    hi,
    po,
    ho,
    hos,
    hof,
    ?_,
    eval
  ⟩
  intro i hilt
  have he := eval.2 ⟨i, hilt⟩ 0
  rw [hdiag] at he
  simp only [Matrix.add_apply, diagonal_mul, Matrix.sub_apply, vector_entry] at he
  change |value (output.getD i 0.0) - (value (mean.getD i 0.0)
    + value (entry 2 k i i) * (value (measurement.getD i 0.0) - value (mean.getD i 0.0)))| ≤ _ at he
  have hb := convex_mean_bound _ _ _ (p.mean_bound i hilt) (p.measurement_bound i hilt)
    (hk i hilt).1 (hk i hilt).2
  have ht := abs_sub_le (value (output.getD i 0.0))
    (value (mean.getD i 0.0) + value (entry 2 k i i)
      * (value (measurement.getD i 0.0) - value (mean.getD i 0.0))) 0
  simp only [sub_zero] at ht
  norm_num at he
  simp only [Array.getD_eq_getD_getElem?] at hb ht ⊢
  linarith

/-- Assemble the runtime's existing mean profile without changing its order. -/
theorem mean_profile (input : Input.Model) (prior : Input.FactorState)
    (innovation : InnovationProfile input prior) (gain : GainProfile innovation)
    (hn : input.stateDimension = 2)
    (d : Kalman.Proofs.DiagonalStages.Prediction.InnovationDomain input prior)
    (v : VectorDomain prior.mean input.measurement)
    (dk : DecodedDiagonal 2 (gainArray gain))
    (hk
      : ∀ i,
          i < 2
          → (3 : ℝ) / 8 ≤ value (entry 2 (gainArray gain) i i)
            ∧ value (entry 2 (gainArray gain) i i) ≤ 13 / 16)
    : ∃ mp : MeanProfile gain,
        mp.projectedMass = 8
        ∧ mp.incrementMass = 8
        ∧ mp.residualExponent = 2
        ∧ mp.meanExponent = 2
        ∧ mp.mean.size = 2
        ∧ mp.mean.all Float.isFinite = true
        ∧ (∀ i, i < 2 → |value (mp.mean.getD i 0.0)| ≤ 9 / 8)
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-44 : Int)) (matrix 2 1 mp.mean)
            (matrix 2 1 prior.mean
              + matrix 2 2 (gainArray gain)
                * (matrix 2 1 input.measurement - matrix 2 1 prior.mean)) := by
  have hm := d.observation.measurement_dimension
  have hkf : (gainArray gain).all Float.isFinite = true :=
    (Flare.Matrix.Multiplication.transpose_storage _ _ gain.solution gain.finite_solution).2.1
  obtain ⟨projected, residual, increment, output, pp, hp, ps, hs, pi, hi, po, ho, hos, hof, hom, eval⟩ :=
    mean_stages input.observation prior.mean input.measurement (gainArray gain) v
      d.observation.observation_finite hkf d.observation.observation_identity dk hk
  let mp : MeanProfile gain := {
    projected := projected, residual := residual, increment := increment, mean := output
    projectedMass := 8, incrementMass := 8, residualExponent := 2, meanExponent := 2
    measurement_shape := by simpa only [hm] using v.measurement_size
    prior_shape := by simpa only [hn] using v.mean_size
    projectedProduct := by simpa only [hn, hm] using pp
    computeProjected := by simpa only [hn, hm] using hp
    residualSum := ps
    computeResidual := hs
    incrementProduct := by simpa only [hn, hm] using pi
    computeIncrement := by simpa only [hn, hm] using hi
    meanSum := po
    computeMean := ho
  }
  exact ⟨mp, rfl, rfl, rfl, rfl, hos, hof, hom, eval⟩

private theorem mean_reference_accuracy (n m : Nat) (ε : ℝ)
    (f h q r lower mean measurement output : Array Float) (hn : n = 2) (hm : m = 2)
    (hH : matrix 2 2 h = 1)
    (e
      : EntrywiseWithin ε (matrix 2 1 output)
          (matrix 2 1 mean
            + (FactorRecursion.gram (matrix 2 2 lower)
                * (FactorRecursion.gram (matrix 2 2 lower) + matrix 2 2 r)⁻¹)
              * (matrix 2 1 measurement - matrix 2 1 mean)))
    : ∀ i,
        |vector n output i
          - (CovarianceRecursion.update .joseph
              (⟨matrix n n f, matrix m n h, matrix n n q, matrix m m r⟩
                : LinearModel.Model n m)
              (⟨vector n mean, FactorRecursion.gram (matrix n n lower)⟩
                : LinearModel.State n)
              (vector m measurement)).mean
              i|
        ≤ ε := by
  subst n m
  intro i
  simpa [CovarianceRecursion.update, CovarianceRecursion.gain,
    CovarianceRecursion.innovation, CovarianceRecursion.innovationCovariance, hH, vector,
    matrix, Flare.Matrix.Value.matrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    using e.2 i 0

/-- Compose a supplied derived mean evaluation and native gain discrepancy
against the ideal correction of the same stored prior and original H/R/z. -/
theorem mean_accuracy_sharp (input : Input.Model) (prior : Input.FactorState)
    (d : TwoStateDomain input prior)
    (innovation : InnovationProfile input prior) (gain : GainProfile innovation)
    (mp : MeanProfile gain) (dk : DecodedDiagonal 2 (gainArray gain))
    (ek
      : EntrywiseWithin ((2 : ℝ) ^ (-27 : Int))
          (matrix input.stateDimension input.measurementDimension (gainArray gain))
          (CovarianceRecursion.gain (model input)
            (factorState input.stateDimension prior)))
    (eval
      : EntrywiseWithin ((2 : ℝ) ^ (-44 : Int)) (matrix 2 1 mp.mean)
          (matrix 2 1 prior.mean
            + matrix 2 2 (gainArray gain)
              * (matrix 2 1 input.measurement - matrix 2 1 prior.mean)))
    : ∀ i,
        |vector input.stateDimension mp.mean i
          - (CovarianceRecursion.update .joseph (model input)
              (factorState input.stateDimension prior)
              (vector input.measurementDimension input.measurement)).mean
              i|
        ≤ 9 * (2 : ℝ) ^ (-29 : Int) := by
  have hn := d.state_dimension
  have hm := d.observation.measurement_dimension
  have ek' : EntrywiseWithin ((2 : ℝ)^(-27 : Int)) (matrix 2 2 (gainArray gain))
      (FactorRecursion.gram (matrix 2 2 prior.lower)
        * (FactorRecursion.gram (matrix 2 2 prior.lower) + matrix 2 2 input.measurementNoise)⁻¹) := by
    simp only [CovarianceRecursion.gain, CovarianceRecursion.innovationCovariance, model, factorState] at ek
    exact FloatObservableGain.full_observation_gain_reference _ _ _ _ _ _ _ hn hm
      d.observation.observation_identity ek
  have hki := FloatObservableGain.ideal_gain_diagonal input prior d.toInnovationDomain d.diagonal
  have hdideal : FactorRecursion.gram (matrix 2 2 prior.lower)
      * (FactorRecursion.gram (matrix 2 2 prior.lower) + matrix 2 2 input.measurementNoise)⁻¹
      = diagonal (fun i => (FactorRecursion.gram (matrix 2 2 prior.lower)
          * (FactorRecursion.gram (matrix 2 2 prior.lower) + matrix 2 2 input.measurementNoise)⁻¹) i i) := by
    rw [hki]
    simp only [diagonal_apply_eq]
  have hrb : ∀ i j, |(matrix 2 1 input.measurement - matrix 2 1 prior.mean) i j| ≤ 35 / 16 := by
    intro i j
    have hb : |value (input.measurement.getD i.val 0.0) - value (prior.mean.getD i.val 0.0)|
        ≤ (35 : ℝ) / 16 := by
      calc
        _ ≤ |value (input.measurement.getD i.val 0.0)|
            + |value (prior.mean.getD i.val 0.0)| :=
          abs_sub _ _
        _ ≤ 1 + 19 / 16 :=
          add_le_add (d.vectors.measurement_bound i.val i.isLt)
            (d.vectors.mean_bound i.val i.isLt)
        _ = 35 / 16 := by norm_num
    fin_cases j
    simpa [Matrix.sub_apply, matrix, Flare.Matrix.Value.matrix] using hb
  have eg := within_diagonal_mul_right ek'
    (FloatDiagonalStorage.matrix_diagonal 2 (gainArray gain) dk) hdideal
    (matrix 2 1 input.measurement - matrix 2 1 prior.mean) (by norm_num : (0 : ℝ) ≤ 35 / 16) hrb
  have em := within_trans eval (within_add (within_refl (matrix 2 1 prior.mean)) eg)
  have em' : EntrywiseWithin (9 * (2 : ℝ)^(-29 : Int)) (matrix 2 1 mp.mean)
      (matrix 2 1 prior.mean + (FactorRecursion.gram (matrix 2 2 prior.lower)
        * (FactorRecursion.gram (matrix 2 2 prior.lower) + matrix 2 2 input.measurementNoise)⁻¹)
        * (matrix 2 1 input.measurement - matrix 2 1 prior.mean)) :=
    ⟨by positivity, fun i j => (em.2 i j).trans (by norm_num)⟩
  exact mean_reference_accuracy _ _ _ input.transition input.observation
    input.processNoise input.measurementNoise prior.lower prior.mean input.measurement
    mp.mean hn hm d.observation.observation_identity em'

/-- Compatibility cap for the sharper local mean comparison. -/
theorem mean_accuracy (input : Input.Model) (prior : Input.FactorState)
    (d : TwoStateDomain input prior)
    (innovation : InnovationProfile input prior) (gain : GainProfile innovation)
    (mp : MeanProfile gain) (dk : DecodedDiagonal 2 (gainArray gain))
    (ek
      : EntrywiseWithin ((2 : ℝ) ^ (-27 : Int))
          (matrix input.stateDimension input.measurementDimension (gainArray gain))
          (CovarianceRecursion.gain (model input)
            (factorState input.stateDimension prior)))
    (eval
      : EntrywiseWithin ((2 : ℝ) ^ (-44 : Int)) (matrix 2 1 mp.mean)
          (matrix 2 1 prior.mean
            + matrix 2 2 (gainArray gain)
              * (matrix 2 1 input.measurement - matrix 2 1 prior.mean)))
    : ∀ i,
        |vector input.stateDimension mp.mean i
          - (CovarianceRecursion.update .joseph (model input)
              (factorState input.stateDimension prior)
              (vector input.measurementDimension input.measurement)).mean
              i|
        ≤ (2 : ℝ) ^ (-25 : Int) := by
  intro i
  exact (mean_accuracy_sharp input prior d innovation gain mp dk ek eval i).trans
    (by norm_num)

/-- Local input conditions derive the gain and every mean operation. Error is
against the ideal correction from the same stored prior and original H/R/z;
diagonal gain error propagation avoids an unnecessary dimension factor. -/
theorem correction_accuracy (input : Input.Model) (prior : Input.FactorState)
    (d : TwoStateDomain input prior)
    : ∃ innovation : InnovationProfile input prior,
      ∃ gain : GainProfile innovation,
      ∃ mp : MeanProfile gain,
        gain.gainBound = 13 / 16
        ∧ DecodedDiagonal 2 (gainArray gain)
        ∧ mp.projectedMass = 8
        ∧ mp.incrementMass = 8
        ∧ mp.residualExponent = 2
        ∧ mp.meanExponent = 2
        ∧ mp.mean.size = 2
        ∧ mp.mean.all Float.isFinite = true
        ∧ (∀ i, i < 2 → |value (mp.mean.getD i 0.0)| ≤ 9 / 8)
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-44 : Int)) (matrix 2 1 mp.mean)
            (matrix 2 1 prior.mean
              + matrix 2 2 (gainArray gain)
                * (matrix 2 1 input.measurement - matrix 2 1 prior.mean))
        ∧ (∀ i,
            |vector input.stateDimension mp.mean i
              - (CovarianceRecursion.update .joseph (model input)
                  (factorState input.stateDimension prior)
                  (vector input.measurementDimension input.measurement)).mean
                  i|
            ≤ (2 : ℝ) ^ (-25 : Int)) := by
  have hn := d.state_dimension
  have hm := d.observation.measurement_dimension
  obtain ⟨innovation, gain, _, _, _, _, hg, dk, _, ek, hk⟩ :=
    FloatObservableGain.gain_accuracy input prior hn d.toInnovationDomain d.diagonal
  obtain ⟨mp, hpm, him, hre, hme, hs, hf, hb, eval⟩ :=
    mean_profile input prior innovation gain hn d.toInnovationDomain d.vectors dk hk
  exact ⟨innovation, gain, mp, hg, dk, hpm, him, hre, hme, hs, hf, hb, eval,
    mean_accuracy input prior d innovation gain mp dk ek eval⟩

private theorem prediction_mean_execution (input : Input.Model)
    (initial prior : Input.FactorState)
    (hr
      : Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok prior)
    : multiply input.stateDimension input.stateDimension 1 input.transition initial.mean
      = .ok prior.mean := by
  cases hq : cholesky input.stateDimension input.processNoise with
  | error e =>
      simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, hq, bind, Except.bind] at hr
  | ok tq =>
      cases hfl
            : multiply input.stateDimension input.stateDimension input.stateDimension
                input.transition initial.lower with
      | error e =>
          simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, hq, hfl, bind, Except.bind] at hr
      | ok fl =>
          cases hl
                : Kalman.Implementation.OrthogonalFactorization.gramFactor
                    input.stateDimension (input.stateDimension + input.stateDimension)
                    (fromCols input.stateDimension input.stateDimension
                      input.stateDimension fl tq) with
          | error e =>
              simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, hq, hfl, hl, bind, Except.bind] at hr
          | ok lower =>
              cases hm
                    : multiply input.stateDimension input.stateDimension 1
                        input.transition initial.mean with
              | error e =>
                  simp [Kalman.Implementation.SquareRootFilter.predictUnchecked, hq, hfl, hl, hm, bind, Except.bind] at hr
              | ok mean =>
                  have eq : (⟨mean, lower⟩ : Input.FactorState) = prior := by
                    simpa [Kalman.Implementation.SquareRootFilter.predictUnchecked, hq,
                      hfl, hl, hm, bind, Except.bind, pure, Except.pure]
                      using hr
                  rw [← eq]

/-- The original prediction domain, observation/noise and bounded measurement
derive the reached complete local mean-correction domain. -/
theorem prediction_correction_domain (input : Input.Model) (initial : Input.FactorState)
    (d : Kalman.Proofs.DiagonalStages.Prediction.TwoStateDomain input initial)
    (o
      : Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.ObservationInputs
          input)
    (di : DecodedDiagonal 2 initial.lower) (hzs : input.measurement.size = 2)
    (hzf : input.measurement.all Float.isFinite = true)
    (hz : ∀ i, i < 2 → |value (input.measurement.getD i 0.0)| ≤ 1)
    : ∃ prior,
        Kalman.Implementation.SquareRootFilter.predictUnchecked input initial = .ok prior
        ∧ Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
            ((2 : ℝ) ^ (-24 : Int)) ((2 : ℝ) ^ (-46 : Int)) input.stateDimension prior
            (CovarianceRecursion.predict (model input)
              (factorState input.stateDimension initial))
        ∧ TwoStateDomain input prior := by
  obtain ⟨prior, hr, ha, id, dpi, _⟩ :=
    FloatObservableDiagonal.prediction_innovation_diagonal input initial d o di
  obtain ⟨mean, _, hm, hs, hf, hb⟩ := FloatObservablePrediction.mean_stage input initial d
  have hp := prediction_mean_execution input initial prior hr
  have hp' : multiply 2 2 1 input.transition initial.mean = .ok prior.mean := by
    simpa only [d.state_dimension] using hp
  have eq : mean = prior.mean := Except.ok.inj (hm.symm.trans hp')
  subst mean
  exact ⟨prior, hr, ha, ⟨id, d.state_dimension, dpi, ⟨hs, hzs, hf, hzf, hb, hz⟩⟩⟩

end Kalman.Proofs.FloatObservableMean
