import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.FloatInnovationDomain
import Kalman.Proofs.RecursionSensitivity

/-! Successful native mean correction from stored input bounds, including
every product/sum profile and an output magnitude invariant. Accuracy against
the stored gain and accuracy against the ideal Kalman gain are distinct. -/

namespace Kalman.Proofs.FloatMeanDomain

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CorrelatedStages.Mean
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-- Entry bounds derive the vector product mass-eight profile. -/
theorem vector_product_profile (a b : Array Float) (A B : ℝ)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hA : 0 ≤ A) (hm : A * B ≤ 4)
    (ham : ∀ i j, i < 2 → j < 2 → |value (entry 2 a i j)| ≤ A)
    (hbm : ∀ i, i < 2 → |value (b.getD i 0.0)| ≤ B)
    : ProductProfile 2 2 1 a b 8 := by
  refine ⟨by decide, ha, hb, ?_, ?_, ?_⟩
  · simpa only [show (2 : ℝ)^(3 : Int) = 8 by norm_num]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 : Int) ≤ 990)
  · simpa only [show (2 : ℝ)^(3 : Int) = 8 by norm_num]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-1022 : Int) ≤ 3)
  · intro i j hi hj
    have hj0 : j = 0 := by omega
    subst j
    calc
      _ ≤ ∑ _k ∈ Finset.range 2, A * B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        apply mul_le_mul (ham i k hi (Finset.mem_range.mp hk)) _ (abs_nonneg _) hA
        simpa only [entry, Flare.Matrix.Dense.entry, Nat.mul_one, Nat.add_zero]
          using hbm k (Finset.mem_range.mp hk)
      _ ≤ 8 := by simp; linarith only [hm]

/-- Actual two-state matrix/vector multiplication and a stored output bound. -/
theorem vector_product (a b : Array Float) (A B : ℝ)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hA : 0 ≤ A) (hm : A * B ≤ 4)
    (ham : ∀ i j, i < 2 → j < 2 → |value (entry 2 a i j)| ≤ A)
    (hbm : ∀ i, i < 2 → |value (b.getD i 0.0)| ≤ B)
    : ∃ r,
        ProductProfile 2 2 1 a b 8
        ∧ multiply 2 2 1 a b = .ok r
        ∧ r.size = 2
        ∧ r.all Float.isFinite = true
        ∧ EntrywiseWithin (productRadius 2 8) (matrix 2 1 r) (matrix 2 2 a * matrix 2 1 b)
        ∧ (∀ i, i < 2 → |value (r.getD i 0.0)| ≤ 2 * A * B + productRadius 2 8) := by
  have p := vector_product_profile a b A B ha hb hA hm ham hbm
  obtain ⟨r, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy 2 2 1 a b
    (fun _ _ => (8 : ℝ)) p.inner_le ha hb (fun _ _ _ _ => p.upper)
    (fun _ _ _ _ => p.lower) p.mass
  have ht :=
    product_magnitude (matrix 2 2 a) (matrix 2 1 b) A B
      (fun i j => ham i.val j.val i.isLt j.isLt)
      (by
        intro i j
        fin_cases j
        simpa only [matrix, Flare.Matrix.Value.matrix, Nat.mul_one, Nat.add_zero]
          using hbm i.val i.isLt)
  refine ⟨r, p, hr, hs, hf, ⟨by norm_num [productRadius], he⟩, ?_⟩
  intro i hi
  have hmag := abs_sub_le (matrix 2 1 r ⟨i, hi⟩ 0)
    ((matrix 2 2 a * matrix 2 1 b) ⟨i, hi⟩ 0) 0
  have herr := he ⟨i, hi⟩ 0
  have htarget := ht ⟨i, hi⟩ 0
  simp only [sub_zero] at hmag
  change |value (r.getD i 0.0)| ≤ _
  have heq : matrix 2 1 r ⟨i, hi⟩ 0 = value (r.getD i 0.0) := by
    simp [matrix, Flare.Matrix.Value.matrix]
  rw [heq] at hmag herr
  change |value (r.getD i 0.0) - _| ≤ productRadius 2 8 at herr
  norm_num only [Nat.cast_ofNat] at htarget
  linarith only [hmag, herr, htarget]

/-- Both vector sums use exponent two, with explicit exact-operand headroom. -/
theorem vector_sum_profile (a b : Array Float) (A B : ℝ) (subtract : Bool)
    (hs : a.size = 2) (ha : a.all Float.isFinite = true)
    (hb : b.all Float.isFinite = true) (hm : A + B ≤ 4)
    (ham : ∀ i, i < 2 → |value (a.getD i 0.0)| ≤ A)
    (hbm : ∀ i, i < 2 → |value (b.getD i 0.0)| ≤ B)
    : SumProfile a b 2 subtract := by
  refine ⟨by norm_num, by norm_num, ha, hb, ?_⟩
  intro i hi
  have hi' : i < 2 := by simpa only [hs] using hi
  cases subtract
  · simpa only [Bool.false_eq_true, ↓reduceIte, show (2 : ℝ)^(2 : Int) = 4 by norm_num]
      using (abs_add_le _ _).trans ((add_le_add (ham i hi') (hbm i hi')).trans hm)
  · simpa only [↓reduceIte, ← sub_eq_add_neg, show (2 : ℝ)^(2 : Int) = 4 by norm_num]
      using (abs_sub _ _).trans ((add_le_add (ham i hi') (hbm i hi')).trans hm)

/-- Native vector subtraction and its profile from exact operand headroom. -/
theorem sub_vector (a b : Array Float) (A B : ℝ) (hs : a.size = 2)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true) (hm : A + B ≤ 4)
    (ham : ∀ i, i < 2 → |value (a.getD i 0.0)| ≤ A)
    (hbm : ∀ i, i < 2 → |value (b.getD i 0.0)| ≤ B)
    : ∃ r,
        SumProfile a b 2 true
        ∧ sub a b = .ok r
        ∧ r.size = 2
        ∧ r.all Float.isFinite = true
        ∧ EntrywiseWithin (sumRadius 2) (matrix 2 1 r) (matrix 2 1 a - matrix 2 1 b)
        ∧ (∀ i, i < 2 → |value (r.getD i 0.0)| ≤ A + B + sumRadius 2) := by
  have p := vector_sum_profile a b A B true hs ha hb hm ham hbm
  obtain ⟨r, hr, hrs, hrf, he⟩ := FloatDenseError.sub_accuracy a b 2
    (by norm_num) (by norm_num) ha hb (by
      simpa only [↓reduceIte, ← sub_eq_add_neg] using p.magnitude)
  refine ⟨
    r,
    p,
    hr,
    hrs.trans hs,
    hrf,
    FloatJosephError.subtract_within p (by simpa using hs) hr,
    ?_
  ⟩
  intro i hi
  have hi' : i < a.size := by simpa only [hs] using hi
  have herr := he i hi'
  have hmag := abs_sub_le (value (r.getD i 0.0)) (value (a.getD i 0.0) - value (b.getD i 0.0)) 0
  simp only [sub_zero] at hmag
  have ht := (abs_sub _ _).trans (add_le_add (ham i hi) (hbm i hi))
  change |value (r.getD i 0.0) - _| ≤ sumRadius 2 at herr
  linarith only [hmag, herr, ht]

/-- Native vector addition and its profile from exact operand headroom. -/
theorem add_vector (a b : Array Float) (A B : ℝ) (hs : a.size = 2)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true) (hm : A + B ≤ 4)
    (ham : ∀ i, i < 2 → |value (a.getD i 0.0)| ≤ A)
    (hbm : ∀ i, i < 2 → |value (b.getD i 0.0)| ≤ B)
    : ∃ r,
        SumProfile a b 2 false
        ∧ add a b = .ok r
        ∧ r.size = 2
        ∧ r.all Float.isFinite = true
        ∧ EntrywiseWithin (sumRadius 2) (matrix 2 1 r) (matrix 2 1 a + matrix 2 1 b)
        ∧ (∀ i, i < 2 → |value (r.getD i 0.0)| ≤ A + B + sumRadius 2) := by
  have p := vector_sum_profile a b A B false hs ha hb hm ham hbm
  obtain ⟨r, hr, hrs, hrf, he⟩ := FloatDenseError.add_accuracy a b 2
    (by norm_num) (by norm_num) ha hb (by simpa only [Bool.false_eq_true, ↓reduceIte] using p.magnitude)
  refine ⟨
    r,
    p,
    hr,
    hrs.trans hs,
    hrf,
    FloatJosephError.add_within p (by simpa using hs) hr,
    ?_
  ⟩
  intro i hi
  have hi' : i < a.size := by simpa only [hs] using hi
  have herr := he i hi'
  have hmag := abs_sub_le (value (r.getD i 0.0)) (value (a.getD i 0.0) + value (b.getD i 0.0)) 0
  simp only [sub_zero] at hmag
  have ht := (abs_add_le _ _).trans (add_le_add (ham i hi) (hbm i hi))
  change |value (r.getD i 0.0) - _| ≤ sumRadius 2 at herr
  linarith only [hmag, herr, ht]

/-- Evaluation error at the same stored gain is distinct from gain error. -/
theorem stored_gain_mean_radius_cap
    : sumRadius 2 + productRadius 2 8 + 2 * (1 / 3) * (sumRadius 2 + productRadius 2 8)
      ≤ (2 : ℝ) ^ (-45 : Int) := by norm_num [sumRadius, productRadius]

/-- All four actual correction operations and profiles from stored operands.
The small predicted mean and measurement cap imply returned magnitude at most
one. The error reference uses the same stored H, mean, measurement and gain. -/
theorem mean_stages (h mean measurement k : Array Float)
    (p : VectorDomain mean measurement)
    (hh : h.all Float.isFinite = true) (hk : k.all Float.isFinite = true)
    (hH : ∀ i j, i < 2 → j < 2 → |value (entry 2 h i j)| ≤ 1 / 64)
    (hK : ∀ i j, i < 2 → j < 2 → |value (entry 2 k i j)| ≤ 1 / 3)
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
        ∧ (∀ i, i < 2 → |value (output.getD i 0.0)| ≤ 1)
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-45 : Int)) (matrix 2 1 output)
            (matrix 2 1 mean
              + matrix 2 2 k
                * (matrix 2 1 measurement - matrix 2 2 h * matrix 2 1 mean)) := by
  obtain ⟨projected, pp, hp, _, hpf, ep, hpm⟩ := vector_product h mean (1 / 64) (9 / 32)
    hh p.mean_finite (by norm_num) (by norm_num) hH p.mean_bound
  have hpbound : ∀ i, i < 2 → |value (projected.getD i 0.0)| ≤ 1 / 64 := by
    intro i hi
    exact (hpm i hi).trans (by norm_num [productRadius])
  obtain ⟨residual, ps, hs, _, hsf, es, hsm⟩ := sub_vector measurement projected 1 (1 / 64)
    p.measurement_size p.measurement_finite hpf (by norm_num) p.measurement_bound hpbound
  have hsbound : ∀ i, i < 2 → |value (residual.getD i 0.0)| ≤ 33 / 32 := by
    intro i hi
    exact (hsm i hi).trans (by norm_num [sumRadius])
  obtain ⟨increment, pi, hi, _, hif, ei, him⟩ := vector_product k residual (1 / 3) (33 / 32)
    hk hsf (by norm_num) (by norm_num) hK hsbound
  have hibound : ∀ i, i < 2 → |value (increment.getD i 0.0)| ≤ 45 / 64 := by
    intro i hi
    exact (him i hi).trans (by norm_num [productRadius])
  obtain ⟨output, po, ho, hos, hof, eo, hom⟩ := add_vector mean increment (9 / 32) (45 / 64)
    p.mean_size p.mean_finite hif (by norm_num) p.mean_bound hibound
  have eResidual := within_trans es (within_sub (within_refl (matrix 2 1 measurement)) ep)
  have eIncrement := within_trans ei (within_mul_left (matrix 2 2 k) eResidual
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (fun i j => hK i.val j.val i.isLt j.isLt))
  have eOutput := within_trans eo (within_add (within_refl (matrix 2 1 mean)) eIncrement)
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
    ?_
  ⟩
  · intro i hi
    exact (hom i hi).trans (by norm_num [sumRadius])
  · refine ⟨by positivity, fun i j => ?_⟩
    have he := eOutput.2 i j
    simp only [zero_add, Nat.cast_ofNat] at he
    exact he.trans (by simpa only [add_assoc] using stored_gain_mean_radius_cap)

/-- Assemble the existing mean profile from vector and stored matrix bounds.
Every mean-stage execution/profile is a conclusion, while the supplied gain
has its own preceding conditioning and accuracy proof. -/
theorem mean_profile (input : Input.Model) (prior : Input.FactorState)
    (innovation : InnovationProfile input prior) (gain : GainProfile innovation)
    (hn : input.stateDimension = 2) (hm : input.measurementDimension = 2)
    (p : VectorDomain prior.mean input.measurement)
    (hh : input.observation.all Float.isFinite = true)
    (hH : ∀ i j, i < 2 → j < 2 → |value (entry 2 input.observation i j)| ≤ 1 / 64)
    (hK
      : ∀ i j,
          |matrix input.stateDimension input.measurementDimension (gainArray gain) i j|
          ≤ 1 / 3)
    : ∃ mp : MeanProfile gain,
        mp.projectedMass = 8
        ∧ mp.incrementMass = 8
        ∧ mp.residualExponent = 2
        ∧ mp.meanExponent = 2
        ∧ mp.mean.size = 2
        ∧ mp.mean.all Float.isFinite = true
        ∧ (∀ i, i < 2 → |value (mp.mean.getD i 0.0)| ≤ 1)
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-45 : Int)) (matrix 2 1 mp.mean)
            (matrix 2 1 prior.mean
              + matrix 2 2 (gainArray gain)
                * (matrix 2 1 input.measurement
                    - matrix 2 2 input.observation * matrix 2 1 prior.mean)) := by
  have hkf : (gainArray gain).all Float.isFinite = true :=
    (Flare.Matrix.Multiplication.transpose_storage input.measurementDimension input.stateDimension
      gain.solution gain.finite_solution).2.1
  have hkn : ∀ i j : Nat, i < input.stateDimension → j < input.measurementDimension →
      |value (entry input.measurementDimension (gainArray gain) i j)| ≤ 1 / 3 :=
    fun i j hi hj => hK ⟨i, hi⟩ ⟨j, hj⟩
  have hk : ∀ i j, i < 2 → j < 2 → |value (entry 2 (gainArray gain) i j)| ≤ 1 / 3 := by
    simpa only [hn, hm] using hkn
  obtain ⟨projected, residual, increment, output, pp, hp, ps, hs, pi, hi, po, ho, hos, hof, hom, he⟩ :=
    mean_stages input.observation prior.mean input.measurement (gainArray gain) p hh hkf hH hk
  let mp : MeanProfile gain := {
    projected := projected, residual := residual, increment := increment, mean := output
    projectedMass := 8, incrementMass := 8, residualExponent := 2, meanExponent := 2
    measurement_shape := by simpa only [hm] using p.measurement_size
    prior_shape := by simpa only [hn] using p.mean_size
    projectedProduct := by simpa only [hn, hm] using pp
    computeProjected := by simpa only [hn, hm] using hp
    residualSum := ps
    computeResidual := hs
    incrementProduct := by simpa only [hn, hm] using pi
    computeIncrement := by simpa only [hn, hm] using hi
    meanSum := po
    computeMean := ho
  }
  exact ⟨mp, rfl, rfl, rfl, rfl, hos, hof, hom, he⟩

/-- Original local inputs derive innovation, gain and mean profiles together.
The mean output magnitude is included for a later trajectory invariant. -/
theorem correction_profiles (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∃ innovation : InnovationProfile input prior,
      ∃ gain : GainProfile innovation,
        innovation.noiseMass = 8
        ∧ innovation.noiseFloor = 1 / 2
        ∧ innovation.noiseBound = 2
        ∧ innovation.productMass = 8
        ∧ innovation.qrBudget = 2
        ∧ innovation.observationBound = 1 / 64
        ∧ innovation.factorBound = 2
        ∧ gain.productMass = 8
        ∧ gain.solveMass = 32
        ∧ gain.solveFloor = 1 / 2
        ∧ gain.solveBound = 2
        ∧ gain.gainBound = 1
        ∧ ∃ mp : MeanProfile gain,
            mp.projectedMass = 8
            ∧ mp.incrementMass = 8
            ∧ mp.residualExponent = 2
            ∧ mp.meanExponent = 2
            ∧ mp.mean.size = 2
            ∧ mp.mean.all Float.isFinite = true
            ∧ (∀ i, i < 2 → |value (mp.mean.getD i 0.0)| ≤ 1)
            ∧ EntrywiseWithin ((2 : ℝ) ^ (-45 : Int)) (matrix 2 1 mp.mean)
                (matrix 2 1 prior.mean
                  + matrix 2 2 (gainArray gain)
                    * (matrix 2 1 input.measurement
                        - matrix 2 2 input.observation * matrix 2 1 prior.mean)) := by
  obtain ⟨innovation, hn, hf, hb, hp, hqr, ho, hl, gain, hgp, hgs, hgf, hgb, hgk, hg⟩ :=
    FloatInnovationDomain.innovation_and_gain_profiles input prior p.toTwoStateDomain
  obtain ⟨mp, hmp⟩ := mean_profile input prior innovation gain p.state_dimension p.measurement_dimension
    p.vectors p.gain_inputs.observation_finite p.gain_inputs.observation_bound hg
  exact ⟨innovation, gain, hn, hf, hb, hp, hqr, ho, hl, hgp, hgs, hgf, hgb, hgk, mp, hmp⟩

/-- Ideal gain and residual bounds follow from the same local stored inputs,
including the original measurement-noise covariance. -/
theorem ideal_mean_operand_bounds (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : (matrix input.measurementDimension input.measurementDimension input.measurementNoise
        - (3 / 4 : ℝ) • 1).PosSemidef
      ∧ (∀ i j,
          |CovarianceRecursion.gain (model input) (factorState input.stateDimension prior)
            i j|
          ≤ 1 / 6)
      ∧ (∀ i,
          |CovarianceRecursion.innovation (model input)
            (factorState input.stateDimension prior)
            (vector input.measurementDimension input.measurement) i|
          ≤ 2) := by
  have hrn : ∀ m : Nat, m = 2 →
      (matrix m m input.measurementNoise - (3 / 4 : ℝ) • 1).PosSemidef := by
    intro m hm
    subst m
    exact FloatCholeskyDomain.input_lower_bound input.measurementNoise p.noise
  have hr := hrn _ p.measurement_dimension
  have hpn : ∀ n : Nat, n = 2 → ∀ i j,
      |FactorRecursion.gram (matrix n n prior.lower) i j| ≤ 2 := by
    intro n hn
    subst n
    exact p.gain_inputs.covariance_bound
  have hH : ∀ i j, |matrix input.measurementDimension input.stateDimension input.observation i j|
      ≤ 1 / 64 := by
    intro i j
    have hi : i.val < 2 := by simpa only [p.measurement_dimension] using i.isLt
    have hj : j.val < 2 := by simpa only [p.state_dimension] using j.isLt
    simpa only [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry,
      p.state_dimension]
      using p.gain_inputs.observation_bound i.val j.val hi hj
  have hmu : ∀ (i : Fin input.stateDimension) (j : Fin 1),
      |matrix input.stateDimension 1 prior.mean i j| ≤ 9 / 32 := by
    intro i j
    fin_cases j
    have hi : i.val < 2 := by simpa only [p.state_dimension] using i.isLt
    simpa [matrix, Flare.Matrix.Value.matrix] using p.vectors.mean_bound i.val hi
  have hg := RecursionSensitivity.gain_magnitude (model input) (factorState input.stateDimension prior)
    (3 / 4) 2 (1 / 64) (by norm_num) (by norm_num) (by norm_num)
    (CovarianceStructure.gram_posSemidef (matrix input.stateDimension input.stateDimension prior.lower))
    hr (hpn _ p.state_dimension) hH
  have hcap : Kalman.Definitions.Theorems.RecursionSensitivity.gainMagnitude
      input.stateDimension input.measurementDimension (3 / 4) 2 (1 / 64) ≤ 1 / 6 := by
    norm_num [Kalman.Definitions.Theorems.RecursionSensitivity.gainMagnitude,
      p.state_dimension, p.measurement_dimension]
  have hproject := product_magnitude
    (matrix input.measurementDimension input.stateDimension input.observation)
    (matrix input.stateDimension 1 prior.mean) (1 / 64) (9 / 32) hH hmu
  refine ⟨hr, fun i j => (hg i j).trans hcap, ?_⟩
  intro i
  have hi : i.val < 2 := by simpa only [p.measurement_dimension] using i.isLt
  have hz := p.vectors.measurement_bound i.val hi
  have hp := hproject i 0
  have hpm : |Matrix.mulVec (model input).observation (factorState input.stateDimension prior).mean i|
      ≤ 9 / 1024 := by
    convert hp using 1
    · simp [model, factorState, vector, matrix, Flare.Matrix.Value.matrix,
        Matrix.mul_apply, Matrix.mulVec, dotProduct]
    · norm_num [p.state_dimension]
  exact (abs_sub _ _).trans ((add_le_add hz hpm).trans (by norm_num))

/-- The closed local allowance fits the existing refined absolute tolerance.
Higher-order terms and the normal/subnormal allowance are retained. -/
theorem local_mean_radius_cap : localMeanRadius ≤ (2 : ℝ) ^ (-25 : Int) := by
  let η : ℝ := (2 : ℝ)^(-1022 : Int)
  have hη : (2 : ℝ)^(-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  simp only [localMeanRadius, qrGramRadius, iterationGramRadius, iterationRadius,
    sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius,
    reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
    productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius, hη]
  norm_num
  ring_nf
  linarith

/-- Native mean correction against the ideal Real Kalman update, with no
intermediate arithmetic profile or ideal gain/residual bound as a premise.
The input prior is interpreted by its exact stored-factor Gram. -/
theorem correction_accuracy (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∃ innovation : InnovationProfile input prior,
      ∃ gain : GainProfile innovation,
      ∃ mp : MeanProfile gain,
        mp.projectedMass = 8
        ∧ mp.incrementMass = 8
        ∧ mp.residualExponent = 2
        ∧ mp.meanExponent = 2
        ∧ mp.mean.size = 2
        ∧ mp.mean.all Float.isFinite = true
        ∧ (∀ i, i < 2 → |value (mp.mean.getD i 0.0)| ≤ 1)
        ∧ meanRadius mp (3 / 4) (1 / 6) 2 = localMeanRadius
        ∧ 0 ≤ localMeanRadius
        ∧ (∀ i,
            |vector input.stateDimension mp.mean i
              - (CovarianceRecursion.update .joseph (model input)
                  (factorState input.stateDimension prior)
                  (vector input.measurementDimension input.measurement)).mean
                  i|
            ≤ localMeanRadius) := by
  obtain ⟨innovation, gain, hn, hnf, hnb, hpr, hqr, ho, hl, hgp, hgs, hgf, hgb, hgk, mp,
      hp, hi, hr, hm, hs, hf, hb, _⟩ := correction_profiles input prior p
  obtain ⟨hnoise, hgain, hz⟩ := ideal_mean_operand_bounds input prior p
  obtain ⟨_, _, he, ha⟩ := FloatSquareRootUpdate.mean_accuracy input prior innovation gain mp
    (3 / 4) (1 / 6) 2 (by norm_num) (by norm_num) (by norm_num) hnoise hgain hz
  have hrad : meanRadius mp (3 / 4) (1 / 6) 2 = localMeanRadius := by
    simp only [meanRadius, gainRadius, gainResidualRadius, innovationRadius, localMeanRadius,
      p.state_dimension, p.measurement_dimension, hn, hnf, hnb, hpr, hqr, ho, hl,
      hgp, hgs, hgf, hgb, hgk, hp, hi, hr, hm]
    norm_num
  exact ⟨innovation, gain, mp, hp, hi, hr, hm, hs, hf, hb, hrad, hrad ▸ he, hrad ▸ ha⟩

/-- A nonzero predicted mean at both domain endpoints and bounded measurement. -/
theorem vector_domain_nonempty : VectorDomain #[0.0625, -0.0625] #[1.0, -1.0] := by
  have hv : value (0.0625 : Float) = (1 : ℝ) / 16 := by
    have he : value (0.0625 : Float) = (4503599627370496 : ℝ) * (2 : ℝ)^(-56 : Int) := rfl
    rw [he]
    norm_num
  have hn := (Flare.Binary64.Order.neg_value (0.0625 : Float) (by decide +kernel)).2
  have ho := (Flare.Binary64.Order.neg_value (1.0 : Float) (by decide +kernel)).2
  refine ⟨by decide, by decide, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> norm_num [hv, hn]
  · intro i hi
    interval_cases i <;> norm_num [Flare.Binary64.Arithmetic.one_value, ho]

/-- The complete local correction domain admits nonzero observation and mean,
correlated prior, and endpoint measurements. -/
theorem input_domain_nonempty
    : ∃ input : Input.Model,
      ∃ prior : Input.FactorState,
        TwoStateDomain input prior
        ∧ prior.mean = #[0.0625, -0.0625]
        ∧ input.measurement = #[1.0, -1.0]
        ∧ input.observation = #[0.015625, 0.0, 0.0, 0.015625]
        ∧ prior.lower = #[1.0, 0.0, 0.125, 1.0] := by
  obtain ⟨input, prior, p, hh, hl⟩ := FloatInnovationDomain.input_domain_nonempty
  let input' := {input with measurement := #[1.0, -1.0]}
  let prior' := {prior with mean := #[0.0625, -0.0625]}
  have p' : Kalman.Proofs.CorrelatedStages.Innovation.TwoStateDomain input' prior' :=
    ⟨p.state_dimension, p.measurement_dimension, p.gain_inputs, p.noise, p.noise_diagonal_cap⟩
  exact ⟨input', prior', ⟨p', vector_domain_nonempty⟩, rfl, rfl, hh, hl⟩

end Kalman.Proofs.FloatMeanDomain
