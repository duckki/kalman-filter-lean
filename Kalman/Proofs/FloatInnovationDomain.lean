import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.FloatGainDomain

/-! Derive the two-state innovation QR energy/rank domain and assemble its
profile from stored observation, prior factor and original noise inputs.
The composed gain profile then needs no intermediate stage profile premise. -/

namespace Kalman.Proofs.FloatInnovationDomain

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.CorrelatedStages.Innovation
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-- The rounded observation block's enclosure follows from its actual product. -/
theorem observation_block_bound (h l hl : Array Float)
    (p : Kalman.Proofs.CorrelatedStages.Gain.TwoStateDomain h l)
    (hrun : multiply 2 2 2 h l = .ok hl)
    : ∀ i j, |matrix 2 2 hl i j| ≤ 1 / 8 := by
  have pp := FloatGainDomain.product_profile_two h l (1 / 64) 2
    p.observation_finite p.factor_finite (by norm_num) (by norm_num) (by norm_num)
    p.observation_bound p.factor_bound
  have he := (FloatJosephError.product_within pp hrun).2.2
  have ht := product_magnitude (matrix 2 2 h) (matrix 2 2 l) (1 / 64) 2
    (fun i j => p.observation_bound i.val j.val i.isLt j.isLt)
    (fun i j => p.factor_bound i.val j.val i.isLt j.isLt)
  intro i j
  have hm := abs_sub_le (matrix 2 2 hl i j) ((matrix 2 2 h * matrix 2 2 l) i j) 0
  simp only [sub_zero] at hm
  have he' := he.2 i j
  have ht' := ht i j
  norm_num [productRadius] at he' ht'
  linarith only [hm, he', ht']

/-- Noise and rounded observation-block bounds derive every prearray input
condition, including row-energy headroom and a quantitative spectral floor. -/
theorem prearray_domain (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior) (tr hl : Array Float)
    (hnoise : cholesky 2 input.measurementNoise = .ok tr)
    (hproduct : multiply 2 2 2 input.observation prior.lower = .ok hl)
    : GramFactorInputDomain 2 4 (fromCols 2 2 2 tr hl) 2 := by
  obtain ⟨tr', _, hr, hf, _, _, _, _, he⟩ :=
    FloatCholeskyDomain.cholesky_accuracy input.measurementNoise p.noise
  have het : tr' = tr := Except.ok.inj (hr.symm.trans hnoise)
  subst tr'
  have pp := FloatGainDomain.product_profile_two input.observation prior.lower (1 / 64) 2
    p.gain_inputs.observation_finite p.gain_inputs.factor_finite
    (by norm_num) (by norm_num) (by norm_num)
    p.gain_inputs.observation_bound p.gain_inputs.factor_bound
  have hhlf := (FloatJosephError.product_within pp hproduct).2.1
  have hhlm := observation_block_bound input.observation prior.lower hl p.gain_inputs hproduct
  have hid := FloatQRInitialDomain.identity_input_domain 2 (by decide)
  refine ⟨
    by decide,
    by decide,
    FloatPrearray.fromCols_size 2 2 2 tr hl,
    FloatPrearray.fromCols_finite 2 2 2 tr hl hf hhlf,
    hid.budget_lower,
    hid.budget_upper,
    ?_,
    ?_
  ⟩
  · intro i
    have hnoiseDiag : FactorRecursion.gram (matrix 2 2 tr) i i ≤ 3 / 2 + (2 : ℝ)^(-42 : Int) := by
      have herr := (abs_le.mp (he.2 i i)).2
      have hd := p.noise_diagonal_cap i.val i.isLt
      change matrix 2 2 input.measurementNoise i i ≤ _ at hd
      change FactorRecursion.gram (matrix 2 2 tr) i i - matrix 2 2 input.measurementNoise i i ≤ _ at herr
      calc
        _ ≤ (2 : ℝ) ^ (-42 : Int) + matrix 2 2 input.measurementNoise i i := by
          simpa only [add_comm] using (sub_le_iff_le_add).mp herr
        _ ≤ (2 : ℝ) ^ (-42 : Int) + 3 / 2 := add_le_add le_rfl hd
        _ = _ := add_comm _ _
    have hhlDiag : FactorRecursion.gram (matrix 2 2 hl) i i ≤ 1 / 32 := by
      have h0 := hhlm i 0
      have h1 := hhlm i 1
      have hs0 : (matrix 2 2 hl i 0)^2 ≤ 1 / 64 := by nlinarith [sq_abs (matrix 2 2 hl i 0), abs_nonneg (matrix 2 2 hl i 0)]
      have hs1 : (matrix 2 2 hl i 1)^2 ≤ 1 / 64 := by nlinarith [sq_abs (matrix 2 2 hl i 1), abs_nonneg (matrix 2 2 hl i 1)]
      simp only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
      nlinarith only [hs0, hs1]
    have heq := congr_fun (congr_fun (FloatPrearray.fromCols_gram 2 2 2 tr hl) i) i
    have hb : FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 tr hl)) i i ≤ 2 := by
      simp only [Matrix.add_apply] at heq
      norm_num at hnoiseDiag
      linarith only [heq, hnoiseDiag, hhlDiag]
    norm_num only
    simpa only [FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
      using hb
  · have hfloor := FloatQRFactorDomain.innovation_prearray_lower input.measurementNoise tr hl p.noise hnoise
    convert hfloor.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul
      (by norm_num : 0 ≤ (2 / 3 : ℝ) - 1 / 2)) using 1
    norm_num
    module

/-- The full innovation profile, including Cholesky/product/QR executions and
QR input energy/rank conditions, follows from this stored local stage domain. -/
theorem innovation_profile (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∃ innovation : InnovationProfile input prior,
        innovation.noiseMass = 8
        ∧ innovation.noiseFloor = 1 / 2
        ∧ innovation.noiseBound = 2
        ∧ innovation.productMass = 8
        ∧ innovation.qrBudget = 2
        ∧ innovation.observationBound = 1 / 64
        ∧ innovation.factorBound = 2 := by
  obtain ⟨tr, _, pn, _, _, _⟩ := FloatCholeskyDomain.cholesky_profile input.measurementNoise p.noise
  obtain ⟨hl, _, pp, hproduct, _, _, _, _, _, _, _, _, _⟩ :=
    FloatGainDomain.formed_rhs input.observation prior.lower p.gain_inputs
  have d := prearray_domain input prior p tr hl pn.execution hproduct
  obtain ⟨_, _, l, hlrun, _, _, _, _, _⟩ :=
    FloatQRInitialDomain.gramFactor_accuracy_initial 2 4 _ 2 d
  have hobs : ∀ n m : Nat, n = 2 → m = 2 → ∀ i j : Nat, i < m → j < n →
      |value (entry n input.observation i j)| ≤ 1 / 64 := by
    intro n m hn hm
    subst n
    subst m
    intro i j hi hj
    exact (p.gain_inputs.observation_bound i j hi hj).trans (by norm_num)
  have hfactor : ∀ n : Nat, n = 2 → ∀ i j : Nat, i < n → j < n →
      |value (entry n prior.lower i j)| ≤ 2 := by
    intro n hn
    subst n
    exact p.gain_inputs.factor_bound
  let innovation : InnovationProfile input prior := {
    tr := tr, hl := hl, lower := l
    noiseMass := 8, noiseFloor := 1 / 2, noiseBound := 2
    productMass := 8, qrBudget := 2, observationBound := 1 / 64, factorBound := 2
    noise := by simpa only [p.measurement_dimension] using pn
    product := by simpa only [p.state_dimension, p.measurement_dimension] using pp
    computeProduct := by simpa only [p.state_dimension, p.measurement_dimension] using hproduct
    qr := by simpa only [p.state_dimension, p.measurement_dimension] using d
    computeQR := by simpa only [p.state_dimension, p.measurement_dimension] using hlrun
    observation_nonneg := by norm_num
    factor_nonneg := by norm_num
    observation_magnitude := fun i j => hobs _ _ p.state_dimension p.measurement_dimension
      i.val j.val i.isLt j.isLt
    factor_magnitude := fun i j => hfactor _ p.state_dimension i.val j.val i.isLt j.isLt
  }
  exact ⟨innovation, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Both innovation and gain profiles now follow without intermediate profile
or successful-run assumptions. Other filter stages and invariants remain open. -/
theorem innovation_and_gain_profiles (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∃ innovation : InnovationProfile input prior,
        innovation.noiseMass = 8
        ∧ innovation.noiseFloor = 1 / 2
        ∧ innovation.noiseBound = 2
        ∧ innovation.productMass = 8
        ∧ innovation.qrBudget = 2
        ∧ innovation.observationBound = 1 / 64
        ∧ innovation.factorBound = 2
        ∧ ∃ g : GainProfile innovation,
            g.productMass = 8
            ∧ g.solveMass = 32
            ∧ g.solveFloor = 1 / 2
            ∧ g.solveBound = 2
            ∧ g.gainBound = 1
            ∧ (∀ i j,
                |matrix input.stateDimension input.measurementDimension (gainArray g) i j|
                ≤ 1 / 3) := by
  obtain ⟨innovation, hn, hf, hb, hp, hqr, ho, hl⟩ := innovation_profile input prior p
  obtain ⟨g, hg⟩ := FloatGainDomain.gain_profile input prior innovation
    p.state_dimension p.measurement_dimension hqr p.noise p.gain_inputs
  exact ⟨innovation, hn, hf, hb, hp, hqr, ho, hl, g, hg⟩

/-- Innovation and gain error against the decoded original noise/model and
the exact Gram of the stored prior factor. Both stage profiles are derived;
the allowance includes noise Cholesky, both products, QR and both solve passes. -/
theorem innovation_and_gain_accuracy (input : Input.Model) (prior : Input.FactorState)
    (p : TwoStateDomain input prior)
    : ∃ innovation : InnovationProfile input prior,
      ∃ g : GainProfile innovation,
        solveCholesky input.measurementDimension input.stateDimension innovation.lower
            (transpose input.stateDimension input.measurementDimension g.pht)
          = .ok g.solution
        ∧ EntrywiseWithin (innovationRadius innovation)
            (FactorRecursion.gram
              (matrix input.measurementDimension input.measurementDimension
                innovation.lower))
            (CovarianceRecursion.innovationCovariance (model input)
              (factorState input.stateDimension prior))
        ∧ EntrywiseWithin (gainRadius g (3 / 4))
            (matrix input.stateDimension input.measurementDimension (gainArray g))
            (CovarianceRecursion.gain (model input)
              (factorState input.stateDimension prior))
        ∧ (∀ i j,
            |matrix input.stateDimension input.measurementDimension (gainArray g) i j|
            ≤ 1 / 3) := by
  obtain ⟨innovation, _, _, _, _, _, _, _, g, _, _, _, _, _, hg⟩ :=
    innovation_and_gain_profiles input prior p
  have hnoise : (matrix input.measurementDimension input.measurementDimension input.measurementNoise
      - (3 / 4 : ℝ) • 1).PosSemidef := by
    have hn : ∀ m : Nat, m = 2 → (matrix m m input.measurementNoise - (3 / 4 : ℝ) • 1).PosSemidef := by
      intro m hm
      subst m
      exact FloatCholeskyDomain.input_lower_bound input.measurementNoise p.noise
    exact hn _ p.measurement_dimension
  obtain ⟨hr, he⟩ := FloatSquareRootUpdate.gain_accuracy input prior innovation g
    (3 / 4) (by norm_num) hnoise
  exact ⟨
    innovation,
    g,
    hr,
    (FloatSquareRootUpdate.innovation_accuracy input prior innovation).2.2.2,
    he,
    hg
  ⟩

/-- A nonzero observation and correlated prior, with identity noise, establish
nonvacuity of the complete local innovation/gain input domain. -/
theorem input_domain_nonempty
    : ∃ input : Input.Model,
      ∃ prior : Input.FactorState,
        TwoStateDomain input prior
        ∧ input.observation = #[0.015625, 0.0, 0.0, 0.015625]
        ∧ prior.lower = #[1.0, 0.0, 0.125, 1.0] := by
  let r : Array Float := #[1.0, 0.0, 0.0, 1.0]
  let input : Input.Model := ⟨2, 2, r, #[0.015625, 0.0, 0.0, 0.015625], r, r, #[0.5, -0.5]⟩
  let prior : Input.FactorState := ⟨#[0.0, 0.0], #[1.0, 0.0, 0.125, 1.0]⟩
  have hn : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain r := by
    refine ⟨by decide, by decide +kernel, ?_, ?_, ?_, ?_⟩
    · simp [r, entry, Flare.Matrix.Dense.entry]
    · intro i hi
      interval_cases i <;> norm_num [r, entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.one_value]
    · intro i hi
      interval_cases i <;> norm_num [r, entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.one_value]
    · norm_num [r, entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.zero_value]
  refine ⟨
    input,
    prior,
    ⟨rfl, rfl, FloatGainDomain.input_domain_nonempty, hn, ?_⟩,
    rfl,
    rfl
  ⟩
  intro i hi
  interval_cases i <;> norm_num [input, r, entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.one_value]

end Kalman.Proofs.FloatInnovationDomain
