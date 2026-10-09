import Kalman.Proofs.DiagonalStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FloatObservableDiagonal
import Kalman.Proofs.FloatDiagonalSolve
import Kalman.Proofs.RealDiagonalObservation

/-! Larger full-observation gain products and both substitution passes. The
input domain is the reached stored prior plus original H/R words. Exact gain
comparison includes HL/PHT rounding, original-R factorization and innovation QR.
Mean/posterior correction is composed in separate modules. Accumulated
observable-trajectory accuracy remains separate work. -/

namespace Kalman.Proofs.FloatObservableGain

open Matrix hiding transpose
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.DiagonalStages.Prediction
open Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-- The returned innovation's diagonal structure and proved floor derive the
larger solve factor domain; no desired solve outcome is a premise. -/
theorem solve_factor_domain (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (di : DecodedDiagonal 2 prior.lower)
    (tr hl s : Array Float) (hr : cholesky 2 input.measurementNoise = .ok tr)
    (hh : multiply 2 2 2 input.observation prior.lower = .ok hl)
    (hs
      : Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
          (fromCols 2 2 2 tr hl)
        = .ok s)
    : Kalman.Proofs.CholeskyProfiles.DiagonalSolve.FactorDomain s := by
  obtain ⟨tr', hl', s', htr, hhl, hsr, hsize, hfinite, hp, _, hfloor, _, hb, _⟩ :=
    FloatObservableInnovation.factor_accuracy input prior d
  have etr : tr' = tr := Except.ok.inj (htr.symm.trans hr)
  subst tr'
  have ehl : hl' = hl := Except.ok.inj (hhl.symm.trans hh)
  subst hl'
  have es : s' = s := Except.ok.inj (hsr.symm.trans hs)
  subst s'
  have hd := FloatObservableDiagonal.innovation_diagonal input prior d di tr hl s hr hh hs
  refine ⟨hsize, hfinite, hd, ?_, hb⟩
  intro i hi
  have hlo := hfloor.diag_nonneg (i := ⟨i, hi⟩)
  rw [FloatDiagonalStorage.gram_diagonal 2 s hd] at hlo
  simp only [Matrix.sub_apply, diagonal_apply_eq, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at hlo
  change 0 ≤ (value (entry 2 s i i))^2 - 29 / 16 at hlo
  have hpos := hp.2 ⟨i, hi⟩
  change 0 < value (entry 2 s i i) at hpos
  nlinarith

/-- Assemble the original innovation profile at budget 25/8 from the local
native inputs, using the existing runtime and same decoded H/R. -/
theorem innovation_profile (input : Input.Model) (prior : Input.FactorState)
    (hn : input.stateDimension = 2) (d : InnovationDomain input prior)
    : ∃ p : InnovationProfile input prior,
        p.noiseMass = 8
        ∧ p.noiseFloor = 1 / 2
        ∧ p.noiseBound = 2
        ∧ p.productMass = 8
        ∧ p.qrBudget = 25 / 8
        ∧ p.observationBound = 1
        ∧ p.factorBound = 2 := by
  obtain ⟨tr, _, noise, _, _, _⟩ := FloatCholeskyDomain.cholesky_profile
    input.measurementNoise d.observation.noise.covariance
  obtain ⟨hl, product, hh, _, _, _⟩ := FloatObservableInnovation.observation_product input prior d
  have qr := FloatObservableInnovation.prearray_domain input prior d tr hl noise.execution hh
  obtain ⟨_, _, s, hs, _, _, _, _, _⟩ :=
    FloatQRInitialDomain.gramFactor_accuracy_initial 2 4 _ (25 / 8) qr
  let p : InnovationProfile input prior := {
    tr := tr, hl := hl, lower := s
    noiseMass := 8, noiseFloor := 1 / 2, noiseBound := 2
    productMass := 8, qrBudget := 25 / 8, observationBound := 1, factorBound := 2
    noise := by simpa only [d.observation.measurement_dimension] using noise
    product := by simpa only [hn, d.observation.measurement_dimension] using product
    computeProduct := by simpa only [hn, d.observation.measurement_dimension] using hh
    qr := by simpa only [hn, d.observation.measurement_dimension] using qr
    computeQR := by simpa only [hn, d.observation.measurement_dimension] using hs
    observation_nonneg := by norm_num
    factor_nonneg := by norm_num
    observation_magnitude := by
      intro i j
      have hi := i.isLt
      have hj := j.isLt
      simp only [hn, d.observation.measurement_dimension] at hi hj
      change |value (entry input.stateDimension input.observation i.val j.val)| ≤ 1
      have ho : |value (entry 2 input.observation i.val j.val)| ≤ 1 := by
        change |matrix 2 2 input.observation ⟨i.val, hi⟩ ⟨j.val, hj⟩| ≤ 1
        rw [d.observation.observation_identity]
        simp only [Matrix.one_apply]
        split_ifs <;> norm_num
      simpa only [hn] using ho
    factor_magnitude := by
      intro i j
      have hi := i.isLt
      have hj := j.isLt
      simp only [hn] at hi hj
      change |value (entry input.stateDimension prior.lower i.val j.val)| ≤ 2
      simpa only [hn] using d.factor_bound i.val j.val hi hj
  }
  exact ⟨p, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem product_profile_sixteen (a b : Array Float) (A B : ℝ)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hA : 0 ≤ A) (hm : A * B ≤ 8)
    (ham : ∀ i j, i < 2 → j < 2 → |value (entry 2 a i j)| ≤ A)
    (hbm : ∀ i j, i < 2 → j < 2 → |value (entry 2 b i j)| ≤ B)
    : ProductProfile 2 2 2 a b 16 := by
  refine ⟨by decide, ha, hb, ?_, ?_, ?_⟩
  · simpa only [show (2 : ℝ)^(4 : Int) = 16 by norm_num]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (4 : Int) ≤ 990)
  · simpa only [show (2 : ℝ)^(4 : Int) = 16 by norm_num]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-1022 : Int) ≤ 4)
  · intro i j hi hj
    calc
      _ ≤ ∑ _k ∈ Finset.range 2, A * B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (ham i k hi (Finset.mem_range.mp hk))
          (hbm k j (Finset.mem_range.mp hk) hj) (abs_nonneg _) hA
      _ ≤ 16 := by simp; linarith

theorem stored_covariance_bound (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (di : DecodedDiagonal 2 prior.lower)
    : ∀ i j, |FactorRecursion.gram (matrix 2 2 prior.lower) i j| ≤ 13 / 4 := by
  rw [FloatDiagonalStorage.gram_diagonal 2 prior.lower di]
  intro i j
  by_cases hij : i = j
  · subst j
    rw [diagonal_apply_eq, abs_of_nonneg (sq_nonneg _)]
    have hc := d.covariance_diagonal_cap i
    rw [FloatDiagonalStorage.gram_diagonal 2 prior.lower di, diagonal_apply_eq] at hc
    exact hc
  · rw [diagonal_apply_ne _ hij, abs_zero]
    norm_num

/-- The actual rounded HL, PHT and transposed RHS preserve decoded diagonality.
Both product profiles/runs are derived; PHT error is ≤2^-43 against the incoming
stored prior covariance and its entries are bounded by 7/2. -/
theorem formed_rhs (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (di : DecodedDiagonal 2 prior.lower)
    : ∃ hl pht,
        multiply 2 2 2 input.observation prior.lower = .ok hl
        ∧ ProductProfile 2 2 2 prior.lower (transpose 2 2 hl) 16
        ∧ multiply 2 2 2 prior.lower (transpose 2 2 hl) = .ok pht
        ∧ pht.size = 4
        ∧ pht.all Float.isFinite = true
        ∧ DecodedDiagonal 2 pht
        ∧ Kalman.Proofs.CholeskyProfiles.DiagonalSolve.RightHandSideDomain
            (transpose 2 2 pht)
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-43 : Int)) (matrix 2 2 pht)
            (FactorRecursion.gram (matrix 2 2 prior.lower))
        ∧ (∀ i j, |matrix 2 2 pht i j| ≤ 7 / 2) := by
  obtain ⟨hl, _, hh, _, hhf, eh⟩ := FloatObservableInnovation.observation_product input prior d
  have hhm : ∀ i j, |matrix 2 2 hl i j| ≤ 17 / 8 := by
    intro i j
    have ht := abs_sub_le (matrix 2 2 hl i j) (matrix 2 2 prior.lower i j) 0
    simp only [sub_zero] at ht
    have he := eh.2 i j
    have hb := d.factor_bound i.val j.val i.isLt j.isLt
    change |matrix 2 2 prior.lower i j| ≤ 2 at hb
    norm_num [productRadius] at he
    linarith
  have ht := Flare.Matrix.Multiplication.transpose_storage 2 2 hl hhf
  have htm : matrix 2 2 (transpose 2 2 hl) = (matrix 2 2 hl).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 hl hhf
  have pp := product_profile_sixteen prior.lower (transpose 2 2 hl) 2 (17 / 8)
    d.factor_finite ht.2.1 (by norm_num) (by norm_num) d.factor_bound (by
      intro i j hi hj
      change |matrix 2 2 (transpose 2 2 hl) ⟨i, hi⟩ ⟨j, hj⟩| ≤ _
      rw [htm]
      exact hhm ⟨j, hj⟩ ⟨i, hi⟩)
  obtain ⟨pht, hp, hps, hpf, ep⟩ := FloatDenseError.multiply_entrywise_accuracy 2 2 2
    prior.lower (transpose 2 2 hl) (fun _ _ => (16 : ℝ)) pp.inner_le pp.finite_left pp.finite_right
    (fun _ _ _ _ => pp.upper) (fun _ _ _ _ => pp.lower) pp.mass
  rw [htm] at ep
  have ec' : EntrywiseWithin ((2 : ℝ)^(-43 : Int)) (matrix 2 2 pht)
      (FactorRecursion.gram (matrix 2 2 prior.lower)) := by
    have ebase : EntrywiseWithin (productRadius 2 16 + 4 * productRadius 2 8)
        (matrix 2 2 pht) (FactorRecursion.gram (matrix 2 2 prior.lower)) := by
      convert within_trans (show EntrywiseWithin (productRadius 2 16) _ _ from
        ⟨by norm_num [productRadius], ep⟩)
        (within_mul_left (matrix 2 2 prior.lower) (within_transpose eh)
          (by norm_num : (0 : ℝ) ≤ 2)
          (fun i j => d.factor_bound i.val j.val i.isLt j.isLt)) using 1
      all_goals norm_num [FactorRecursion.gram]
    exact ⟨by positivity, fun i j => (ebase.2 i j).trans (by norm_num [productRadius])⟩
  have hm : ∀ i j, |matrix 2 2 pht i j| ≤ 7 / 2 := by
    intro i j
    have ht := abs_sub_le (matrix 2 2 pht i j)
      (FactorRecursion.gram (matrix 2 2 prior.lower) i j) 0
    simp only [sub_zero] at ht
    have he := ec'.2 i j
    norm_num at he
    linarith [stored_covariance_bound input prior d di i j]
  have hdhl := FloatDiagonalStorage.multiply_diagonal_two _ _ _
    d.observation.observation_finite d.factor_finite
    (FloatObservableDiagonal.observation_diagonal input d.observation) di hh
  have hd := FloatDiagonalStorage.multiply_diagonal_two _ _ _ d.factor_finite ht.2.1 di
    (FloatDiagonalStorage.transpose_diagonal 2 hl hhf hdhl) hp
  have hb := Flare.Matrix.Multiplication.transpose_storage 2 2 pht hpf
  have hbm : matrix 2 2 (transpose 2 2 pht) = (matrix 2 2 pht).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 pht hpf
  refine ⟨hl, pht, hh, pp, hp, hps, hpf, hd, ?_, ec', hm⟩
  refine ⟨by simpa using hb.1, hb.2.1, ?_⟩
  intro i j hi hj
  change |matrix 2 2 (transpose 2 2 pht) ⟨i, hi⟩ ⟨j, hj⟩| ≤ 4
  rw [hbm]
  exact (hm ⟨j, hj⟩ ⟨i, hi⟩).trans (by norm_num)

theorem ideal_gain_diagonal (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior) (di : DecodedDiagonal 2 prior.lower)
    : FactorRecursion.gram (matrix 2 2 prior.lower)
        * (FactorRecursion.gram (matrix 2 2 prior.lower)
            + matrix 2 2 input.measurementNoise)⁻¹
      = diagonal
          (fun i =>
            FactorRecursion.gram (matrix 2 2 prior.lower) i i
            / (FactorRecursion.gram (matrix 2 2 prior.lower) i i
                + matrix 2 2 input.measurementNoise i i)) := by
  have hp : ∀ i, 0 ≤ FactorRecursion.gram (matrix 2 2 prior.lower) i i :=
    fun i => (CovarianceStructure.gram_posSemidef _).diag_nonneg
  have hr : ∀ i, 0 < matrix 2 2 input.measurementNoise i i := by
    intro i
    exact (by norm_num : (0 : ℝ) < 1).trans_le
      (d.observation.noise.covariance.diagonal_lower i.val i.isLt)
  have hP := FloatDiagonalStorage.gram_diagonal 2 prior.lower di
  have hR := FloatDiagonalStorage.matrix_diagonal 2 input.measurementNoise d.observation.noise.diagonal
  have hP' : FactorRecursion.gram (matrix 2 2 prior.lower)
      = diagonal (fun i => FactorRecursion.gram (matrix 2 2 prior.lower) i i) := by
    rw [hP]
    simp only [diagonal_apply_eq]
  conv_lhs =>
    rw [hP', hR, diagonal_add,
      RealDiagonalObservation.diagonal_inverse _ (fun i => (add_pos_of_nonneg_of_pos (hp i) (hr i)).ne'),
      diagonal_mul_diagonal]
  simp only [div_eq_mul_inv]

theorem ideal_gain_bounds (input : Input.Model) (prior : Input.FactorState)
    (d : InnovationDomain input prior)
    : ∀ i,
        (5 : ℝ) / 13
          ≤ FactorRecursion.gram (matrix 2 2 prior.lower) i i
            / (FactorRecursion.gram (matrix 2 2 prior.lower) i i
                + matrix 2 2 input.measurementNoise i i)
        ∧ FactorRecursion.gram (matrix 2 2 prior.lower) i i
            / (FactorRecursion.gram (matrix 2 2 prior.lower) i i
                + matrix 2 2 input.measurementNoise i i)
          ≤ 13 / 17 := by
  intro i
  have hp := d.covariance_floor.diag_nonneg (i := i)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hp
  have hu := d.covariance_diagonal_cap i
  have hr := d.observation.noise.covariance.diagonal_lower i.val i.isLt
  have hr' := d.observation.noise.diagonal_cap i.val i.isLt
  change 1 ≤ matrix 2 2 input.measurementNoise i i at hr
  change matrix 2 2 input.measurementNoise i i ≤ 3 / 2 at hr'
  have hden : 0 < FactorRecursion.gram (matrix 2 2 prior.lower) i i
      + matrix 2 2 input.measurementNoise i i := by linarith
  exact ⟨(le_div_iff₀ hden).mpr (by linarith), (div_le_iff₀ hden).mpr (by linarith)⟩

private theorem raw_gain_profile (input : Input.Model) (prior : Input.FactorState)
    (hn : input.stateDimension = 2) (d : InnovationDomain input prior)
    (di : DecodedDiagonal 2 prior.lower) (p : InnovationProfile input prior)
    : ∃ g : GainProfile p,
        g.productMass = 16
        ∧ g.solveMass = 16
        ∧ g.solveFloor = 1
        ∧ g.solveBound = 9 / 4
        ∧ g.gainBound = 6
        ∧ DecodedDiagonal 2 (gainArray g) := by
  have hm := d.observation.measurement_dimension
  have hr : cholesky 2 input.measurementNoise = .ok p.tr := by simpa only [hm] using p.noise.execution
  have hh : multiply 2 2 2 input.observation prior.lower = .ok p.hl := by
    simpa only [hn, hm] using p.computeProduct
  have hs : Kalman.Implementation.OrthogonalFactorization.gramFactor 2 4
      (fromCols 2 2 2 p.tr p.hl) = .ok p.lower := by simpa only [hn, hm] using p.computeQR
  have sd := solve_factor_domain input prior d di p.tr p.hl p.lower hr hh hs
  obtain ⟨hl, pht, hhl, pp, hpht, _, hpf, hdp, rhs, _, _⟩ := formed_rhs input prior d di
  have ehl : hl = p.hl := Except.ok.inj (hhl.symm.trans hh)
  subst hl
  obtain ⟨y, x, _, _, hyf, hxf, solve, _, _, mx⟩ :=
    FloatDiagonalSolve.solve_accuracy p.lower (transpose 2 2 pht) sd rhs
  have hdb := FloatDiagonalStorage.transpose_diagonal 2 pht hpf hdp
  have hdx := FloatDiagonalSolve.solve_diagonal _ _ y x sd rhs hdb hyf hxf solve
  have hdk := FloatDiagonalStorage.transpose_diagonal 2 x hxf hdx
  have ht := Flare.Matrix.Multiplication.transpose_storage 2 2 x hxf
  have hmag : ∀ n m : Nat, n = 2 → m = 2 → ∀ i j, i < n → j < m →
      |value (entry m (transpose m n x) i j)| ≤ 6 := by
    intro n m en em
    subst n m
    intro i j hi hj
    change |value (Flare.Matrix.Dense.entry 2 (Flare.Matrix.Dense.transpose 2 2 x) i j)| ≤ 6
    rw [ht.2.2 i j hi hj]
    exact mx j i hj hi
  let g : GainProfile p := {
    pht := pht, forward := y, solution := x
    productMass := 16, solveMass := 16, solveFloor := 1, solveBound := 9 / 4, gainBound := 6
    product := by simpa only [hn, hm] using pp
    computeProduct := by simpa only [hn, hm] using hpht
    solve := by simpa only [hn, hm] using solve
    finite_solution := hxf
    mass_nonneg := by norm_num
    gain_nonneg := by norm_num
    gain_magnitude := fun i j => hmag _ _ hn hm i.val j.val i.isLt j.isLt
  }
  exact ⟨g, rfl, rfl, rfl, rfl, rfl, by simpa only [gainArray, hn, hm] using hdk⟩

/-- Retaining the exact four/three-row QR constants gives a stronger innovation
profile radius than the earlier power-of-two convenience cap. -/
theorem innovation_radius_cap (input : Input.Model) (prior : Input.FactorState)
    (hn : input.stateDimension = 2) (hm : input.measurementDimension = 2)
    (p : InnovationProfile input prior)
    (hM : p.noiseMass = 8) (hF : p.noiseFloor = 1 / 2) (hB : p.noiseBound = 2)
    (hP : p.productMass = 8) (hQ : p.qrBudget = 25 / 8)
    (hH : p.observationBound = 1) (hL : p.factorBound = 2)
    : innovationRadius p ≤ 9 * (2 : ℝ) ^ (-32 : Int) := by
  have hc := FloatCholeskyDomain.backward_radius_cap
  simp only [innovationRadius, hn, hm, hM, hF, hB, hP, hQ, hH, hL]
  apply le_trans (add_le_add (add_le_add le_rfl hc) le_rfl)
  simp only [qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius,
    sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius,
    Finset.sum_range_succ, Finset.sum_range_zero, productRadius]
  norm_num

private theorem gain_radius_cap (input : Input.Model) (prior : Input.FactorState)
    (hn : input.stateDimension = 2) (hm : input.measurementDimension = 2)
    (p : InnovationProfile input prior) (g : GainProfile p)
    (hI : innovationRadius p ≤ 9 * (2 : ℝ) ^ (-32 : Int))
    (hP : p.productMass = 8) (hL : p.factorBound = 2)
    (hPM : g.productMass = 16) (hSM : g.solveMass = 16) (hSF : g.solveFloor = 1)
    (hSB : g.solveBound = 9 / 4)
    : gainRadius g 1
      ≤ 2
        * ((1 + 2 * (9 / 4)) * (11 * (2 : ℝ) ^ (-46 : Int))
            + productRadius 2 16
            + 4 * productRadius 2 8
            + 2 * g.gainBound * (9 * (2 : ℝ) ^ (-32 : Int))) := by
  simp only [gainRadius, gainResidualRadius, hn, hm, hP, hL, hPM, hSM, hSF, hSB, div_one]
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * 2 = 4 by norm_num]
  have hd := mul_le_mul_of_nonneg_left FloatDiagonalSolve.division_radius_cap
    (by norm_num : (0 : ℝ) ≤ 1 + 2 * (9 / 4))
  have hi := mul_le_mul_of_nonneg_left hI
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) g.gain_nonneg)
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add hd le_rfl) le_rfl) hi) (by norm_num)

/-- Transport a fully observed gain comparison to the two-state matrices. -/
theorem full_observation_gain_reference (n m : Nat) (ε : ℝ)
    (observation noise lower gain : Array Float) (hn : n = 2) (hm : m = 2)
    (hH : matrix 2 2 observation = 1)
    (e
      : EntrywiseWithin ε (matrix n m gain)
          (FactorRecursion.gram (matrix n n lower) * (matrix m n observation).transpose
            * (matrix m n observation * FactorRecursion.gram (matrix n n lower)
                  * (matrix m n observation).transpose
                + matrix m m noise)⁻¹))
    : EntrywiseWithin ε (matrix 2 2 gain)
        (FactorRecursion.gram (matrix 2 2 lower)
          * (FactorRecursion.gram (matrix 2 2 lower) + matrix 2 2 noise)⁻¹) := by
  subst n m
  simpa only [hH, Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul] using e

/-- Successful diagonal gain construction and accuracy from original local
inputs. The comparison includes both formed products and innovation QR, against
the ideal gain of the same stored prior and original decoded H/R. -/
theorem gain_accuracy (input : Input.Model) (prior : Input.FactorState)
    (hn : input.stateDimension = 2) (d : InnovationDomain input prior)
    (di : DecodedDiagonal 2 prior.lower)
    : ∃ p : InnovationProfile input prior,
      ∃ g : GainProfile p,
        g.productMass = 16
        ∧ g.solveMass = 16
        ∧ g.solveFloor = 1
        ∧ g.solveBound = 9 / 4
        ∧ g.gainBound = 13 / 16
        ∧ DecodedDiagonal 2 (gainArray g)
        ∧ solveCholesky input.measurementDimension input.stateDimension p.lower
            (transpose input.stateDimension input.measurementDimension g.pht)
          = .ok g.solution
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-27 : Int))
            (matrix input.stateDimension input.measurementDimension (gainArray g))
            (CovarianceRecursion.gain (model input)
              (factorState input.stateDimension prior))
        ∧ (∀ i,
            i < 2
            → (3 : ℝ) / 8 ≤ value (entry 2 (gainArray g) i i)
              ∧ value (entry 2 (gainArray g) i i) ≤ 13 / 16) := by
  have hm := d.observation.measurement_dimension
  obtain ⟨p, hM, hF, hB, hP, hQ, hH, hL⟩ := innovation_profile input prior hn d
  have hI := innovation_radius_cap input prior hn hm p hM hF hB hP hQ hH hL
  obtain ⟨g0, hPM, hSM, hSF, hSB, hGB, hdk⟩ := raw_gain_profile input prior hn d di p
  have hR : (matrix input.measurementDimension input.measurementDimension input.measurementNoise
      - (1 : ℝ) • 1).PosSemidef := by
    rw [hm]
    exact FloatObservablePrediction.noise_input_floor _ d.observation.noise
  obtain ⟨_, e0⟩ := FloatSquareRootUpdate.gain_accuracy input prior p g0 1 (by norm_num) hR
  have hc0 : gainRadius g0 1 ≤ (2 : ℝ)^(-24 : Int) := by
    apply (gain_radius_cap input prior hn hm p g0 hI hP hL hPM hSM hSF hSB).trans
    rw [hGB]
    norm_num [productRadius]
  have e02 : EntrywiseWithin ((2 : ℝ)^(-24 : Int))
      (matrix 2 2 (gainArray g0))
      (FactorRecursion.gram (matrix 2 2 prior.lower)
        * (FactorRecursion.gram (matrix 2 2 prior.lower) + matrix 2 2 input.measurementNoise)⁻¹) := by
    have e := show EntrywiseWithin ((2 : ℝ)^(-24 : Int)) _ _ from
      ⟨by positivity, fun i j => (e0.2 i j).trans hc0⟩
    simp only [CovarianceRecursion.gain, CovarianceRecursion.innovationCovariance, model, factorState] at e
    exact full_observation_gain_reference _ _ _ input.observation input.measurementNoise
      prior.lower (gainArray g0) hn hm d.observation.observation_identity e
  rw [ideal_gain_diagonal input prior d di] at e02
  have hdiag : ∀ i, i < 2 → (3 : ℝ) / 8 ≤ value (entry 2 (gainArray g0) i i)
      ∧ value (entry 2 (gainArray g0) i i) ≤ 13 / 16 := by
    intro i hi
    have he := abs_le.mp (e02.2 ⟨i, hi⟩ ⟨i, hi⟩)
    simp only [diagonal_apply_eq] at he
    change -(2 : ℝ)^(-24 : Int) ≤ value (entry 2 (gainArray g0) i i) - _
      ∧ value (entry 2 (gainArray g0) i i) - _ ≤ (2 : ℝ)^(-24 : Int) at he
    have hb := ideal_gain_bounds input prior d ⟨i, hi⟩
    norm_num at he
    constructor <;> linarith
  have hmag : ∀ i j, i < 2 → j < 2 → |value (entry 2 (gainArray g0) i j)| ≤ 13 / 16 := by
    intro i j hi hj
    by_cases hij : i = j
    · subst j
      have hb := hdiag i hi
      rw [abs_of_pos (by linarith : 0 < value (entry 2 (gainArray g0) i i))]
      exact hb.2
    · rw [hdk i j hi hj hij, abs_zero]
      norm_num
  have hmag' : ∀ i j, |matrix input.stateDimension input.measurementDimension (gainArray g0) i j|
      ≤ 13 / 16 := by
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    simp only [hn, hm] at hi hj
    simpa only [hn, hm, matrix, Flare.Matrix.Value.matrix, entry,
      Flare.Matrix.Dense.entry]
      using hmag i.val j.val hi hj
  let g : GainProfile p := {
    g0 with
    gainBound := 13 / 16
    gain_nonneg := by norm_num
    gain_magnitude := hmag'
  }
  obtain ⟨hr, he⟩ := FloatSquareRootUpdate.gain_accuracy input prior p g 1 (by norm_num) hR
  have hc : gainRadius g 1 ≤ (2 : ℝ)^(-27 : Int) := by
    apply (gain_radius_cap input prior hn hm p g hI hP hL hPM hSM hSF hSB).trans
    norm_num [g, productRadius]
  exact ⟨
    p,
    g,
    hPM,
    hSM,
    hSF,
    hSB,
    rfl,
    hdk,
    hr,
    ⟨by positivity, fun i j => (he.2 i j).trans hc⟩,
    hdiag
  ⟩

end Kalman.Proofs.FloatObservableGain
