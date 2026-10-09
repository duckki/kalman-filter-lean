import Kalman.Proofs.CorrelatedStages
import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Proofs.FloatQRFactorDomain
import Kalman.Proofs.FloatSquareRootUpdate

/-! Derive both rounded gain products, their transposed RHS, and gain solve
profiles from stored observation/prior-factor conditions and innovation margins.
The full filter operating invariant remains a separate obligation. -/

namespace Kalman.Proofs.FloatGainDomain

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.CholeskyProfiles.SolveDomain
open Kalman.Proofs.CorrelatedStages.Gain
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-- Entry bounds derive the existing mass-eight product profile. -/
theorem product_profile_two (a b : Array Float) (A B : ℝ)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hm : A * B ≤ 4)
    (ham : ∀ i j, i < 2 → j < 2 → |value (entry 2 a i j)| ≤ A)
    (hbm : ∀ i j, i < 2 → j < 2 → |value (entry 2 b i j)| ≤ B)
    : ProductProfile 2 2 2 a b 8 := by
  refine ⟨by decide, ha, hb, ?_, ?_, ?_⟩
  · simpa only [show (2 : ℝ)^(3 : Int) = 8 by norm_num]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 : Int) ≤ 990)
  · simpa only [show (2 : ℝ)^(3 : Int) = 8 by norm_num]
      using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-1022 : Int) ≤ 3)
  · intro i j hi hj
    calc
      _ ≤ ∑ _k ∈ Finset.range 2, A * B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (ham i k hi (Finset.mem_range.mp hk))
          (hbm k j (Finset.mem_range.mp hk) hj) (abs_nonneg _) hA
      _ ≤ 8 := by simp; linarith only [hm]

private theorem product_success (a b : Array Float) (p : ProductProfile 2 2 2 a b 8)
    : ∃ r,
        multiply 2 2 2 a b = .ok r
        ∧ r.size = 4
        ∧ r.all Float.isFinite = true
        ∧ EntrywiseWithin (productRadius 2 8) (matrix 2 2 r)
            (matrix 2 2 a * matrix 2 2 b) := by
  obtain ⟨r, hr, hs, hf, he⟩ := FloatDenseError.multiply_entrywise_accuracy 2 2 2 a b
    (fun _ _ => (8 : ℝ)) p.inner_le p.finite_left p.finite_right
    (fun _ _ _ _ => p.upper) (fun _ _ _ _ => p.lower) p.mass
  exact ⟨r, hr, hs, hf, ⟨by norm_num [productRadius], he⟩⟩

/-- The propagated product allowance leaves ample room inside RHS cap 1/8. -/
theorem rhs_radius_cap : (1 : ℝ) / 16 + 5 * productRadius 2 8 ≤ 1 / 8 := by
  norm_num [productRadius]

/-- Form the actual rounded HL, L(HL)^T, and copied transposed RHS. Both
product profiles and runs are conclusions; covariance-level bounds preserve
the cancellation/structure lost by bounding every factor product separately. -/
theorem formed_rhs (h l : Array Float) (p : TwoStateDomain h l)
    : ∃ hl pht,
        ProductProfile 2 2 2 h l 8
        ∧ multiply 2 2 2 h l = .ok hl
        ∧ hl.size = 4
        ∧ hl.all Float.isFinite = true
        ∧ ProductProfile 2 2 2 l (transpose 2 2 hl) 8
        ∧ multiply 2 2 2 l (transpose 2 2 hl) = .ok pht
        ∧ pht.size = 4
        ∧ pht.all Float.isFinite = true
        ∧ EntrywiseWithin (5 * productRadius 2 8) (matrix 2 2 pht)
            ((matrix 2 2 l * (matrix 2 2 l).transpose) * (matrix 2 2 h).transpose)
        ∧ RightHandSideDomain (transpose 2 2 pht)
        ∧ (∀ i j, |matrix 2 2 pht i j| ≤ 1 / 16 + 5 * productRadius 2 8) := by
  have pHL := product_profile_two h l (1 / 64) 2 p.observation_finite p.factor_finite
    (by norm_num) (by norm_num) (by norm_num) p.observation_bound p.factor_bound
  obtain ⟨hl, hhl, hhs, hhf, eh⟩ := product_success h l pHL
  have hehl := product_magnitude (matrix 2 2 h) (matrix 2 2 l) (1 / 64) 2
    (fun i j => p.observation_bound i.val j.val i.isLt j.isLt)
    (fun i j => p.factor_bound i.val j.val i.isLt j.isLt)
  have hhlm : ∀ i j, |matrix 2 2 hl i j| ≤ 1 / 8 := by
    intro i j
    have hm := abs_sub_le (matrix 2 2 hl i j) ((matrix 2 2 h * matrix 2 2 l) i j) 0
    have he := eh.2 i j
    have ht := hehl i j
    simp only [sub_zero] at hm
    norm_num [productRadius] at he ht
    linarith only [hm, he, ht]
  have ht := Flare.Matrix.Multiplication.transpose_storage 2 2 hl hhf
  have htm : matrix 2 2 (transpose 2 2 hl) = (matrix 2 2 hl).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 hl hhf
  have pPHT := product_profile_two l (transpose 2 2 hl) 2 (1 / 8) p.factor_finite ht.2.1
    (by norm_num) (by norm_num) (by norm_num) p.factor_bound (by
      intro i j hi hj
      change |matrix 2 2 (transpose 2 2 hl) ⟨i, hi⟩ ⟨j, hj⟩| ≤ _
      rw [htm]
      exact hhlm ⟨j, hj⟩ ⟨i, hi⟩)
  obtain ⟨pht, hpht, hps, hpf, ep⟩ := product_success l (transpose 2 2 hl) pPHT
  rw [htm] at ep
  have eprop := within_mul_left (matrix 2 2 l) (within_transpose eh) (by norm_num : (0 : ℝ) ≤ 2)
    (fun i j => p.factor_bound i.val j.val i.isLt j.isLt)
  have ec : EntrywiseWithin (5 * productRadius 2 8) (matrix 2 2 pht)
      ((matrix 2 2 l * (matrix 2 2 l).transpose) * (matrix 2 2 h).transpose) := by
    convert within_trans ep eprop using 1
    · norm_num; ring
    · simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have htarget := product_magnitude (matrix 2 2 l * (matrix 2 2 l).transpose)
    (matrix 2 2 h).transpose 2 (1 / 64) p.covariance_bound
    (fun i j => p.observation_bound j.val i.val j.isLt i.isLt)
  have hm : ∀ i j, |matrix 2 2 pht i j| ≤ 1 / 16 + 5 * productRadius 2 8 := by
    intro i j
    have hmag := abs_sub_le (matrix 2 2 pht i j)
      (((matrix 2 2 l * (matrix 2 2 l).transpose) * (matrix 2 2 h).transpose) i j) 0
    simp only [sub_zero] at hmag
    have he := ec.2 i j
    have ht := htarget i j
    norm_num at ht
    linarith only [hmag, he, ht]
  have hb := Flare.Matrix.Multiplication.transpose_storage 2 2 pht hpf
  have hbm : matrix 2 2 (transpose 2 2 pht) = (matrix 2 2 pht).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 pht hpf
  have q : RightHandSideDomain (transpose 2 2 pht) := by
    refine ⟨by simpa using hb.1, hb.2.1, ?_⟩
    intro i j hi hj
    change |matrix 2 2 (transpose 2 2 pht) ⟨i, hi⟩ ⟨j, hj⟩| ≤ _
    rw [hbm]
    exact (hm ⟨j, hj⟩ ⟨i, hi⟩).trans rhs_radius_cap
  exact ⟨hl, pht, pHL, hhl, hhs, hhf, pPHT, hpht, hps, hpf, ec, q, hm⟩

/-- A sharper gain magnitude from the formed RHS, while retaining the existing
solve accuracy radius and mass/floor/entry constants. -/
theorem formed_gain (h l s : Array Float) (p : TwoStateDomain h l)
    (sd : FactorDomain s)
    (sf : (matrix 2 2 s * (matrix 2 2 s).transpose - (1 / 2 : ℝ) • 1).PosSemidef)
    : ∃ hl pht y x,
        multiply 2 2 2 h l = .ok hl
        ∧ multiply 2 2 2 l (transpose 2 2 hl) = .ok pht
        ∧ SolveProfile 2 2 s (transpose 2 2 pht) y x 32 (1 / 2) 2
        ∧ solveCholesky 2 2 s (transpose 2 2 pht) = .ok x
        ∧ x.size = 4
        ∧ x.all Float.isFinite = true
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-37 : Int)) (matrix 2 2 x)
            ((matrix 2 2 s * (matrix 2 2 s).transpose)⁻¹ * matrix 2 2 (transpose 2 2 pht))
        ∧ (∀ i j, |matrix 2 2 (transpose 2 2 x) i j| ≤ 1 / 3) := by
  obtain ⟨hl, pht, _, hhl, _, _, _, hpht, _, hpf, _, q, hm⟩ := formed_rhs h l p
  obtain ⟨y, x, _, hxs, _, hxf, hp, hx, he, _⟩ := FloatCholeskySolveDomain.solve_accuracy
    s (transpose 2 2 pht) sd q sf
  have hinv := Flare.Analysis.NumericalBounds.inverse_entry_bound
    (matrix 2 2 s * (matrix 2 2 s).transpose) (1 / 2) (by norm_num) sf
  have hbt : matrix 2 2 (transpose 2 2 pht) = (matrix 2 2 pht).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 pht hpf
  have htarget := product_magnitude (matrix 2 2 s * (matrix 2 2 s).transpose)⁻¹
    (matrix 2 2 (transpose 2 2 pht)) 2 (1 / 16 + 5 * productRadius 2 8)
    (by simpa using hinv) (by intro i j; rw [hbt]; exact hm j i)
  have hxt : matrix 2 2 (transpose 2 2 x) = (matrix 2 2 x).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 x hxf
  refine ⟨hl, pht, y, x, hhl, hpht, hp, hx, hxs, hxf, he, ?_⟩
  intro i j
  rw [hxt]
  simp only [Matrix.transpose_apply]
  have hmag := abs_sub_le (matrix 2 2 x j i)
    (((matrix 2 2 s * (matrix 2 2 s).transpose)⁻¹ * matrix 2 2 (transpose 2 2 pht)) j i) 0
  simp only [sub_zero] at hmag
  have ht := htarget j i
  have herr := he.2 j i
  norm_num [productRadius] at ht herr
  linarith only [ht, herr, hmag]

/-- Assemble the existing gain profile from a reached innovation profile and
stored model/prior-factor bounds. Every gain-stage execution and solve row
profile is derived here; innovation prearray energy remains its own obligation. -/
theorem gain_profile (input : Input.Model) (prior : Input.FactorState)
    (innovation : InnovationProfile input prior)
    (hn : input.stateDimension = 2) (hm : input.measurementDimension = 2)
    (hqr : innovation.qrBudget = 2)
    (noise
      : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain
          input.measurementNoise)
    (p : TwoStateDomain input.observation prior.lower)
    : ∃ g : GainProfile innovation,
        g.productMass = 8
        ∧ g.solveMass = 32
        ∧ g.solveFloor = 1 / 2
        ∧ g.solveBound = 2
        ∧ g.gainBound = 1
        ∧ (∀ i j,
            |matrix input.stateDimension input.measurementDimension (gainArray g) i j|
            ≤ 1 / 3) := by
  have d : Kalman.Proofs.QRProfiles.GramFactorInputDomain
      2 4 (fromCols 2 2 2 innovation.tr innovation.hl) 2 := by
    simpa only [hn, hm, hqr] using innovation.qr
  have hrun : Kalman.Implementation.OrthogonalFactorization.gramFactor
      2 4 (fromCols 2 2 2 innovation.tr innovation.hl) = .ok innovation.lower := by
    simpa only [hn, hm] using innovation.computeQR
  have hnoise : cholesky 2 input.measurementNoise = .ok innovation.tr := by
    simpa only [hm] using innovation.noise.execution
  have sd := FloatQRFactorDomain.factor_domain_of_qr 4 _ innovation.lower d hrun
  have sf := FloatQRFactorDomain.qr_solve_floor 4 _ innovation.lower d hrun
    (FloatQRFactorDomain.innovation_prearray_lower input.measurementNoise innovation.tr innovation.hl noise hnoise)
  obtain ⟨hl, pht, _, hhl, _, _, pPHT, hpht, _, _, _, _, _⟩ :=
    formed_rhs input.observation prior.lower p
  have hhl' : multiply 2 2 2 input.observation prior.lower = .ok innovation.hl := by
    simpa only [hn, hm] using innovation.computeProduct
  have ehl : hl = innovation.hl := Except.ok.inj (hhl.symm.trans hhl')
  subst hl
  obtain ⟨hl', pht', y, x, hh, hph, hp, _, _, hxf, _, hg⟩ :=
    formed_gain input.observation prior.lower innovation.lower p sd sf
  have ehl : hl' = innovation.hl := Except.ok.inj (hh.symm.trans hhl')
  subst hl'
  have epht : pht' = pht := Except.ok.inj (hph.symm.trans hpht)
  subst pht'
  have hgn : ∀ n m : Nat, n = 2 → m = 2 → ∀ i j : Nat, i < n → j < m →
      |value (entry m (transpose m n x) i j)| ≤ 1 / 3 := by
    intro n m hn hm
    subst n
    subst m
    intro i j hi hj
    exact hg ⟨i, hi⟩ ⟨j, hj⟩
  let g : GainProfile innovation := {
    pht := pht, forward := y, solution := x
    productMass := 8, solveMass := 32, solveFloor := 1 / 2, solveBound := 2, gainBound := 1
    product := by simpa only [hn, hm] using pPHT
    computeProduct := by simpa only [hn, hm] using hpht
    solve := by simpa only [hn, hm] using hp
    finite_solution := hxf
    mass_nonneg := by norm_num
    gain_nonneg := by norm_num
    gain_magnitude := by
      intro i j
      change |value (entry input.measurementDimension
        (transpose input.measurementDimension input.stateDimension x) i.val j.val)| ≤ 1
      exact (hgn _ _ hn hm i.val j.val i.isLt j.isLt).trans (by norm_num : (1 : ℝ) / 3 ≤ 1)
  }
  refine ⟨g, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i j
  change |value (entry input.measurementDimension
    (transpose input.measurementDimension input.stateDimension x) i.val j.val)| ≤ 1 / 3
  exact hgn _ _ hn hm i.val j.val i.isLt j.isLt

/-- A nonzero observation and correlated stored prior factor satisfy this domain. -/
theorem input_domain_nonempty
    : TwoStateDomain #[0.015625, 0.0, 0.0, 0.015625] #[1.0, 0.0, 0.125, 1.0] := by
  have hv : value (0.015625 : Float) = (1 : ℝ) / 64 := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-58 : Int) = _
    norm_num
  have hc : value (0.125 : Float) = (1 : ℝ) / 8 := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-55 : Int) = _
    norm_num
  refine ⟨by decide, by decide, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      norm_num [entry, Flare.Matrix.Dense.entry, hv, Flare.Binary64.Arithmetic.zero_value]
  · intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      norm_num [entry, Flare.Matrix.Dense.entry, hc,
        Flare.Binary64.Arithmetic.zero_value, Flare.Binary64.Arithmetic.one_value]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrix, Flare.Matrix.Value.matrix, entry, Flare.Matrix.Dense.entry,
        Matrix.mul_apply, Fin.sum_univ_two, hc,
        Flare.Binary64.Arithmetic.zero_value, Flare.Binary64.Arithmetic.one_value]

end Kalman.Proofs.FloatGainDomain
