import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRInitialDomain
import Kalman.Proofs.FloatCholeskySolveDomain
import Kalman.Proofs.FloatPrearray

/-! Two-state native QR output satisfies the stored-factor solve domain.
An additional prearray floor supplies solve conditioning; a Cholesky noise
block derives that floor independently of the other innovation block. -/

namespace Kalman.Proofs.FloatQRFactorDomain

open Matrix
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.CholeskyProfiles.SolveDomain
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-- A spectral floor for a two-state lower-positive Gram bounds both diagonal
entries of its factor, including the second pivot after correlation. -/
theorem lowerPositive_diagonal_floor (l : Matrix (Fin 2) (Fin 2) ℝ)
    (hp : FactorRecursion.LowerPositive l)
    (hf : (FactorRecursion.gram l - (1 / 4 : ℝ) • 1).PosSemidef)
    : ∀ i, (1 : ℝ) / 2 ≤ l i i := by
  have hz : l 0 1 = 0 := hp.1 0 1 (by decide)
  have hd := hf.diag_nonneg (i := 0)
  simp [FactorRecursion.gram, Matrix.mul_apply, Fin.sum_univ_two, hz] at hd
  have h0 : (1 : ℝ) / 2 ≤ l 0 0 := by nlinarith [hp.2 0]
  have hq := hf.dotProduct_mulVec_nonneg ![-l 1 0 / l 0 0, 1]
  simp [star_trivial, dotProduct, Matrix.mulVec, FactorRecursion.gram,
    Matrix.mul_apply, Fin.sum_univ_two, hz] at hq
  have he : (-l 1 0 / l 0 0) * l 0 0 + l 1 0 = 0 := by
    field_simp
    ring
  have hcancel : (-l 1 0 / l 0 0) ^ 2 * (l 0 0)^2
      + 2 * (-l 1 0 / l 0 0) * l 0 0 * l 1 0 + (l 1 0)^2 = 0 := by
    nlinarith [sq_nonneg ((-l 1 0 / l 0 0) * l 0 0 + l 1 0)]
  have h1 : (1 : ℝ) / 2 ≤ l 1 1 := by
    nlinarith [hp.2 1, sq_nonneg (-l 1 0 / l 0 0)]
  intro i
  fin_cases i <;> assumption

/-- The original prearray domain with budget two derives every stored factor
condition required by the two-state solve. Successful execution identifies
the output; success itself follows from that same input domain. -/
theorem factor_domain_of_qr (columns : Nat) (a l : Array Float)
    (d : GramFactorInputDomain 2 columns a 2)
    (hrun : gramFactor 2 columns a = .ok l)
    : FactorDomain l := by
  obtain ⟨l', hr, hs, hf, hp, _, hfloor, he⟩ :=
    FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 columns a 2 d
  have heq : l' = l := Except.ok.inj (hr.symm.trans hrun)
  subst l'
  have hdiag := lowerPositive_diagonal_floor (matrix 2 2 l) hp (by norm_num at hfloor ⊢; exact hfloor)
  have hm : ∀ i j, |matrix 2 2 l i j| ≤ 2 := by
    intro i j
    have hsq := FloatQRDomain.columnGram_entry_sq_le (matrix 2 2 l).transpose j i
    simp only [Matrix.transpose_apply, Matrix.transpose_transpose] at hsq
    have henergy : FactorRecursion.gram (matrix 2 columns a) i i ≤ 2 := by
      simpa [FactorRecursion.gram, Matrix.mul_apply, pow_two] using d.row_energy i
    have herr := (abs_le.mp (he.2 i i)).2
    change FactorRecursion.gram (matrix 2 2 l) i i
      - FactorRecursion.gram (matrix 2 columns a) i i ≤ _ at herr
    change (matrix 2 2 l i j)^2 ≤ FactorRecursion.gram (matrix 2 2 l) i i at hsq
    norm_num at herr
    nlinarith [sq_abs (matrix 2 2 l i j), abs_nonneg (matrix 2 2 l i j)]
  refine ⟨by simpa using hs, hf, hp.1 0 1 (by decide), ?_, ?_⟩
  · intro i hi
    exact hdiag ⟨i, hi⟩
  · intro i j hi hj
    exact hm ⟨i, hi⟩ ⟨j, hj⟩

/-- Additional original prearray rank headroom derives the stronger innovation
conditioning floor; the generic QR output floor alone is only one quarter. -/
theorem qr_solve_floor (columns : Nat) (a l : Array Float)
    (d : GramFactorInputDomain 2 columns a 2)
    (hrun : gramFactor 2 columns a = .ok l)
    (hfloor : (FactorRecursion.gram (matrix 2 columns a) - (2 / 3 : ℝ) • 1).PosSemidef)
    : (FactorRecursion.gram (matrix 2 2 l) - (1 / 2 : ℝ) • 1).PosSemidef := by
  obtain ⟨l', hr, _, _, _, hp, _, he⟩ :=
    FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 columns a 2 d
  have heq : l' = l := Except.ok.inj (hr.symm.trans hrun)
  subst l'
  have hb := ErrorPropagation.lower_bound_of_error _ _ (2 / 3)
    ((2 : ℝ)^2 / 33554432) hfloor hp.isHermitian he
  have hpad : 0 ≤ (2 / 3 : ℝ) - 2 * (2^2 / 33554432) - 1 / 2 := by norm_num
  convert hb.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad) using 1
  norm_num
  module

/-- Noise factorization supplies sufficient innovation prearray headroom.
The other stored block contributes an exact PSD Gram at any finite magnitude;
the separate QR input domain still controls energy, shape and finiteness. -/
theorem innovation_prearray_lower (a tr hl : Array Float)
    (p : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain a)
    (hrun : cholesky 2 a = .ok tr)
    : (FactorRecursion.gram (matrix 2 4 (fromCols 2 2 2 tr hl))
        - (2 / 3 : ℝ) • 1).PosSemidef := by
  obtain ⟨tr', _, hr, _, _, _, hp, _, he⟩ := FloatCholeskyDomain.cholesky_accuracy a p
  have heq : tr' = tr := Except.ok.inj (hr.symm.trans hrun)
  subst tr'
  have hb := ErrorPropagation.lower_bound_of_error _ _ (3 / 4)
    ((2 : ℝ)^(-42 : Int)) (FloatCholeskyDomain.input_lower_bound a p) hp.isHermitian he
  have hpad : 0 ≤ (3 / 4 : ℝ) - 2 * (2 : ℝ)^(-42 : Int) - 2 / 3 := by norm_num
  have ht := hb.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad)
  have hh := CovarianceStructure.gram_posSemidef (matrix 2 2 hl)
  rw [FloatPrearray.fromCols_gram 2 2 2 tr hl]
  convert ht.add hh using 1
  simp only [FactorRecursion.gram, Nat.cast_ofNat, sub_smul]
  module

/-- QR followed by both native substitutions succeeds from the prearray and
RHS domains, with no intermediate solve profile supplied by the caller.
The accuracy reference here is the returned factor's exact Gram. -/
theorem qr_factor_and_solve_accuracy (columns : Nat) (a b : Array Float)
    (d : GramFactorInputDomain 2 columns a 2) (q : RightHandSideDomain b)
    (hfloor : (FactorRecursion.gram (matrix 2 columns a) - (2 / 3 : ℝ) • 1).PosSemidef)
    : ∃ l y x,
        gramFactor 2 columns a = .ok l
        ∧ FactorDomain l
        ∧ (FactorRecursion.gram (matrix 2 2 l) - (1 / 2 : ℝ) • 1).PosSemidef
        ∧ y.size = 4
        ∧ x.size = 4
        ∧ y.all Float.isFinite = true
        ∧ x.all Float.isFinite = true
        ∧ Kalman.Proofs.CholeskyProfiles.SolveProfile 2 2 l b y x 32 (1 / 2) 2
        ∧ solveCholesky 2 2 l b = .ok x
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-37 : Int)) (matrix 2 2 x)
            ((FactorRecursion.gram (matrix 2 2 l))⁻¹ * matrix 2 2 b)
        ∧ (∀ i j, |matrix 2 2 x i j| ≤ 1) := by
  obtain ⟨l, hr, _, _, _, _, _, _⟩ :=
    FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 columns a 2 d
  have hd := factor_domain_of_qr columns a l d hr
  have hf := qr_solve_floor columns a l d hr hfloor
  obtain ⟨y, x, hys, hxs, hyf, hxf, hp, hx, he, hm⟩ :=
    FloatCholeskySolveDomain.solve_accuracy l b hd q hf
  exact ⟨l, y, x, hr, hd, hf, hys, hxs, hyf, hxf, hp, hx, he, hm⟩

/-- For an innovation assembled from a Cholesky noise factor and a stored
observation block, the noise domain derives the extra spectral floor.
The formed prearray energy domain and formed RHS domain remain explicit. -/
theorem innovation_factor_and_solve_accuracy (a tr hl b : Array Float)
    (p : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain a)
    (hrun : cholesky 2 a = .ok tr)
    (d : GramFactorInputDomain 2 4 (fromCols 2 2 2 tr hl) 2)
    (q : RightHandSideDomain b)
    : ∃ l y x,
        gramFactor 2 4 (fromCols 2 2 2 tr hl) = .ok l
        ∧ FactorDomain l
        ∧ (FactorRecursion.gram (matrix 2 2 l) - (1 / 2 : ℝ) • 1).PosSemidef
        ∧ y.size = 4
        ∧ x.size = 4
        ∧ y.all Float.isFinite = true
        ∧ x.all Float.isFinite = true
        ∧ Kalman.Proofs.CholeskyProfiles.SolveProfile 2 2 l b y x 32 (1 / 2) 2
        ∧ solveCholesky 2 2 l b = .ok x
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-37 : Int)) (matrix 2 2 x)
            ((FactorRecursion.gram (matrix 2 2 l))⁻¹ * matrix 2 2 b)
        ∧ (∀ i j, |matrix 2 2 x i j| ≤ 1) :=
  qr_factor_and_solve_accuracy 4 _ b d q (innovation_prearray_lower a tr hl p hrun)

/-- A convenience cap including the QR Gram perturbation and both solve passes. -/
theorem original_qr_solve_radius_cap
    : 2
        * ((1 + 2 * 2) * Kalman.Proofs.CholeskyProfiles.divisionRadius 2 32 (1 / 2) 2
            + 2 * ((2 : ℝ) ^ 2 / 33554432))
        / (2 / 3)
      ≤ (2 : ℝ) ^ (-20 : Int) := by
  have h := FloatCholeskySolveDomain.division_radius_cap
  norm_num at h ⊢
  linarith only [h]

/-- QR and solve accuracy against the original stored prearray's exact Gram.
The QR perturbation is included, rather than treating its returned factor as
an exact factorization of that input. -/
theorem qr_original_factor_and_solve_accuracy (columns : Nat) (a b : Array Float)
    (d : GramFactorInputDomain 2 columns a 2) (q : RightHandSideDomain b)
    (hfloor : (FactorRecursion.gram (matrix 2 columns a) - (2 / 3 : ℝ) • 1).PosSemidef)
    : ∃ l x,
        gramFactor 2 columns a = .ok l
        ∧ solveCholesky 2 2 l b = .ok x
        ∧ x.size = 4
        ∧ x.all Float.isFinite = true
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-20 : Int)) (matrix 2 2 x)
            ((FactorRecursion.gram (matrix 2 columns a))⁻¹ * matrix 2 2 b)
        ∧ (∀ i j, |matrix 2 2 x i j| ≤ 1) := by
  obtain ⟨l, y, x, hl, _, _, _, hxs, _, hxf, hp, hx, _, hm⟩ :=
    qr_factor_and_solve_accuracy columns a b d q hfloor
  obtain ⟨l', hr, _, _, _, _, _, he⟩ :=
    FloatQRInitialDomain.gramFactor_initial_refined_accuracy 2 columns a 2 d
  have heq : l' = l := Except.ok.inj (hr.symm.trans hl)
  subst l'
  obtain ⟨_, _, hres⟩ := FloatCholeskySolve.solve_residual 2 2 l b y x 32 (1 / 2) 2 hp (by norm_num)
  have hperturb := ErrorPropagation.within_mul_right (ErrorPropagation.within_sym he)
    (matrix 2 2 x) (by norm_num : (0 : ℝ) ≤ 1) hm
  let g := FactorRecursion.gram (matrix 2 columns a)
  let ρ := (1 + 2 * 2) * Kalman.Proofs.CholeskyProfiles.divisionRadius
    2 32 (1 / 2) 2 + 2 * ((2 : ℝ)^2 / 33554432)
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    have hd := FloatResidualError.divisionRadius_nonneg 2 32 (1 / 2) 2
      (by norm_num) (by norm_num) (by norm_num)
    positivity
  have href : ∀ i j, |(g * matrix 2 2 x - matrix 2 2 b) i j| ≤ ρ := by
    intro i j
    have ht := abs_sub_le ((g * matrix 2 2 x) i j)
      ((FactorRecursion.gram (matrix 2 2 l) * matrix 2 2 x) i j) (matrix 2 2 b i j)
    have hg := hres i j
    have hd := hperturb.2 i j
    change |(FactorRecursion.gram (matrix 2 2 l) * matrix 2 2 x) i j - matrix 2 2 b i j| ≤ _ at hg
    change |(g * matrix 2 2 x) i j - matrix 2 2 b i j| ≤ _
    dsimp [ρ]
    simpa only [g, FactorRecursion.gram, Nat.cast_ofNat, mul_one, add_comm]
      using ht.trans (add_le_add hd hg)
  have hpd := Flare.Analysis.NumericalBounds.posDef_of_lower_bound g (2 / 3) (by norm_num) hfloor
  have hid : g * g⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hpd.isUnit)
  refine ⟨l, x, hl, hx, hxs, hxf, ⟨by positivity, ?_⟩, hm⟩
  intro i j
  have hexact : g.mulVec (fun k => (g⁻¹ * matrix 2 2 b) k j) = fun k => matrix 2 2 b k j := by
    have hex : g * (g⁻¹ * matrix 2 2 b) = matrix 2 2 b := by
      rw [← Matrix.mul_assoc, hid, Matrix.one_mul]
    ext k
    exact congr_fun (congr_fun hex k) j
  have herr := Flare.Analysis.NumericalBounds.residual_entrywise_bound g (2 / 3) ρ
    (by norm_num) hρ hfloor (fun k => matrix 2 2 x k j)
    (fun k => (g⁻¹ * matrix 2 2 b) k j) (fun k => matrix 2 2 b k j) hexact (fun k => href k j) i
  exact herr.trans original_qr_solve_radius_cap

end Kalman.Proofs.FloatQRFactorDomain
