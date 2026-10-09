import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRSourceTail
import Flare.Matrix.JacobiInitialization

/-! Successful native QR and factor Gram accuracy from initial storage,
energy, rank and scale margins alone. Every intermediate operand profile
is derived by induction; no successful final run or validator is assumed. -/

namespace Kalman.Proofs.FloatQRInitialDomain

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Flare.Binary64.Value

/-- Assemble the next complete operand profile from the initial domain and
profiles of preceding pivots. Storage, magnitude and source margin are derived. -/
theorem iterationProfile_of_previous (height width pivot : Nat) (a current : Array Float)
    (M : ℝ) (d : InitialQRDomain height width a M) (hp : pivot < width)
    (profiles
      : ∀ previousPivot,
          previousPivot < pivot
          → ∀ previous,
              qrIterations height width (List.range previousPivot) a = .ok previous
              → IterationProfile height width previousPivot previous M)
    (hrun : qrIterations height width (List.range pivot) a = .ok current)
    : IterationProfile height width pivot current M := by
  have hM : 0 < M := (by positivity : 0 < (2 : ℝ) ^ (-896 : Int)).trans_le d.budget_lower
  obtain ⟨output, houtput, hs, hf, _, _, _⟩ :=
    FloatQRComposition.qrIterations_prefix_accuracy_of_profiles height width pivot a (fun _ => M)
      d.matrix_finite profiles
  have he : output = current := Except.ok.inj (houtput.symm.trans hrun)
  subst output
  have enclosure := FloatQRDomain.qrIterations_prefix_enclosure height width pivot a current
    (fun _ => M) _ _ d.matrix_finite d.gram_bounds profiles hrun
  have magnitude := (FloatQRDomain.prefixEnclosure_budget_eight height width pivot current M
    d.height_le_eight d.width_le_height hp.le hM.le enclosure).1
  refine ⟨
    hp.trans_le d.width_le_height,
    hp,
    (Nat.sub_le height pivot).trans (d.height_le_eight.trans (by decide : 8 ≤ 32)),
    hs.trans d.matrix_size,
    hf,
    (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-900 : Int) ≤ -896)).trans
      d.budget_lower,
    d.budget_upper,
    ?_,
    ?_
  ⟩
  · intro i _ hi j _ hj
    exact magnitude ⟨i, hi⟩ ⟨j, hj⟩
  · exact FloatQRSourceTail.qrIterations_prefix_source_witness_eight height width pivot a current M
      d.height_le_eight d.width_le_height hp d.matrix_finite d.budget_lower d.gram_bounds profiles hrun

/-- All actual-prefix operand profiles follow from initial input conditions.
The strong induction starts with no preceding profile assumptions. -/
theorem triangularizationProfile_eight (height width : Nat) (a : Array Float) (M : ℝ)
    (d : InitialQRDomain height width a M)
    : TriangularizationProfile height width a (fun _ => M) := by
  refine ⟨d.width_le_height, d.matrix_size, d.matrix_finite, ?_⟩
  intro pivot
  induction pivot using Nat.strong_induction_on with
  | h pivot ih =>
      intro hp current hrun
      apply iterationProfile_of_previous height width pivot a current M d hp _ hrun
      intro previousPivot hprev previous hprevRun
      exact ih previousPivot hprev (hprev.trans hp) previous hprevRun

/-- Every prefix succeeds from the initial domain, with its finite storage,
processed zeros, nonzero diagonals and accumulated original-input Gram bound. -/
theorem qrIterations_prefix_accuracy_initial (height width pivots : Nat) (a : Array Float)
    (M : ℝ) (d : InitialQRDomain height width a M) (hp : pivots ≤ width)
    : QRPrefixAccuracy height width pivots a (fun _ => M) :=
  FloatQRComposition.qrIterations_prefix_accuracy height width pivots a (fun _ => M)
    (triangularizationProfile_eight height width a M d) hp

/-- Complete native triangularization succeeds and meets its Gram-error
contract using only the original stored input's domain. -/
theorem triangularize_accuracy_initial (height width : Nat) (a : Array Float) (M : ℝ)
    (d : InitialQRDomain height width a M)
    : TriangularizationGramAccuracy height width a (fun _ => M) :=
  FloatQRComposition.triangularize_gram_accuracy height width a (fun _ => M)
    (triangularizationProfile_eight height width a M d)

/-- Exact finite native transpose converts the original row-prearray domain
to the initial tall QR domain without rounding or prefix assumptions. -/
theorem inputDomain_transpose (rows columns : Nat) (a : Array Float) (M : ℝ)
    (d : GramFactorInputDomain rows columns a M)
    : InitialQRDomain columns rows (transpose rows columns a) M := by
  have ht := Flare.Matrix.Multiplication.transpose_storage rows columns a d.matrix_finite
  have hm := Flare.Matrix.Multiplication.transpose_matrix rows columns a d.matrix_finite
  refine ⟨d.rows_le_columns, d.columns_le_eight, ?_, ht.2.1, d.budget_lower, d.budget_upper, ?_⟩
  · simpa only [Nat.mul_comm] using ht.1
  · refine ⟨?_, ?_⟩
    · simpa only [hm, Matrix.transpose_apply] using d.row_energy
    · simpa only [hm, Matrix.transpose_transpose, Kalman.Definitions.FactorRecursion.gram] using d.gram_lower

/-- The complete factor contract follows from original prearray conditions.
Success, positive diagonal, strict-PD exact Gram and error are conclusions. -/
theorem gramFactor_accuracy_initial (rows columns : Nat) (a : Array Float) (M : ℝ)
    (d : GramFactorInputDomain rows columns a M)
    : GramFactorAccuracy rows columns a (fun _ => M) :=
  FloatQRComposition.gramFactor_accuracy rows columns a (fun _ => M) d.matrix_size
    d.matrix_finite
    (triangularizationProfile_eight columns rows (transpose rows columns a) M
      (inputDomain_transpose rows columns a M d))

/-- Original input alone guarantees successful finite native factorization,
a retained Gram floor M²/16, and absolute Gram error at most M²/128.
The sharper accumulated allowance remains available in the same conclusion. -/
theorem gramFactor_initial_accuracy (rows columns : Nat) (a : Array Float) (M : ℝ)
    (d : GramFactorInputDomain rows columns a M)
    : InitialGramFactorAccuracy rows columns a M := by
  obtain ⟨hs, hf, l, hrun, hls, hlf, hlp, hpd, herr⟩ := gramFactor_accuracy_initial rows columns a M d
  have hM : 0 ≤ M := (by positivity : 0 < (2 : ℝ) ^ (-896 : Int)).le.trans d.budget_lower
  have hn : rows ≤ 8 := d.rows_le_columns.trans d.columns_le_eight
  have hcap := FloatQRDomain.qrGramRadius_le_eight columns rows M d.columns_le_eight hn hM
  have hG : qrGramRadius columns rows (fun _ => M) ≤ M ^ 2 / 128 := by
    norm_num at hcap
    linarith
  have hfloor := ErrorPropagation.lower_bound_of_error _ _ (M ^ 2 / 8)
    (qrGramRadius columns rows (fun _ => M)) d.gram_lower hpd.isHermitian herr
  have hrows : (rows : ℝ) ≤ 8 := by exact_mod_cast hn
  have hδ := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg rows)
  have hδcap := mul_le_mul_of_nonneg_right hrows (by positivity : 0 ≤ M ^ 2 / 128)
  have hpad : 0 ≤ M ^ 2 / 8 - rows * qrGramRadius columns rows (fun _ => M) - M ^ 2 / 16 := by
    linarith
  have hpsd := hfloor.add ((Matrix.PosSemidef.one (n := Fin rows) (R := ℝ)).smul hpad)
  refine ⟨hs, hf, l, hrun, hls, hlf, hlp, hpd, ?_, herr, ?_⟩
  · convert hpsd using 1
    simp only [sub_smul]
    module
  · exact ⟨by positivity, fun i j => (herr.2 i j).trans hG⟩

/-- On the same original-input domain, the explicit error also meets an
8192-times smaller cap. Success, storage and the spectral floor are preserved. -/
theorem gramFactor_initial_tight_accuracy (rows columns : Nat) (a : Array Float) (M : ℝ)
    (d : GramFactorInputDomain rows columns a M)
    : ∃ l,
        gramFactor rows columns a = .ok l
        ∧ l.size = rows * rows
        ∧ l.all Float.isFinite = true
        ∧ Kalman.Definitions.FactorRecursion.LowerPositive (matrix rows rows l)
        ∧ (Kalman.Definitions.FactorRecursion.gram (matrix rows rows l)).PosDef
        ∧ (Kalman.Definitions.FactorRecursion.gram (matrix rows rows l)
            - (M ^ 2 / 16) • 1).PosSemidef
        ∧ EntrywiseWithin (M ^ 2 / 1048576)
            (Kalman.Definitions.FactorRecursion.gram (matrix rows rows l))
            (matrix rows columns a * (matrix rows columns a).transpose) := by
  obtain ⟨_, _, l, hrun, hs, hf, hl, hp, hfloor, he, _⟩ := gramFactor_initial_accuracy rows columns a M d
  have hM : 0 ≤ M := (by positivity : 0 < (2 : ℝ) ^ (-896 : Int)).le.trans d.budget_lower
  have hcap := FloatQRDomain.qrGramRadius_le_eight_tight columns rows M d.columns_le_eight
    (d.rows_le_columns.trans d.columns_le_eight) hM
  have hG : qrGramRadius columns rows (fun _ => M) ≤ M ^ 2 / 1048576 := by
    norm_num at hcap
    linarith
  exact ⟨l, hrun, hs, hf, hl, hp, hfloor, ⟨by positivity, fun i j => (he.2 i j).trans hG⟩⟩

/-- On the same original-input domain, the explicit error also meets an
262144-times smaller cap than the original M²/128 bound. Success, storage and the spectral floor are preserved. -/
theorem gramFactor_initial_refined_accuracy (rows columns : Nat) (a : Array Float) (M : ℝ)
    (d : GramFactorInputDomain rows columns a M)
    : ∃ l,
        gramFactor rows columns a = .ok l
        ∧ l.size = rows * rows
        ∧ l.all Float.isFinite = true
        ∧ Kalman.Definitions.FactorRecursion.LowerPositive (matrix rows rows l)
        ∧ (Kalman.Definitions.FactorRecursion.gram (matrix rows rows l)).PosDef
        ∧ (Kalman.Definitions.FactorRecursion.gram (matrix rows rows l)
            - (M ^ 2 / 16) • 1).PosSemidef
        ∧ EntrywiseWithin (M ^ 2 / 33554432)
            (Kalman.Definitions.FactorRecursion.gram (matrix rows rows l))
            (matrix rows columns a * (matrix rows columns a).transpose) := by
  obtain ⟨_, _, l, hrun, hs, hf, hl, hp, hfloor, he, _⟩ := gramFactor_initial_accuracy rows columns a M d
  have hM : 0 ≤ M := (by positivity : 0 < (2 : ℝ) ^ (-896 : Int)).le.trans d.budget_lower
  have hcap := FloatQRDomain.qrGramRadius_le_eight_refined columns rows M d.columns_le_eight
    (d.rows_le_columns.trans d.columns_le_eight) hM
  have hG : qrGramRadius columns rows (fun _ => M) ≤ M ^ 2 / 33554432 := by
    norm_num at hcap
    linarith
  exact ⟨l, hrun, hs, hf, hl, hp, hfloor, ⟨by positivity, fun i j => (he.2 i j).trans hG⟩⟩

/-- A kernel-backed nonvacuity family: every stored native identity through
dimension eight satisfies the original-input domain with budget two. -/
theorem identity_input_domain (n : Nat) (hn : n ≤ 8)
    : GramFactorInputDomain n n (identity n) 2 := by
  refine ⟨le_rfl, hn, Flare.Matrix.JacobiInitialization.identity_size n,
    Flare.Matrix.JacobiInitialization.identity_finite n, ?_, ?_, ?_, ?_⟩
  · simpa using (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (-896 : Int) ≤ 1))
  · simpa using (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : Int) ≤ 900))
  · intro i
    have hm : matrix n n (identity n) = (1 : Matrix (Fin n) (Fin n) ℝ) :=
      Flare.Matrix.JacobiInitialization.identity_matrix n
    simp_rw [hm]
    norm_num [Matrix.one_apply]
  · have hg : Kalman.Definitions.FactorRecursion.gram (matrix n n (identity n)) = 1 := by
      simp [Kalman.Definitions.FactorRecursion.gram, Flare.Matrix.JacobiInitialization.identity_matrix]
    rw [hg]
    convert (Matrix.PosSemidef.one (n := Fin n) (R := ℝ)).smul (by norm_num : 0 ≤ (1 : ℝ) / 2) using 1
    norm_num
    module

end Kalman.Proofs.FloatQRInitialDomain
