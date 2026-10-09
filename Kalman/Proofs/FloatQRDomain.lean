import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRComposition

/-! Derive intermediate magnitude and spectral bounds from initial Gram bounds
and the proved errors of preceding native QR iterations. FloatQRSourceTail
derives the quantitative active-source witness. FloatQRInitialDomain closes
the complete initial-input success induction on the supported eight-row domain. -/

namespace Kalman.Proofs.FloatQRDomain

open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity

/-- A stored entry's square is bounded by its exact column energy. -/
theorem columnGram_entry_sq_le {height width : Nat}
    (a : Matrix (Fin height) (Fin width) ℝ) (i : Fin height) (j : Fin width)
    : (a i j) ^ 2 ≤ (a.transpose * a) j j := by
  have h : (a i j) ^ 2 ≤ ∑ k, (a k j) ^ 2 := Finset.single_le_sum
    (fun k _ => sq_nonneg (a k j)) (Finset.mem_univ i)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h

/-- Diagonal Gram error controls every current entry, without an orthogonal
action or an entrywise error bound on the matrices themselves. -/
theorem columnGram_entry_sq_bound {height width : Nat}
    (original current : Matrix (Fin height) (Fin width) ℝ) (S ε : ℝ)
    (hs : ∀ j, ∑ i, (original i j) ^ 2 ≤ S)
    (he : EntrywiseWithin ε (current.transpose * current) (original.transpose * original))
    : ∀ i j, (current i j) ^ 2 ≤ S + ε := by
  intro i j
  have hd : (original.transpose * original) j j ≤ S := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hs j
  have herr := (abs_le.mp (he.2 j j)).2
  exact (columnGram_entry_sq_le current i j).trans (by linarith)

/-- Initial column energy and spectral margin propagate to any actual prefix.
Only the operand profiles of preceding pivots are required, so this can be
used while establishing the next pivot's profile by induction. -/
theorem qrIterations_prefix_enclosure (height width pivots : Nat)
    (a current : Array Float) (budget : Nat → ℝ) (S α : ℝ)
    (hf : a.all Float.isFinite = true) (initial : InitialGramBounds height width a S α)
    (profiles
      : ∀ pivot,
          pivot < pivots
          → ∀ previous,
              qrIterations height width (List.range pivot) a = .ok previous
              → IterationProfile height width pivot previous (budget pivot))
    (hrun : qrIterations height width (List.range pivots) a = .ok current)
    : PrefixEnclosure height width pivots current budget S α := by
  obtain ⟨output, houtput, _, _, _, _, he⟩ :=
    FloatQRComposition.qrIterations_prefix_accuracy_of_profiles height width pivots a budget hf profiles
  have hsame : output = current := Except.ok.inj (houtput.symm.trans hrun)
  subst output
  refine ⟨columnGram_entry_sq_bound _ _ _ _ initial.column_energy he, ?_⟩
  have hsym : ((matrix height width current).transpose * matrix height width current).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
      using Matrix.isHermitian_conjTranspose_mul_self (matrix height width current)
  exact ErrorPropagation.lower_bound_of_error _ _ _ _ initial.gram_lower hsym he

/-- The derived enclosure discharges all panel magnitude conditions when the
initial column energy plus accumulated Gram allowance fits the chosen budget. -/
theorem prefixEnclosure_magnitude (height width pivots : Nat) (current : Array Float)
    (budget : Nat → ℝ) (S α M : ℝ)
    (h : PrefixEnclosure height width pivots current budget S α)
    (hM : 0 ≤ M) (hroom : S + qrGramRadius height pivots budget ≤ M ^ 2)
    : ∀ i j, |matrix height width current i j| ≤ M := by
  intro i j
  have hs := (h.1 i j).trans hroom
  nlinarith [sq_abs (matrix height width current i j), abs_nonneg (matrix height width current i j)]

/-- The magnitude consequence in the exact Nat-indexed form required by
`IterationProfile.panel_magnitude` for the next pivot. -/
theorem prefixEnclosure_panel_magnitude (height width pivots : Nat)
    (current : Array Float) (budget : Nat → ℝ) (S α M : ℝ)
    (h : PrefixEnclosure height width pivots current budget S α) (hM : 0 ≤ M)
    (hroom : S + qrGramRadius height pivots budget ≤ M ^ 2)
    : ∀ i,
        pivots ≤ i
        → i < height
        → ∀ j,
            pivots ≤ j
            → j < width
            → |Flare.Binary64.Value.value
                (Kalman.Implementation.LinearAlgebra.entry width current i j)|
              ≤ M := by
  intro i _ hi j _ hj
  exact prefixEnclosure_magnitude height width pivots current budget S α M h hM hroom ⟨i, hi⟩ ⟨j, hj⟩

/-- A positive remaining spectral margin certifies full column rank at this
prefix through strict PD of its exact column Gram. It does not yet supply the
quantitative active-tail witness required by the next native iteration. -/
theorem prefixEnclosure_posDef (height width pivots : Nat) (current : Array Float)
    (budget : Nat → ℝ) (S α : ℝ)
    (h : PrefixEnclosure height width pivots current budget S α)
    (hmargin : width * qrGramRadius height pivots budget < α)
    : ((matrix height width current).transpose * matrix height width current).PosDef := by
  exact Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ _ (sub_pos.mpr hmargin) h.2

/-- A dimension-specific cap sufficient for the first small-matrix domain.
The exact public radius remains sharper than this convenience bound. -/
theorem iterationGramRadius_le_eight {terms : Nat} (M : ℝ) (hk : terms ≤ 8) (hM : 0 ≤ M)
    : iterationGramRadius terms M ≤ (2 : ℝ) ^ (-10 : Int) * M ^ 2 := by
  have hn : (terms : ℝ) ≤ 8 := by exact_mod_cast hk
  have hE : iterationRadius terms M ≤ (2 : ℝ) ^ (-19 : Int) * M := by
    apply (FloatQRIteration.iterationRadius_mono hk M hM).trans
    unfold iterationRadius
    apply (add_le_add (max_le (show sourceWriteRadius 8 M ≤ (2 : ℝ)^(-33 : Int) * M by
      norm_num [sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius]
      nlinarith) (by norm_num [applicationRadius]; nlinarith)) le_rfl).trans
    norm_num [reflectorRadius]
    nlinarith
  have hE0 : 0 ≤ iterationRadius terms M := by
    unfold iterationRadius sourceWriteRadius sourceResidualRadius columnNormRadius squareSumRadius reflectorRadius
    positivity
  have hB : 2 * (1 + 2 * (terms : ℝ)) * M ≤ 34 * M :=
    mul_le_mul_of_nonneg_right (by linarith) hM
  have hp := mul_le_mul hB hE hE0 (by positivity : (0 : ℝ) ≤ 34 * M)
  have hs := mul_le_mul hE hE hE0 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-19 : Int) * M)
  unfold iterationGramRadius
  calc
    _ ≤ terms
        * (34 * M * ((2 : ℝ) ^ (-19 : Int) * M)
            + ((2 : ℝ) ^ (-19 : Int) * M) * ((2 : ℝ) ^ (-19 : Int) * M)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg terms)
      simpa only [pow_two] using add_le_add hp hs
    _ ≤ 8
        * (34 * M * ((2 : ℝ) ^ (-19 : Int) * M)
            + ((2 : ℝ) ^ (-19 : Int) * M) * ((2 : ℝ) ^ (-19 : Int) * M)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ _ := by norm_num; nlinarith [sq_nonneg M]

/-- At most eight rows and eight preceding pivots, with a constant budget,
consume at most `M² / 128` of the entrywise Gram allowance. -/
theorem qrGramRadius_le_eight (height pivots : Nat) (M : ℝ)
    (hh : height ≤ 8) (hp : pivots ≤ 8) (hM : 0 ≤ M)
    : qrGramRadius height pivots (fun _ => M) ≤ (2 : ℝ) ^ (-7 : Int) * M ^ 2 := by
  have hn : (pivots : ℝ) ≤ 8 := by exact_mod_cast hp
  calc
    _ ≤ ∑ _pivot ∈ Finset.range pivots, (2 : ℝ) ^ (-10 : Int) * M ^ 2 := by
      apply Finset.sum_le_sum
      intro pivot _
      exact iterationGramRadius_le_eight M (by omega) hM
    _ = pivots * ((2 : ℝ) ^ (-10 : Int) * M ^ 2) := by simp
    _ ≤ 8 * ((2 : ℝ) ^ (-10 : Int) * M ^ 2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by norm_num; ring

/-- Tighter eight-row caps using the revised native QR estimates. -/
theorem iterationGramRadius_le_eight_tight {terms : Nat} (M : ℝ) (hk : terms ≤ 8)
    (hM : 0 ≤ M)
    : iterationGramRadius terms M ≤ (2 : ℝ) ^ (-23 : Int) * M ^ 2 := by
  have hn : (terms : ℝ) ≤ 8 := by exact_mod_cast hk
  have hE : iterationRadius terms M ≤ (2 : ℝ) ^ (-32 : Int) * M := by
    apply (FloatQRIteration.iterationRadius_mono hk M hM).trans
    unfold iterationRadius
    apply (add_le_add (max_le (show sourceWriteRadius 8 M ≤ (2 : ℝ)^(-33 : Int) * M by
      norm_num [sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius]
      nlinarith) (by norm_num [applicationRadius]; nlinarith)) le_rfl).trans
    norm_num [reflectorRadius]
    nlinarith
  have hE0 : 0 ≤ iterationRadius terms M := by
    unfold iterationRadius sourceWriteRadius sourceResidualRadius columnNormRadius squareSumRadius reflectorRadius
    positivity
  have hB : 2 * (1 + 2 * (terms : ℝ)) * M ≤ 34 * M :=
    mul_le_mul_of_nonneg_right (by linarith) hM
  have hp := mul_le_mul hB hE hE0 (by positivity : (0 : ℝ) ≤ 34 * M)
  have hs := mul_le_mul hE hE hE0 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-32 : Int) * M)
  unfold iterationGramRadius
  calc
    _ ≤ terms
        * (34 * M * ((2 : ℝ) ^ (-32 : Int) * M)
            + ((2 : ℝ) ^ (-32 : Int) * M) * ((2 : ℝ) ^ (-32 : Int) * M)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg terms)
      simpa only [pow_two] using add_le_add hp hs
    _ ≤ 8
        * (34 * M * ((2 : ℝ) ^ (-32 : Int) * M)
            + ((2 : ℝ) ^ (-32 : Int) * M) * ((2 : ℝ) ^ (-32 : Int) * M)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ _ := by norm_num; nlinarith [sq_nonneg M]

/-- At most eight rows and eight preceding pivots, with a constant budget,
consume at most `M² / 1048576` of the entrywise Gram allowance. -/
theorem qrGramRadius_le_eight_tight (height pivots : Nat) (M : ℝ)
    (hh : height ≤ 8) (hp : pivots ≤ 8) (hM : 0 ≤ M)
    : qrGramRadius height pivots (fun _ => M) ≤ (2 : ℝ) ^ (-20 : Int) * M ^ 2 := by
  have hn : (pivots : ℝ) ≤ 8 := by exact_mod_cast hp
  calc
    _ ≤ ∑ _pivot ∈ Finset.range pivots, (2 : ℝ) ^ (-23 : Int) * M ^ 2 := by
      apply Finset.sum_le_sum
      intro pivot _
      exact iterationGramRadius_le_eight_tight M (by omega) hM
    _ = pivots * ((2 : ℝ) ^ (-23 : Int) * M ^ 2) := by simp
    _ ≤ 8 * ((2 : ℝ) ^ (-23 : Int) * M ^ 2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by norm_num; ring

/-- Dimension-sensitive eight-row caps using the refined native QR estimates. -/
theorem iterationGramRadius_le_eight_refined {terms : Nat} (M : ℝ) (hk : terms ≤ 8)
    (hM : 0 ≤ M)
    : iterationGramRadius terms M ≤ (2 : ℝ) ^ (-28 : Int) * M ^ 2 := by
  have hn : (terms : ℝ) ≤ 8 := by exact_mod_cast hk
  have hE : iterationRadius terms M ≤ (2 : ℝ) ^ (-37 : Int) * M := by
    apply (FloatQRIteration.iterationRadius_mono hk M hM).trans
    unfold iterationRadius
    rw [← le_sub_iff_add_le]
    apply max_le <;>
      norm_num [sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius,
        reflectorRadius, applicationRadius] <;> nlinarith
  have hE0 : 0 ≤ iterationRadius terms M := by
    unfold iterationRadius sourceWriteRadius sourceResidualRadius columnNormRadius squareSumRadius reflectorRadius
    positivity
  have hB : 2 * (1 + 2 * (terms : ℝ)) * M ≤ 34 * M :=
    mul_le_mul_of_nonneg_right (by linarith) hM
  have hp := mul_le_mul hB hE hE0 (by positivity : (0 : ℝ) ≤ 34 * M)
  have hs := mul_le_mul hE hE hE0 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-37 : Int) * M)
  unfold iterationGramRadius
  calc
    _ ≤ terms
        * (34 * M * ((2 : ℝ) ^ (-37 : Int) * M)
            + ((2 : ℝ) ^ (-37 : Int) * M) * ((2 : ℝ) ^ (-37 : Int) * M)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg terms)
      simpa only [pow_two] using add_le_add hp hs
    _ ≤ 8
        * (34 * M * ((2 : ℝ) ^ (-37 : Int) * M)
            + ((2 : ℝ) ^ (-37 : Int) * M) * ((2 : ℝ) ^ (-37 : Int) * M)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ _ := by norm_num; nlinarith [sq_nonneg M]

/-- At most eight rows and eight preceding pivots, with a constant budget,
consume at most `M² / 33554432` of the entrywise Gram allowance. -/
theorem qrGramRadius_le_eight_refined (height pivots : Nat) (M : ℝ)
    (hh : height ≤ 8) (hp : pivots ≤ 8) (hM : 0 ≤ M)
    : qrGramRadius height pivots (fun _ => M) ≤ (2 : ℝ) ^ (-25 : Int) * M ^ 2 := by
  have hn : (pivots : ℝ) ≤ 8 := by exact_mod_cast hp
  calc
    _ ≤ ∑ _pivot ∈ Finset.range pivots, (2 : ℝ) ^ (-28 : Int) * M ^ 2 := by
      apply Finset.sum_le_sum
      intro pivot _
      exact iterationGramRadius_le_eight_refined M (by omega) hM
    _ = pivots * ((2 : ℝ) ^ (-28 : Int) * M ^ 2) := by simp
    _ ≤ 8 * ((2 : ℝ) ^ (-28 : Int) * M ^ 2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by norm_num; ring

/-- Concrete headroom for up to eight rows: initial column energy `M² / 2`
and Gram floor `M² / 8` preserve entry magnitude `M` and Gram floor `M² / 16`.
The enclosure still comes from proved preceding profiles; this is not yet
an initial-input theorem guaranteeing all later source witnesses. -/
theorem prefixEnclosure_budget_eight (height width pivots : Nat) (current : Array Float)
    (M : ℝ) (hh : height ≤ 8) (hw : width ≤ height) (hp : pivots ≤ width) (hM : 0 ≤ M)
    (h : PrefixEnclosure height width pivots current (fun _ => M) (M ^ 2 / 2) (M ^ 2 / 8))
    : (∀ i j, |matrix height width current i j| ≤ M)
      ∧ ((matrix height width current).transpose * matrix height width current
          - (M ^ 2 / 16) • 1).PosSemidef := by
  have hG := qrGramRadius_le_eight height pivots M hh (by omega) hM
  have hn : (width : ℝ) ≤ 8 := by exact_mod_cast (show width ≤ 8 by omega)
  have hδ := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg width)
  have hcap := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (2 : ℝ) ^ (-7 : Int) * M ^ 2)
  have hroom : M ^ 2 / 2 + qrGramRadius height pivots (fun _ => M) ≤ M ^ 2 := by
    norm_num at hG
    nlinarith [sq_nonneg M]
  refine ⟨
    prefixEnclosure_magnitude height width pivots current (fun _ => M) _ _ M h hM hroom,
    ?_
  ⟩
  have hpad : 0 ≤ M ^ 2 / 8 - width * qrGramRadius height pivots (fun _ => M) - M ^ 2 / 16 := by
    norm_num at hδ hcap
    linarith
  have hpsd := h.2.add ((Matrix.PosSemidef.one (n := Fin width) (R := ℝ)).smul hpad)
  convert hpsd using 1
  simp only [sub_smul]
  module

end Kalman.Proofs.FloatQRDomain
