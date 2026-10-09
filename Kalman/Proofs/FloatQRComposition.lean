import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRGram
import Kalman.Proofs.ErrorPropagation

/-! Compose the actual native QR loop's Gram changes and exact retention.
The resulting reference is the original stored prearray. Prefix operand
profiles are explicit hypotheses, not an established initial rank domain. -/

namespace Kalman.Proofs.FloatQRComposition

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Flare.Binary64.Value

private theorem qrIterations_cons (height width pivot : Nat) (pivots : List Nat)
    (a : Array Float)
    : qrIterations height width (pivot :: pivots) a
      = (do
          let next ← qrIteration height width pivot a
          qrIterations height width pivots next) := by
  simp [qrIterations]

private theorem qrIterations_nil (height width : Nat) (a : Array Float)
    : qrIterations height width [] a = .ok a := by
  simp [qrIterations, pure, Except.pure, bind, Except.bind]

/-- Splitting the same pivot schedule preserves all values and failures. -/
theorem qrIterations_append (height width : Nat) (left right : List Nat) (a : Array Float)
    : qrIterations height width (left ++ right) a
      = (do
          let current ← qrIterations height width left a
          qrIterations height width right current) := by
  induction left generalizing a with
  | nil => simp [qrIterations_nil, bind, Except.bind]
  | cons pivot left ih =>
      rw [List.cons_append, qrIterations_cons, qrIterations_cons]
      cases qrIteration height width pivot a with
      | error e => simp [bind, Except.bind]
      | ok next =>
          simp only [bind, Except.bind]
          exact ih next

private theorem qrIterations_succ (height width pivots : Nat) (a : Array Float)
    : qrIterations height width (List.range (pivots + 1)) a
      = (do
          let current ← qrIterations height width (List.range pivots) a
          qrIteration height width pivots current) := by
  rw [List.range_succ, qrIterations_append]
  have hs : ∀ current, qrIterations height width [pivots] current
      = qrIteration height width pivots current := by
    intro current
    rw [qrIterations_cons]
    simp only [qrIterations_nil]
    cases qrIteration height width pivots current <;> rfl
  simp_rw [hs]

/-- The local input profile guarantees a nonzero stored diagonal, including
the checked rescaling and intentional source-tail zero assignments. -/
theorem qrIteration_diagonal_nonzero (height width pivot : Nat) (a output : Array Float)
    (M : ℝ) (p : IterationProfile height width pivot a M)
    (h : qrIteration height width pivot a = .ok output)
    : value (entry width output pivot pivot) ≠ 0 := by
  obtain ⟨scale, _, _, _, _, _, result, _, _, _, _, hrun, _, _, _, _, hscale, _, _, _, _, _, _, _,
      hdiag, _, _, _, _, _, _⟩ := FloatQRIteration.qrIteration_accuracy height width pivot a M p
  have he : result = output := Except.ok.inj (hrun.symm.trans h)
  subst result
  have hp : 0 < |value (entry width output pivot pivot)| := (by linarith : 0 < value scale / 4).trans_le hdiag
  exact abs_pos.mp hp

/-- A prefix needs operand profiles only for its own preceding iterations.
No condition on later pivots or successful final factorization is required. -/
theorem qrIterations_prefix_accuracy_of_profiles (height width pivots : Nat)
    (a : Array Float) (budget : Nat → ℝ) (hf : a.all Float.isFinite = true)
    (profiles
      : ∀ pivot,
          pivot < pivots
          → ∀ current,
              qrIterations height width (List.range pivot) a = .ok current
              → IterationProfile height width pivot current (budget pivot))
    : QRPrefixAccuracy height width pivots a budget := by
  induction pivots with
  | zero =>
      refine ⟨a, ?_, rfl, hf, ?_, ?_, ?_⟩
      · exact qrIterations_nil height width a
      · simp [ProcessedColumns]
      · simp
      · simpa [qrGramRadius] using ErrorPropagation.within_refl
          ((matrix height width a).transpose * matrix height width a)
  | succ pivots ih =>
      obtain ⟨current, hprefix, hs, _, hz, hd, he⟩ :=
        ih (fun pivot hp current hrun => profiles pivot (by omega) current hrun)
      have profile := profiles pivots (by omega) current hprefix
      obtain ⟨output, hrun, hos, hof, herr⟩ :=
        FloatQRGram.qrIteration_gram_accuracy height width pivots current (budget pivots) profile hz
      have hzeros := (FloatQRTriangular.qrIteration_processed height width pivots current output
        profile.pivot_height profile.pivot_width profile.matrix_size profile.matrix_finite hrun hz).2.2
      refine ⟨output, ?_, hos.trans hs, hof, hzeros, ?_, ?_⟩
      · rw [qrIterations_succ, hprefix]
        exact hrun
      · intro j hj
        by_cases hlt : j < pivots
        · rw [← FloatQRTriangular.qrIteration_earlierColumn height width pivots current output
            profile.pivot_height profile.pivot_width profile.matrix_size profile.matrix_finite hrun j hlt j]
          exact hd j hlt
        · have hjp : j = pivots := by omega
          subst j
          exact qrIteration_diagonal_nonzero height width pivots current output (budget pivots) profile hrun
      · have hc := ErrorPropagation.within_trans herr he
        simpa only [qrGramRadius, Finset.sum_range_succ, add_comm] using hc

/-- Every certified prefix succeeds. Structural zeros and nonzero diagonals
are propagated from the program; only numerical operand profiles are supplied. -/
theorem qrIterations_prefix_accuracy (height width pivots : Nat) (a : Array Float)
    (budget : Nat → ℝ) (p : TriangularizationProfile height width a budget)
    (hp : pivots ≤ width)
    : QRPrefixAccuracy height width pivots a budget := by
  exact qrIterations_prefix_accuracy_of_profiles height width pivots a budget
    p.matrix_finite
    (fun pivot hlt current hrun => p.prefix_profile pivot (by omega) current hrun)

/-- Complete native QR succeeds with a retained nonzero diagonal and its exact
column Gram is within the sum of local allowances of the original stored input. -/
theorem triangularize_gram_accuracy (height width : Nat) (a : Array Float)
    (budget : Nat → ℝ) (p : TriangularizationProfile height width a budget)
    : TriangularizationGramAccuracy height width a budget := by
  obtain ⟨r, hrun, hs, hf, hz, hd, he⟩ := qrIterations_prefix_accuracy height width width a budget p le_rfl
  have hr : triangularize height width a = .ok r := hrun
  exact ⟨r, ⟨hr, hs.trans p.matrix_size, hf, hz⟩, ⟨hf, hd⟩, he⟩

/-- The actual retained factor is accurate against the exact Gram of the same
original stored prearray and has a strictly PD exact Gram. All later operand
profiles are still hypotheses; no final-success or final-validation premise is needed. -/
theorem gramFactor_accuracy (rows columns : Nat) (a : Array Float) (budget : Nat → ℝ)
    (hs : a.size = rows * columns) (hf : a.all Float.isFinite = true)
    (p : TriangularizationProfile columns rows (transpose rows columns a) budget)
    : GramFactorAccuracy rows columns a budget := by
  obtain ⟨r, ht, profile, herr⟩ := triangularize_gram_accuracy columns rows
    (transpose rows columns a) budget p
  obtain ⟨l, hretain, hls, hlf, _, _, hlp, hgram, hpd⟩ := FloatQRRetain.retainFactor_accuracy rows r profile
  have hrun : gramFactor rows columns a = .ok l := by
    unfold gramFactor
    rw [ht.1]
    exact hretain
  have hfull := FloatQRTriangular.retainedUpper_gram_eq_full columns rows r p.width_le_height ht.2.2.2
  have htranspose := Flare.Matrix.Multiplication.transpose_matrix rows columns a hf
  have herror : EntrywiseWithin (qrGramRadius columns rows budget)
      (Kalman.Definitions.FactorRecursion.gram (matrix rows rows l))
      (Kalman.Definitions.FactorRecursion.gram (matrix rows columns a)) := by
    rw [hgram, hfull]
    simpa only [htranspose, Matrix.transpose_transpose, Kalman.Definitions.FactorRecursion.gram] using herr
  exact ⟨hs, hf, l, hrun, hls, hlf, hlp, hpd, herror⟩

/-- A uniform conservative cap for the accumulated radius. The sharper public
radius retains the active heights and individual budgets of every pivot. -/
theorem qrGramRadius_le (height pivots : Nat) (budget : Nat → ℝ) (B : ℝ)
    (hk : ∀ pivot < pivots, height - pivot ≤ 32)
    (hb : ∀ pivot < pivots, 0 ≤ budget pivot ∧ budget pivot ≤ B)
    : qrGramRadius height pivots budget ≤ pivots * (2 : ℝ) ^ (-4 : Int) * B ^ 2 := by
  unfold qrGramRadius
  calc
    _ ≤ ∑ _pivot ∈ Finset.range pivots, (2 : ℝ) ^ (-4 : Int) * B ^ 2 := by
      apply Finset.sum_le_sum
      intro pivot hp
      have hlt := Finset.mem_range.mp hp
      apply (FloatQRGram.iterationGramRadius_le (budget pivot) (hk pivot hlt)
              (hb pivot hlt).1).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [(hb pivot hlt).1, (hb pivot hlt).2]
    _ = _ := by simp; ring

end Kalman.Proofs.FloatQRComposition
