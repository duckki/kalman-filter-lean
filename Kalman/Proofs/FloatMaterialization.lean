import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FloatDenseError
import Kalman.Proofs.FloatFactorValidity
import Kalman.Proofs.FloatGramSymmetry
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy

/-! Error of optional dense LLᵀ materialization. This is a theorem about
the actual checked multiply, relative to the exact Gram of stored Float entries. -/

namespace Kalman.Proofs.FloatMaterialization

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.SquareRootProfiles
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Flare.Binary64.Value

theorem factor_storage (n : Nat) (factor : Input.FactorState)
    (h : factor.validate n = .ok ())
    : factor.mean.size = n
      ∧ factor.lower.size = n * n
      ∧ factor.mean.all Float.isFinite = true
      ∧ factor.lower.all Float.isFinite = true := by
  cases hs : (factor.mean.size == n && factor.lower.size == n * n) with
  | false => simp [Input.FactorState.validate, hs] at h
  | true =>
      cases hf : (factor.mean.all Float.isFinite && factor.lower.all Float.isFinite) with
      | false => simp [Input.FactorState.validate, hs, hf] at h
      | true =>
          obtain ⟨hm, hl⟩ := Bool.and_eq_true_iff.mp hs
          obtain ⟨hmf, hlf⟩ := Bool.and_eq_true_iff.mp hf
          exact ⟨of_decide_eq_true hm, of_decide_eq_true hl, hmf, hlf⟩

/-- A common absolute dot-product mass M gives an entrywise n·2⁻⁵⁰·M
allowance. The lower bound on M explicitly covers gradual underflow. -/
theorem materialization_accuracy (n : Nat) (factor : Input.FactorState) (M : ℝ)
    (hn : 0 < n) (hn' : n ≤ 32) (hv : ValidFactor n factor)
    (hM : M ≤ (2 : ℝ) ^ (990 : Int)) (hη : (2 : ℝ) ^ (-1022 : Int) ≤ M)
    (hmass
      : ∀ i j,
          i < n
          → j < n
          → (∑ k ∈ Finset.range n,
              |value (entry n factor.lower i k) * value (entry n factor.lower j k)|)
            ≤ M)
    : ∃ output,
        MaterializationWithin (n * (2 : ℝ) ^ (-50 : Int) * M) n factor output := by
  obtain ⟨hms, hls, hmf, hlf⟩ := factor_storage n factor hv.1
  have ht := Flare.Matrix.Multiplication.transpose_storage n n factor.lower hlf
  obtain ⟨r, hr, hrs, hrf, he⟩ := Kalman.Proofs.FloatDenseError.multiply_entrywise_accuracy
    n n n factor.lower (transpose n n factor.lower) (fun _ _ => M) hn' hlf ht.2.1
    (fun _ _ _ _ => hM) (fun _ _ _ _ => hη) (by
      intro i j hi hj
      have heq : ∀ k ∈ Finset.range n,
          entry n (transpose n n factor.lower) k j = entry n factor.lower j k := by
        intro k hk
        exact ht.2.2 _ _ (Finset.mem_range.mp hk) hj
      have hsum : (∑ k ∈ Finset.range n, |value (entry n factor.lower i k) *
          value (entry n (transpose n n factor.lower) k j)|) =
          (∑ k ∈ Finset.range n, |value (entry n factor.lower i k) * value (entry n factor.lower j k)|) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [heq k hk]
      rw [hsum]
      exact hmass i j hi hj)
  refine ⟨⟨factor.mean, r⟩, hv, ?_, ?_, ?_, ?_⟩
  · simp [Kalman.Implementation.SquareRootFilter.materialize, hn, hn', hv.1, hr, bind, Except.bind, pure, Except.pure]
  · have hmf' : factor.mean.all Float.isFinite 0 n = true := by simpa only [hms] using hmf
    have hrf' : r.all Float.isFinite 0 (n * n) = true := by simpa only [hrs] using hrf
    simp only [Input.State.validate, hms, hrs, beq_self_eq_true, Bool.and_self, hmf', hrf',
      ↓reduceIte, pure, Except.pure]
  · have hM0 : 0 ≤ M := (zpow_pos (by norm_num : (0 : ℝ) < 2) (-1022 : Int)).le.trans hη
    positivity
  · intro i j
    have hm := Flare.Matrix.Multiplication.transpose_matrix n n factor.lower hlf
    simpa only [state, factorState, FactorRecursion.gram, hm] using he i j

/-- Successful materialization copies the mean words and returns exactly the
checked dense product. This extracts the native schedule, without an error premise. -/
theorem materialization_output (n : Nat) (factor : Input.FactorState)
    (output : Input.State) (hn : 0 < n) (hn' : n ≤ 32) (hv : factor.validate n = .ok ())
    (h : Kalman.Implementation.SquareRootFilter.materialize n factor = .ok output)
    : ∃ r,
        multiply n n n factor.lower (transpose n n factor.lower) = .ok r
        ∧ output = ⟨factor.mean, r⟩ := by
  cases hr : multiply n n n factor.lower (transpose n n factor.lower) with
  | error e =>
      simp [Kalman.Implementation.SquareRootFilter.materialize, hn, hn', hv, hr,
        bind, Except.bind] at h
  | ok r =>
      refine ⟨r, rfl, ?_⟩
      have he : (Except.ok (⟨factor.mean, r⟩ : Input.State) : Except Input.Error Input.State)
          = .ok output := by
        simpa [Kalman.Implementation.SquareRootFilter.materialize, hn, hn', hv, hr, bind,
          Except.bind, pure, Except.pure]
          using h
      exact (Except.ok.inj he).symm

private theorem product_abs_le_squares (a b : ℝ) : 2 * |a * b| ≤ a * a + b * b := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- The preserved covariance cap bounds the absolute mass of every dot product,
including correlations. The elementary inequality 2|ab| ≤ a²+b² avoids a loose
factor-entry-based mass estimate. -/
theorem two_state_dot_mass_of_diagonal_cap (factor : Input.FactorState)
    (hcap : ∀ i, (factorState 2 factor).covariance i i ≤ 2)
    : ∀ i j,
        i < 2
        → j < 2
        → (∑ k ∈ Finset.range 2,
            |value (entry 2 factor.lower i k) * value (entry 2 factor.lower j k)|)
          ≤ (2 : ℝ) := by
  intro i j hi hj
  have hdi := hcap ⟨i, hi⟩
  have hdj := hcap ⟨j, hj⟩
  simp only [factorState, FactorRecursion.gram, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two] at hdi hdj
  change value (entry 2 factor.lower i 0) * value (entry 2 factor.lower i 0) +
    value (entry 2 factor.lower i 1) * value (entry 2 factor.lower i 1) ≤ 2 at hdi
  change value (entry 2 factor.lower j 0) * value (entry 2 factor.lower j 0) +
    value (entry 2 factor.lower j 1) * value (entry 2 factor.lower j 1) ≤ 2 at hdj
  have h0 := product_abs_le_squares (value (entry 2 factor.lower i 0)) (value (entry 2 factor.lower j 0))
  have h1 := product_abs_le_squares (value (entry 2 factor.lower i 1)) (value (entry 2 factor.lower j 1))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith

/-- Compatibility interface for the earlier preserved-state invariant. -/
theorem two_state_dot_mass (factor : Input.FactorState)
    (p
      : Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.StateInvariant
          factor)
    : ∀ i j,
        i < 2
        → j < 2
        → (∑ k ∈ Finset.range 2,
            |value (entry 2 factor.lower i k) * value (entry 2 factor.lower j k)|)
          ≤ (2 : ℝ) :=
  two_state_dot_mass_of_diagonal_cap factor
    (fun i => (le_abs_self _).trans (p.covariance_bound i i))

/-- The preserved two-state stored invariant derives finite dense output and
entrywise error 2^-48, unchanged mean words, exact off-diagonal word equality,
and Hermitian Real decoding. Dense positivity is a separate spectral argument. -/
theorem two_state_accuracy_of_diagonal_cap (factor : Input.FactorState)
    (hv : ValidFactor 2 factor) (hcap : ∀ i, (factorState 2 factor).covariance i i ≤ 2)
    : ∃ output,
        Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.DenseMaterializationWithin
          factor output := by
  open Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy in
    have hupper : (2 : ℝ) ≤ (2 : ℝ)^(990 : Int) := by
      calc
        2 = (2 : ℝ)^(1 : Int) := by norm_num
        _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    have hlower : (2 : ℝ)^(-1022 : Int) ≤ 2 := by
      calc
        _ ≤ (2 : ℝ)^(1 : Int) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
        _ = 2 := by norm_num
    obtain ⟨output, he⟩ := materialization_accuracy 2 factor 2 (by decide) (by decide) hv
      hupper hlower (two_state_dot_mass_of_diagonal_cap factor hcap)
    have he' : MaterializationWithin materializationRadius 2 factor output := by
      convert he using 1
      norm_num [materializationRadius]
    obtain ⟨r, hr, eq⟩ := materialization_output 2 factor output (by decide) (by decide) hv.1 he'.2.1
    subst output
    have hf := (factor_storage 2 factor hv.1).2.2.2
    exact ⟨_, he', rfl, FloatGramSymmetry.multiply_gram_two_symmetric _ r hf hr,
      FloatGramSymmetry.multiply_gram_two_hermitian _ r hf hr⟩

/-- Compatibility interface for the earlier preserved-state invariant. -/
theorem two_state_accuracy (factor : Input.FactorState)
    (p
      : Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.StateInvariant
          factor)
    : ∃ output,
        Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy.DenseMaterializationWithin
          factor output :=
  two_state_accuracy_of_diagonal_cap factor p.valid
    (fun i => (le_abs_self _).trans (p.covariance_bound i i))

end Kalman.Proofs.FloatMaterialization
