import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Proofs.FloatFilterBudget

/-! A completed original-input witness for arbitrarily long supported horizons.
This reset example proves nonvacuity. The general horizon theorem covers other
models with the same operand-domain certificate, without assuming their error. -/

namespace Kalman.Proofs.FloatFilterDomain

open Matrix
open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra hiding identity
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.FilterComposition
open Kalman.Proofs.FilterComposition.Horizon
open Kalman.Proofs.FilterComposition.Budget
open Kalman.Proofs.FilterComposition.Reset
open Flare.Binary64.Value

set_option maxHeartbeats 1600000
set_option maxRecDepth 20000

private theorem negative_zero_value : value (-0.0 : Float) = 0 := by
  simpa only [Flare.Binary64.Arithmetic.zero_value, neg_zero]
    using (Flare.Binary64.Order.neg_value 0.0 (by decide +kernel)).2

theorem signedIdentity_matrix
    : matrix 2 2 signedIdentity = (1 : LinearModel.Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Flare.Matrix.Value.matrix, signedIdentity, Matrix.one_apply,
      negative_zero_value, Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]

theorem identity_matrix : matrix 2 2 identity = (1 : LinearModel.Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Flare.Matrix.Value.matrix, identity, Matrix.one_apply,
      Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]

theorem zeros_matrix : matrix 2 2 zeros = (0 : LinearModel.Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Flare.Matrix.Value.matrix, zeros, Flare.Binary64.Arithmetic.zero_value]

theorem zero_mean : vector 2 zeroMean = 0 := by
  ext i
  fin_cases i <;> norm_num [vector, zeroMean, Flare.Binary64.Arithmetic.zero_value]

private theorem bounded_getD (a : Array Float)
    (h : a = identity ∨ a = zeros ∨ a = zeroMean ∨ a = measurement ∨ a = signedIdentity)
    : a.all Float.isFinite = true ∧ ∀ i, |value (a.getD i 0.0)| ≤ 1 := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · decide +kernel
    · intro i
      by_cases h0 : i = 0
      · subst i; norm_num [identity, zeros, zeroMean, measurement, signedIdentity, negative_zero_value,
          Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]
      by_cases h1 : i = 1
      · subst i; norm_num [identity, zeros, zeroMean, measurement, signedIdentity, negative_zero_value,
          Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]
      by_cases h2 : i = 2
      · subst i; norm_num [identity, zeros, zeroMean, measurement, signedIdentity, negative_zero_value,
          Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]
      by_cases h3 : i = 3
      · subst i; norm_num [identity, zeros, zeroMean, measurement, signedIdentity, negative_zero_value,
          Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]
      have hi : 4 ≤ i := by omega
      simp [identity, zeros, zeroMean, measurement, signedIdentity, Array.getD,
        show ¬ i < 4 by omega, show ¬ i < 2 by omega, Flare.Binary64.Arithmetic.zero_value]

private theorem entry_bounded (cols : Nat) (a : Array Float)
    (h : a = identity ∨ a = zeros ∨ a = zeroMean ∨ a = measurement ∨ a = signedIdentity)
    (i j : Nat)
    : |value (entry cols a i j)| ≤ 1 :=
  (bounded_getD a h).2 _

private theorem power_budget (e : Int) (he : -1022 ≤ e) (he' : e ≤ 990)
    : (2 : ℝ) ^ (-1022 : Int) ≤ (2 : ℝ) ^ e ∧ (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (990 : Int) :=
  ⟨zpow_le_zpow_right₀ (by norm_num) he, zpow_le_zpow_right₀ (by norm_num) he'⟩

private theorem product_profile (rows cols : Nat) (a b : Array Float)
    (ha : a = identity ∨ a = zeros ∨ a = zeroMean ∨ a = measurement ∨ a = signedIdentity)
    (hb : b = identity ∨ b = zeros ∨ b = zeroMean ∨ b = measurement ∨ b = signedIdentity)
    : ProductProfile rows 2 cols a b 8 := by
  refine ⟨by decide +kernel, (bounded_getD a ha).1, (bounded_getD b hb).1, ?_, ?_, ?_⟩
  · simpa only [show (2 : ℝ) ^ (3 : Int) = 8 by norm_num] using (power_budget 3 (by norm_num) (by norm_num)).2
  · simpa only [show (2 : ℝ) ^ (3 : Int) = 8 by norm_num] using (power_budget 3 (by norm_num) (by norm_num)).1
  · intro i j _ _
    have hterm : ∀ k ∈ Finset.range 2, |value (entry 2 a i k) * value (entry cols b k j)| ≤ 1 := by
      intro k _
      rw [abs_mul]
      exact (mul_le_mul (entry_bounded 2 a ha i k) (entry_bounded cols b hb k j)
        (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    calc
      _ ≤ ∑ _k ∈ Finset.range 2, (1 : ℝ) := Finset.sum_le_sum hterm
      _ ≤ 8 := by norm_num

private theorem sum_profile (a b : Array Float) (subtract : Bool)
    (ha : a = identity ∨ a = zeros ∨ a = zeroMean ∨ a = measurement ∨ a = signedIdentity)
    (hb : b = identity ∨ b = zeros ∨ b = zeroMean ∨ b = measurement ∨ b = signedIdentity)
    : SumProfile a b 2 subtract := by
  refine ⟨by norm_num, by norm_num, (bounded_getD a ha).1, (bounded_getD b hb).1, ?_⟩
  intro i _
  have ht := abs_add_le (value (a.getD i 0.0))
    (if subtract then -value (b.getD i 0.0) else value (b.getD i 0.0))
  have hs : |if subtract then -value (b.getD i 0.0) else value (b.getD i 0.0)| ≤ 1 := by
    cases subtract <;> simpa using (bounded_getD b hb).2 i
  exact ht.trans ((add_le_add ((bounded_getD a ha).2 i) hs).trans (by norm_num))

private theorem residual_profile (indices : List Nat) (left right : Nat → Float)
    (x : Float) (M : ℝ) (hM : 4 ≤ M) (hM' : M ≤ (2 : ℝ) ^ (990 : Int))
    (hl : indices.length ≤ 2) (hx : x.isFinite = true) (hxb : |value x| ≤ 1)
    (hleft : ∀ k ∈ indices, (left k).isFinite = true ∧ |value (left k)| ≤ 1)
    (hright : ∀ k ∈ indices, (right k).isFinite = true ∧ |value (right k)| ≤ 1)
    : ResidualProfile indices left right x M := by
  refine ⟨
    hl.trans (by decide +kernel),
    hx,
    fun k hk => (hleft k hk).1,
    fun k hk => (hright k hk).1,
    hM',
    ?_
  ⟩
  have heta : (2 : ℝ) ^ (-1022 : Int) ≤ 1 := by
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-1022 : Int) ≤ 0)
  have hs : (indices.map (fun k => |value (left k) * value (right k)|)).sum ≤ (indices.length : ℝ) := by
    calc
      _ ≤ (indices.map (fun _ => (1 : ℝ))).sum :=
        List.sum_le_sum
          (by
            intro k hk
            rw [abs_mul]
            exact (mul_le_mul (hleft k hk).2 (hright k hk).2 (abs_nonneg _)
                    (by norm_num)).trans_eq
              (by norm_num))
      _ = _ := by simp
  have hlen : (indices.length : ℝ) ≤ 2 := by exact_mod_cast hl
  linarith

private theorem finite_entry (cols : Nat) (a : Array Float)
    (h : a = identity ∨ a = zeros ∨ a = zeroMean ∨ a = measurement ∨ a = signedIdentity)
    (i j : Nat)
    : (entry cols a i j).isFinite = true :=
  Flare.Matrix.Storage.getD_finite _ _ (bounded_getD a h).1

theorem identity_lower : FactorRecursion.LowerPositive (matrix 2 2 identity) := by
  rw [identity_matrix]
  constructor
  · intro i j hij
    simp [ne_of_lt hij]
  · intro i
    simp

private theorem identity_diagonal (i : Nat) (hi : i < 2)
    : value (entry 2 identity i i) = 1 := by
  interval_cases i <;> norm_num [entry, Flare.Matrix.Dense.entry, identity,
    Flare.Binary64.Arithmetic.one_value]

theorem signedIdentity_lower
    : FactorRecursion.LowerPositive (matrix 2 2 signedIdentity) := by
  rw [signedIdentity_matrix]
  constructor
  · intro i j hij
    simp [ne_of_lt hij]
  · intro i
    simp

private theorem signedIdentity_diagonal (i : Nat) (hi : i < 2)
    : value (entry 2 signedIdentity i i) = 1 := by
  interval_cases i <;> norm_num [entry, Flare.Matrix.Dense.entry, signedIdentity,
    Flare.Binary64.Arithmetic.one_value]

theorem noise_profile : FactorProfile 2 identity identity 8 (1 / 2) 2 := by
  refine ⟨
    by decide +kernel,
    by decide +kernel,
    ?_,
    by decide +kernel,
    by norm_num,
    by norm_num,
    ?_,
    by norm_num,
    ?_,
    ?_,
    ?_
  ⟩
  · rw [identity_matrix]
    exact Matrix.isHermitian_one
  · intro i hi
    rw [identity_diagonal i hi]
    norm_num
  · intro i hi
    rw [identity_diagonal i hi]
    norm_num
  · calc
      _ ≤ 32 := by norm_num [residualRadius]
      _ ≤ (2 : ℝ) ^ (1000 : Int) := by
        simpa only [show (2 : ℝ) ^ (5 : Int) = 32 by norm_num]
          using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (5 : Int) ≤ 1000)
  · intro i j hi hj
    exact residual_profile (List.range j) _ _ _ 8 (by norm_num)
      (by simpa only [show (2 : ℝ) ^ (3 : Int) = 8 by norm_num] using (power_budget 3 (by norm_num) (by norm_num)).2)
      (by simpa using hj.trans hi.le) (finite_entry 2 identity (Or.inl rfl) i j)
      (entry_bounded 2 identity (Or.inl rfl) i j)
      (fun k _ => ⟨finite_entry 2 identity (Or.inl rfl) i k,
        entry_bounded 2 identity (Or.inl rfl) i k⟩)
      (fun k _ => ⟨finite_entry 2 identity (Or.inl rfl) j k,
        entry_bounded 2 identity (Or.inl rfl) j k⟩)

theorem solve_profile
    : SolveProfile 2 2 signedIdentity zeros zeros zeros 32 (1 / 2) 2 := by
  refine ⟨
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    signedIdentity_lower,
    by norm_num,
    (by
      intro i hi
      rw [signedIdentity_diagonal i hi]
      norm_num),
    by norm_num,
    ?_,
    ?_,
    ?_,
    ?_
  ⟩
  · intro i j
    rw [signedIdentity_matrix]
    simp [Matrix.one_apply]
    split_ifs <;> norm_num
  · calc
      _ ≤ 128 := by norm_num [residualRadius]
      _ ≤ (2 : ℝ) ^ (1000 : Int) := by
        simpa only [show (2 : ℝ) ^ (7 : Int) = 128 by norm_num]
          using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (7 : Int) ≤ 1000)
  · intro i j hi _
    exact residual_profile (List.range i) _ _ _ 32 (by norm_num)
      (by simpa only [show (2 : ℝ) ^ (5 : Int) = 32 by norm_num] using (power_budget 5 (by norm_num) (by norm_num)).2)
      (by simpa using hi.le) (finite_entry 2 zeros (Or.inr (Or.inl rfl)) i j)
      (entry_bounded 2 zeros (Or.inr (Or.inl rfl)) i j)
      (fun k _ => ⟨finite_entry 2 signedIdentity (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) i k,
        entry_bounded 2 signedIdentity (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) i k⟩)
      (fun k _ => ⟨finite_entry 2 zeros (Or.inr (Or.inl rfl)) k j,
        entry_bounded 2 zeros (Or.inr (Or.inl rfl)) k j⟩)
  · intro i j _ _
    exact residual_profile (List.range' (i + 1) (2 - (i + 1))) _ _ _ 32 (by norm_num)
      (by simpa only [show (2 : ℝ) ^ (5 : Int) = 32 by norm_num] using (power_budget 5 (by norm_num) (by norm_num)).2)
      (by simp; omega) (finite_entry 2 zeros (Or.inr (Or.inl rfl)) i j)
      (entry_bounded 2 zeros (Or.inr (Or.inl rfl)) i j)
      (fun k _ => ⟨finite_entry 2 signedIdentity (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) k i,
        entry_bounded 2 signedIdentity (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) k i⟩)
      (fun k _ => ⟨finite_entry 2 zeros (Or.inr (Or.inl rfl)) k j,
        entry_bounded 2 zeros (Or.inr (Or.inl rfl)) k j⟩)

theorem prearray_profile (a b : Array Float)
    (h : (a = zeros ∧ b = identity) ∨ (a = identity ∧ b = zeros))
    : GramFactorInputDomain 2 4 (fromCols 2 2 2 a b) 2 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_⟩
    · simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (-896 : Int) ≤ 1)
    · simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : Int) ≤ 900)
    · intro i
      fin_cases i <;>
        norm_num [matrix, Flare.Matrix.Value.matrix, Kalman.Implementation.LinearAlgebra.fromCols, entry, Flare.Matrix.Dense.entry,
          zeros, identity, Fin.sum_univ_four, Flare.Binary64.Arithmetic.zero_value,
          Flare.Binary64.Arithmetic.one_value]
    · rw [FloatPrearray.fromCols_gram 2 2 2, identity_matrix, zeros_matrix]
      simp only [FactorRecursion.gram, Matrix.transpose_one, Matrix.transpose_zero,
        Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
      convert (Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul (by norm_num : 0 ≤ (1 : ℝ) / 2) using 1
      norm_num
      module

noncomputable def prediction_profile : PredictionProfile input initial where
  tq := identity
  fl := zeros
  mean := zeroMean
  noiseMass := 8
  noiseFloor := 1 / 2
  noiseBound := 2
  productMass := 8
  meanMass := 8
  qrBudget := 2
  transitionBound := 1 / 32
  factorBound := 2
  noise_shape := by decide +kernel
  noise_finite := by decide +kernel
  noise := noise_profile
  product :=
    product_profile 2 2 zeros signedIdentity (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  computeProduct := by decide +kernel
  meanProduct :=
    product_profile 2 1 zeros zeroMean (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr (Or.inl rfl)))
  computeMean := by decide +kernel
  qr := prearray_profile zeros identity (Or.inl ⟨rfl, rfl⟩)
  transition_nonneg := by norm_num
  factor_nonneg := by norm_num
  transition_magnitude := by simp [input, zeros_matrix]
  factor_magnitude := by
    change ∀ (i j : Fin 2), |matrix 2 2 signedIdentity i j| ≤ 2
    intro i j
    rw [signedIdentity_matrix]
    simp [Matrix.one_apply]; split_ifs <;> norm_num

noncomputable def innovation_profile : InnovationProfile input initial where
  tr := identity
  hl := zeros
  lower := signedIdentity
  noiseMass := 8
  noiseFloor := 1 / 2
  noiseBound := 2
  productMass := 8
  qrBudget := 2
  observationBound := 1 / 32
  factorBound := 2
  noise := noise_profile
  product :=
    product_profile 2 2 zeros signedIdentity (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  computeProduct := by decide +kernel
  qr := prearray_profile identity zeros (Or.inr ⟨rfl, rfl⟩)
  computeQR := by decide +kernel
  observation_nonneg := by norm_num
  factor_nonneg := by norm_num
  observation_magnitude := by simp [input, zeros_matrix]
  factor_magnitude := prediction_profile.factor_magnitude

noncomputable def gain_profile : GainProfile innovation_profile where
  pht := zeros
  forward := zeros
  solution := zeros
  productMass := 8
  solveMass := 32
  solveFloor := 1 / 2
  solveBound := 2
  gainBound := 1
  product := by
    have ht : Kalman.Implementation.LinearAlgebra.transpose 2 2 zeros = zeros := by decide +kernel
    simpa only [input, initial, innovation_profile, ht]
      using product_profile 2 2 signedIdentity zeros
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (Or.inr (Or.inl rfl))
  computeProduct := by decide +kernel
  solve := by
    have ht : Kalman.Implementation.LinearAlgebra.transpose 2 2 zeros = zeros := by decide +kernel
    simpa only [input, innovation_profile, ht] using solve_profile
  finite_solution := by decide +kernel
  mass_nonneg := by norm_num
  gain_nonneg := by norm_num
  gain_magnitude := by
    have ht : Kalman.Implementation.LinearAlgebra.transpose 2 2 zeros = zeros := by decide +kernel
    change ∀ (i j : Fin 2), |matrix 2 2 (Kalman.Implementation.LinearAlgebra.transpose 2 2 zeros) i j| ≤ 1
    rw [ht, zeros_matrix]
    norm_num

noncomputable def mean_profile : MeanProfile gain_profile where
  projected := zeroMean
  residual := measurement
  increment := zeroMean
  mean := zeroMean
  projectedMass := 8
  incrementMass := 8
  residualExponent := 2
  meanExponent := 2
  measurement_shape := by decide +kernel
  prior_shape := by decide +kernel
  projectedProduct := prediction_profile.meanProduct
  computeProjected := by decide +kernel
  residualSum :=
    sum_profile measurement zeroMean true (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (Or.inr (Or.inr (Or.inl rfl)))
  computeResidual := by decide +kernel
  incrementProduct := by
    have ht : gainArray gain_profile = zeros := by decide +kernel
    rw [ht]
    exact product_profile 2 1 zeros measurement
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  computeIncrement := by decide +kernel
  meanSum :=
    sum_profile zeroMean zeroMean false (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inr (Or.inr (Or.inl rfl)))
  computeMean := by decide +kernel

noncomputable def posterior_profile : PosteriorProfile gain_profile where
  kh := zeros
  w := identity
  wl := identity
  ktr := zeros
  khMass := 8
  wlMass := 8
  ktrMass := 8
  qrBudget := 2
  noiseFactorBound := 2
  wExponent := 2
  khProduct := by
    have ht : gainArray gain_profile = zeros := by decide +kernel
    rw [ht]
    exact product_profile 2 2 zeros zeros
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
  computeKH := by decide +kernel
  wSum := by
    have hi : Kalman.Implementation.LinearAlgebra.identity 2 = identity := by decide +kernel
    simpa only [input, hi]
      using sum_profile identity zeros true (Or.inl rfl) (Or.inr (Or.inl rfl))
  computeW := by decide +kernel
  wlProduct :=
    product_profile 2 2 identity signedIdentity (Or.inl rfl)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  computeWL := by decide +kernel
  ktrProduct := by
    have ht : gainArray gain_profile = zeros := by decide +kernel
    rw [ht]
    exact product_profile 2 2 zeros identity (Or.inr (Or.inl rfl)) (Or.inl rfl)
  computeKTR := by decide +kernel
  qr := prearray_profile identity zeros (Or.inr ⟨rfl, rfl⟩)
  noise_nonneg := by norm_num
  noise_magnitude := by
    change ∀ (i j : Fin 2), |matrix 2 2 identity i j| ≤ 2
    rw [identity_matrix]
    intro i j
    simp [Matrix.one_apply]; split_ifs <;> norm_num

noncomputable def step_profile : StepProfile input initial where
  prediction := prediction_profile
  lower := signedIdentity
  computeQR := by decide +kernel
  innovation := innovation_profile
  gain := gain_profile
  mean := mean_profile
  posterior := posterior_profile

theorem interpreted_model : model input = (⟨0, 0, 1, 1⟩ : LinearModel.Model 2 2) := by
  simp [model, input, zeros_matrix, identity_matrix]

theorem interpreted_initial : factorState 2 initial = (⟨0, 1⟩ : LinearModel.State 2) := by
  simp [factorState, initial, FactorRecursion.gram, zero_mean, signedIdentity_matrix]

noncomputable def environment : StepEnvironment input (factorState 2 initial) where
  noiseFloor := 1
  covarianceBound := 2
  noiseBound := 1
  innovationBound := 2
  floor_positive := by norm_num
  covariance_nonneg := by norm_num
  noise_nonneg := by norm_num
  innovation_nonneg := by norm_num
  process_psd := by rw [interpreted_model]; exact Matrix.PosSemidef.one
  noise_lower := by
    change (matrix 2 2 identity - (1 : ℝ) • (1 : LinearModel.Square 2)).PosSemidef
    rw [identity_matrix]
    simp only [one_smul, sub_self]
    exact Matrix.PosSemidef.zero
  covariance_magnitude := by
    change ∀ (i j : Fin 2), |(CovarianceRecursion.predict (model input) (factorState 2 initial)).covariance i j| ≤ 2
    rw [interpreted_model, interpreted_initial]
    dsimp only [input]
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [CovarianceRecursion.predict, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.one_apply, Fin.sum_univ_two]
  noise_magnitude := by
    change ∀ (i j : Fin 2), |(model input).measurementNoise i j| ≤ 1
    rw [interpreted_model]
    intro i j
    simp [Matrix.one_apply]; split_ifs <;> norm_num
  innovation_magnitude := by
    change ∀ (i : Fin 2), |CovarianceRecursion.innovation (model input) (CovarianceRecursion.predict (model input) (factorState 2 initial)) (vector 2 input.measurement) i| ≤ 2
    rw [interpreted_model]
    dsimp only [input]
    intro i
    fin_cases i <;> norm_num [CovarianceRecursion.innovation, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, vector, input, measurement,
      Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]

theorem uniform_parameters : UniformStepParameters step_profile environment := by
  constructor <;> rfl

private instance : DecidableEq Input.FactorState :=
  fun a b =>
    decidable_of_iff (a.mean = b.mean ∧ a.lower = b.lower) (by cases a; cases b; simp)

theorem native_step_certificate
    : Kalman.Implementation.SquareRootFilter.step input initial = .ok initial := by
  decide +kernel

theorem native_trace_certificate (t : Nat)
    : nativeRun (fun _ => input) initial t = .ok initial := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have ih' : Kalman.Implementation.SquareRootFilter.run (fun _ => input) initial t =
          .ok initial := ih
      rw [nativeRun, Kalman.Implementation.SquareRootFilter.run, ih']
      exact native_step_certificate

theorem exact_step_certificate
    : CovarianceRecursion.step .joseph (model input) (factorState 2 initial)
        (vector 2 input.measurement)
      = factorState 2 initial := by
  rw [interpreted_model, interpreted_initial]
  dsimp only [input]
  simp [CovarianceRecursion.step, CovarianceRecursion.predict, CovarianceRecursion.update,
    CovarianceRecursion.gain, CovarianceRecursion.correctedCovariance, CovarianceRecursion.joseph]

theorem exact_trace_certificate (t : Nat)
    : exactRun 2 2 (fun _ => input) (factorState 2 initial) t
      = factorState 2 initial := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [exactRun, ih]
      exact exact_step_certificate

theorem initial_accuracy
    : FactorAccuracy (1 / 128) (1 / 128) 2 initial (factorState 2 initial) := by
  refine ⟨
    FloatFactorValidity.factor_validate_sound 2 initial (by decide +kernel),
    ⟨by norm_num, fun i j => by simp⟩,
    by norm_num,
    fun i => ?_
  ⟩
  simp [factorState]

noncomputable def environment_at (t : Nat)
    : StepEnvironment (atDimensions 2 2 input)
        (exactRun 2 2 (fun _ => input) (factorState 2 initial) t) where
  noiseFloor := 1
  covarianceBound := 2
  noiseBound := 1
  innovationBound := 2
  floor_positive := by norm_num
  covariance_nonneg := by norm_num
  noise_nonneg := by norm_num
  innovation_nonneg := by norm_num
  process_psd := environment.process_psd
  noise_lower := environment.noise_lower
  covariance_magnitude := by
    rw [exact_trace_certificate]; exact environment.covariance_magnitude
  noise_magnitude := environment.noise_magnitude
  innovation_magnitude := by
    rw [exact_trace_certificate]; exact environment.innovation_magnitude

noncomputable def profile_at (t : Nat) (current : Input.FactorState)
    (hrun : nativeRun (fun _ => input) initial t = .ok current)
    : StepProfile (atDimensions 2 2 input) current := by
  have he : current = initial := Except.ok.inj (hrun.symm.trans (native_trace_certificate t))
  subst current
  exact step_profile

/-- A certificate from the original fixed input, with all Cholesky, solve,
product, QR, reference and coefficient assumptions discharged for every prefix. -/
noncomputable def uniform_domain (horizon : Nat)
    : UniformHorizonDomain horizon (fun _ => input) initial (factorState 2 initial) where
  operands :=
    {
      initial_positive :=
        FloatFactorValidity.validFactor_posDef 2 initial initial_accuracy.1
      dimensions := fun _ _ => ⟨rfl, rfl⟩
      input_valid := fun _ _ => by decide +kernel
      process_positive :=
        fun _ _ => by
          change (model input).processNoise.PosDef
          rw [interpreted_model]
          exact Matrix.PosDef.one
      environment := fun t _ => environment_at t
      profile := fun t _ current hrun => profile_at t current hrun
    }
  initial_accuracy := initial_accuracy
  parameters := by
    intro t _ current hrun
    have he : current = initial := Except.ok.inj (hrun.symm.trans (native_trace_certificate t))
    subst current
    change UniformStepParameters (profile_at t initial hrun) (environment_at t)
    constructor <;> rfl

/-- The same exact reset witness meets the tightened initial tolerance. -/
noncomputable def tight_uniform_domain (horizon : Nat)
    : UniformHorizonDomain horizon (fun _ => input) initial (factorState 2 initial)
        (1 / 1048576) where
  operands := (uniform_domain horizon).operands
  parameters := (uniform_domain horizon).parameters
  initial_accuracy := by
    refine ⟨
      FloatFactorValidity.factor_validate_sound 2 initial (by decide +kernel),
      ⟨by norm_num, fun i j => by simp⟩,
      by norm_num,
      fun i => ?_
    ⟩
    simp [factorState]

theorem tight_uniform_domain_nonempty (horizon : Nat)
    : Nonempty
        (UniformHorizonDomain horizon (fun _ => input) initial (factorState 2 initial)
          (1 / 1048576)) :=
  ⟨tight_uniform_domain horizon⟩

/-- The reset trace also discharges the dimension-sensitive uniform budget. -/
noncomputable def refined_uniform_domain (horizon : Nat)
    : UniformHorizonDomain horizon (fun _ => input) initial (factorState 2 initial)
        (1 / 33554432) where
  operands := (uniform_domain horizon).operands
  parameters := (uniform_domain horizon).parameters
  initial_accuracy := by
    refine ⟨
      FloatFactorValidity.factor_validate_sound 2 initial (by decide +kernel),
      ⟨by norm_num, fun i j => by simp⟩,
      by norm_num,
      fun i => ?_
    ⟩
    simp [factorState]

theorem refined_uniform_domain_nonempty (horizon : Nat)
    : Nonempty
        (UniformHorizonDomain horizon (fun _ => input) initial (factorState 2 initial)
          (1 / 33554432)) :=
  ⟨refined_uniform_domain horizon⟩

/-- The uniform horizon domain has a fully discharged original-input member
at every finite length. -/
theorem uniform_domain_nonempty (horizon : Nat)
    : Nonempty
        (UniformHorizonDomain horizon (fun _ => input) initial (factorState 2 initial)) :=
  ⟨uniform_domain horizon⟩

/-- The complete native filter is accurate and both covariances are PD at
every finite horizon on this fully discharged original-input nonvacuity example. -/
theorem supported_horizon (horizon : Nat)
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            nativeRun (fun _ => input) initial t = .ok output
            ∧ FactorAccuracy (1 / 128) (1 / 128) 2 output
                (exactRun 2 2 (fun _ => input) (factorState 2 initial) t)
            ∧ (factorState 2 output).covariance.PosDef
            ∧ (exactRun 2 2 (fun _ => input) (factorState 2 initial)
                t).covariance.PosDef :=
  FloatFilterBudget.uniform_horizon_accuracy horizon (fun _ => input) initial
    (factorState 2 initial) (uniform_domain horizon)

end Kalman.Proofs.FloatFilterDomain
