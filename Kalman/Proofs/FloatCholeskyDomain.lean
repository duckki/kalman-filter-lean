import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.FloatCholeskyFactor
import Kalman.Proofs.FactorStructure
import Kalman.Proofs.FloatFilterInitialization
import Flare.Analysis.NumericalBounds

/-! Two-state native Cholesky success from the original finite stored covariance.
All pivot, quotient and final operand-profile conditions are derived here. -/

namespace Kalman.Proofs.FloatCholeskyDomain

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.FloatDenseError
open Kalman.Proofs.FloatResidualError
open Flare.Binary64.Value

set_option maxHeartbeats 800000

/-- The actual two-column schedule, including every exceptional-value rejection.
The upper off-diagonal is not read by the factor kernel. -/
theorem cholesky_two_schedule (a : Array Float)
    : cholesky 2 a
      = (do
          let d0 ← positiveSqrt (entry 2 a 0 0)
          let c ← finite (entry 2 a 1 0 / d0)
          let pivot ← subtractProducts [0] (fun _ => c) (fun _ => c) (entry 2 a 1 1)
          let d1 ← positiveSqrt pivot
          return #[d0, 0.0, c, d1]) := by
  simp [cholesky, Std.Legacy.Range.forIn_eq_forIn_range', List.range', List.range,
    List.range.loop,
    entry, Flare.Matrix.Dense.entry, subtractProducts, subtractProductsCore, adapt,
    divideResidual, Bind.bind, Except.bind, pure, Except.pure]
  cases positiveSqrt (a[0]?.getD 0.0) with
  | error e => simp
  | ok d0 =>
      dsimp only
      cases finite (a[2]?.getD 0.0 / d0) with
      | error e => simp
      | ok c =>
          have hfirst : ((Array.replicate 4 (0.0 : Float)).setIfInBounds 0 d0).setIfInBounds 2 c
              = #[d0, 0.0, c, 0.0] := by rfl
          simp [hfirst]
          cases Flare.Matrix.Dense.finite (c * c) with
          | error e => cases e <;> rfl
          | ok product =>
              dsimp only
              cases Flare.Matrix.Dense.finite (a[3]?.getD 0.0 - product) with
              | error e => cases e <;> rfl
              | ok pivot =>
                  dsimp only
                  cases positiveSqrt pivot <;> rfl

private theorem denormal_le_one : (2 : ℝ) ^ (-1022 : Int) ≤ 1 := by
  simpa using (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (-1022 : Int) ≤ 0))

private theorem mass_upper : (8 : ℝ) ≤ (2 : ℝ) ^ (990 : Int) := by
  simpa only [show (2 : ℝ)^(3 : Int) = 8 by norm_num]
    using (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (3 : Int) ≤ 990))

private theorem diagonal_enclosure (d : Float) (T : ℝ) (hd : 0 < value d)
    (hT : 3 / 4 ≤ T) (hT' : T ≤ 2)
    (he : |(value d) ^ 2 - T| ≤ diagonalRadius 1 8)
    : (3 : ℝ) / 4 ≤ value d ∧ value d ≤ 2 := by
  have h := abs_le.mp he
  norm_num [diagonalRadius, residualRadius] at h
  constructor <;> nlinarith

/-- Exact finite decoding of the two symmetric off-diagonal words suffices. -/
theorem input_hermitian (a : Array Float) (p : TwoStateCovarianceDomain a)
    : (matrix 2 2 a).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change value (entry 2 a j.val i.val) = value (entry 2 a i.val j.val)
  fin_cases i <;> fin_cases j <;> simp [p.symmetry]

/-- A quantitative exact-input floor is a conclusion of the entry conditions. -/
theorem input_lower_bound (a : Array Float) (p : TwoStateCovarianceDomain a)
    : (matrix 2 2 a - (3 / 4 : ℝ) • 1).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (input_hermitian a p).sub
      ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul (by norm_num : 0 ≤ (3 / 4 : ℝ))).1
  · intro x
    have h0 := mul_nonneg (sub_nonneg.mpr (p.diagonal_lower 0 (by decide))) (sq_nonneg (x 0))
    have h1 := mul_nonneg (sub_nonneg.mpr (p.diagonal_lower 1 (by decide))) (sq_nonneg (x 1))
    have hb := abs_le.mp p.off_diagonal_bound
    have hplus := mul_nonneg (by linarith : 0 ≤ 1 / 4 + value (entry 2 a 1 0))
      (sq_nonneg (x 0 + x 1))
    have hminus := mul_nonneg (by linarith : 0 ≤ 1 / 4 - value (entry 2 a 1 0))
      (sq_nonneg (x 0 - x 1))
    simp [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    change 0 ≤ x 0 * ((value (entry 2 a 0 0) - 3 / 4) * x 0
        + value (entry 2 a 0 1) * x 1)
      + x 1 * (value (entry 2 a 1 0) * x 0 + (value (entry 2 a 1 1) - 3 / 4) * x 1)
    rw [p.symmetry]
    nlinarith

theorem input_positive (a : Array Float) (p : TwoStateCovarianceDomain a)
    : (matrix 2 2 a).PosDef :=
  Flare.Analysis.NumericalBounds.posDef_of_lower_bound _ _ (by norm_num)
    (input_lower_bound a p)

/-- The checked initializer's native symmetry guard accepts decoded symmetry,
including opposite signed-zero words in the off-diagonal positions. -/
theorem input_symmetric (a : Array Float) (p : TwoStateCovarianceDomain a)
    : Input.symmetric 2 a = true := by
  have heq : (a.getD 2 0.0 == a.getD 1 0.0) = true := by
    apply (Flare.Binary64.Order.beq_iff _ _
      (Flare.Matrix.Storage.getD_finite _ _ p.finite)
      (Flare.Matrix.Storage.getD_finite _ _ p.finite)).mpr
    exact p.symmetry.symm
  simp only [Array.getD_eq_getD_getElem?] at heq
  have hne : (a[2]?.getD 0.0 != a[1]?.getD 0.0) = false := by
    simp only [bne, heq, Bool.not_true]
  simp [Input.symmetric, Std.Legacy.Range.forIn_eq_forIn_range', List.range',
    hne, pure, Id.run, bind]

/-- Input-only Cholesky success, with every final operand-profile field derived.
The profile constants match the existing two-state noise-factor allowances. -/
theorem cholesky_profile (a : Array Float) (p : TwoStateCovarianceDomain a)
    : ∃ l,
        l.size = 4
        ∧ FactorProfile 2 a l 8 (1 / 2) 2
        ∧ FactorRecursion.LowerPositive (matrix 2 2 l)
        ∧ (∀ i, i < 2 → (3 : ℝ) / 4 ≤ value (entry 2 l i i))
        ∧ |value (entry 2 l 1 0)| ≤ 1 / 2 := by
  have haf (i j : Nat) : (entry 2 a i j).isFinite = true :=
    Flare.Matrix.Storage.getD_finite _ _ p.finite
  let d0 := (entry 2 a 0 0).sqrt
  obtain ⟨hd0, hd0f, hd0p, hd0e⟩ := positiveSqrt_accuracy (entry 2 a 0 0) (haf 0 0)
    (by linarith [p.diagonal_lower 0 (by decide)])
  have hd0f' : d0.isFinite = true := hd0f
  have hd0p' : 0 < value d0 := hd0p
  have hd0e' : |(value d0)^2 - value (entry 2 a 0 0)| ≤ diagonalRadius 1 8 := by
    apply hd0e.trans
    have hm := mul_le_mul_of_nonneg_left (p.diagonal_upper 0 (by decide))
      (by positivity : 0 ≤ 2 * (2 : ℝ)^(-53 : Int) + ((2 : ℝ)^(-53 : Int))^2)
    norm_num [diagonalRadius, residualRadius] at hm ⊢
    linarith
  obtain ⟨hd0lo, hd0hi⟩ := diagonal_enclosure d0 (value (entry 2 a 0 0)) hd0p
    (by linarith [p.diagonal_lower 0 (by decide)]) (p.diagonal_upper 0 (by decide)) hd0e'
  have hquot : |value (entry 2 a 1 0) / value d0| ≤ (1 : ℝ) / 3 := by
    rw [abs_div, abs_of_pos hd0p]
    apply (div_le_iff₀ hd0p).mpr
    linarith [p.off_diagonal_bound]
  have hc := Flare.Binary64.Division.div_error (entry 2 a 1 0) d0 (-1)
    (haf 1 0) hd0f hd0p.ne' (by norm_num) (by norm_num)
    (hquot.trans (by norm_num))
  let c := entry 2 a 1 0 / d0
  have hcf : c.isFinite = true := hc.1
  have hcm : |value c| ≤ (1 : ℝ) / 2 := by
    have ht := abs_sub_le (value c) (value (entry 2 a 1 0) / value d0) 0
    simp only [sub_zero] at ht
    have he := hc.2
    norm_num at he
    linarith
  have hcsq : (value c)^2 ≤ (1 : ℝ) / 4 := by
    nlinarith [(abs_le.mp hcm).1, (abs_le.mp hcm).2]
  have row : ResidualProfile [0] (fun _ => c) (fun _ => c) (entry 2 a 1 1) 8 := by
    refine ⟨by decide, haf 1 1, fun _ _ => hc.1, fun _ _ => hc.1, mass_upper, ?_⟩
    have ha := p.diagonal_upper 1 (by decide)
    have hal := p.diagonal_lower 1 (by decide)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ← pow_two, abs_of_nonneg (sq_nonneg (value c)), abs_of_pos (by linarith : 0 < value (entry 2 a 1 1))]
    linarith [denormal_le_one]
  obtain ⟨pivot, hpivot, hd1, hd1f, hd1p, hd1e⟩ := choleskyDiagonal_accuracy [0]
    (fun _ => c) (entry 2 a 1 1) 8 row (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      norm_num [residualRadius]
      nlinarith [p.diagonal_lower 1 (by decide)])
  have hd1e' : |(value pivot.sqrt)^2 - (value (entry 2 a 1 1) - (value c)^2)|
      ≤ diagonalRadius 1 8 := by simpa [pow_two] using hd1e
  obtain ⟨hd1lo, hd1hi⟩ := diagonal_enclosure pivot.sqrt
    (value (entry 2 a 1 1) - (value c)^2) hd1p
    (by linarith [p.diagonal_lower 1 (by decide)])
    (by linarith [p.diagonal_upper 1 (by decide), sq_nonneg (value c)]) hd1e'
  let l := #[d0, 0.0, c, pivot.sqrt]
  have hlrun : cholesky 2 a = .ok l := by
    rw [cholesky_two_schedule, hd0]
    change (do
      let c' ← finite c
      let p' ← subtractProducts [0] (fun _ => c') (fun _ => c') (entry 2 a 1 1)
      let d1 ← positiveSqrt p'
      return #[d0, 0.0, c', d1]) = .ok l
    rw [finite_ok _ hc.1]
    change (do
      let p' ← subtractProducts [0] (fun _ => c) (fun _ => c) (entry 2 a 1 1)
      let d1 ← positiveSqrt p'
      return #[d0, 0.0, c, d1]) = .ok l
    rw [hpivot]
    change (do let d1 ← positiveSqrt pivot; return #[d0, 0.0, c, d1]) = .ok l
    rw [hd1]
    rfl
  have hlf : l.all Float.isFinite = true := by
    simp [l, hd0f', hcf, hd1f, show (0.0 : Float).isFinite = true by decide]
  have hdiaglo : ∀ i, i < 2 → (3 : ℝ) / 4 ≤ value (entry 2 l i i) := by
    intro i hi
    interval_cases i
    · simpa [l, entry, Flare.Matrix.Dense.entry] using hd0lo
    · simpa [l, entry, Flare.Matrix.Dense.entry] using hd1lo
  have hdiaghi : ∀ i, i < 2 → |value (entry 2 l i i)| ≤ 2 := by
    intro i hi
    interval_cases i
    · simpa [l, entry, Flare.Matrix.Dense.entry, abs_of_pos hd0p'] using hd0hi
    · simpa [l, entry, Flare.Matrix.Dense.entry, abs_of_pos hd1p] using hd1hi
  have hprofile : FactorProfile 2 a l 8 (1 / 2) 2 := by
    refine ⟨
      by decide,
      hlrun,
      input_hermitian a p,
      hlf,
      by norm_num,
      by norm_num,
      fun i hi => (by linarith [hdiaglo i hi]),
      by norm_num,
      hdiaghi,
      ?_,
      ?_
    ⟩
    · calc
        _ ≤ (32 : ℝ) := by norm_num [residualRadius]
        _ ≤ (2 : ℝ) ^ (1000 : Int) := by
          simpa only [show (2 : ℝ)^(5 : Int) = 32 by norm_num]
            using (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
                    (by norm_num : (5 : Int) ≤ 1000))
    · intro i j hi hj
      have hj2 : j < 2 := by omega
      interval_cases j
      · refine ⟨by decide, haf i 0, by simp, by simp, mass_upper, ?_⟩
        simp only [List.range_zero, List.map_nil, List.sum_nil, add_zero]
        have hb : |value (entry 2 a i 0)| ≤ 2 := by
          interval_cases i
          · rw [abs_of_pos (by linarith [p.diagonal_lower 0 (by decide)] : 0 < value (entry 2 a 0 0))]
            exact p.diagonal_upper 0 (by decide)
          · exact p.off_diagonal_bound.trans (by norm_num)
        linarith [denormal_le_one]
      · have hi1 : i = 1 := by omega
        subst i
        refine ⟨by decide, haf 1 1, ?_, ?_, mass_upper, ?_⟩
        · intro k hk
          have hk0 : k = 0 := by simpa using hk
          subst k
          simpa [l, entry, Flare.Matrix.Dense.entry] using hcf
        · intro k hk
          have hk0 : k = 0 := by simpa using hk
          subst k
          simpa [l, entry, Flare.Matrix.Dense.entry] using hcf
        · simpa [l, entry, Flare.Matrix.Dense.entry, List.range, List.range.loop] using row.mass
  have hlp : FactorRecursion.LowerPositive (matrix 2 2 l) := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [matrix, Flare.Matrix.Value.matrix, l, Flare.Binary64.Arithmetic.zero_value]
    · intro i
      exact (by norm_num : (0 : ℝ) < 3 / 4).trans_le (hdiaglo i.val i.isLt)
  exact ⟨
    l,
    by simp [l],
    hprofile,
    hlp,
    hdiaglo,
    by simpa [l, entry, Flare.Matrix.Dense.entry] using hcm
  ⟩

/-- The existing whole-factor allowance instantiated on the input-only domain.
This is an absolute entrywise bound in the chosen units. -/
theorem backward_radius_cap
    : diagonalRadius 2 8 + divisionRadius 2 8 (1 / 2) 2 ≤ (2 : ℝ) ^ (-42 : Int) := by
  have hd : divisionRadius 2 8 (1 / 2) 2 ≤ residualRadius 2 8
      + 2 * (2 : ℝ)^(-50 : Int) * ((8 + residualRadius 2 8) / (1 / 2) + 1) := by
    unfold divisionRadius
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl denormal_le_one) (by norm_num)
  calc
    _ ≤ diagonalRadius 2 8
        + (residualRadius 2 8
            + 2 * (2 : ℝ) ^ (-50 : Int) * ((8 + residualRadius 2 8) / (1 / 2) + 1)) :=
      add_le_add le_rfl hd
    _ ≤ _ := by norm_num [diagonalRadius, residualRadius]

/-- Success, strict represented positivity, a quantitative Gram floor, and
backward accuracy, all from the original stored covariance entries alone.
The Gram here uses exact Real multiplication of the returned native factor. -/
theorem cholesky_accuracy (a : Array Float) (p : TwoStateCovarianceDomain a)
    : ∃ l,
        l.size = 4
        ∧ cholesky 2 a = .ok l
        ∧ l.all Float.isFinite = true
        ∧ FactorRecursion.LowerPositive (matrix 2 2 l)
        ∧ (matrix 2 2 a).PosDef
        ∧ (matrix 2 2 l * (matrix 2 2 l).transpose).PosDef
        ∧ (matrix 2 2 l * (matrix 2 2 l).transpose - (1 / 2 : ℝ) • 1).PosSemidef
        ∧ EntrywiseWithin ((2 : ℝ) ^ (-42 : Int))
            (matrix 2 2 l * (matrix 2 2 l).transpose) (matrix 2 2 a) := by
  obtain ⟨l, hls, hl, hlp, _, _⟩ := cholesky_profile a p
  have he := FloatCholeskyFactor.factor_backward_error 2 a l 8 (1 / 2) 2 hl
  have he' : EntrywiseWithin ((2 : ℝ)^(-42 : Int))
      (matrix 2 2 l * (matrix 2 2 l).transpose) (matrix 2 2 a) :=
    ⟨by positivity, fun i j => (he.2 i j).trans backward_radius_cap⟩
  have hpd := FactorStructure.lowerPositive_gram_posDef _ hlp
  have hfloor := ErrorPropagation.lower_bound_of_error _ _ (3 / 4)
    ((2 : ℝ)^(-42 : Int)) (input_lower_bound a p) hpd.isHermitian he'
  have hpad : 0 ≤ (3 : ℝ) / 4 - 2 * (2 : ℝ)^(-42 : Int) - 1 / 2 := by norm_num
  have hpsd := hfloor.add ((Matrix.PosSemidef.one (n := Fin 2) (R := ℝ)).smul hpad)
  refine ⟨l, hls, hl.execution, hl.finite_lower, hlp, input_positive a p, hpd, ?_, he'⟩
  convert hpsd using 1
  simp only [FactorRecursion.gram, Nat.cast_ofNat, sub_smul]
  module

/-- Checked covariance-to-factor initialization with no assumed Cholesky run
or intermediate operand profile. Other model/state validation remains explicit. -/
theorem fromCovariance_accuracy (input : Input.Model) (initial : Input.State)
    (hn : input.stateDimension = 2) (p : TwoStateCovarianceDomain initial.covariance)
    (hinput : input.validate = .ok ()) (hstate : initial.validate 2 = .ok ())
    : ∃ l,
        Kalman.Implementation.SquareRootFilter.fromCovariance input initial
          = .ok ⟨initial.mean, l⟩
        ∧ Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
            ((2 : ℝ) ^ (-42 : Int)) 0 2 ⟨initial.mean, l⟩ (state 2 initial)
        ∧ (matrix 2 2 initial.covariance).PosDef
        ∧ (matrix 2 2 l * (matrix 2 2 l).transpose).PosDef := by
  rcases input with ⟨n, m, f, h, q, r, z⟩
  change n = 2 at hn
  subst n
  let checkedInput : Input.Model := ⟨2, m, f, h, q, r, z⟩
  obtain ⟨l, _, hl, hlp, _, _⟩ := cholesky_profile initial.covariance p
  obtain ⟨hrun, hacc⟩ := FloatFilterInitialization.fromCovariance_accuracy
    checkedInput initial l 8 (1 / 2) 2 hl hinput hstate
    (input_symmetric initial.covariance p)
  have hacc' : Kalman.Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy
      (diagonalRadius 2 8 + divisionRadius 2 8 (1 / 2) 2) 0 2
      ⟨initial.mean, l⟩ (state 2 initial) := hacc
  obtain ⟨hv, he, hz, hm⟩ := hacc'
  refine ⟨
    l,
    hrun,
    ?_,
    input_positive _ p,
    FactorStructure.lowerPositive_gram_posDef _ hlp
  ⟩
  refine ⟨hv, ?_, hz, hm⟩
  exact ⟨by positivity, fun i j => (he.2 i j).trans backward_radius_cap⟩

/-- A correlated original input, with all domain premises discharged. -/
theorem correlated_domain_nonempty
    : TwoStateCovarianceDomain #[1.0, 0.25, 0.25, 2.0] := by
  have hq : value (0.25 : Float) = (1 : ℝ) / 4 := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-54 : Int) = _
    norm_num
  have ht : value (2.0 : Float) = (2 : ℝ) := by
    change (4503599627370496 : ℝ) * (2 : ℝ)^(-51 : Int) = _
    norm_num
  refine ⟨by decide, by decide +kernel, rfl, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i <;>
      norm_num [entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.one_value, ht]
  · intro i hi
    interval_cases i <;>
      norm_num [entry, Flare.Matrix.Dense.entry, Flare.Binary64.Arithmetic.one_value, ht]
  · norm_num [entry, Flare.Matrix.Dense.entry, hq]

end Kalman.Proofs.FloatCholeskyDomain
