import Kalman.Proofs.FloatJosephPositionArithmetic
import Kalman.Proofs.JosephPositionCorrection
import Kalman.Implementation.Correctness.JosephPositionCorrection

/-! Computed gain for a correlated two-state prior and one position observation.
The scalar innovation and actual native LDL divisions are derived from the
original operand envelope, without intermediate success premises. -/

namespace Kalman.Proofs.FloatJosephPositionGain

open Matrix hiding transpose
open Kalman.Definitions Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.JosephPositionCorrection
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Definitions.Theorems.JosephPositionCorrection
open Kalman.Proofs.ArithmeticProfiles Kalman.Proofs.ErrorPropagation
open Kalman.Proofs.FloatJosephPositionArithmetic
open Flare.Binary64.Value

set_option maxHeartbeats 1600000

structure GainStages (input : Input.Model) (prior : Input.State) where
  (hp hph innovation pht solution : Array Float)
  computeHP : multiply 1 2 2 input.observation prior.covariance = .ok hp
  computeHPH : multiply 1 2 1 hp (transpose 1 2 input.observation) = .ok hph
  computeInnovation : add hph input.measurementNoise = .ok innovation
  computePHT : multiply 2 2 1 prior.covariance (transpose 1 2 input.observation) = .ok pht
  computeSolution : solveSPD 1 2 innovation (transpose 2 1 pht) = .ok solution
  gain_size : (transpose 1 2 solution).size = 2
  gain_finite : (transpose 1 2 solution).all Float.isFinite = true
  gain_bound : ∀ i j, |matrix 2 1 (transpose 1 2 solution) i j| ≤ 2
  gain_error
    : EntrywiseWithin ((2 : ℝ) ^ (-36 : Int))
        (matrix 2 1 (transpose 1 2 solution))
        (CovarianceRecursion.gain (model (atDimensions 2 1 input)) (state 2 prior))

/-- The fixed observation words decode exactly to the position row. -/
theorem observation_decode (input : Input.Model) (prior : Input.State)
    (d : Domain input prior)
    : matrix 1 2 input.observation = positionRow := by
  rw [d.observation]
  ext i j
  fin_cases i
  fin_cases j <;> norm_num [matrix, Flare.Matrix.Value.matrix, positionRow,
    Flare.Binary64.Arithmetic.zero_value, Flare.Binary64.Arithmetic.one_value]

/-- Original covariance floor implies a positive scalar observed variance. -/
theorem observed_floor (input : Input.Model) (prior : Input.State)
    (d : Domain input prior)
    : (1 / 2 : ℝ) ≤ matrix 2 2 prior.covariance 0 0 := by
  have h := d.prior_floor.diag_nonneg (i := 0)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  linarith

theorem gain_stages (input : Input.Model) (prior : Input.State) (d : Domain input prior)
    : Nonempty (GainStages input prior) := by
  let m : LinearModel.Model 2 1 := model (atDimensions 2 1 input)
  let p : LinearModel.State 2 := state 2 prior
  let sref : ℝ := matrix 2 2 prior.covariance 0 0 + value (input.measurementNoise.getD 0 0.0)
  have hh := observation_decode input prior d
  have hf : input.observation.all Float.isFinite = true := by rw [d.observation]; decide +kernel
  have hb : ∀ i j, |matrix 1 2 input.observation i j| ≤ 1 := by
    rw [hh]
    intro i j
    fin_cases i
    fin_cases j <;> norm_num [positionRow]
  have ht := transpose_bound 1 2 input.observation 1 hf hb
  have htm : matrix 2 1 (transpose 1 2 input.observation) = (matrix 1 2 input.observation).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 1 2 input.observation hf
  have rb : ∀ i j, |matrix 1 1 input.measurementNoise i j| ≤ 3/2 := by
    intro i j
    fin_cases i
    fin_cases j
    change |value (input.measurementNoise.getD 0 0.0)| ≤ 3/2
    rw [abs_of_pos (by linarith [d.noise_lower])]
    exact d.noise_upper
  have hpIdeal : ∀ i j, |(matrix 1 2 input.observation * matrix 2 2 prior.covariance) i j| ≤ 2 := by
    intro i j
    fin_cases i
    simpa [hh, positionRow, Matrix.mul_apply] using d.prior_bound 0 j
  have phtIdeal : ∀ i j, |(matrix 2 2 prior.covariance * (matrix 1 2 input.observation).transpose) i j| ≤ 2 := by
    intro i j
    fin_cases j
    simpa [hh, positionRow, Matrix.mul_apply] using d.prior_bound i 0
  obtain ⟨hp, _, hhp, hps, hpf, ehp⟩ := product 1 2 2 input.observation prior.covariance 1 2
    (by decide) hf d.prior_finite (by norm_num) (by norm_num) (by norm_num) hb d.prior_bound
  have hpb := near_bound hp _ _ 2 3 ehp hpIdeal (by norm_num)
  obtain ⟨hph, _, hhph, hphs, hphf, ehph⟩ := product 1 2 1 hp (transpose 1 2 input.observation) 3 1
    (by decide) hpf ht.1 (by norm_num) (by norm_num) (by norm_num) hpb ht.2
  have ehphOriginal := within_trans ehph (within_mul_right ehp (matrix 2 1 (transpose 1 2 input.observation))
    (by norm_num : (0 : ℝ) ≤ 1) ht.2)
  rw [htm] at ehphOriginal
  have innovationIdeal : matrix 1 2 input.observation * matrix 2 2 prior.covariance *
      (matrix 1 2 input.observation).transpose + matrix 1 1 input.measurementNoise
      = diagonal (fun _ : Fin 1 => sref) :=
    JosephPositionCorrection.innovation_diagonal m p hh
  have hphIdeal : ∀ i j, |(matrix 1 2 input.observation * matrix 2 2 prior.covariance *
      (matrix 1 2 input.observation).transpose) i j| ≤ 2 := by
    intro i j
    fin_cases i
    fin_cases j
    simpa [hh, positionRow, Matrix.mul_apply] using d.prior_bound 0 0
  have hphb := near_bound hph _ _ 2 3 ehphOriginal hphIdeal (by norm_num)
  have ps := sum_profile 1 1 hph input.measurementNoise 3 (3/2) 3 false
    (by decide) hphs hphf d.noise_finite (by norm_num) (by norm_num) (by norm_num) hphb rb
  obtain ⟨s, hs, ss, sf, _⟩ := FloatDenseError.add_accuracy hph input.measurementNoise 3
    ps.exponent_lower ps.exponent_upper hphf d.noise_finite
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using ps.magnitude)
  have es := FloatJosephError.add_within (n := 1) (m := 1) ps hphs hs
  have eref := within_trans es (within_add ehphOriginal (within_refl (matrix 1 1 input.measurementNoise)))
  rw [innovationIdeal] at eref
  have esmall : |value (s.getD 0 0.0) - sref| ≤ (2 : ℝ)^(-38 : Int) := by
    have he := eref.2 0 0
    simp only [Matrix.diagonal_apply_eq] at he
    exact he.trans (by norm_num [sumRadius])
  have slo : 1 ≤ value (s.getD 0 0.0) := by
    have he := (abs_le.mp esmall).1
    have hp0 := observed_floor input prior d
    have hr0 := d.noise_lower
    dsimp only [sref] at he
    norm_num only at he
    linarith
  obtain ⟨pht, _, hpht, _, phtf, epht⟩ := product 2 2 1 prior.covariance (transpose 1 2 input.observation) 2 1
    (by decide) d.prior_finite ht.1 (by norm_num) (by norm_num) (by norm_num) d.prior_bound ht.2
  rw [htm] at epht
  have phtb := near_bound pht _ _ 2 3 epht phtIdeal (by norm_num)
  have bt := transpose_bound 2 1 pht 3 phtf phtb
  have btm : matrix 1 2 (transpose 2 1 pht) = (matrix 2 1 pht).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 1 pht phtf
  have bb : ∀ j, j < 2 → |value ((transpose 2 1 pht).getD j 0.0)| ≤ 3 := by
    intro j hj
    have hb' := bt.2 0 ⟨j, hj⟩
    simpa only [matrix, Flare.Matrix.Value.matrix, Fin.val_zero, Nat.zero_mul, Nat.zero_add] using hb'
  obtain ⟨solution, hsolution, solsize, solfinite, solveError⟩ := scalar_solve s (transpose 2 1 pht) sf bt.1 slo bb
  have kt := Flare.Matrix.Multiplication.transpose_storage 1 2 solution solfinite
  have ktm : matrix 2 1 (transpose 1 2 solution) = (matrix 1 2 solution).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 1 2 solution solfinite
  have sreflo : 1 ≤ sref := by
    have hp0 := observed_floor input prior d
    have hr0 := d.noise_lower
    dsimp only [sref]
    linarith
  have gainError : EntrywiseWithin ((2 : ℝ)^(-36 : Int))
      (matrix 2 1 (transpose 1 2 solution)) (CovarianceRecursion.gain m p) := by
    refine ⟨by positivity, ?_⟩
    intro i j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    rw [ktm]
    change |matrix 1 2 solution 0 i - CovarianceRecursion.gain m p i 0| ≤ _
    rw [JosephPositionCorrection.gain_entry m p hh i]
    have hnum := epht.2 i 0
    have hnum' : |value ((transpose 2 1 pht).getD i.val 0.0) - matrix 2 2 prior.covariance i 0|
        ≤ (2 : ℝ)^(-41 : Int) := by
      have heq : (matrix 2 2 prior.covariance * (matrix 1 2 input.observation).transpose) i 0
          = matrix 2 2 prior.covariance i 0 := by
        simp [hh, positionRow, Matrix.mul_apply]
      rw [heq] at hnum
      have hn := congrArg (fun a : Matrix (Fin 1) (Fin 2) ℝ => a 0 i) btm
      simp only [Matrix.transpose_apply] at hn
      rw [← hn] at hnum
      simpa only [matrix, Flare.Matrix.Value.matrix, Fin.val_zero, Nat.zero_mul, Nat.zero_add] using hnum
    have he := quotient_accuracy _ _ (matrix 2 2 prior.covariance i 0) _ sref slo sreflo
      (d.prior_bound i 0) (solveError i) hnum' esmall
    simpa only [p, m, sref, model, state, atDimensions, matrix, Flare.Matrix.Value.matrix,
      Fin.val_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero] using he
  have idealGainBound : ∀ i j, |CovarianceRecursion.gain m p i j| ≤ 3/2 := by
    intro i j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    have hspos : 0 < p.covariance 0 0 + m.measurementNoise 0 0 := by
      change 0 < sref
      linarith
    rw [JosephPositionCorrection.gain_entry m p hh i, abs_div, abs_of_pos hspos]
    apply (div_le_iff₀ (by change 0 < sref; linarith)).mpr
    have hp0 := observed_floor input prior d
    have hr0 := d.noise_lower
    have hb' := d.prior_bound i 0
    change |matrix 2 2 prior.covariance i 0| ≤ 3/2 * sref
    dsimp only [sref]
    linarith
  have gainBound := near_bound (transpose 1 2 solution) _ _ (3/2) 2 gainError idealGainBound (by norm_num)
  exact ⟨⟨
          hp,
          hph,
          s,
          pht,
          solution,
          hhp,
          hhph,
          hs,
          hpht,
          hsolution,
          by simpa using kt.1,
          kt.2.1,
          gainBound,
          gainError
        ⟩⟩

end Kalman.Proofs.FloatJosephPositionGain
