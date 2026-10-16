import Kalman.Proofs.FloatJosephSolve
import Kalman.Proofs.FloatGainDomain

/-! Original-input analysis of the dense Joseph innovation and optimal-gain
stages, on the fully observed diagonal operating domain. -/

namespace Kalman.Proofs.FloatJosephGain

open Matrix hiding transpose
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.ErrorPropagation
open Flare.Binary64.Value

set_option maxHeartbeats 1200000

/-! ----------------------------------------------------------------------
## Original operands and successful native gain stages
-------------------------------------------------------------------------- -/

structure GainDomain (p h r : Array Float) : Prop where
  prior_finite : p.all Float.isFinite = true
  observation_finite : h.all Float.isFinite = true
  noise_finite : r.all Float.isFinite = true
  prior_diagonal : DecodedDiagonal 2 p
  noise_diagonal : DecodedDiagonal 2 r
  observation_identity : matrix 2 2 h = 1
  prior_floor : ∀ i, (15 : ℝ) / 16 ≤ matrix 2 2 p i i
  prior_cap : ∀ i, matrix 2 2 p i i ≤ (13 : ℝ) / 4
  noise_floor : ∀ i, (1 : ℝ) ≤ matrix 2 2 r i i
  noise_cap : ∀ i, matrix 2 2 r i i ≤ (3 : ℝ) / 2

structure GainStages (p h r : Array Float) where
  (hp hph innovation pht solution : Array Float)
  computeHP : multiply 2 2 2 h p = .ok hp
  computeHPH : multiply 2 2 2 hp (transpose 2 2 h) = .ok hph
  computeInnovation : add hph r = .ok innovation
  computePHT : multiply 2 2 2 p (transpose 2 2 h) = .ok pht
  computeSolution : solveSPD 2 2 innovation (transpose 2 2 pht) = .ok solution
  innovation_size : innovation.size = 4
  innovation_finite : innovation.all Float.isFinite = true
  gain_size : (transpose 2 2 solution).size = 4
  gain_finite : (transpose 2 2 solution).all Float.isFinite = true
  gain_diagonal : DecodedDiagonal 2 (transpose 2 2 solution)
  gain_floor : ∀ i, (3 : ℝ) / 8 ≤ matrix 2 2 (transpose 2 2 solution) i i
  gain_cap : ∀ i, matrix 2 2 (transpose 2 2 solution) i i ≤ (13 : ℝ) / 16
  gain_pointwise
    : ∀ i,
        |matrix 2 2 (transpose 2 2 solution) i i
          - matrix 2 2 p i i / (matrix 2 2 p i i + matrix 2 2 r i i)|
        ≤ (2 : ℝ) ^ (-36 : Int)
  accuracy
    : EntrywiseWithin ((2 : ℝ) ^ (-36 : Int))
        (matrix 2 2 (transpose 2 2 solution))
        (matrix 2 2 p * (matrix 2 2 p + matrix 2 2 r)⁻¹)

/-! ----------------------------------------------------------------------
## Storage bounds and gain perturbation
-------------------------------------------------------------------------- -/

private theorem near_bound (a : Array Float) (reference : Matrix (Fin 2) (Fin 2) ℝ)
    (e cap target : ℝ) (he : EntrywiseWithin e (matrix 2 2 a) reference)
    (hb : ∀ i j, |reference i j| ≤ cap) (hc : cap + e ≤ target)
    : ∀ i j, |matrix 2 2 a i j| ≤ target := by
  intro i j
  have ht := abs_sub_le (matrix 2 2 a i j) (reference i j) 0
  simp only [sub_zero] at ht
  linarith [he.2 i j, hb i j]

private theorem product (a b : Array Float) (A B : ℝ)
    (af : a.all Float.isFinite = true) (bf : b.all Float.isFinite = true)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : A * B ≤ 4)
    (ab : ∀ i j, |matrix 2 2 a i j| ≤ A)
    (bb : ∀ i j, |matrix 2 2 b i j| ≤ B)
    : ∃ result,
        multiply 2 2 2 a b = .ok result
        ∧ result.size = 4
        ∧ result.all Float.isFinite = true
        ∧ EntrywiseWithin (productRadius 2 8) (matrix 2 2 result)
            (matrix 2 2 a * matrix 2 2 b) := by
  have p := FloatGainDomain.product_profile_two a b A B af bf hA hB hm
    (fun i j hi hj => ab ⟨i, hi⟩ ⟨j, hj⟩) (fun i j hi hj => bb ⟨i, hi⟩ ⟨j, hj⟩)
  obtain ⟨x, hx, xs, xf, xe⟩ := FloatDenseError.multiply_entrywise_accuracy
    2 2 2 a b (fun _ _ => (8 : ℝ)) p.inner_le af bf
    (fun _ _ _ _ => p.upper) (fun _ _ _ _ => p.lower) p.mass
  exact ⟨x, hx, xs, xf, ⟨by norm_num [productRadius], xe⟩⟩

private theorem array_bound (a : Array Float) (A : ℝ)
    (h : ∀ i j, |matrix 2 2 a i j| ≤ A) (t : Nat) (ht : t < 4)
    : |value (a.getD t 0.0)| ≤ A := by
  have hi : t / 2 < 2 := by omega
  have hj : t % 2 < 2 := by omega
  have hm := h ⟨t / 2, hi⟩ ⟨t % 2, hj⟩
  have he : t / 2 * 2 + t % 2 = t := by omega
  change |value (a.getD (t / 2 * 2 + t % 2) 0.0)| ≤ A at hm
  simpa only [he] using hm

private theorem ratio_accuracy (x b p s t : ℝ)
    (hs : 1 ≤ s) (hs' : s ≤ 5) (ht : 1 ≤ t) (hx : |x| ≤ 4)
    (hxs : |x - b / s| ≤ (2 : ℝ) ^ (-40 : Int))
    (hbp : |b - p| ≤ (2 : ℝ) ^ (-46 : Int))
    (hst : |t - s| ≤ (2 : ℝ) ^ (-44 : Int))
    : |x - p / t| ≤ (2 : ℝ) ^ (-36 : Int) := by
  have hs0 : s ≠ 0 := by linarith
  have ht0 : 0 < t := by linarith
  have he : x * t - p = x * (t - s) + (x - b / s) * s + (b - p) := by
    field_simp
    ring
  have hb : |x * t - p| ≤ 4 * (2 : ℝ)^(-44 : Int)
      + (2 : ℝ)^(-40 : Int) * 5 + (2 : ℝ)^(-46 : Int) := by
    rw [he]
    calc
      _ ≤ |x * (t - s)| + |(x - b / s) * s| + |b - p| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < s)]
        exact add_le_add
          (add_le_add
            (mul_le_mul hx hst (abs_nonneg _) (by norm_num))
            (mul_le_mul hxs hs' (by linarith) (by positivity)))
          hbp
  rw [show x - p / t = (x * t - p) / t by field_simp, abs_div, abs_of_pos ht0]
  apply (div_le_iff₀ ht0).mpr
  have h := mul_le_mul_of_nonneg_left ht
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(-36 : Int))
  norm_num at hb h ⊢
  linarith

private theorem ideal_gain_bounds (p r : ℝ) (hp : 15 / 16 ≤ p) (hp' : p ≤ 13 / 4)
    (hr : 1 ≤ r) (hr' : r ≤ 3 / 2)
    : 5 / 13 ≤ p / (p + r) ∧ p / (p + r) ≤ 13 / 17 := by
  have ht : 0 < p + r := by linarith
  constructor
  · apply (le_div_iff₀ ht).mpr
    linarith
  · apply (div_le_iff₀ ht).mpr
    linarith

/-! ----------------------------------------------------------------------
## Computed gain from original stored inputs
-------------------------------------------------------------------------- -/

/-- The original stored operands derive every native innovation/gain stage;
accuracy is relative to the original decoded prior and measurement noise. -/
theorem gain_stages (p h r : Array Float) (d : GainDomain p h r)
    : Nonempty (GainStages p h r) := by
  have pb := FloatDiagonalStorage.diagonal_magnitude 2 p (13 / 4) d.prior_diagonal
    (fun i => (by norm_num : (0 : ℝ) ≤ 15 / 16).trans (d.prior_floor i)) d.prior_cap (by norm_num)
  have rb := FloatDiagonalStorage.diagonal_magnitude 2 r (3 / 2) d.noise_diagonal
    (fun i => (by norm_num : (0 : ℝ) ≤ 1).trans (d.noise_floor i)) d.noise_cap (by norm_num)
  have hb : ∀ i j, |matrix 2 2 h i j| ≤ 1 := by
    rw [d.observation_identity]
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hz : DecodedDiagonal 2 h := by
    intro i j hi hj hij
    change matrix 2 2 h ⟨i, hi⟩ ⟨j, hj⟩ = 0
    rw [d.observation_identity]
    exact Matrix.one_apply_ne (fun he => hij (Fin.val_eq_of_eq he))
  have ht := Flare.Matrix.Multiplication.transpose_storage 2 2 h d.observation_finite
  have htm : matrix 2 2 (transpose 2 2 h) = (matrix 2 2 h).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 h d.observation_finite
  have hti : matrix 2 2 (transpose 2 2 h) = 1 := by rw [htm, d.observation_identity, Matrix.transpose_one]
  have htb : ∀ i j, |matrix 2 2 (transpose 2 2 h) i j| ≤ 1 := by
    intro i j
    rw [htm]
    exact hb j i
  obtain ⟨hp, hhp, hps, hpf, ehp⟩ := product h p 1 (13 / 4) d.observation_finite d.prior_finite
    (by norm_num) (by norm_num) (by norm_num) hb pb
  rw [d.observation_identity, Matrix.one_mul] at ehp
  have hpb := near_bound hp _ _ (13 / 4) (7 / 2) ehp pb (by norm_num [productRadius])
  have hpz := FloatDiagonalStorage.multiply_diagonal_two h p hp d.observation_finite d.prior_finite hz d.prior_diagonal hhp
  obtain ⟨hph, hhph, hphs, hphf, ehph⟩ := product hp (transpose 2 2 h) (7 / 2) 1 hpf ht.2.1
    (by norm_num) (by norm_num) (by norm_num) hpb htb
  rw [hti, Matrix.mul_one] at ehph
  have ehph' := within_trans ehph ehp
  have hphb := near_bound hph _ _ (13 / 4) (7 / 2) ehph' pb (by norm_num [productRadius])
  have htz := FloatDiagonalStorage.transpose_diagonal 2 h d.observation_finite hz
  have hphz := FloatDiagonalStorage.multiply_diagonal_two hp (transpose 2 2 h) hph hpf ht.2.1 hpz htz hhph
  have ps : SumProfile hph r 3 false := by
    refine ⟨by norm_num, by norm_num, hphf, d.noise_finite, ?_⟩
    intro t ht'
    have hb' := array_bound hph (7 / 2) hphb t (by omega)
    have hr' := array_bound r (3 / 2) rb t (by omega)
    simpa only [Bool.false_eq_true, ↓reduceIte, show (2 : ℝ)^(3 : Int) = 8 by norm_num]
      using (abs_add_le _ _).trans ((add_le_add hb' hr').trans (by norm_num))
  obtain ⟨s, hs, ss, sf, _⟩ := FloatDenseError.add_accuracy hph r 3
    ps.exponent_lower ps.exponent_upper ps.finite_left ps.finite_right
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using ps.magnitude)
  have es := FloatJosephError.add_within (n := 2) (m := 2) ps hphs hs
  have eref : EntrywiseWithin (sumRadius 3 + (productRadius 2 8 + productRadius 2 8))
      (matrix 2 2 s) (matrix 2 2 p + matrix 2 2 r) := by
    simpa only [add_zero]
      using within_trans es (within_add ehph' (within_refl (matrix 2 2 r)))
  have esmall : EntrywiseWithin ((2 : ℝ)^(-44 : Int))
      (matrix 2 2 s) (matrix 2 2 p + matrix 2 2 r) := by
    refine ⟨by positivity, fun i j => (eref.2 i j).trans ?_⟩
    norm_num [sumRadius, productRadius]
  have sz := FloatDiagonalStorage.add_diagonal_two hph r s 3 ps hphs hphz d.noise_diagonal hs
  have slo : ∀ i, i < 2 → (3 : ℝ) / 2 ≤ value (entry 2 s i i) := by
    intro i hi
    have he := (abs_le.mp (esmall.2 ⟨i, hi⟩ ⟨i, hi⟩)).1
    simp only [Matrix.add_apply] at he
    have ha := d.prior_floor ⟨i, hi⟩
    have hb' := d.noise_floor ⟨i, hi⟩
    norm_num only at he
    change (3 : ℝ) / 2 ≤ matrix 2 2 s ⟨i, hi⟩ ⟨i, hi⟩
    linarith
  have shi : ∀ i, i < 2 → value (entry 2 s i i) ≤ (5 : ℝ) := by
    intro i hi
    have he := (abs_le.mp (esmall.2 ⟨i, hi⟩ ⟨i, hi⟩)).2
    simp only [Matrix.add_apply] at he
    have ha := d.prior_cap ⟨i, hi⟩
    have hb' := d.noise_cap ⟨i, hi⟩
    norm_num only at he
    change matrix 2 2 s ⟨i, hi⟩ ⟨i, hi⟩ ≤ (5 : ℝ)
    linarith
  obtain ⟨pht, hpht, phts, phtf, epht⟩ := product p (transpose 2 2 h) (13 / 4) 1 d.prior_finite ht.2.1
    (by norm_num) (by norm_num) (by norm_num) pb htb
  rw [hti, Matrix.mul_one] at epht
  have phtb := near_bound pht _ _ (13 / 4) (7 / 2) epht pb (by norm_num [productRadius])
  have phtz := FloatDiagonalStorage.multiply_diagonal_two p (transpose 2 2 h) pht d.prior_finite ht.2.1 d.prior_diagonal htz hpht
  have bt := Flare.Matrix.Multiplication.transpose_storage 2 2 pht phtf
  have btm : matrix 2 2 (transpose 2 2 pht) = (matrix 2 2 pht).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 pht phtf
  have bz := FloatDiagonalStorage.transpose_diagonal 2 pht phtf phtz
  have bb : ∀ i j, i < 2 → j < 2 → |value (entry 2 (transpose 2 2 pht) i j)| ≤ (4 : ℝ) := by
    intro i j hi hj
    change |matrix 2 2 (transpose 2 2 pht) ⟨i, hi⟩ ⟨j, hj⟩| ≤ _
    rw [btm]
    exact (phtb ⟨j, hj⟩ ⟨i, hi⟩).trans (by norm_num)
  obtain ⟨kt, hkt, kts, ktf, ekt, ktz⟩ := FloatJosephSolve.solve_accuracy s (transpose 2 2 pht) sf bt.2.1 sz slo shi bb
  have kdiag := ktz bz
  have ktstore := Flare.Matrix.Multiplication.transpose_storage 2 2 kt ktf
  have ktm : matrix 2 2 (transpose 2 2 kt) = (matrix 2 2 kt).transpose :=
    Flare.Matrix.Multiplication.transpose_matrix 2 2 kt ktf
  have kz := FloatDiagonalStorage.transpose_diagonal 2 _ ktf kdiag
  have point : ∀ i, |matrix 2 2 (transpose 2 2 kt) i i
      - matrix 2 2 p i i / (matrix 2 2 p i i + matrix 2 2 r i i)| ≤ (2 : ℝ)^(-36 : Int) := by
    intro i
    have he := ekt.2 i i
    rw [FloatDiagonalStorage.matrix_diagonal 2 s sz,
      RealDiagonalObservation.diagonal_inverse _ (fun j => by have := slo j.val j.isLt; change value (entry 2 s j.val j.val) ≠ 0; linarith),
      Matrix.diagonal_mul] at he
    rw [mul_comm, ← div_eq_mul_inv] at he
    have eb := epht.2 i i
    have eb' : |matrix 2 2 (transpose 2 2 pht) i i - matrix 2 2 p i i| ≤ (2 : ℝ)^(-46 : Int) := by
      rw [btm]
      change |matrix 2 2 pht i i - matrix 2 2 p i i| ≤ _
      convert eb using 1
      norm_num [productRadius]
    have et := esmall.2 i i
    simp only [Matrix.add_apply] at et
    have sq : (3 : ℝ) / 2 ≤ matrix 2 2 s i i := slo i.val i.isLt
    have cap : matrix 2 2 s i i ≤ (5 : ℝ) := shi i.val i.isLt
    have hquot : |matrix 2 2 (transpose 2 2 pht) i i / matrix 2 2 s i i| ≤ 3 := by
      rw [abs_div, abs_of_pos (by linarith : 0 < matrix 2 2 s i i)]
      apply (div_le_iff₀ (by linarith : 0 < matrix 2 2 s i i)).mpr
      rw [btm]
      change |matrix 2 2 pht i i| ≤ _
      linarith [phtb i i]
    have xb : |matrix 2 2 kt i i| ≤ 4 := by
      have hh := abs_sub_le (matrix 2 2 kt i i)
        (matrix 2 2 (transpose 2 2 pht) i i / matrix 2 2 s i i) 0
      simp only [sub_zero] at hh
      norm_num only at he
      linarith
    rw [ktm]
    exact ratio_accuracy _ _ _ _ _ (by linarith) cap
      (by linarith [d.prior_floor i, d.noise_floor i]) xb he eb' (by simpa only [abs_sub_comm] using et)
  have ideal : matrix 2 2 p * (matrix 2 2 p + matrix 2 2 r)⁻¹
      = diagonal (fun i => matrix 2 2 p i i / (matrix 2 2 p i i + matrix 2 2 r i i)) := by
    rw [FloatDiagonalStorage.matrix_diagonal 2 p d.prior_diagonal,
      FloatDiagonalStorage.matrix_diagonal 2 r d.noise_diagonal,
      Matrix.diagonal_add, RealDiagonalObservation.diagonal_inverse _ (fun i => by
        change matrix 2 2 p i i + matrix 2 2 r i i ≠ 0
        linarith [d.prior_floor i, d.noise_floor i]),
      Matrix.diagonal_mul_diagonal]
    simp only [Matrix.diagonal_apply_eq, div_eq_mul_inv]
  refine ⟨⟨
            hp,
            hph,
            s,
            pht,
            kt,
            hhp,
            hhph,
            hs,
            hpht,
            hkt,
            ss.trans hphs,
            sf,
            ktstore.1,
            ktstore.2.1,
            kz,
            ?_,
            ?_,
            point,
            ?_
          ⟩⟩
  · intro i
    have hb' := (ideal_gain_bounds _ _ (d.prior_floor i) (d.prior_cap i) (d.noise_floor i) (d.noise_cap i)).1
    have he := (abs_le.mp (point i)).1
    norm_num only at he
    linarith
  · intro i
    have hb' := (ideal_gain_bounds _ _ (d.prior_floor i) (d.prior_cap i) (d.noise_floor i) (d.noise_cap i)).2
    have he := (abs_le.mp (point i)).2
    norm_num only at he
    linarith
  · refine ⟨by positivity, ?_⟩
    intro i j
    rw [ideal]
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using point i
    · rw [Matrix.diagonal_apply_ne _ hij]
      have hz' := kz i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
      change |value (entry 2 (transpose 2 2 kt) i.val j.val) - 0| ≤ _
      rw [hz', sub_self, abs_zero]
      positivity

end Kalman.Proofs.FloatJosephGain
