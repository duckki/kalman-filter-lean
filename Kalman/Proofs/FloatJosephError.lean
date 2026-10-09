import Kalman.Proofs.FloatDenseError
import Kalman.Proofs.ErrorPropagation
import Kalman.Proofs.ArithmeticProfiles

/-! A composed forward-error bound for the actual direct Joseph covariance
evaluation, relative to the same stored prior, noise, observation, and gain.
It covers every multiply and sum in that kernel. Gain and prediction error are
separate from evaluation error; this does not assume an exact computed gain. -/

namespace Kalman.Proofs.FloatJosephError

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.ErrorPropagation

theorem product_within {rows inner columns : Nat} {a b r : Array Float} {M : ℝ}
    (p : ProductProfile rows inner columns a b M)
    (h : multiply rows inner columns a b = .ok r)
    : r.size = rows * columns
      ∧ r.all Float.isFinite = true
      ∧ EntrywiseWithin (productRadius inner M) (matrix rows columns r)
          (matrix rows inner a * matrix inner columns b) := by
  obtain ⟨s, hs, hsize, hf, he⟩ := Kalman.Proofs.FloatDenseError.multiply_entrywise_accuracy
    rows inner columns a b (fun _ _ => M) p.inner_le p.finite_left p.finite_right
    (fun _ _ _ _ => p.upper) (fun _ _ _ _ => p.lower) p.mass
  have hsr : s = r := Except.ok.inj (hs.symm.trans h)
  subst s
  have hM : 0 ≤ M := (zpow_pos (by norm_num : (0 : ℝ) < 2) (-1022 : Int)).le.trans p.lower
  exact ⟨hsize, hf, by unfold productRadius; positivity, he⟩

theorem subtract_within {n m : Nat} {a b r : Array Float} {E : Int}
    (p : SumProfile a b E true) (has : a.size = n * m) (h : sub a b = .ok r)
    : EntrywiseWithin (sumRadius E) (matrix n m r) (matrix n m a - matrix n m b) := by
  obtain ⟨s, hs, _, _, he⟩ := Kalman.Proofs.FloatDenseError.sub_accuracy a b E
    p.exponent_lower p.exponent_upper p.finite_left p.finite_right (by
      simpa only [Bool.true_eq_false, ↓reduceIte, sub_eq_add_neg] using p.magnitude)
  have hsr : s = r := Except.ok.inj (hs.symm.trans h)
  subst s
  refine ⟨zpow_pos (by norm_num) _ |>.le, fun i j => ?_⟩
  exact he (i.val * m + j.val)
    (by
      rw [has]
      have := Nat.mul_le_mul_right m i.isLt
      rw [Nat.succ_mul] at this
      omega)

theorem add_within {n m : Nat} {a b r : Array Float} {E : Int}
    (p : SumProfile a b E false) (has : a.size = n * m) (h : add a b = .ok r)
    : EntrywiseWithin (sumRadius E) (matrix n m r) (matrix n m a + matrix n m b) := by
  obtain ⟨s, hs, _, _, he⟩ := Kalman.Proofs.FloatDenseError.add_accuracy a b E
    p.exponent_lower p.exponent_upper p.finite_left p.finite_right (by
      simpa only [Bool.false_eq_true, ↓reduceIte] using p.magnitude)
  have hsr : s = r := Except.ok.inj (hs.symm.trans h)
  subst s
  refine ⟨zpow_pos (by norm_num) _ |>.le, fun i j => ?_⟩
  exact he (i.val * m + j.val)
    (by
      rw [has]
      have := Nat.mul_le_mul_right m i.isLt
      rw [Nat.succ_mul] at this
      omega)

theorem identity_matrix (n : Nat)
    : matrix n n (identity n) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  have hn : 0 < n := Nat.pos_of_ne_zero (by intro hz; subst n; exact Fin.elim0 i)
  have hidx : i.val * n + j.val < n * n := by
    have := Nat.mul_le_mul_right n i.isLt
    rw [Nat.succ_mul] at this
    omega
  have hd : (i.val * n + j.val) / n = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have hm : (i.val * n + j.val) % n = j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  simp [Flare.Matrix.Value.matrix, identity, Flare.Matrix.Dense.identity, hidx, hd, hm,
    Fin.ext_iff, Matrix.one_apply]
  split_ifs <;> simp [Flare.Binary64.Arithmetic.one_value, Flare.Binary64.Arithmetic.zero_value]

/-- Compatibility name; the shared radius is defined in `Proofs.ArithmeticProfiles`. -/
noncomputable abbrev josephRadius :=
  @Kalman.Proofs.ArithmeticProfiles.josephRadius

theorem joseph_evaluation_error {input : Input.Model} {prior : Input.State}
    {k output : Array Float} (p : JosephProfile input prior k output) (P W K : ℝ)
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hK : 0 ≤ K)
    (hp
      : ∀ i j,
          |matrix input.stateDimension input.stateDimension prior.covariance i j| ≤ P)
    (hw
      : ∀ i j,
          |((1 : Matrix (Fin input.stateDimension) (Fin input.stateDimension) ℝ)
            - matrix input.stateDimension input.measurementDimension k
              * matrix input.measurementDimension input.stateDimension input.observation)
            i j|
          ≤ W)
    (hk : ∀ i j, |matrix input.stateDimension input.measurementDimension k i j| ≤ K)
    : Kalman.Implementation.CovarianceFilter.covarianceUnchecked .joseph input prior k
        = .ok output
      ∧ EntrywiseWithin (josephRadius p P W K)
          (matrix input.stateDimension input.stateDimension output)
          (CovarianceRecursion.joseph (model input) (state input.stateDimension prior)
            (matrix input.stateDimension input.measurementDimension k)) := by
  refine ⟨?_, ?_⟩
  · simp [Kalman.Implementation.CovarianceFilter.covarianceUnchecked, p.computeKH, p.computeW,
      p.computeWP, p.computeFirst, p.computeKR, p.computeSecond, p.computeSum, bind, Except.bind]
  · let n := input.stateDimension
    let m := input.measurementDimension
    let A := matrix n n prior.covariance
    let B := matrix n m k
    let D := (1 : Matrix (Fin n) (Fin n) ℝ) - B * matrix m n input.observation
    have ekh := (product_within p.profileKH p.computeKH).2.2
    have ew := subtract_within (n := n) (m := n) p.profileW (by simp [identity, Flare.Matrix.Dense.identity, n]) p.computeW
    rw [identity_matrix] at ew
    have ewideal := within_trans ew (within_sub (within_refl 1) ekh)
    simp only [zero_add] at ewideal
    have ewp := within_trans (product_within p.profileWP p.computeWP).2.2
      (within_mul ewideal (within_refl A) hW hP hw hp)
    simp only [mul_zero, add_zero] at ewp
    have ewpt := within_transpose ewideal
    rw [← Flare.Matrix.Multiplication.transpose_matrix n n p.w p.profileWP.finite_left] at ewpt
    have efirst := within_trans (product_within p.profileFirst p.computeFirst).2.2
      (within_mul ewp ewpt (by positivity : 0 ≤ (n : ℝ) * W * P) hW
        (product_magnitude D A W P hw hp) (fun i j => hw j i))
    have ekr := (product_within p.profileKR p.computeKR).2.2
    let TK := matrix input.measurementDimension input.stateDimension
      (transpose input.stateDimension input.measurementDimension k)
    have htk : TK = B.transpose := Flare.Matrix.Multiplication.transpose_matrix
      input.stateDimension input.measurementDimension k p.profileKH.finite_left
    have hk' : ∀ i j, |TK i j| ≤ K := by
      intro i j
      calc
        _ = |B.transpose i j| := congrArg (fun X => |X i j|) htk
        _ ≤ K := hk j i
    have esecond' := within_trans (product_within p.profileSecond p.computeSecond).2.2
      (within_mul_right ekr TK hK hk')
    have esum := add_within (n := n) (m := n) p.profileSum (product_within p.profileFirst p.computeFirst).1 p.computeSum
    have eresult := within_trans esum (within_add efirst esecond')
    convert eresult using 1
    · unfold josephRadius Kalman.Proofs.ArithmeticProfiles.josephRadius
      dsimp only [n, m]
      ring
    · dsimp only [CovarianceRecursion.joseph, model, state]
      rw [htk]

end Kalman.Proofs.FloatJosephError
