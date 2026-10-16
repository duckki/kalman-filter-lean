import Kalman.Proofs.ArithmeticProfiles
import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Proofs.FloatCholeskyDomain

/-! Exact diagonal interpretation and two-state native multiplication/Cholesky
preserve decoded off-diagonal zero, including either signed-zero input. No
symmetry repair is used. FloatQRDiagonal covers native QR separately. -/

namespace Kalman.Proofs.FloatDiagonalStorage

open Matrix
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Flare.Binary64.Value

/-- Subtraction of either signed-zero encoding retains decoded zero. -/
theorem sub_zero (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (ha0 : value a = 0) (hb0 : value b = 0)
    : (a - b).isFinite = true ∧ value (a - b) = 0 := by
  have hf := Flare.Binary64.Nearest.sub_error_nearest a b ha hb
    (by rw [ha0, hb0]; simp)
  refine ⟨hf.1, ?_⟩
  obtain ⟨sa, hsa⟩ := Flare.Binary64.Zero.unpack_zero a ha ha0
  obtain ⟨sb, hsb⟩ := Flare.Binary64.Zero.unpack_zero b hb hb0
  change (Flare.Binary64.Value.modelToReal (Float.Model.pack
    (Float.Model.UnpackedFloat.sub Float.Model.Format.binary64
      a.toModel.unpack b.toModel.unpack))).getD 0 = 0
  rw [hsa, hsb]
  cases sa <;> cases sb <;> rfl

/-- The actual elementwise subtraction preserves decoded diagonal storage.
The ordinary sum profile derives finiteness of all diagonal differences. -/
theorem sub_diagonal_two (a b result : Array Float)
    (p : Kalman.Proofs.ArithmeticProfiles.SumProfile a b 2 true)
    (hs : a.size = 4) (da : DecodedDiagonal 2 a) (db : DecodedDiagonal 2 b)
    (hr : sub a b = .ok result)
    : DecodedDiagonal 2 result := by
  have he (i : Nat) (hi : i < a.size) := Flare.Binary64.Arithmetic.sub_error
    (a.getD i 0.0) (b.getD i 0.0) 2
    (Flare.Matrix.Storage.getD_finite _ _ p.finite_left)
    (Flare.Matrix.Storage.getD_finite _ _ p.finite_right)
    p.exponent_lower p.exponent_upper
    (by simpa only [↓reduceIte, ← sub_eq_add_neg] using p.magnitude i hi)
  have hm : sub a b = .ok ((Array.range a.size).map (fun i => a.getD i 0.0 - b.getD i 0.0)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro i hi
    exact FloatDenseError.finite_ok _ (he i (by simpa using hi)).1
  have eq := Except.ok.inj (hm.symm.trans hr)
  rw [← eq]
  intro i j hi hj hij
  have hidx : i * 2 + j < a.size := by rw [hs]; omega
  have hz := sub_zero (entry 2 a i j) (entry 2 b i j)
    (Flare.Matrix.Storage.getD_finite a _ p.finite_left)
    (Flare.Matrix.Storage.getD_finite b _ p.finite_right)
    (da i j hi hj hij) (db i j hi hj hij)
  simpa [entry, Flare.Matrix.Dense.entry, Array.getD_eq_getD_getElem?, hidx] using hz.2

/-- Rounded elementwise addition preserves decoded diagonal storage, including
both zero signs, on every finite sum profile. -/
theorem add_diagonal_two (a b result : Array Float) (E : Int)
    (p : Kalman.Proofs.ArithmeticProfiles.SumProfile a b E false) (hs : a.size = 4)
    (da : DecodedDiagonal 2 a) (db : DecodedDiagonal 2 b)
    (hr : add a b = .ok result)
    : DecodedDiagonal 2 result := by
  have he (i : Nat) (hi : i < a.size) := Flare.Binary64.Arithmetic.add_error
    (a.getD i 0.0) (b.getD i 0.0) E
    (Flare.Matrix.Storage.getD_finite _ _ p.finite_left)
    (Flare.Matrix.Storage.getD_finite _ _ p.finite_right)
    p.exponent_lower p.exponent_upper
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using p.magnitude i hi)
  have hm : add a b = .ok ((Array.range a.size).map (fun i => a.getD i 0.0 + b.getD i 0.0)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro i hi
    exact FloatDenseError.finite_ok _ (he i (by simpa using hi)).1
  have eq := Except.ok.inj (hm.symm.trans hr)
  rw [← eq]
  intro i j hi hj hij
  have hidx : i * 2 + j < a.size := by rw [hs]; omega
  have hz := Flare.Binary64.Zero.add_zero (entry 2 a i j) (entry 2 b i j)
    (Flare.Matrix.Storage.getD_finite a _ p.finite_left)
    (Flare.Matrix.Storage.getD_finite b _ p.finite_right)
    (da i j hi hj hij) (db i j hi hj hij)
  simpa [entry, Flare.Matrix.Dense.entry, Array.getD_eq_getD_getElem?, hidx] using hz.2

/-- Nonnegative diagonal bounds also bound every decoded stored entry. -/
theorem diagonal_magnitude (n : Nat) (a : Array Float) (cap : ℝ)
    (hd : DecodedDiagonal n a) (hlo : ∀ i, 0 ≤ matrix n n a i i)
    (hhi : ∀ i, matrix n n a i i ≤ cap) (hc : 0 ≤ cap)
    : ∀ i j, |matrix n n a i j| ≤ cap := by
  intro i j
  by_cases eq : i = j
  · subst j
    rw [abs_of_nonneg (hlo i)]
    exact hhi i
  · change |value (entry n a i.val j.val)| ≤ cap
    rw [hd i.val j.val i.isLt j.isLt (fun h => eq (Fin.ext h)), abs_zero]
    exact hc

theorem matrix_diagonal (n : Nat) (a : Array Float) (h : DecodedDiagonal n a)
    : matrix n n a = diagonal (fun i => matrix n n a i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [diagonal_apply_ne _ hij]
    exact h i.val j.val i.isLt j.isLt (fun he => hij (Fin.ext he))

/-- A decoded diagonal factor has an exactly diagonal Real covariance. This
forms its mathematical Gram; no rounded dense materialization is performed. -/
theorem gram_diagonal (n : Nat) (a : Array Float) (h : DecodedDiagonal n a)
    : Kalman.Definitions.FactorRecursion.gram (matrix n n a)
      = diagonal (fun i => (matrix n n a i i) ^ 2) := by
  unfold Kalman.Definitions.FactorRecursion.gram
  rw [matrix_diagonal n a h, diagonal_transpose, diagonal_mul_diagonal]
  simp only [pow_two, diagonal_apply_eq]

theorem transpose_diagonal (n : Nat) (a : Array Float)
    (hf : a.all Float.isFinite = true) (h : DecodedDiagonal n a)
    : DecodedDiagonal n (transpose n n a) := by
  intro i j hi hj hij
  change value (Flare.Matrix.Dense.entry n (Flare.Matrix.Dense.transpose n n a) i j) = 0
  rw [(Flare.Matrix.Multiplication.transpose_storage n n a hf).2.2 i j hi hj]
  exact h j i hj hi hij.symm

private def dot2 (a b c d : Float) : Except Flare.Matrix.DenseError Float := do
  let first ← Flare.Matrix.Dense.finite (a * b)
  let s ← Flare.Matrix.Dense.finite (0.0 + first)
  let second ← Flare.Matrix.Dense.finite (c * d)
  Flare.Matrix.Dense.finite (s + second)

private theorem dot2_zero (a b c d : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hc : c.isFinite = true) (hd : d.isFinite = true)
    (hab : value a * value b = 0) (hcd : value c * value d = 0)
    : ∃ v, dot2 a b c d = .ok v ∧ value v = 0 := by
  have h1 := Flare.Binary64.Zero.mul_zero a b ha hb hab
  have h2 := Flare.Binary64.Zero.add_zero 0.0 (a * b) (by decide) h1.1 rfl h1.2
  have h3 := Flare.Binary64.Zero.mul_zero c d hc hd hcd
  have h4 := Flare.Binary64.Zero.add_zero _ _ h2.1 h3.1 h2.2 h3.2
  exact ⟨
    _,
    by simp [dot2, Flare.Matrix.Dense.finite, h1.1, h2.1, h3.1, h4.1,
      bind, Except.bind],
    h4.2
  ⟩

private theorem store_four (x y z w : Float)
    : ((((Array.replicate 4 0.0).setIfInBounds 0 x).setIfInBounds 1 y).setIfInBounds 2
        z).setIfInBounds
        3 w
      = #[x, y, z, w] :=
  rfl

private theorem multiply_two_schedule (a b : Array Float)
    : Flare.Matrix.Dense.multiply 2 2 2 a b
      = (do
          let x ← dot2 (entry 2 a 0 0) (entry 2 b 0 0) (entry 2 a 0 1) (entry 2 b 1 0)
          let y ← dot2 (entry 2 a 0 0) (entry 2 b 0 1) (entry 2 a 0 1) (entry 2 b 1 1)
          let z ← dot2 (entry 2 a 1 0) (entry 2 b 0 0) (entry 2 a 1 1) (entry 2 b 1 0)
          let w ← dot2 (entry 2 a 1 0) (entry 2 b 0 1) (entry 2 a 1 1) (entry 2 b 1 1)
          return #[x, y, z, w]) := by
  simp [Flare.Matrix.Dense.multiply, dot2, Std.Legacy.Range.forIn_eq_forIn_range',
    List.range', List.forIn_cons, List.forIn_nil, bind_assoc, entry, -bind_pure_comp, store_four]

/-- Zero products and the actual ascending two-term accumulation preserve
decoded diagonality on successful multiplication, without a magnitude bound. -/
theorem multiply_diagonal_two (a b result : Array Float)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (da : DecodedDiagonal 2 a) (db : DecodedDiagonal 2 b)
    (hr : multiply 2 2 2 a b = .ok result)
    : DecodedDiagonal 2 result := by
  have h := (FloatDenseError.adapt_ok _ result).mp hr
  rw [multiply_two_schedule] at h
  have haf (i j : Nat) : (entry 2 a i j).isFinite = true :=
    Flare.Matrix.Storage.getD_finite a (i * 2 + j) ha
  have hbf (i j : Nat) : (entry 2 b i j).isFinite = true :=
    Flare.Matrix.Storage.getD_finite b (i * 2 + j) hb
  obtain ⟨y, hy, hy0⟩ := dot2_zero _ _ _ _ (haf 0 0) (hbf 0 1) (haf 0 1) (hbf 1 1)
    (by rw [db 0 1 (by decide) (by decide) (by decide)]; simp)
    (by rw [da 0 1 (by decide) (by decide) (by decide)]; simp)
  obtain ⟨z, hz, hz0⟩ := dot2_zero _ _ _ _ (haf 1 0) (hbf 0 0) (haf 1 1) (hbf 1 0)
    (by rw [da 1 0 (by decide) (by decide) (by decide)]; simp)
    (by rw [db 1 0 (by decide) (by decide) (by decide)]; simp)
  rw [hy, hz] at h
  cases hx : dot2 (entry 2 a 0 0) (entry 2 b 0 0) (entry 2 a 0 1) (entry 2 b 1 0) <;>
    cases hw : dot2 (entry 2 a 1 0) (entry 2 b 0 1) (entry 2 a 1 1) (entry 2 b 1 1) <;>
    simp_all [bind, Except.bind, pure, Except.pure]
  subst result
  intro i j hi hj hij
  interval_cases i <;> interval_cases j <;>
    simp_all [entry, Flare.Matrix.Dense.entry]

/-- A derived Cholesky profile also yields decoded diagonal storage when the
original covariance is diagonal. The native quotient can retain either zero sign. -/
theorem cholesky_diagonal_two (a : Array Float)
    (p : Kalman.Implementation.Correctness.InputInterpretation.TwoStateCovarianceDomain a)
    (d : DecodedDiagonal 2 a) (l : Array Float) (hl : cholesky 2 a = .ok l)
    : DecodedDiagonal 2 l := by
  have haf (i j : Nat) : (entry 2 a i j).isFinite = true :=
    Flare.Matrix.Storage.getD_finite a (i * 2 + j) p.finite
  obtain ⟨hd, hdf, hdp, _⟩ := FloatResidualError.positiveSqrt_accuracy
    (entry 2 a 0 0) (haf 0 0) (by linarith [p.diagonal_lower 0 (by decide)])
  have hc := Flare.Binary64.Zero.div_zero (entry 2 a 1 0) (entry 2 a 0 0).sqrt
    (haf 1 0) hdf (d 1 0 (by decide) (by decide) (by decide)) hdp.ne'
  rw [FloatCholeskyDomain.cholesky_two_schedule, hd] at hl
  simp only [bind, Except.bind] at hl
  rw [FloatDenseError.finite_ok _ hc.1] at hl
  cases hp : subtractProducts [0] (fun _ => entry 2 a 1 0 / (entry 2 a 0 0).sqrt)
      (fun _ => entry 2 a 1 0 / (entry 2 a 0 0).sqrt) (entry 2 a 1 1) <;>
    simp only [hp] at hl
  · cases hl
  · rename_i pivot
    cases hroot : positiveSqrt pivot <;> simp only [hroot, pure, Except.pure] at hl
    · cases hl
    · cases hl
      intro i j hi hj hij
      interval_cases i <;> interval_cases j <;>
        simp_all [entry, Flare.Matrix.Dense.entry, show value (0.0 : Float) = 0 from rfl]

end Kalman.Proofs.FloatDiagonalStorage
