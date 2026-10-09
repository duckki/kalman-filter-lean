import Kalman.Proofs.FloatDiagonalStorage
import Kalman.Proofs.FloatPrearray

/-! Exact decoded zero preservation in native two-state QR. Diagonal input
blocks have disjoint column support after transposition. The proof follows the
checked division, reflector construction, dot/update and signed retention loops.
Success is conditional here; numerical domains derive it in separate modules. -/

namespace Kalman.Proofs.FloatQRDiagonal

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.FloatDenseError
open Flare.Binary64.Value

set_option maxHeartbeats 800000

private theorem bind_success {α β : Type} (p : Except Kalman.Definitions.Input.Error α)
    (f : α → Except Kalman.Definitions.Input.Error β) (b : β)
    (h : (p >>= f) = .ok b)
    : ∃ a, p = .ok a ∧ f a = .ok b := by
  cases p with
  | error e => simp only [bind, Except.bind, reduceCtorEq] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem finite_success (x result : Float) (h : finite x = .ok result)
    : result = x ∧ x.isFinite = true := by
  by_cases hf : x.isFinite = true
  · rw [finite_ok x hf] at h
    exact ⟨(Except.ok.inj h).symm, hf⟩
  · simp [finite, adapt, Flare.Matrix.Dense.finite, hf] at h

private theorem zero_set (P : Nat → Prop) (a : Array Float) (i : Nat) (x : Float)
    (hz : ∀ j, P j → value (a.getD j 0.0) = 0) (hx : P i → value x = 0)
    : ∀ j, P j → value ((a.set! i x).getD j 0.0) = 0 := by
  intro j hj
  by_cases he : j = i
  · subst j
    by_cases hi : i < a.size
    · simpa [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hi] using hx hj
    · simpa [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hi] using hz i hj
  · simpa [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne (Ne.symm he)] using hz j hj

private theorem sub_zero (a b : Float) (ha : a.isFinite = true) (hb : b.isFinite = true)
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

private theorem scale_finite (indices : List Nat) (x : Nat → Float) (s : Float)
    (hs : s.isFinite = true) (hx : ∀ i ∈ indices, (x i).isFinite = true)
    : (indices.foldl (fun scale i => max scale (x i).abs) s).isFinite = true := by
  induction indices generalizing s with
  | nil => exact hs
  | cons i indices ih =>
      exact ih (max s (x i).abs)
        (Flare.Binary64.Order.max_value s (x i).abs hs
          (Flare.Binary64.Order.abs_value _ (hx i (by simp))).1).1
        (fun j hj => hx j (by simp [hj]))

private theorem scaledSquares_zeros (indices : List Nat) (x : Nat → Float) (scale : Float)
    (v w : Array Float) (s r : Float) (P : Nat → Prop)
    (hs : scale.isFinite = true) (hs0 : value scale ≠ 0)
    (hx : ∀ i ∈ indices, (x i).isFinite = true)
    (hv : v.all Float.isFinite = true)
    (hz : ∀ j, P j → value (v.getD j 0.0) = 0)
    (hx0 : ∀ j ∈ indices, P j → value (x j) = 0)
    (hr : scaledSquares indices x scale v s = .ok (w, r))
    : w.all Float.isFinite = true ∧ ∀ j, P j → value (w.getD j 0.0) = 0 := by
  induction indices generalizing v s with
  | nil =>
      have he : v = w := congrArg Prod.fst (Except.ok.inj hr)
      subst w
      exact ⟨hv, hz⟩
  | cons i indices ih =>
      have hc : scaledSquares (i :: indices) x scale v s = (do
          let q ← finite (x i / scale)
          let term ← finite (q * q)
          let sum ← finite (s + term)
          scaledSquares indices x scale (v.set! i q) sum) := by
        simp [scaledSquares, List.forIn_cons, bind_assoc]
      rw [hc] at hr
      obtain ⟨q, hq, hr⟩ := bind_success _ _ _ hr
      obtain ⟨term, _, hr⟩ := bind_success _ _ _ hr
      obtain ⟨sum, _, hr⟩ := bind_success _ _ _ hr
      obtain ⟨rfl, hqf⟩ := finite_success _ _ hq
      apply ih (v.set! i (x i / scale)) sum
        (fun j hj => hx j (by simp [hj]))
        (Flare.Matrix.Storage.all_set v i _ hv hqf)
        (zero_set P v i _ hz
          (fun hi =>
            (Flare.Binary64.Zero.div_zero _ _ (hx i (by simp)) hs (hx0 i (by simp) hi)
              hs0).2))
        (fun j hj => hx0 j (by simp [hj])) hr

private theorem columnNorm_zeros (size : Nat) (indices : List Nat) (x : Nat → Float)
    (scale norm : Float) (v : Array Float) (P : Nat → Prop)
    (hx : ∀ i ∈ indices, (x i).isFinite = true)
    (hx0 : ∀ i ∈ indices, P i → value (x i) = 0)
    (h : scaledColumnNorm size indices x = .ok (scale, v, norm))
    : v.all Float.isFinite = true ∧ ∀ j, P j → value (v.getD j 0.0) = 0 := by
  have hs : (columnScale indices x).isFinite = true :=
    scale_finite indices x 0.0 (by decide) hx
  unfold scaledColumnNorm at h
  by_cases hg : 0.0 < columnScale indices x
  · simp only [hg, ite_true] at h
    obtain ⟨⟨w, s⟩, hw, h⟩ := bind_success _ _ _ h
    obtain ⟨result, _, h⟩ := bind_success _ _ _ h
    have he : w = v := congrArg (fun t => t.2.1) (Except.ok.inj h)
    subst w
    have hs0 : value (columnScale indices x) ≠ 0 :=
      ne_of_gt
        (by
          simpa only [Flare.Binary64.Arithmetic.zero_value]
            using (Flare.Binary64.Order.lt_iff _ _ (by decide) hs).mp hg)
    exact scaledSquares_zeros indices x _ (Array.replicate size 0.0) v 0.0 s P hs hs0 hx
      (Flare.Matrix.Storage.replicate_storage size).2
      (by
        intro j _
        by_cases hj : j < size <;>
          simp [Array.getD_eq_getD_getElem?, hj, Flare.Binary64.Arithmetic.zero_value])
      hx0 hw
  · simp [hg, bind, Except.bind] at h

private theorem normalize_zeros (indices : List Nat) (v w : Array Float) (norm : Float)
    (P : Nat → Prop) (hn : norm.isFinite = true) (hn0 : value norm ≠ 0)
    (hv : v.all Float.isFinite = true)
    (hz : ∀ j, P j → value (v.getD j 0.0) = 0)
    (h : normalizeVector indices v norm = .ok w)
    : w.all Float.isFinite = true ∧ ∀ j, P j → value (w.getD j 0.0) = 0 := by
  induction indices generalizing v with
  | nil =>
      have he : v = w := Except.ok.inj h
      subst w
      exact ⟨hv, hz⟩
  | cons i indices ih =>
      have hc : normalizeVector (i :: indices) v norm = (do
          let q ← finite (v.getD i 0.0 / norm)
          normalizeVector indices (v.set! i q) norm) := by simp [normalizeVector]
      rw [hc] at h
      obtain ⟨q, hq, h⟩ := bind_success _ _ _ h
      obtain ⟨rfl, hqf⟩ := finite_success _ _ hq
      exact ih (v.set! i _) (Flare.Matrix.Storage.all_set v i _ hv hqf)
        (zero_set P v i _ hz (fun hi => (Flare.Binary64.Zero.div_zero _ _
          (Flare.Matrix.Storage.getD_finite v i hv) hn (hz i hi) hn0).2)) h

private theorem reflector_zeros (first : Nat) (indices : List Nat) (v w : Array Float)
    (norm alpha : Float) (P : Nat → Prop) (hfirst : ¬P first)
    (hv : v.all Float.isFinite = true)
    (hz : ∀ j, P j → value (v.getD j 0.0) = 0)
    (h : householderReflector first indices v norm = .ok (alpha, w))
    : w.all Float.isFinite = true ∧ ∀ j, P j → value (w.getD j 0.0) = 0 := by
  unfold householderReflector at h
  obtain ⟨head, hh, h⟩ := bind_success _ _ _ h
  obtain ⟨squared, _, h⟩ := bind_success _ _ _ h
  obtain ⟨vnorm, hn, h⟩ := bind_success _ _ _ h
  have hnf : vnorm.isFinite = true := (finite_success _ _ hn).1 ▸ (finite_success _ _ hn).2
  by_cases hg : 0.0 < vnorm
  · simp only [hg, ite_true] at h
    obtain ⟨output, hout, h⟩ := bind_success _ _ _ h
    have he : output = w := congrArg Prod.snd (Except.ok.inj h)
    subst output
    have hn0 : value vnorm ≠ 0 :=
      ne_of_gt
        (by
          simpa only [Flare.Binary64.Arithmetic.zero_value]
            using (Flare.Binary64.Order.lt_iff _ _ (by decide) hnf).mp hg)
    exact normalize_zeros indices (v.set! first head) w vnorm P hnf hn0
      (Flare.Matrix.Storage.all_set v first head hv
        ((finite_success _ _ hh).1 ▸ (finite_success _ _ hh).2))
      (zero_set P v first head hz (fun hi => (hfirst hi).elim)) hout
  · simp [hg, bind, Except.bind] at h

private theorem dot_zero (width column : Nat) (indices : List Nat) (v a : Array Float)
    (s : Float) (hv : v.all Float.isFinite = true) (ha : a.all Float.isFinite = true)
    (hs : s.isFinite = true) (hs0 : value s = 0)
    (hz : ∀ i ∈ indices, value (v.getD i 0.0) * value (entry width a i column) = 0)
    : ∃ dot,
        reflectorDot width column indices v a s = .ok dot
        ∧ dot.isFinite = true
        ∧ value dot = 0 := by
  induction indices generalizing s with
  | nil => exact ⟨s, rfl, hs, hs0⟩
  | cons i indices ih =>
      have hp := Flare.Binary64.Zero.mul_zero _ _
        (Flare.Matrix.Storage.getD_finite v i hv)
        (Flare.Matrix.Storage.getD_finite a _ ha) (hz i (by simp))
      have hadd := Flare.Binary64.Zero.add_zero s _ hs hp.1 hs0 hp.2
      obtain ⟨dot, hdot, hf, h0⟩ := ih (s + v.getD i 0.0 * entry width a i column)
        hadd.1 hadd.2 (fun j hj => hz j (by simp [hj]))
      refine ⟨dot, ?_, hf, h0⟩
      have hc : reflectorDot width column (i :: indices) v a s = (do
          let term ← finite (v.getD i 0.0 * entry width a i column)
          let sum ← finite (s + term)
          reflectorDot width column indices v a sum) := by simp [reflectorDot]
      rw [hc, finite_ok (v.getD i 0.0 * entry width a i column) hp.1]
      change (do
        let sum ← finite (s + v.getD i 0.0 * entry width a i column)
        reflectorDot width column indices v a sum) = .ok dot
      rw [finite_ok (s + v.getD i 0.0 * entry width a i column) hadd.1]
      exact hdot

private theorem updates_zeros (width column : Nat) (indices : List Nat)
    (v a output : Array Float) (twice : Float) (P : Nat → Prop)
    (hv : v.all Float.isFinite = true) (ha : a.all Float.isFinite = true)
    (ht : twice.isFinite = true) (ht0 : value twice = 0)
    (hz : ∀ j, P j → value (a.getD j 0.0) = 0)
    (h : reflectorUpdates width column indices v a twice = .ok output)
    : ∀ j, P j → value (output.getD j 0.0) = 0 := by
  induction indices generalizing a with
  | nil =>
      have he : a = output := Except.ok.inj h
      subst output
      exact hz
  | cons i indices ih =>
      have hc : reflectorUpdates width column (i :: indices) v a twice = (do
          let term ← finite (v.getD i 0.0 * twice)
          let x ← finite (entry width a i column - term)
          reflectorUpdates width column indices v (a.set! (i * width + column) x) twice) := by
        simp [reflectorUpdates]
      rw [hc] at h
      obtain ⟨term, hterm, h⟩ := bind_success _ _ _ h
      obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
      obtain ⟨rfl, _⟩ := finite_success _ _ hterm
      obtain ⟨rfl, hxf⟩ := finite_success _ _ hx
      have hp := Flare.Binary64.Zero.mul_zero _ _
        (Flare.Matrix.Storage.getD_finite v i hv) ht (by rw [ht0]; simp)
      exact ih (a.set! _ _) (Flare.Matrix.Storage.all_set a _ _ ha hxf)
        (zero_set P a _ _ hz (fun hi => (sub_zero _ _
          (Flare.Matrix.Storage.getD_finite a _ ha) hp.1 (hz _ hi) hp.2).2)) h

private theorem apply_zeros (width column : Nat) (indices : List Nat)
    (v a output : Array Float) (P : Nat → Prop)
    (hv : v.all Float.isFinite = true) (ha : a.all Float.isFinite = true)
    (cross : ∀ i ∈ indices, value (v.getD i 0.0) * value (entry width a i column) = 0)
    (hz : ∀ j, P j → value (a.getD j 0.0) = 0)
    (h : applyReflector width column indices v a = .ok output)
    : ∀ j, P j → value (output.getD j 0.0) = 0 := by
  obtain ⟨dot, hdot, hdf, hd0⟩ := dot_zero width column indices v a 0.0 hv ha
    (by decide) rfl cross
  have ht := Flare.Binary64.Zero.mul_zero 2.0 dot (by decide) hdf (by rw [hd0]; simp)
  unfold applyReflector at h
  rw [hdot] at h
  simp only [bind, Except.bind] at h
  rw [finite_ok _ ht.1] at h
  exact updates_zeros width column indices v a output _ P hv ha ht.1 ht.2 hz h

/-- A finite tall 4×2 matrix with disjoint even/odd column support has no
decoded fill-in in R₀₁ on successful native QR. There is no magnitude cap. -/
theorem triangularize_disjoint_two (a r : Array Float) (hs : a.size = 8)
    (hf : a.all Float.isFinite = true)
    (hzero : ∀ i j, i < 4 → j < 2 → i % 2 ≠ j → value (entry 2 a i j) = 0)
    (h : triangularize 4 2 a = .ok r)
    : value (entry 2 r 0 1) = 0 := by
  have schedule : triangularize 4 2 a = (do
      let next ← qrIteration 4 2 0 a
      qrIteration 4 2 1 next) := by
    simp [triangularize, qrIterations, List.range_succ, List.forIn_cons, List.forIn_nil,
      -bind_pure_comp]
  rw [schedule] at h
  obtain ⟨next, hnext, hlast⟩ := bind_success _ _ _ h
  have hstorage := FloatQRTriangular.qrIteration_storage 4 2 0 a next (by decide)
    (by decide) hs hf hnext
  have hfirst := hnext
  unfold qrIteration at hfirst
  dsimp only at hfirst
  obtain ⟨⟨scale, v, norm⟩, hnorm, hfirst⟩ := bind_success _ _ _ hfirst
  obtain ⟨⟨alpha, w⟩, hreflect, hfirst⟩ := bind_success _ _ _ hfirst
  obtain ⟨panel, hpanel, hfinish⟩ := bind_success _ _ _ hfirst
  obtain ⟨hvf, hvzero⟩ := columnNorm_zeros 4 (List.range' 0 4)
    (fun i => entry 2 a i 0) scale norm v (fun i => i % 2 = 1)
    (fun i _ => Flare.Matrix.Storage.getD_finite a _ hf) (by
      intro i hi hiz
      have hib : i < 4 := by simpa using hi
      exact hzero i 0 hib (by decide) (by omega)) hnorm
  obtain ⟨hwf, hwzero⟩ := reflector_zeros 0 (List.range' 0 4) v w norm alpha
    (fun i => i % 2 = 1) (by decide) hvf hvzero hreflect
  have happly : applyReflector 2 1 (List.range' 0 4) w a = .ok panel := by
    change applyReflectorColumns 2 [1] (List.range' 0 4) w a = .ok panel at hpanel
    have hc : applyReflectorColumns 2 [1] (List.range' 0 4) w a
        = applyReflector 2 1 (List.range' 0 4) w a := by
      cases hh : applyReflector 2 1 (List.range' 0 4) w a <;>
        simp [applyReflectorColumns, hh, bind, Except.bind, pure, Except.pure]
    exact hc ▸ hpanel
  have hpzero := apply_zeros 2 1 (List.range' 0 4) w a panel
    (fun t => t = 1 ∨ t = 5) hwf hf (by
      intro i hi
      have hib : i < 4 := by simpa using hi
      by_cases hi0 : i % 2 = 1
      · rw [hwzero i hi0]; simp
      · rw [hzero i 1 hib (by decide) hi0]; simp) (by
      intro t ht
      rcases ht with rfl | rfl
      · exact hzero 0 1 (by decide) (by decide) (by decide)
      · exact hzero 2 1 (by decide) (by decide) (by decide)) happly
  have hps := FloatQRTriangular.applyReflector_storage 2 1 (List.range' 0 4) w a panel hf happly
  have hdf : (alpha * scale).isFinite = true := by
    unfold finishColumn at hfinish
    obtain ⟨diagonal, hd, _⟩ := bind_success _ _ _ hfinish
    exact (finite_success _ _ hd).2
  obtain ⟨output, hout, _, _, _, _, hcopy⟩ := FloatQRFinish.finishColumn_storage 4 2 0 0
    [1, 2, 3] panel alpha scale hps.2.1 (hps.1.trans hs) (by decide)
    (by intro i hi; simp at hi; omega)
    (by simp) hdf
  have he : output = next := Except.ok.inj (hout.symm.trans hfinish)
  subst output
  have hnzero : value (entry 2 next 0 1) = 0 := by
    change value (next.getD 1 0.0) = 0
    rw [hcopy 1 (by decide) (by intro i hi; simp at hi; omega)]
    exact hpzero 1 (by simp)
  have hframe := (FloatQRTriangular.qrIteration_storage 4 2 1 next r (by decide) (by decide)
    (hstorage.1.trans hs) hstorage.2.1 hlast).2.2.1
  change value (r.getD 1 0.0) = 0
  rw [hframe 1 (by
    intro i hi j hj
    simp [List.range'] at hi hj
    omega)]
  exact hnzero

/-- Actual signed retention returns a decoded diagonal factor for two finite
diagonal 2×2 blocks. Signed-zero words are permitted. Successful execution is a
premise, independent of the numerical profiles that guarantee it. -/
theorem gramFactor_diagonal_two (a b l : Array Float)
    (ha : a.all Float.isFinite = true) (hb : b.all Float.isFinite = true)
    (da : DecodedDiagonal 2 a) (db : DecodedDiagonal 2 b)
    (h : gramFactor 2 4 (fromCols 2 2 2 a b) = .ok l)
    : DecodedDiagonal 2 l := by
  unfold gramFactor at h
  obtain ⟨r, hqr, hretain⟩ := bind_success _ _ _ h
  let pre := fromCols 2 2 2 a b
  have hpf := FloatPrearray.fromCols_finite 2 2 2 a b ha hb
  have ht := Flare.Matrix.Multiplication.transpose_storage 2 4 pre hpf
  have hts : (transpose 2 4 pre).size = 8 := by simp [transpose, Flare.Matrix.Dense.transpose]
  have hz : ∀ i j, i < 4 → j < 2 → i % 2 ≠ j →
      value (entry 2 (transpose 2 4 pre) i j) = 0 := by
    intro i j hi hj hij
    change value (Flare.Matrix.Dense.entry 2 (Flare.Matrix.Dense.transpose 2 4 pre) i j) = 0
    rw [ht.2.2 i j hi hj]
    change value (entry 4 (fromCols 2 2 2 a b) j i) = 0
    rw [FloatPrearray.fromCols_entry 2 2 2 a b ⟨j, hj⟩ ⟨i, hi⟩]
    by_cases hil : i < 2
    · simp only [hil, ite_true]
      exact da j i hj hil (by omega)
    · simp only [hil, ite_false]
      exact db j (i - 2) hj (by omega) (by omega)
  have hrzero := triangularize_disjoint_two _ r hts ht.2.1 hz hqr
  have hr := FloatQRTriangular.triangularize_structure 4 2 _ r (by decide) hts ht.2.1 hqr
  obtain ⟨output, hout, _, _, hcopy, _, _, _, _⟩ := FloatQRRetain.retainFactor_accuracy 2 r
    (FloatQRTriangular.retainFactor_profile 2 r l hr.2.2.1 hretain)
  have he : output = l := Except.ok.inj (hout.symm.trans hretain)
  subst output
  intro i j hi hj hij
  rw [hcopy i j hi hj]
  interval_cases i <;> interval_cases j
  all_goals try norm_num at hij
  all_goals norm_num [Flare.Binary64.Arithmetic.zero_value]
  rw [(FloatQRRetain.retainedSign_mul_value (entry 2 r 0 0) (entry 2 r 0 1)
    (Flare.Matrix.Storage.getD_finite r _ hr.2.2.1)
    (Flare.Matrix.Storage.getD_finite r _ hr.2.2.1)).2, hrzero, mul_zero]

end Kalman.Proofs.FloatQRDiagonal
