import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRIteration
import Kalman.Proofs.FloatQRRetain

/-! Structural invariants of every successful native QR run. These proofs use
checked writes and exact zero assignments, without a numerical magnitude cap.
The Gram reference is the full stored QR result, not the original prearray. -/

namespace Kalman.Proofs.FloatQRTriangular

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.FloatDenseError
open Flare.Binary64.Value

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

private theorem set_copy (a : Array Float) (k t : Nat) (x : Float) (h : t ≠ k)
    : (a.set! k x).getD t 0.0 = a.getD t 0.0 := by
  simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne (Ne.symm h)]

private theorem reflectorUpdates_cons (width column i : Nat) (indices : List Nat)
    (w a : Array Float) (twice : Float)
    : reflectorUpdates width column (i :: indices) w a twice
      = (do
          let term ← finite (w.getD i 0.0 * twice)
          let x ← finite (entry width a i column - term)
          reflectorUpdates width column indices w (a.set! (i * width + column) x)
            twice) := by
  simp [reflectorUpdates]

/-- Every successful checked update preserves shape, finiteness and unvisited
slots. No bound, distinctness or valid-index premise is needed for this storage fact. -/
theorem reflectorUpdates_storage (width column : Nat) (indices : List Nat)
    (w a output : Array Float) (twice : Float) (hf : a.all Float.isFinite = true)
    (h : reflectorUpdates width column indices w a twice = .ok output)
    : output.size = a.size
      ∧ output.all Float.isFinite = true
      ∧ (∀ t,
          (∀ i ∈ indices, t ≠ i * width + column)
          → output.getD t 0.0 = a.getD t 0.0) := by
  induction indices generalizing a with
  | nil =>
      have he : a = output := by
        simpa [reflectorUpdates, pure, Except.pure, bind, Except.bind] using h
      subst output
      exact ⟨rfl, hf, by simp⟩
  | cons i indices ih =>
      rw [reflectorUpdates_cons] at h
      obtain ⟨term, _, h⟩ := bind_success _ _ _ h
      obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
      have hxf := (finite_success _ _ hx).2
      have hxfinite : x.isFinite = true := (finite_success _ _ hx).1 ▸ hxf
      obtain ⟨hs, hfinite, hcopy⟩ := ih (a.set! (i*width+column) x)
        (Flare.Matrix.Storage.all_set a _ x hf hxfinite) h
      refine ⟨hs.trans (by simp), hfinite, ?_⟩
      intro t ht
      rw [hcopy t (fun j hj => ht j (by simp [hj]))]
      exact set_copy a _ t x (ht i (by simp))

theorem applyReflector_storage (width column : Nat) (indices : List Nat)
    (w a output : Array Float) (hf : a.all Float.isFinite = true)
    (h : applyReflector width column indices w a = .ok output)
    : output.size = a.size
      ∧ output.all Float.isFinite = true
      ∧ (∀ t,
          (∀ i ∈ indices, t ≠ i * width + column)
          → output.getD t 0.0 = a.getD t 0.0) := by
  unfold applyReflector at h
  obtain ⟨dot, _, h⟩ := bind_success _ _ _ h
  obtain ⟨twice, _, h⟩ := bind_success _ _ _ h
  exact reflectorUpdates_storage width column indices w a output twice hf h

private theorem applyReflectorColumns_cons (width column : Nat)
    (columns indices : List Nat) (w a : Array Float)
    : applyReflectorColumns width (column :: columns) indices w a
      = (do
          let next ← applyReflector width column indices w a
          applyReflectorColumns width columns indices w next) := by
  simp [applyReflectorColumns]

theorem applyReflectorColumns_storage (width : Nat) (columns indices : List Nat)
    (w a output : Array Float) (hf : a.all Float.isFinite = true)
    (h : applyReflectorColumns width columns indices w a = .ok output)
    : output.size = a.size
      ∧ output.all Float.isFinite = true
      ∧ OutsidePanel width indices columns a output := by
  induction columns generalizing a with
  | nil =>
      have he : a = output := by
        simpa [applyReflectorColumns, pure, Except.pure, bind, Except.bind] using h
      subst output
      exact ⟨rfl, hf, by simp [OutsidePanel]⟩
  | cons c columns ih =>
      rw [applyReflectorColumns_cons] at h
      obtain ⟨next, hn, h⟩ := bind_success _ _ _ h
      obtain ⟨hns, hnf, hnc⟩ := applyReflector_storage width c indices w a next hf hn
      obtain ⟨hs, hfinite, hcopy⟩ := ih next hnf h
      refine ⟨hs.trans hns, hfinite, ?_⟩
      intro t ht
      rw [hcopy t (fun i hi j hj => ht i hi j (by simp [hj]))]
      exact hnc t (fun i hi => ht i hi c (by simp))

private theorem mem_unit_range (start stop i : Nat)
    : i ∈ List.range' start (stop - start) ↔ start ≤ i ∧ i < stop := by
  rw [List.mem_range']
  constructor
  · rintro ⟨t, ht, he⟩
    simp only [Nat.one_mul] at he
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨i-start, by omega, ?_⟩
    omega

/-- A successful iteration copies every unselected slot and assigns its source
column tail to positive zero, independently of the numerical success profiles. -/
theorem qrIteration_storage (height width pivot : Nat) (a output : Array Float)
    (hh : pivot < height) (hw : pivot < width) (hs : a.size = height * width)
    (hf : a.all Float.isFinite = true) (h : qrIteration height width pivot a = .ok output)
    : output.size = a.size
      ∧ output.all Float.isFinite = true
      ∧ OutsidePanel width (List.range' pivot (height - pivot))
          (pivot :: List.range' (pivot + 1) (width - (pivot + 1))) a output
      ∧ (∀ i, pivot < i → i < height → entry width output i pivot = 0.0) := by
  unfold qrIteration at h
  dsimp only at h
  obtain ⟨⟨scale, v, norm⟩, _, h⟩ := bind_success _ _ _ h
  obtain ⟨⟨alpha, w⟩, _, h⟩ := bind_success _ _ _ h
  obtain ⟨panel, hpanel, hfinish⟩ := bind_success _ _ _ h
  obtain ⟨hps, hpf, hpc⟩ := applyReflectorColumns_storage width
    (List.range' (pivot+1) (width-(pivot+1))) (List.range' pivot (height-pivot))
    w a panel hf hpanel
  have hdiag : (alpha*scale).isFinite = true := by
    unfold finishColumn at hfinish
    obtain ⟨diagonal, hd, _⟩ := bind_success _ _ _ hfinish
    exact (finite_success _ _ hd).2
  obtain ⟨result, hresult, hrs, hrf, _, hrzero, hrcopy⟩ :=
    FloatQRFinish.finishColumn_storage height width pivot pivot
      (List.range' (pivot+1) (height-(pivot+1))) panel alpha scale hpf (hps.trans hs) hw
      (by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hh
        · exact ((mem_unit_range (pivot+1) height i).mp hi).2)
      (by
        intro hi
        have := ((mem_unit_range (pivot+1) height pivot).mp hi).1
        omega) hdiag
  have he : result = output := Except.ok.inj (hresult.symm.trans hfinish)
  subst result
  refine ⟨hrs.trans hps, hrf, ?_, ?_⟩
  · intro t ht
    rw [hrcopy t (ht pivot ((mem_unit_range pivot height pivot).mpr ⟨le_rfl, hh⟩) pivot (by simp))
      (fun i hi => ht i ((mem_unit_range pivot height i).mpr
        ⟨by have := ((mem_unit_range (pivot+1) height i).mp hi).1; omega,
          ((mem_unit_range (pivot+1) height i).mp hi).2⟩) pivot (by simp))]
    exact hpc t (fun i hi j hj => ht i hi j (by simp [hj]))
  · intro i hpi hib
    exact hrzero i ((mem_unit_range (pivot+1) height i).mpr ⟨by omega, hib⟩)

/-- Later iterations preserve all earlier columns as the same stored Float values. -/
theorem qrIteration_earlierColumn (height width pivot : Nat) (a output : Array Float)
    (hh : pivot < height) (hw : pivot < width) (hs : a.size = height * width)
    (hf : a.all Float.isFinite = true) (h : qrIteration height width pivot a = .ok output)
    (column : Nat) (hc : column < pivot)
    : SameColumn width column a output := by
  have hp := (qrIteration_storage height width pivot a output hh hw hs hf h).2.2.1
  apply FloatQRIteration.outsidePanel_sameColumn width
    (List.range' pivot (height - pivot))
    (pivot :: List.range' (pivot + 1) (width - (pivot + 1))) a output hp
    (by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hw
      · exact ((mem_unit_range (pivot+1) width j).mp hj).2)
    column (hc.trans hw)
  intro hj
  rcases List.mem_cons.mp hj with he | hj
  · omega
  · have := ((mem_unit_range (pivot+1) width column).mp hj).1
    omega

/-- Each successful ascending iteration establishes its new source zeros and
preserves every previously processed column. -/
theorem qrIteration_processed (height width pivot : Nat) (a output : Array Float)
    (hh : pivot < height) (hw : pivot < width) (hs : a.size = height * width)
    (hf : a.all Float.isFinite = true) (h : qrIteration height width pivot a = .ok output)
    (hp : ProcessedColumns height width pivot a)
    : output.size = a.size
      ∧ output.all Float.isFinite = true
      ∧ ProcessedColumns height width (pivot + 1) output := by
  obtain ⟨hos, hof, _, hz⟩ := qrIteration_storage height width pivot a output hh hw hs hf h
  refine ⟨hos, hof, ?_⟩
  intro j hj hjb i hib hji
  by_cases hc : j < pivot
  · rw [← qrIteration_earlierColumn height width pivot a output hh hw hs hf h j hc i]
    exact hp j hc hjb i hib hji
  · have he : j = pivot := by omega
    subst j
    exact hz i hji hib

private theorem qrIterations_cons (height width pivot : Nat) (pivots : List Nat)
    (a : Array Float)
    : qrIterations height width (pivot :: pivots) a
      = (do
          let next ← qrIteration height width pivot a
          qrIterations height width pivots next) := by
  simp [qrIterations]

/-- Extraction of the previous ascending pivot loop, including all failures. -/
theorem triangularize_range_schedule (height width : Nat) (a : Array Float)
    : triangularize height width a
      = (do
          let mut a := a
          for pivot in [:width] do
            a ← qrIteration height width pivot a
          return a) := by
  simp [triangularize, qrIterations, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range_eq_range']

/-- Structural loop invariant for a successful consecutive pivot range.
There is no 32-row cap or arithmetic-magnitude condition in this theorem. -/
theorem qrIterations_processed (height width first count : Nat) (a output : Array Float)
    (hh : width ≤ height) (hw : first + count ≤ width) (hs : a.size = height * width)
    (hf : a.all Float.isFinite = true) (hp : ProcessedColumns height width first a)
    (h : qrIterations height width (List.range' first count) a = .ok output)
    : output.size = a.size
      ∧ output.all Float.isFinite = true
      ∧ ProcessedColumns height width (first + count) output := by
  induction count generalizing first a with
  | zero =>
      have he : a = output := by simpa [qrIterations, pure, Except.pure, bind, Except.bind] using h
      subst output
      exact ⟨rfl, hf, by simpa using hp⟩
  | succ count ih =>
      rw [List.range'_succ, qrIterations_cons] at h
      obtain ⟨next, hn, h⟩ := bind_success _ _ _ h
      obtain ⟨hns, hnf, hnp⟩ := qrIteration_processed height width first a next
        (by omega) (by omega) hs hf hn hp
      obtain ⟨hos, hof, hop⟩ := ih (first+1) next (by omega) (hns.trans hs) hnf hnp h
      exact ⟨
        hos.trans hns,
        hof,
        by simpa only [Nat.add_assoc, Nat.add_comm 1 count] using hop
      ⟩

/-- Every successful complete loop has finite rectangular storage and assigned
positive zeros throughout its lower triangle and all extra tall rows. -/
theorem triangularize_structure (height width : Nat) (a r : Array Float)
    (hh : width ≤ height) (hs : a.size = height * width)
    (hf : a.all Float.isFinite = true) (h : triangularize height width a = .ok r)
    : TriangularizationStructure height width a r := by
  have hrun : qrIterations height width (List.range' 0 width) a = .ok r := by
    simpa only [triangularize, List.range_eq_range'] using h
  obtain ⟨hos, hof, hop⟩ := qrIterations_processed height width 0 width a r hh
    (by simp) hs hf (by simp [ProcessedColumns]) hrun
  exact ⟨h, hos.trans hs, hof, by simpa using hop⟩

/-- The full tall result and its retained upper square block have the same
exact column Gram once the proved triangular-zero invariant holds. -/
theorem retainedUpper_gram_eq_full (height width : Nat) (r : Array Float)
    (hh : width ≤ height) (hz : ProcessedColumns height width width r)
    : (retainedUpper width r).transpose * retainedUpper width r
      = (matrix height width r).transpose * matrix height width r := by
  have htop : ∀ k c : Fin width,
      retainedUpper width r k c = value (entry width r k.val c.val) := by
    intro k c
    unfold retainedUpper
    by_cases h : c < k
    · rw [ite_eq_left h, hz c.val c.isLt c.isLt k.val (k.isLt.trans_le hh) h,
        Flare.Binary64.Arithmetic.zero_value]
    · rw [ite_eq_right h]
  ext i j
  change (∑ k : Fin width, retainedUpper width r k i * retainedUpper width r k j)
    = ∑ k : Fin height, value (entry width r k.val i.val) * value (entry width r k.val j.val)
  simp_rw [htop]
  let f := fun k : Nat => value (entry width r k i.val) * value (entry width r k j.val)
  change (∑ k : Fin width, f k.val) = ∑ k : Fin height, f k.val
  rw [Fin.sum_univ_eq_sum_range f width, Fin.sum_univ_eq_sum_range f height]
  apply Finset.sum_subset (Finset.range_mono hh)
  intro k hk hn
  have hkw : width ≤ k := Nat.le_of_not_gt (fun hh => hn (Finset.mem_range.mpr hh))
  dsimp only [f]
  rw [hz i.val i.isLt i.isLt k (Finset.mem_range.mp hk) (i.isLt.trans_le hkw),
    Flare.Binary64.Arithmetic.zero_value, zero_mul]

private theorem retainColumns_cons (rows column : Nat) (columns : List Nat)
    (r l : Array Float)
    : retainColumns rows (column :: columns) r l
      = (do
          unless 0.0 < (entry rows r column column).abs do
            throw Kalman.Definitions.Input.Error.nonpositivePivot
          let next ← copyFactorColumn rows column (List.range' column (rows - column)) r l
          retainColumns rows columns r next) := by
  by_cases h : 0.0 < (entry rows r column column).abs
  · cases hc : copyFactorColumn rows column (List.range' column (rows-column)) r l <;>
      simp [retainColumns, h, hc, bind, Except.bind, pure, Except.pure]
  · simp [retainColumns, h]

private theorem retainColumns_guards (rows : Nat) (columns : List Nat)
    (r l output : Array Float) (h : retainColumns rows columns r l = .ok output)
    : ∀ j ∈ columns, 0.0 < (entry rows r j j).abs := by
  induction columns generalizing l with
  | nil => simp
  | cons c columns ih =>
      rw [retainColumns_cons] at h
      by_cases hg : 0.0 < (entry rows r c c).abs
      · simp only [hg, ite_true] at h
        obtain ⟨next, _, h⟩ := bind_success _ _ _ h
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hg
        · exact ih next h j hj
      · simp only [hg, ite_false] at h
        change (Except.error Kalman.Definitions.Input.Error.nonpositivePivot
          : Except Kalman.Definitions.Input.Error (Array Float)) = .ok output at h
        cases h

/-- A successful retention call on finite storage certifies every stored
retained diagonal is nonzero, even without a numerical QR profile. -/
theorem retainFactor_profile (rows : Nat) (r l : Array Float)
    (hf : r.all Float.isFinite = true) (h : retainFactor rows r = .ok l)
    : RetentionProfile rows r := by
  refine ⟨hf, ?_⟩
  intro j hj
  have hg := retainColumns_guards rows (List.range rows) r
    (Array.replicate (rows*rows) 0.0) l h j (List.mem_range.mpr hj)
  obtain ⟨haf, hav⟩ := Flare.Binary64.Order.abs_value (entry rows r j j)
    (Flare.Matrix.Storage.getD_finite r _ hf)
  have hreal := (Flare.Binary64.Order.lt_iff 0.0 (entry rows r j j).abs (by decide) haf).mp hg
  rw [Flare.Binary64.Arithmetic.zero_value, hav] at hreal
  exact abs_pos.mp hreal

private theorem transpose_storage (rows columns : Nat) (a : Array Float)
    (hs : a.size = rows * columns) (hf : a.all Float.isFinite = true)
    : (transpose rows columns a).size = a.size
      ∧ (transpose rows columns a).all Float.isFinite = true := by
  constructor
  · rw [hs]
    simp [transpose, Flare.Matrix.Dense.transpose]
  · change ((Array.range (rows*columns)).map
      (fun i => entry columns a (i % rows) (i / rows))).all Float.isFinite = true
    rw [Array.all_eq_true]
    intro i hi
    simp only [Array.getElem_map]
    exact Flare.Matrix.Storage.getD_finite a _ hf

/-- Any successful factor call on finite correctly shaped input has a strictly
PD exact Gram equal to the column Gram of its full stored QR result. Success is
conditional; no accuracy bound relative to the original prearray is claimed. -/
theorem gramFactor_structure (rows columns : Nat) (a l : Array Float)
    (hh : rows ≤ columns) (hs : a.size = rows * columns)
    (hf : a.all Float.isFinite = true) (h : gramFactor rows columns a = .ok l)
    : SuccessfulGramFactorStructure rows columns a l := by
  unfold gramFactor at h
  obtain ⟨r, hqr, hretain⟩ := bind_success _ _ _ h
  obtain ⟨hts, htf⟩ := transpose_storage rows columns a hs hf
  have ht := triangularize_structure columns rows (transpose rows columns a) r hh
    ((hts.trans hs).trans (Nat.mul_comm rows columns)) htf hqr
  have p := retainFactor_profile rows r l ht.2.2.1 hretain
  obtain ⟨output, hout, hos, hof, _, _, hlp, hgram, hpd⟩ :=
    FloatQRRetain.retainFactor_accuracy rows r p
  have he : output = l := Except.ok.inj (hout.symm.trans hretain)
  subst output
  exact ⟨r, ht, hretain, hos, hof, hlp,
    hgram.trans (retainedUpper_gram_eq_full columns rows r hh ht.2.2.2), hpd⟩

end Kalman.Proofs.FloatQRTriangular
