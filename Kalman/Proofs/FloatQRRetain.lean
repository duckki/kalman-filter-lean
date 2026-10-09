import Flare.Binary64.SignMultiplication
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatDenseError
import Kalman.Proofs.FactorStructure

/-! Exact sign multiplication and retained-factor conversion. The input reference
is the stored upper block. FloatQRComposition separately bounds whole-QR error;
FloatQRInitialDomain derives success on the supported initial-input domain. -/

namespace Kalman.Proofs.FloatQRRetain

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.FloatDenseError
open Float.Model Float.Model.UnpackedFloat
open Flare.Binary64.Value Flare.Binary64.Arithmetic
open Flare.Binary64.Model.Rounding

/-! Exact scalar sign facts, proved for the full finite domain in FLARE. -/

alias one_mul_value := Flare.Binary64.SignMultiplication.one_mul_value
alias neg_one_mul_value := Flare.Binary64.SignMultiplication.neg_one_mul_value

/-- The runtime diagonal comparison selects exactly the decoded real sign.
Each checked sign product is finite and has zero real error. -/
theorem retainedSign_mul_value (diagonal x : Float)
    (hd : diagonal.isFinite = true) (hx : x.isFinite = true)
    : (retainedSign diagonal * x).isFinite = true
      ∧ value (retainedSign diagonal * x)
        = (if value diagonal < 0 then (-1 : ℝ) else 1) * value x := by
  have ho := Flare.Binary64.Order.lt_iff diagonal 0.0 hd (by decide)
  simp only [zero_value] at ho
  by_cases h : diagonal < 0.0
  · have hr := ho.mp h
    simpa only [retainedSign, ite_eq_left h, ite_eq_left hr, neg_mul, one_mul]
      using neg_one_mul_value x hx
  · have hr : ¬value diagonal < 0 := fun hh => h (ho.mpr hh)
    simpa only [retainedSign, ite_eq_right h, ite_eq_right hr, one_mul] using one_mul_value x hx

theorem retained_diagonal (diagonal : Float) (hd : diagonal.isFinite = true)
    (hn : value diagonal ≠ 0)
    : 0.0 < diagonal.abs
      ∧ value (retainedSign diagonal * diagonal) = |value diagonal| := by
  obtain ⟨haf, hav⟩ := Flare.Binary64.Order.abs_value diagonal hd
  have hp : 0 < |value diagonal| := abs_pos.mpr hn
  refine ⟨
    (Flare.Binary64.Order.lt_iff 0.0 diagonal.abs (by decide) haf).mpr
      (by simpa only [zero_value, hav] using hp),
    ?_
  ⟩
  rw [(retainedSign_mul_value diagonal diagonal hd hd).2]
  by_cases h : value diagonal < 0
  · rw [ite_eq_left h, abs_of_neg h]; ring
  · rw [ite_eq_right h, abs_of_nonneg (le_of_not_gt h), one_mul]

/-- Exact extraction of the original signed transpose/copy block, including
all exceptional-value rejections and empty ranges. -/
theorem retainFactor_schedule (rows : Nat) (r : Array Float)
    : retainFactor rows r
      = (do
          let mut l := Array.replicate (rows * rows) 0.0
          for j in [:rows] do
            let diagonal := entry rows r j j
            unless 0.0 < diagonal.abs do
              throw Kalman.Definitions.Input.Error.nonpositivePivot
            let sign := if diagonal < 0.0 then -1.0 else 1.0
            for i in [j:rows] do
              l := l.set! (i * rows + j) (← finite (sign * entry rows r j i))
          return l) := by
  simp [retainFactor, retainColumns, copyFactorColumn, retainedSign,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range_eq_range']

/-- The extracted retention block preserves the whole old gramFactor schedule. -/
theorem gramFactor_retention_schedule (rows columns : Nat) (a : Array Float)
    : gramFactor rows columns a
      = (do
          let mut r := transpose rows columns a
          for k in [:rows] do
            r ← qrIteration columns rows k r
          let mut l := Array.replicate (rows * rows) 0.0
          for j in [:rows] do
            let diagonal := entry rows r j j
            unless 0.0 < diagonal.abs do
              throw Kalman.Definitions.Input.Error.nonpositivePivot
            let sign := if diagonal < 0.0 then -1.0 else 1.0
            for i in [j:rows] do
              l := l.set! (i * rows + j) (← finite (sign * entry rows r j i))
          return l) := by
  simp [gramFactor, triangularize, qrIterations, retainFactor_schedule,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range_eq_range']

private theorem copyFactorColumn_cons (rows column i : Nat) (indices : List Nat)
    (r l : Array Float)
    : copyFactorColumn rows column (i :: indices) r l
      = (do
          let x ←
            finite (retainedSign (entry rows r column column) * entry rows r column i)
          copyFactorColumn rows column indices r (l.set! (i * rows + column) x)) := by
  simp [copyFactorColumn]

/-- Copying a signed upper row succeeds and preserves every unvisited entry.
Repeated indices are harmless here: each reads the same immutable source. -/
theorem copyFactorColumn_storage (rows column : Nat) (indices : List Nat)
    (r l : Array Float) (hc : column < rows) (hi : ∀ i ∈ indices, i < rows)
    (hr : r.all Float.isFinite = true) (hl : l.size = rows * rows)
    (hf : l.all Float.isFinite = true)
    : ∃ output,
        copyFactorColumn rows column indices r l = .ok output
        ∧ output.size = rows * rows
        ∧ output.all Float.isFinite = true
        ∧ ∀ i j,
            i < rows
            → j < rows
            → entry rows output i j
              = if j = column ∧ i ∈ indices then
                  retainedSign (entry rows r column column) * entry rows r column i
                else
                  entry rows l i j := by
  induction indices generalizing l with
  | nil => exact ⟨l, rfl, hl, hf, by simp⟩
  | cons k indices ih =>
      have hk := hi k (by simp)
      let x := retainedSign (entry rows r column column) * entry rows r column k
      have hx := (retainedSign_mul_value (entry rows r column column) (entry rows r column k)
        (Flare.Matrix.Storage.getD_finite r _ hr) (Flare.Matrix.Storage.getD_finite r _ hr)).1
      obtain ⟨output, hrun, hs, hfinite, hcopy⟩ :=
        ih (l.set! (k * rows + column) x) (fun i hh => hi i (by simp [hh])) (by simpa using hl)
          (Flare.Matrix.Storage.all_set l _ x hf hx)
      refine ⟨output, ?_, hs, hfinite, ?_⟩
      · rw [copyFactorColumn_cons, finite_ok _ hx]
        simpa only [x, bind, Except.bind] using hrun
      · intro i j hib hjb
        rw [hcopy i j hib hjb]
        simp only [Flare.Matrix.Storage.entry_set rows l k column i j x hl hk hc hjb]
        by_cases hcol : j = column
        · subst j
          by_cases hmem : i ∈ indices
          · simp only [hmem, List.mem_cons, or_true, and_self, ite_true]
          · by_cases heq : i = k
            · subst i; simp [hmem, x]
            · simp [hmem, heq]
        · simp [hcol]

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

/-- Signed lower-triangle copies depend only on the immutable stored source.
Unselected columns and entries above the diagonal retain their initial values. -/
theorem retainColumns_storage (rows : Nat) (columns : List Nat) (r l : Array Float)
    (hc : ∀ j ∈ columns, j < rows) (hr : r.all Float.isFinite = true)
    (hn : ∀ j ∈ columns, value (entry rows r j j) ≠ 0)
    (hl : l.size = rows * rows) (hf : l.all Float.isFinite = true)
    : ∃ output,
        retainColumns rows columns r l = .ok output
        ∧ output.size = rows * rows
        ∧ output.all Float.isFinite = true
        ∧ ∀ i j,
            i < rows
            → j < rows
            → entry rows output i j
              = if j ∈ columns ∧ j ≤ i then
                  retainedSign (entry rows r j j) * entry rows r j i
                else
                  entry rows l i j := by
  induction columns generalizing l with
  | nil => exact ⟨l, rfl, hl, hf, by simp⟩
  | cons c columns ih =>
      have hcb := hc c (by simp)
      have hguard := (retained_diagonal (entry rows r c c)
        (Flare.Matrix.Storage.getD_finite r _ hr) (hn c (by simp))).1
      obtain ⟨next, hrun, hs, hfinite, hcopy⟩ := copyFactorColumn_storage rows c
        (List.range' c (rows-c)) r l hcb (by
          intro i hi
          have := (mem_unit_range c rows i).mp hi
          omega) hr hl hf
      obtain ⟨output, hout, hos, hof, hoc⟩ := ih next (fun j hj => hc j (by simp [hj]))
        (fun j hj => hn j (by simp [hj])) hs hfinite
      refine ⟨output, ?_, hos, hof, ?_⟩
      · rw [retainColumns_cons]
        simp only [hguard, ite_true, hrun, bind, Except.bind]
        exact hout
      · intro i j hib hjb
        rw [hoc i j hib hjb, hcopy i j hib hjb]
        have hmem : i ∈ List.range' c (rows-c) ↔ c ≤ i := by
          simpa only [hib, and_true] using mem_unit_range c rows i
        simp only [hmem]
        by_cases htail : j ∈ columns
        · by_cases hle : j ≤ i
          · simp [htail, hle]
          · have hnot : ¬(j = c ∧ c ≤ i) := by rintro ⟨rfl, hh⟩; exact hle hh
            simp [htail, hle, hnot]
        · by_cases heq : j = c
          · subst j
            by_cases hle : c ≤ i <;> simp [htail, hle]
          · simp [htail, heq]

/-- Exact conversion of decoded entries to a signed upper transpose. -/
theorem retained_factor_interpretation (rows : Nat) (r l : Array Float)
    (hr : r.all Float.isFinite = true)
    (hcopy
      : ∀ i j,
          i < rows
          → j < rows
          → entry rows l i j
            = if i < j then
                0.0
              else
                retainedSign (entry rows r j j) * entry rows r j i)
    : Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l
      = (retainedUpper rows r).transpose
        * Matrix.diagonal (fun j : Fin rows => retainedSignValue rows r j.val) := by
  ext i j
  rw [Matrix.mul_diagonal]
  change value (entry rows l i.val j.val)
    = (retainedUpper rows r) j i * retainedSignValue rows r j.val
  rw [hcopy i.val j.val i.isLt j.isLt]
  by_cases h : i < j
  · simp only [show i.val < j.val from h, h, ite_true, retainedUpper, zero_value, zero_mul]
  · simp only [show ¬i.val < j.val from h, h, ite_false, retainedUpper]
    rw [(retainedSign_mul_value (entry rows r j.val j.val) (entry rows r j.val i.val)
      (Flare.Matrix.Storage.getD_finite r _ hr) (Flare.Matrix.Storage.getD_finite r _ hr)).2]
    unfold retainedSignValue
    ring

/-- Retention adds no Gram error relative to the stored upper triangle.
This statement does not assume a triangular-zero invariant for the full QR result. -/
theorem retained_factor_gram (rows : Nat) (r l : Array Float)
    (hr : r.all Float.isFinite = true)
    (hcopy
      : ∀ i j,
          i < rows
          → j < rows
          → entry rows l i j
            = if i < j then
                0.0
              else
                retainedSign (entry rows r j j) * entry rows r j i)
    : Kalman.Definitions.FactorRecursion.gram
        (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)
      = (retainedUpper rows r).transpose * retainedUpper rows r := by
  let d := Matrix.diagonal (fun j : Fin rows => retainedSignValue rows r j.val)
  have hd : d * d.transpose = 1 := by
    simp only [d, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, retainedSignValue]
      split_ifs <;> norm_num
    · simp [h]
  rw [retained_factor_interpretation rows r l hr hcopy]
  change ((retainedUpper rows r).transpose*d)
    * ((retainedUpper rows r).transpose*d).transpose = _
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc d, hd, Matrix.one_mul]

/-- Every finite stored QR result with nonzero diagonals yields a finite lower
factor with positive diagonal, zero conversion error and strictly PD exact Gram.
There is no dimension cap or magnitude headroom assumption in this theorem. -/
theorem retainFactor_accuracy (rows : Nat) (r : Array Float) (p : RetentionProfile rows r)
    : RetentionAccuracy rows r := by
  obtain ⟨l, hrun, hs, hf, hcopy⟩ := retainColumns_storage rows (List.range rows) r
    (Array.replicate (rows*rows) 0.0) (by simp) p.matrix_finite
    (by simpa using p.diagonal_nonzero)
    (Array.size_replicate ..) (Flare.Matrix.Storage.replicate_storage _).2
  have hentry : ∀ i j, i < rows → j < rows →
      entry rows l i j = if i < j then 0.0
        else retainedSign (entry rows r j j) * entry rows r j i := by
    intro i j hib hjb
    rw [hcopy i j hib hjb]
    simp only [List.mem_range.mpr hjb, true_and]
    have hz : entry rows (Array.replicate (rows*rows) 0.0) i j = 0.0 := by
      change (Array.replicate (rows*rows) (0.0 : Float)).getD (i*rows+j) 0.0 = 0.0
      by_cases hi : i*rows+j < rows*rows <;> simp [Array.getD_eq_getD_getElem?, hi]
    by_cases h : i < j
    · simp [h, not_le.mpr h, hz]
    · simp [h, le_of_not_gt h]
  have hd : ∀ j < rows, value (entry rows l j j) = |value (entry rows r j j)| := by
    intro j hj
    rw [hentry j j hj hj, ite_eq_right (by omega : ¬j < j)]
    exact (retained_diagonal _ (Flare.Matrix.Storage.getD_finite r _ p.matrix_finite)
      (p.diagonal_nonzero j hj)).2
  have hp : Kalman.Definitions.FactorRecursion.LowerPositive
      (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l) := by
    constructor
    · intro i j hij
      change value (entry rows l i.val j.val) = 0
      rw [hentry i.val j.val i.isLt j.isLt, ite_eq_left (show i.val < j.val from hij), zero_value]
    · intro j
      change 0 < value (entry rows l j.val j.val)
      rw [hd j.val j.isLt]
      exact abs_pos.mpr (p.diagonal_nonzero j.val j.isLt)
  exact ⟨l, hrun, hs, hf, hentry, hd, hp,
    retained_factor_gram rows r l p.matrix_finite hentry,
    Kalman.Proofs.FactorStructure.lowerPositive_gram_posDef _ hp⟩

end Kalman.Proofs.FloatQRRetain
