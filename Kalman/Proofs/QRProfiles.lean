import Kalman.Implementation.OrthogonalFactorization
import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Definitions.OrthogonalFactorization
import Mathlib.Analysis.Real.Sqrt

/-!
# QR profiles and intermediate comparison relations

Native QR contracts and structural postconditions. Input profiles describe
storage, magnitudes and source witnesses, not success or desired error bounds.
Numerical witnesses are in FloatQRNorm, FloatQRReflector, FloatQRApplication,
FloatQRFinish, FloatQRIteration, FloatQRRetain, FloatQRGram and FloatQRComposition.
FloatQRDomain derives prefix magnitude and spectral enclosures from initial Gram bounds.
FloatQRSourceTail derives the active source witness from those margins and prior zeros.
FloatQRInitialDomain closes the initial-input induction on the supported eight-row domain.
The full QR Gram allowance uses operand profiles at every actual prefix.
FloatQRTriangular separately proves structure conditional on successful runs.
Broader QR domains and full-filter error propagation remain separate obligations. -/

namespace Kalman.Proofs.QRProfiles

open Flare.Binary64.Value
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Implementation.LinearAlgebra

noncomputable section

/-! ----------------------------------------------------------------------
## Scaled column norm
-------------------------------------------------------------------------- -/

structure ColumnProfile (size : Nat) (indices : List Nat) (x : Nat → Float) : Prop where
  length_le : indices.length ≤ 32
  in_bounds : ∀ i ∈ indices, i < size
  finite : ∀ i ∈ indices, (x i).isFinite = true
  nonzero : ∃ i ∈ indices, value (x i) ≠ 0

/-- Exact squared norm after division by the exactly decoded stored scale. -/
def normalizedSquares (indices : List Nat) (x : Nat → Float) (scale : Float) : ℝ :=
  (indices.map (fun i => (value (x i) / value scale) ^ 2)).sum

/-- Dimension-sensitive division/square/accumulation allowance. -/
def squareSumRadius (terms : Nat) : ℝ := terms * (terms + 20) * (2 : ℝ) ^ (-52 : Int)

/-- Includes division, separately rounded squares/additions, and native sqrt.
The allowance bounds squared normalized norm error; it is dimensionless. -/
def columnNormRadius (terms : Nat) : ℝ :=
  squareSumRadius terms
  + (2 * (2 : ℝ) ^ (-53 : Int) + ((2 : ℝ) ^ (-53 : Int)) ^ 2)
    * (terms + squareSumRadius terms)

/-- ColumnNormAccuracy
Proof witness: `Kalman.Proofs.FloatQRNorm.scaledColumnNorm_accuracy`. -/
def ColumnNormAccuracy (size : Nat) (indices : List Nat) (x : Nat → Float) : Prop :=
  ∃ scale v norm,
    scaledColumnNorm size indices x = .ok (scale, v, norm)
    ∧ scale = columnScale indices x
    ∧ scale.isFinite = true
    ∧ 0 < value scale
    ∧ v.size = size
    ∧ v.all Float.isFinite = true
    ∧ (∀ i, v.getD i 0.0 = if i ∈ indices then x i / scale else 0.0)
    ∧ (∀ i ∈ indices,
        |value (v.getD i 0.0) - value (x i) / value scale| ≤ (2 : ℝ) ^ (-51 : Int))
    ∧ norm.isFinite = true
    ∧ 0 < value norm
    ∧ |(value norm) ^ 2 - normalizedSquares indices x scale|
      ≤ columnNormRadius indices.length
    ∧ |value norm - Real.sqrt (normalizedSquares indices x scale)|
      ≤ columnNormRadius indices.length

/-! ----------------------------------------------------------------------
## Reflector construction
-------------------------------------------------------------------------- -/

/-- Local operands supplied by the column-norm stage. These are magnitude and
storage conditions, not assumed execution success or assumed error conclusions. -/
structure ReflectorProfile (first : Nat) (indices : List Nat) (v : Array Float)
    (norm : Float)
    : Prop where
  length_le : indices.length ≤ 32
  nodup : indices.Nodup
  first_mem : first ∈ indices
  in_bounds : ∀ i ∈ indices, i < v.size
  finite : v.all Float.isFinite = true
  magnitude : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 2
  norm_finite : norm.isFinite = true
  norm_lower : (1 : ℝ) / 2 ≤ value norm
  norm_upper : value norm ≤ 6

/-- Exact decoding of the vector after the checked first-component subtraction.
Only that subtraction is rounded here; this is the normalization reference. -/
def constructedVector (first : Nat) (v : Array Float) (norm : Float) : Array Float :=
  v.set! first (v.getD first 0.0 - reflectorAlpha (v.getD first 0.0) norm)

def vectorSquares (indices : List Nat) (v : Array Float) : ℝ :=
  (indices.map (fun i => (value (v.getD i 0.0)) ^ 2)).sum

def reflectorSumRadius (terms : Nat) : ℝ := terms * (2 : ℝ) ^ (-39 : Int)

/-- Component and squared-unit-norm allowance, retaining the actual active length. -/
def reflectorRadius (terms : Nat) : ℝ := (9 * terms + 5) * (2 : ℝ) ^ (-50 : Int)

/-- Completed by FloatQRReflector. The reference is the exactly decoded
constructed vector normalized over the active indices. It is not yet a bound
for reflector application to another column or for whole QR.
Proof witness: `Kalman.Proofs.FloatQRReflector.householderReflector_accuracy`. -/
def ReflectorAccuracy (first : Nat) (indices : List Nat) (v : Array Float) (norm : Float)
    : Prop :=
  ∃ alpha w,
    householderReflector first indices v norm = .ok (alpha, w)
    ∧ alpha = reflectorAlpha (v.getD first 0.0) norm
    ∧ alpha.isFinite = true
    ∧ |value alpha| = value norm
    ∧ (v.getD first 0.0 - alpha).isFinite = true
    ∧ |value (v.getD first 0.0 - alpha) - (value (v.getD first 0.0) - value alpha)|
      ≤ (2 : ℝ) ^ (-49 : Int)
    ∧ (1 : ℝ) / 4 ≤ |value (v.getD first 0.0 - alpha)|
    ∧ w.size = v.size
    ∧ w.all Float.isFinite = true
    ∧ (∀ i, i ∉ indices → w.getD i 0.0 = v.getD i 0.0)
    ∧ (∀ i ∈ indices,
        |value (w.getD i 0.0)
          - value ((constructedVector first v norm).getD i 0.0)
            / Real.sqrt (vectorSquares indices (constructedVector first v norm))|
        ≤ reflectorRadius indices.length)
    ∧ |vectorSquares indices w - 1| ≤ reflectorRadius indices.length

/-- Original finite column inputs suffice for both local stages. The caller
selects a valid first component and visits each active index once.
Proof witness: `Kalman.Proofs.FloatQRReflector.scaledColumn_reflector_accuracy`. -/
def ColumnReflectorAccuracy (size first : Nat) (indices : List Nat) (x : Nat → Float)
    : Prop :=
  ∃ scale v norm,
    scaledColumnNorm size indices x = .ok (scale, v, norm)
    ∧ v.size = size
    ∧ ReflectorAccuracy first indices v norm

/-! ----------------------------------------------------------------------
## Reflector application
-------------------------------------------------------------------------- -/

/-- Local application domain. M bounds the active stored target column, not its
final result. No native success, dot-product error, or output error is assumed. -/
structure ApplicationProfile (height width column : Nat) (indices : List Nat)
    (v a : Array Float) (M : ℝ)
    : Prop where
  length_le : indices.length ≤ 32
  nodup : indices.Nodup
  column_bound : column < width
  in_bounds : ∀ i ∈ indices, i < height
  vector_size : v.size = height
  matrix_size : a.size = height * width
  vector_finite : v.all Float.isFinite = true
  matrix_finite : a.all Float.isFinite = true
  vector_magnitude : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 2
  budget_lower : (2 : ℝ) ^ (-1022 : Int) ≤ M
  budget_upper : M ≤ (2 : ℝ) ^ (900 : Int)
  column_magnitude : ∀ i ∈ indices, |value (entry width a i column)| ≤ M

/-- Exact dot product of the same stored operands, before any column writes. -/
def reflectorDotValue (width column : Nat) (indices : List Nat) (v a : Array Float) : ℝ :=
  (indices.map (fun i => value (v.getD i 0.0) * value (entry width a i column))).sum

def reflectorAppliedValue (width column : Nat) (indices : List Nat) (v a : Array Float)
    (i : Nat)
    : ℝ :=
  value (entry width a i column)
  - 2 * value (v.getD i 0.0) * reflectorDotValue width column indices v a

def applicationRadius (terms : Nat) (M : ℝ) : ℝ :=
  (terms + 1) * (2 : ℝ) ^ (-42 : Int) * M

/-- Actual application compared with I - 2wwᵀ for the supplied stored vector w.
Its closeness to an exactly normalized reflector is a separate composition.
Proof witness: `Kalman.Proofs.FloatQRApplication.applyReflector_accuracy`. -/
def ApplicationAccuracy (width column : Nat) (indices : List Nat) (v a : Array Float)
    (M : ℝ)
    : Prop :=
  ∃ output,
    applyReflector width column indices v a = .ok output
    ∧ output.size = a.size
    ∧ output.all Float.isFinite = true
    ∧ (∀ t, (∀ i ∈ indices, t ≠ i * width + column) → output.getD t 0.0 = a.getD t 0.0)
    ∧ (∀ i ∈ indices,
        |value (entry width output i column)
          - reflectorAppliedValue width column indices v a i|
        ≤ applicationRadius indices.length M)

/-- Incoming target-column conditions for composition with a constructed
reflector. The source ColumnProfile supplies active-index and length conditions. -/
structure TargetColumnProfile (height width column : Nat) (indices : List Nat)
    (a : Array Float) (M : ℝ)
    : Prop where
  column_bound : column < width
  matrix_size : a.size = height * width
  matrix_finite : a.all Float.isFinite = true
  budget_lower : (2 : ℝ) ^ (-1022 : Int) ≤ M
  budget_upper : M ≤ (2 : ℝ) ^ (900 : Int)
  column_magnitude : ∀ i ∈ indices, |value (entry width a i column)| ≤ M

def constructedUnitComponent (first : Nat) (indices : List Nat)
    (v : Array Float) (norm : Float) (i : Nat)
    : ℝ :=
  value ((constructedVector first v norm).getD i 0.0)
  / Real.sqrt (vectorSquares indices (constructedVector first v norm))

/-- Exact normalized-reflector application, still using the decoded stored
constructed vector from the preceding subtraction and the same target column. -/
def constructedAppliedValue (width column first : Nat) (indices : List Nat)
    (v : Array Float) (norm : Float) (a : Array Float) (i : Nat)
    : ℝ :=
  value (entry width a i column)
  - 2 * constructedUnitComponent first indices v norm i
    * (indices.map
        (fun j =>
          constructedUnitComponent first indices v norm j
          * value (entry width a j column))).sum

def constructedApplicationRadius (terms : Nat) (M : ℝ) : ℝ :=
  applicationRadius terms M + 6 * terms * reflectorRadius terms * M

/-- Three actual native stages, starting from original finite column inputs.
The final comparison accounts for stored-reflector error as well as application
rounding; it does not yet compare to an ideal QR factorization of the original matrix.
Proof witness: `Kalman.Proofs.FloatQRApplication.scaledColumn_applyReflector_accuracy`. -/
def ColumnApplicationAccuracy (height width column first : Nat) (indices : List Nat)
    (x : Nat → Float) (a : Array Float) (M : ℝ)
    : Prop :=
  ∃ scale v norm alpha w output,
    scaledColumnNorm height indices x = .ok (scale, v, norm)
    ∧ householderReflector first indices v norm = .ok (alpha, w)
    ∧ applyReflector width column indices w a = .ok output
    ∧ output.size = a.size
    ∧ output.all Float.isFinite = true
    ∧ (∀ t, (∀ i ∈ indices, t ≠ i * width + column) → output.getD t 0.0 = a.getD t 0.0)
    ∧ (∀ i ∈ indices,
        |value (entry width output i column)
          - reflectorAppliedValue width column indices w a i|
        ≤ applicationRadius indices.length M)
    ∧ (∀ i ∈ indices,
        |value (entry width output i column)
          - constructedAppliedValue width column first indices v norm a i|
        ≤ constructedApplicationRadius indices.length M)

/-! ----------------------------------------------------------------------
## Source-column finishing
-------------------------------------------------------------------------- -/

/-- Original stored source-column domain for diagonal rescaling and forced zeros.
The active list is first :: tail. The scale witness and entry cap leave explicit
underflow/overflow headroom; native success or annihilation error is not assumed. -/
structure SourceColumnProfile (height width column first : Nat) (tail : List Nat)
    (a : Array Float)
    : Prop where
  length_le : (first :: tail).length ≤ 32
  tail_nodup : tail.Nodup
  first_not_tail : first ∉ tail
  column_bound : column < width
  in_bounds : ∀ i ∈ first :: tail, i < height
  matrix_size : a.size = height * width
  matrix_finite : a.all Float.isFinite = true
  entry_upper
    : ∀ i ∈ first :: tail, |value (entry width a i column)| ≤ (2 : ℝ) ^ (900 : Int)
  scale_witness
    : ∃ i ∈ first :: tail, (2 : ℝ) ^ (-900 : Int) ≤ |value (entry width a i column)|

def sourceColumnSquares (width column : Nat) (indices : List Nat) (a : Array Float) : ℝ :=
  (indices.map (fun i => (value (entry width a i column)) ^ 2)).sum

/-- Annihilation defect: only the head carries the linear alpha perturbation;
tail construction defects contribute their squares. -/
def sourceResidualRadius (terms : Nat) : ℝ :=
  (2 : ℝ) ^ (-48 : Int)
  + 4
    * ((2 : ℝ) ^ (-44 : Int)
        + terms * ((2 : ℝ) ^ (-48 : Int)) ^ 2
        + columnNormRadius terms)

def sourceWriteRadius (terms : Nat) (scale : ℝ) : ℝ :=
  ((2 : ℝ) ^ (-49 : Int) + sourceResidualRadius terms + 6 * terms * reflectorRadius terms)
  * scale

/-- Finished source-column accuracy relative to the actual stored reflector's
exact application. Positive zeros are intentional writes, not computed residuals.
The squared diagonal reference is the exact squared norm of the same stored input.
Proof witness: `Kalman.Proofs.FloatQRFinish.scaledColumn_finish_accuracy`. -/
def SourceColumnAccuracy (height width column first : Nat) (tail : List Nat)
    (a : Array Float)
    : Prop :=
  ∃ scale v norm alpha w output,
    scaledColumnNorm height (first :: tail) (fun i => entry width a i column)
      = .ok (scale, v, norm)
    ∧ householderReflector first (first :: tail) v norm = .ok (alpha, w)
    ∧ finishColumn width column first tail a alpha scale = .ok output
    ∧ scale.isFinite = true
    ∧ 0 < value scale
    ∧ output.size = a.size
    ∧ output.all Float.isFinite = true
    ∧ entry width output first column = alpha * scale
    ∧ value scale / 4 ≤ |value (entry width output first column)|
    ∧ 0.0 < (entry width output first column).abs
    ∧ (∀ i ∈ tail, entry width output i column = 0.0)
    ∧ (∀ t,
        t ≠ first * width + column
        → (∀ i ∈ tail, t ≠ i * width + column)
        → output.getD t 0.0 = a.getD t 0.0)
    ∧ |(value (entry width output first column)) ^ 2
        - sourceColumnSquares width column (first :: tail) a|
      ≤ (2 : ℝ) ^ (-37 : Int) * (value scale) ^ 2
    ∧ (∀ i ∈ first :: tail,
        |value (entry width output i column)
          - reflectorAppliedValue width column (first :: tail) w a i|
        ≤ sourceWriteRadius (first :: tail).length (value scale))

/-- Equal stored columns at every row, including the default outside storage. -/
def SameColumn (width column : Nat) (a b : Array Float) : Prop :=
  ∀ i, entry width a i column = entry width b i column

/-- Every flat slot outside the selected row/column rectangle is copied exactly. -/
def OutsidePanel (width : Nat) (indices columns : List Nat) (a b : Array Float) : Prop :=
  ∀ t, (∀ i ∈ indices, ∀ j ∈ columns, t ≠ i * width + j) → b.getD t 0.0 = a.getD t 0.0

/-! ----------------------------------------------------------------------
## Panel and QR iteration
-------------------------------------------------------------------------- -/

/-- Original panel operands. Distinct columns ensure each local application
reads its original target column; no successful run or error is assumed. -/
structure ColumnPanelProfile (height width : Nat) (indices columns : List Nat)
    (w a : Array Float) (M : ℝ)
    : Prop where
  length_le : indices.length ≤ 32
  rows_nodup : indices.Nodup
  columns_nodup : columns.Nodup
  columns_bound : ∀ j ∈ columns, j < width
  rows_bound : ∀ i ∈ indices, i < height
  vector_size : w.size = height
  matrix_size : a.size = height * width
  vector_finite : w.all Float.isFinite = true
  matrix_finite : a.all Float.isFinite = true
  vector_magnitude : ∀ i ∈ indices, |value (w.getD i 0.0)| ≤ 2
  budget_lower : (2 : ℝ) ^ (-1022 : Int) ≤ M
  budget_upper : M ≤ (2 : ℝ) ^ (900 : Int)
  panel_magnitude : ∀ j ∈ columns, ∀ i ∈ indices, |value (entry width a i j)| ≤ M

/-- ColumnPanelAccuracy
Proof witness: `Kalman.Proofs.FloatQRIteration.applyReflectorColumns_accuracy`. -/
def ColumnPanelAccuracy (width : Nat) (indices columns : List Nat) (w a : Array Float)
    (M : ℝ)
    : Prop :=
  ∃ output,
    applyReflectorColumns width columns indices w a = .ok output
    ∧ output.size = a.size
    ∧ output.all Float.isFinite = true
    ∧ OutsidePanel width indices columns a output
    ∧ (∀ j ∈ columns,
        ∀ i ∈ indices,
          |value (entry width output i j) - reflectorAppliedValue width j indices w a i|
          ≤ applicationRadius indices.length M)

/-- Input-only domain for a single actual QR iteration. It says nothing about
whether later iterations retain the source witness or fit the magnitude cap. -/
structure IterationProfile (height width pivot : Nat) (a : Array Float) (M : ℝ)
    : Prop where
  pivot_height : pivot < height
  pivot_width : pivot < width
  length_le : height - pivot ≤ 32
  matrix_size : a.size = height * width
  matrix_finite : a.all Float.isFinite = true
  budget_lower : (2 : ℝ) ^ (-900 : Int) ≤ M
  budget_upper : M ≤ (2 : ℝ) ^ (900 : Int)
  panel_magnitude
    : ∀ i,
        pivot ≤ i
        → i < height
        → ∀ j, pivot ≤ j → j < width → |value (entry width a i j)| ≤ M
  source_witness
    : ∃ i,
        pivot ≤ i ∧ i < height ∧ (2 : ℝ) ^ (-900 : Int) ≤ |value (entry width a i pivot)|

/-- A uniform bound for the exact normalized constructed-vector reference.
Take the larger of source finishing and separately rounded trailing application. -/
def iterationRadius (terms : Nat) (M : ℝ) : ℝ :=
  max (sourceWriteRadius terms M) (applicationRadius terms M)
  + 6 * terms * reflectorRadius terms * M

/-- One actual QR iteration compared with its original stored matrix. The
references use the same returned stored reflector and its exactly normalized
constructed vector, respectively. This is not an ideal whole-QR comparison.
Proof witness: `Kalman.Proofs.FloatQRIteration.qrIteration_accuracy`. -/
def IterationAccuracy (height width pivot : Nat) (a : Array Float) (M : ℝ) : Prop :=
  let indices := List.range' pivot (height - pivot)
  let columns := List.range' (pivot + 1) (width - (pivot + 1))
  let tail := List.range' (pivot + 1) (height - (pivot + 1))
  ∃ scale v norm alpha w panel output,
    scaledColumnNorm height indices (fun i => entry width a i pivot)
      = .ok (scale, v, norm)
    ∧ householderReflector pivot indices v norm = .ok (alpha, w)
    ∧ applyReflectorColumns width columns indices w a = .ok panel
    ∧ finishColumn width pivot pivot tail panel alpha scale = .ok output
    ∧ qrIteration height width pivot a = .ok output
    ∧ output.size = a.size
    ∧ output.all Float.isFinite = true
    ∧ OutsidePanel width indices (pivot :: columns) a output
    ∧ scale.isFinite = true
    ∧ 0 < value scale
    ∧ (2 : ℝ) ^ (-900 : Int) ≤ value scale
    ∧ value scale ≤ M
    ∧ w.size = height
    ∧ w.all Float.isFinite = true
    ∧ 0 < vectorSquares indices (constructedVector pivot v norm)
    ∧ (indices.map (fun i => (constructedUnitComponent pivot indices v norm i) ^ 2)).sum
      = 1
    ∧ entry width output pivot pivot = alpha * scale
    ∧ value scale / 4 ≤ |value (entry width output pivot pivot)|
    ∧ 0.0 < (entry width output pivot pivot).abs
    ∧ (∀ i ∈ tail, entry width output i pivot = 0.0)
    ∧ |(value (entry width output pivot pivot)) ^ 2
        - sourceColumnSquares width pivot indices a|
      ≤ (2 : ℝ) ^ (-37 : Int) * (value scale) ^ 2
    ∧ (∀ j ∈ columns,
        ∀ i ∈ indices,
          |value (entry width output i j) - reflectorAppliedValue width j indices w a i|
          ≤ applicationRadius indices.length M)
    ∧ (∀ j ∈ pivot :: columns,
        ∀ i ∈ indices,
          |value (entry width output i j) - reflectorAppliedValue width j indices w a i|
          ≤ max (sourceWriteRadius indices.length M) (applicationRadius indices.length M))
    ∧ (∀ j ∈ pivot :: columns,
        ∀ i ∈ indices,
          |value (entry width output i j)
            - constructedAppliedValue width j pivot indices v norm a i|
          ≤ iterationRadius indices.length M)

end

/-! ----------------------------------------------------------------------
## Loop structure and factor retention
-------------------------------------------------------------------------- -/

/-- Completed columns have assigned positive zeros below the diagonal.
This is a structural invariant, not a numerical error or rank assumption. -/
def ProcessedColumns (height width completed : Nat) (a : Array Float) : Prop :=
  ∀ j, j < completed → j < width → ∀ i, i < height → j < i → entry width a i j = 0.0

/-- Embed the exactly normalized stored constructed vector in the full row space.
Rows before the pivot are zero; this vector is a ghost reference, not native output. -/
noncomputable def iterationUnitVector (height pivot : Nat) (v : Array Float)
    (norm : Float)
    : Fin height → ℝ :=
  fun i =>
    if pivot ≤ i.val then
      constructedUnitComponent pivot (List.range' pivot (height - pivot)) v norm i.val
    else
      0

/-- Full-matrix comparison with an exact Gram-preserving reflection. The witness
uses the same stored constructed vector as IterationAccuracy.
Proof witness: `Kalman.Proofs.FloatQRGram.qrIteration_orthogonal_accuracy`. -/
noncomputable def IterationOrthogonalAccuracy (height width pivot : Nat) (a : Array Float)
    (M : ℝ)
    : Prop :=
  ∃ scale v norm output,
    scaledColumnNorm height (List.range' pivot (height - pivot))
        (fun i => entry width a i pivot)
      = .ok (scale, v, norm)
    ∧ qrIteration height width pivot a = .ok output
    ∧ output.size = a.size
    ∧ output.all Float.isFinite = true
    ∧ (∑ i, (iterationUnitVector height pivot v norm i) ^ 2) = 1
    ∧ Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin
        (iterationRadius (height - pivot) M)
        (Kalman.Implementation.Correctness.InputInterpretation.matrix height width output)
        (Kalman.Definitions.OrthogonalFactorization.reflect
          (iterationUnitVector height pivot v norm)
          (Kalman.Implementation.Correctness.InputInterpretation.matrix height width a))

/-- Conservative absolute column-Gram change for one iteration. Only active rows
contribute; M bounds the incoming active panel and the radius uses its proved error. -/
noncomputable def iterationGramRadius (terms : Nat) (M : ℝ) : ℝ :=
  terms
  * (2 * (1 + 2 * terms) * M * iterationRadius terms M + (iterationRadius terms M) ^ 2)

/-- One complete native iteration compared with its incoming stored matrix's
exact column Gram. Completed by FloatQRGram under a panel profile and prior zeros.
Proof witness: `Kalman.Proofs.FloatQRGram.qrIteration_gram_accuracy`. -/
noncomputable def IterationGramAccuracy (height width pivot : Nat) (a : Array Float)
    (M : ℝ)
    : Prop :=
  ∃ output,
    qrIteration height width pivot a = .ok output
    ∧ output.size = a.size
    ∧ output.all Float.isFinite = true
    ∧ Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin
        (iterationGramRadius (height - pivot) M)
        ((Kalman.Implementation.Correctness.InputInterpretation.matrix height width
            output).transpose
          * Kalman.Implementation.Correctness.InputInterpretation.matrix height width
              output)
        ((Kalman.Implementation.Correctness.InputInterpretation.matrix height width
            a).transpose
          * Kalman.Implementation.Correctness.InputInterpretation.matrix height width a)

/-- Structural postcondition for a successful complete QR loop. Its theorem
does not promise execution success or accuracy relative to the input matrix.
Proof witness: `Kalman.Proofs.FloatQRTriangular.triangularize_structure`. -/
def TriangularizationStructure (height width : Nat) (a r : Array Float) : Prop :=
  triangularize height width a = .ok r
  ∧ r.size = height * width
  ∧ r.all Float.isFinite = true
  ∧ ProcessedColumns height width width r

/-- Only the stored QR result is referenced. No dimension or magnitude cap is
needed for retention, and no execution success is an input premise. -/
structure RetentionProfile (rows : Nat) (r : Array Float) : Prop where
  matrix_finite : r.all Float.isFinite = true
  diagonal_nonzero : ∀ j < rows, value (entry rows r j j) ≠ 0

/-- Upper triangle of the retained square block, with exact decoding and zero
below the diagonal. FloatQRTriangular identifies its Gram with the full tall
result under the proved triangular-zero invariant. -/
noncomputable def retainedUpper (rows : Nat) (r : Array Float)
    : Matrix (Fin rows) (Fin rows) ℝ :=
  fun i j => if j < i then 0 else value (entry rows r i.val j.val)

/-- Exact sign applied to each retained upper row. -/
noncomputable def retainedSignValue (rows : Nat) (r : Array Float) (j : Nat) : ℝ :=
  if value (entry rows r j j) < 0 then -1 else 1

/-- Public retention contract. Its proof witness is in FloatQRRetain;
it compares with the stored upper block, not the original prearray.
Proof witness: `Kalman.Proofs.FloatQRRetain.retainFactor_accuracy`. -/
def RetentionAccuracy (rows : Nat) (r : Array Float) : Prop :=
  ∃ l,
    retainFactor rows r = .ok l
    ∧ l.size = rows * rows
    ∧ l.all Float.isFinite = true
    ∧ (∀ i j,
        i < rows
        → j < rows
        → entry rows l i j
          = if i < j then
              0.0
            else
              retainedSign (entry rows r j j) * entry rows r j i)
    ∧ (∀ j < rows, value (entry rows l j j) = |value (entry rows r j j)|)
    ∧ Kalman.Definitions.FactorRecursion.LowerPositive
        (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)
    ∧ Kalman.Definitions.FactorRecursion.gram
        (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)
      = (retainedUpper rows r).transpose * retainedUpper rows r
    ∧ (Kalman.Definitions.FactorRecursion.gram
        (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)).PosDef

/-- A successful factor call has an exact Gram denotation equal to the full
stored tall QR result's column Gram. Original-prearray error remains separate.
The proof witness is in FloatQRTriangular; success is explicitly conditional.
Proof witness: `Kalman.Proofs.FloatQRTriangular.gramFactor_structure`. -/
def SuccessfulGramFactorStructure (rows columns : Nat) (a l : Array Float) : Prop :=
  ∃ r,
    TriangularizationStructure columns rows (transpose rows columns a) r
    ∧ retainFactor rows r = .ok l
    ∧ l.size = rows * rows
    ∧ l.all Float.isFinite = true
    ∧ Kalman.Definitions.FactorRecursion.LowerPositive
        (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)
    ∧ Kalman.Definitions.FactorRecursion.gram
        (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)
      = (Kalman.Implementation.Correctness.InputInterpretation.matrix columns rows
          r).transpose
        * Kalman.Implementation.Correctness.InputInterpretation.matrix columns rows r
    ∧ (Kalman.Definitions.FactorRecursion.gram
        (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)).PosDef

/-- Operand conditions at every actual ascending-loop prefix. This is a
run-dependent operand profile: no successful final run or error is assumed,
but later source margins and magnitude budgets are not derived from initial rank. -/
structure TriangularizationProfile (height width : Nat) (a : Array Float)
    (budget : Nat → ℝ)
    : Prop where
  width_le_height : width ≤ height
  matrix_size : a.size = height * width
  matrix_finite : a.all Float.isFinite = true
  prefix_profile
    : ∀ pivot,
        pivot < width
        → ∀ current,
            qrIterations height width (List.range pivot) a = .ok current
            → IterationProfile height width pivot current (budget pivot)

/-! ----------------------------------------------------------------------
## Whole-QR error and original-input domains
-------------------------------------------------------------------------- -/

/-- Sum of the proved local Gram allowances. There is no amplification factor:
each local comparison concerns consecutive stored column Grams. -/
noncomputable def qrGramRadius (height pivots : Nat) (budget : Nat → ℝ) : ℝ :=
  ∑ pivot ∈ Finset.range pivots, iterationGramRadius (height - pivot) (budget pivot)

/-- Initial column-energy upper bound and uniform column-Gram lower bound.
These concern only exact decoding of the original stored tall input. -/
structure InitialGramBounds (height width : Nat) (a : Array Float) (S α : ℝ) : Prop where
  column_energy
    : ∀ j : Fin width,
        ∑ i : Fin height,
          (Kalman.Implementation.Correctness.InputInterpretation.matrix height width a i
            j)
          ^ 2
        ≤ S
  gram_lower
    : ((Kalman.Implementation.Correctness.InputInterpretation.matrix height width
            a).transpose
          * Kalman.Implementation.Correctness.InputInterpretation.matrix height width a
        - α • 1).PosSemidef

/-- Conditions on the original stored tall QR input alone. Neither an actual
prefix result nor any later operand profile is part of this domain. -/
structure InitialQRDomain (height width : Nat) (a : Array Float) (M : ℝ) : Prop where
  width_le_height : width ≤ height
  height_le_eight : height ≤ 8
  matrix_size : a.size = height * width
  matrix_finite : a.all Float.isFinite = true
  budget_lower : (2 : ℝ) ^ (-896 : Int) ≤ M
  budget_upper : M ≤ (2 : ℝ) ^ (900 : Int)
  gram_bounds : InitialGramBounds height width a (M ^ 2 / 2) (M ^ 2 / 8)

/-- Original row-major prearray domain for the factor kernel. Its row energies
and row Gram are interpreted exactly; no native transpose or QR prefix is
assumed to satisfy a profile. -/
structure GramFactorInputDomain (rows columns : Nat) (a : Array Float) (M : ℝ)
    : Prop where
  rows_le_columns : rows ≤ columns
  columns_le_eight : columns ≤ 8
  matrix_size : a.size = rows * columns
  matrix_finite : a.all Float.isFinite = true
  budget_lower : (2 : ℝ) ^ (-896 : Int) ≤ M
  budget_upper : M ≤ (2 : ℝ) ^ (900 : Int)
  row_energy
    : ∀ i : Fin rows,
        ∑ j : Fin columns,
          (Kalman.Implementation.Correctness.InputInterpretation.matrix rows columns a i
            j)
          ^ 2
        ≤ M ^ 2 / 2
  gram_lower
    : (Kalman.Definitions.FactorRecursion.gram
          (Kalman.Implementation.Correctness.InputInterpretation.matrix rows columns a)
        - (M ^ 2 / 8) • 1).PosSemidef

/-- Derived bounds at a stored prefix: entries are controlled by original
column energy and the column Gram retains a quantified lower bound.
This does not yet assert a large enough active source-column entry. -/
noncomputable def PrefixEnclosure (height width pivots : Nat) (current : Array Float)
    (budget : Nat → ℝ) (S α : ℝ)
    : Prop :=
  (∀ i j,
    (Kalman.Implementation.Correctness.InputInterpretation.matrix height width current i
        j)
      ^ 2
    ≤ S + qrGramRadius height pivots budget)
  ∧ ((Kalman.Implementation.Correctness.InputInterpretation.matrix height width
          current).transpose
        * Kalman.Implementation.Correctness.InputInterpretation.matrix height width
            current
      - (α - width * qrGramRadius height pivots budget) • 1).PosSemidef

/-- Prefix success, triangular zeros, retained nonzero diagonals and accumulated
column-Gram error against the original stored tall input.
Proof witness: `Kalman.Proofs.FloatQRComposition.qrIterations_prefix_accuracy`. -/
noncomputable def QRPrefixAccuracy (height width pivots : Nat) (a : Array Float)
    (budget : Nat → ℝ)
    : Prop :=
  ∃ output,
    qrIterations height width (List.range pivots) a = .ok output
    ∧ output.size = a.size
    ∧ output.all Float.isFinite = true
    ∧ ProcessedColumns height width pivots output
    ∧ (∀ j, j < pivots → value (entry width output j j) ≠ 0)
    ∧ Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin
        (qrGramRadius height pivots budget)
        ((Kalman.Implementation.Correctness.InputInterpretation.matrix height width
            output).transpose
          * Kalman.Implementation.Correctness.InputInterpretation.matrix height width
              output)
        ((Kalman.Implementation.Correctness.InputInterpretation.matrix height width
            a).transpose
          * Kalman.Implementation.Correctness.InputInterpretation.matrix height width a)

/-- Complete QR error against the same original stored tall input. The completed
witness is in FloatQRComposition; its prefix-profile domain remains explicit.
Proof witness: `Kalman.Proofs.FloatQRComposition.triangularize_gram_accuracy`. -/
noncomputable def TriangularizationGramAccuracy (height width : Nat) (a : Array Float)
    (budget : Nat → ℝ)
    : Prop :=
  ∃ r,
    TriangularizationStructure height width a r
    ∧ RetentionProfile width r
    ∧ Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin
        (qrGramRadius height width budget)
        ((Kalman.Implementation.Correctness.InputInterpretation.matrix height width
            r).transpose
          * Kalman.Implementation.Correctness.InputInterpretation.matrix height width r)
        ((Kalman.Implementation.Correctness.InputInterpretation.matrix height width
            a).transpose
          * Kalman.Implementation.Correctness.InputInterpretation.matrix height width a)

/-- Successful finite native factor with strictly PD exact Gram, within the
accumulated allowance of the exact Gram of the same original stored prearray.
This does not describe a rounded dense Gram or the ideal full Kalman recursion.
Proof witness: `Kalman.Proofs.FloatQRComposition.gramFactor_accuracy`. -/
noncomputable def GramFactorAccuracy (rows columns : Nat) (a : Array Float)
    (budget : Nat → ℝ)
    : Prop :=
  a.size = rows * columns
  ∧ a.all Float.isFinite = true
  ∧ ∃ l,
      gramFactor rows columns a = .ok l
      ∧ l.size = rows * rows
      ∧ l.all Float.isFinite = true
      ∧ Kalman.Definitions.FactorRecursion.LowerPositive
          (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)
      ∧ (Kalman.Definitions.FactorRecursion.gram
          (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows
            l)).PosDef
      ∧ Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin
          (qrGramRadius columns rows budget)
          (Kalman.Definitions.FactorRecursion.gram
            (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l))
          (Kalman.Definitions.FactorRecursion.gram
            (Kalman.Implementation.Correctness.InputInterpretation.matrix rows columns a))

/-- Initial-input native factor conclusion: successful finite positive-diagonal
factor, strict-PD exact Gram with floor M²/16, and both the sharper accumulated
allowance and conservative M²/128 error against the same original prearray.
Proof witness: `Kalman.Proofs.FloatQRInitialDomain.gramFactor_initial_accuracy`. -/
noncomputable def InitialGramFactorAccuracy (rows columns : Nat) (a : Array Float) (M : ℝ)
    : Prop :=
  a.size = rows * columns
  ∧ a.all Float.isFinite = true
  ∧ ∃ l,
      gramFactor rows columns a = .ok l
      ∧ l.size = rows * rows
      ∧ l.all Float.isFinite = true
      ∧ Kalman.Definitions.FactorRecursion.LowerPositive
          (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)
      ∧ (Kalman.Definitions.FactorRecursion.gram
          (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows
            l)).PosDef
      ∧ (Kalman.Definitions.FactorRecursion.gram
            (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l)
          - (M ^ 2 / 16) • 1).PosSemidef
      ∧ Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin
          (qrGramRadius columns rows (fun _ => M))
          (Kalman.Definitions.FactorRecursion.gram
            (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l))
          (Kalman.Definitions.FactorRecursion.gram
            (Kalman.Implementation.Correctness.InputInterpretation.matrix rows columns a))
      ∧ Kalman.Definitions.Theorems.RecursionSensitivity.EntrywiseWithin (M ^ 2 / 128)
          (Kalman.Definitions.FactorRecursion.gram
            (Kalman.Implementation.Correctness.InputInterpretation.matrix rows rows l))
          (Kalman.Definitions.FactorRecursion.gram
            (Kalman.Implementation.Correctness.InputInterpretation.matrix rows columns a))

end Kalman.Proofs.QRProfiles
