import Kalman.Implementation.LinearAlgebra

/-!
# Native Householder QR for covariance factors

Project implementation of classical unpivoted Householder QR, used by Tracy's
square-root stages. It triangularizes a prearray transpose and retains Rᵀ.
Column norms are scaled by their maximum magnitude; reflectors are normalized
before application. A zero diagonal or an exceptional intermediate is rejected.
Companion proofs establish native success and Gram error on an explicit
initial energy/rank/scale domain with at most eight columns.
-/

namespace Kalman.Implementation.OrthogonalFactorization

open Kalman.Definitions.Input
open Kalman.Implementation.LinearAlgebra

/-- Visit caller-supplied indices in list order; maximum absolute stored entry, starting
from positive zero. Exceptional inputs are handled by the subsequent checks. -/
def columnScale (indices : List Nat) (x : Nat → Float) : Float :=
  indices.foldl (fun scale i => max scale (x i).abs) 0.0

/-- Interleave each checked division, array write, separately rounded square,
and checked addition. This is the QR column-norm loop's original schedule. -/
def scaledSquares (indices : List Nat) (x : Nat → Float) (scale : Float)
    (initial : Array Float) (initialSum : Float)
    : Except Error (Array Float × Float) := do
  let mut v := initial
  let mut sum := initialSum
  for i in indices do
    let value ← finite (x i / scale)
    v := v.set! i value
    let term ← finite (value * value)
    sum ← finite (sum + term)
  return (v, sum)

/-- Maximum scaling followed by the original sum-of-squares and square root.
Zero scale and exceptional intermediate values are rejected. The returned norm
is for the normalized column; diagonal rescaling happens later in QR. -/
def scaledColumnNorm (size : Nat) (indices : List Nat) (x : Nat → Float)
    : Except Error (Float × Array Float × Float) := do
  let scale := columnScale indices x
  unless 0.0 < scale do
    throw .nonpositivePivot
  let (v, sum) ← scaledSquares indices x scale (Array.replicate size 0.0) 0.0
  let norm ← finite sum.sqrt
  return (scale, v, norm)

/-- Opposite sign to the first component; both signed zeros take the negative-norm
branch. This avoids cancellation in the following first-component subtraction. -/
def reflectorAlpha (first norm : Float) : Float :=
  if first < 0.0 then norm else -norm

/-- Separately rounded squares and additions in the supplied index order. -/
def sumSquares (indices : List Nat) (v : Array Float) (initial : Float)
    : Except Error Float := do
  let mut squared := initial
  for i in indices do
    let term ← finite (v.getD i 0.0 * v.getD i 0.0)
    squared ← finite (squared + term)
  return squared

/-- Divide and overwrite in list order. Repeated indices divide repeatedly;
the QR caller supplies a duplicate-free ascending range. -/
def normalizeVector (indices : List Nat) (v : Array Float) (norm : Float)
    : Except Error (Array Float) := do
  let mut v := v
  for i in indices do
    v := v.set! i (← finite (v.getD i 0.0 / norm))
  return v

/-- Construct and normalize the Householder vector using the original QR
schedule. Return its signed diagonal choice and stored normalized vector.
Reject exceptional intermediates or a nonpositive computed vector norm. -/
def householderReflector (first : Nat) (indices : List Nat) (v : Array Float)
    (norm : Float)
    : Except Error (Float × Array Float) := do
  let alpha := reflectorAlpha (v.getD first 0.0) norm
  let head ← finite (v.getD first 0.0 - alpha)
  let v := v.set! first head
  let squared ← sumSquares indices v 0.0
  let vnorm ← finite squared.sqrt
  unless 0.0 < vnorm do
    throw .nonpositivePivot
  let v ← normalizeVector indices v vnorm
  return (alpha, v)

/-- Read the pre-update column in list order, with separately rounded and
checked products and additions. -/
def reflectorDot (width column : Nat) (indices : List Nat) (v a : Array Float)
    (initial : Float)
    : Except Error Float := do
  let mut dot := initial
  for i in indices do
    let term ← finite (v.getD i 0.0 * entry width a i column)
    dot ← finite (dot + term)
  return dot

/-- Apply the fixed doubled dot product in list order. Read the mutable matrix,
then separately multiply, subtract, check, and overwrite each selected slot.
Repeated indices would update their slot repeatedly. -/
def reflectorUpdates (width column : Nat) (indices : List Nat) (v a : Array Float)
    (twice : Float)
    : Except Error (Array Float) := do
  let mut a := a
  for i in indices do
    let term ← finite (v.getD i 0.0 * twice)
    let value ← finite (entry width a i column - term)
    a := a.set! (i * width + column) value
  return a

/-- Apply a stored Householder vector to one matrix column using the original
QR schedule. Exceptional intermediates are rejected immediately. -/
def applyReflector (width column : Nat) (indices : List Nat) (v a : Array Float)
    : Except Error (Array Float) := do
  let dot ← reflectorDot width column indices v a 0.0
  let twice ← finite (2.0 * dot)
  reflectorUpdates width column indices v a twice

/-- Apply one fixed reflector to columns in list order. Each column application
reads the current matrix; repeated columns would be transformed repeatedly. -/
def applyReflectorColumns (width : Nat) (columns indices : List Nat) (v a : Array Float)
    : Except Error (Array Float) := do
  let mut a := a
  for column in columns do
    a ← applyReflector width column indices v a
  return a

/-- Write positive zeros in list order. Out-of-bounds writes retain the native
set! behavior; callers supply valid slots. This helper cannot reject. -/
def zeroColumn (width column : Nat) (indices : List Nat) (a : Array Float)
    : Except Error (Array Float) := do
  let mut a := a
  for i in indices do
    a := a.set! (i * width + column) 0.0
  return a

/-- Finish the source column in the original QR order: checked diagonal
rescaling, diagonal write, then positive-zero tail writes. Exceptional products
reject before any returned writes. No new domain check is added here. -/
def finishColumn (width column first : Nat) (tail : List Nat) (a : Array Float)
    (alpha scale : Float)
    : Except Error (Array Float) := do
  let diagonal ← finite (alpha * scale)
  zeroColumn width column tail (a.set! (first * width + column) diagonal)

/-- One original QR iteration: construct from the source column, update all
trailing columns in ascending order, then rescale and overwrite the source.
The source is read before any trailing-column writes. -/
def qrIteration (height width pivot : Nat) (a : Array Float)
    : Except Error (Array Float) := do
  let indices := List.range' pivot (height - pivot)
  let (scale, v, norm) ← scaledColumnNorm height indices (fun i => entry width a i pivot)
  let (alpha, v) ← householderReflector pivot indices v norm
  let a ←
    applyReflectorColumns width (List.range' (pivot + 1) (width - (pivot + 1))) indices v
      a
  finishColumn width pivot pivot (List.range' (pivot + 1) (height - (pivot + 1))) a alpha
    scale

/-- Visit pivots in list order, reading the current matrix at each iteration.
The QR caller supplies all columns once in ascending order. -/
def qrIterations (height width : Nat) (pivots : List Nat) (a : Array Float)
    : Except Error (Array Float) := do
  let mut a := a
  for pivot in pivots do
    a ← qrIteration height width pivot a
  return a

/-- Triangularize the stored tall matrix; retainFactor is a separate final stage. -/
def triangularize (height width : Nat) (a : Array Float) : Except Error (Array Float) :=
  qrIterations height width (List.range width) a

/-- Retain the original diagonal sign choice; signed zeros take the positive branch. -/
def retainedSign (diagonal : Float) : Float :=
  if diagonal < 0.0 then -1.0 else 1.0

/-- Copy one signed upper row into a lower column in the supplied index order.
Products are checked before each write. Reads always use the fixed QR result. -/
def copyFactorColumn (rows column : Nat) (indices : List Nat) (r l : Array Float)
    : Except Error (Array Float) := do
  let sign := retainedSign (entry rows r column column)
  let mut l := l
  for i in indices do
    l := l.set! (i * rows + column) (← finite (sign * entry rows r column i))
  return l

/-- Visit columns in list order, checking each diagonal before its signed copy.
The QR caller supplies every column once in ascending order. -/
def retainColumns (rows : Nat) (columns : List Nat) (r l : Array Float)
    : Except Error (Array Float) := do
  let mut l := l
  for j in columns do
    unless 0.0 < (entry rows r j j).abs do
      throw .nonpositivePivot
    l ← copyFactorColumn rows j (List.range' j (rows - j)) r l
  return l

/-- Signed transpose of the retained upper block, initialized with positive zeros.
No rounded dense Gram matrix is formed. -/
def retainFactor (rows : Nat) (r : Array Float) : Except Error (Array Float) :=
  retainColumns rows (List.range rows) r (Array.replicate (rows * rows) 0.0)

/-- Return a positive-diagonal lower factor for the Gram matrix of a full-row-rank
rows × columns prearray. Internal callers provide columns ≥ rows and valid shape.
The returned factor represents an exact-real Gram matrix, not a rounded dense one. -/
def gramFactor (rows columns : Nat) (a : Array Float) : Except Error (Array Float) := do
  let r ← triangularize columns rows (transpose rows columns a)
  retainFactor rows r

end Kalman.Implementation.OrthogonalFactorization
