import Kalman.Definitions.Input
import Flare.Matrix.Dense

/-!
# Native binary64 storage and linear algebra

The product and LDLᵀ solve are FLARE's actual native kernels, reused unchanged
through an error adapter. Shapes are supplied by checked public entry points.
Every product and sum is separately rounded; no FMA is requested.
No covariance symmetry repair is performed. LDLᵀ reads the lower triangle.
-/

namespace Kalman.Implementation.LinearAlgebra

open Kalman.Definitions.Input

def adapt {α : Type} (result : Except Flare.Matrix.DenseError α) : Except Error α :=
  match result with
  | .ok x => .ok x
  | .error .nonpositivePivot => .error .nonpositivePivot
  | .error .nonfiniteComputation => .error .nonfiniteComputation

def finite (x : Float) : Except Error Float :=
  adapt (Flare.Matrix.Dense.finite x)

abbrev entry := Flare.Matrix.Dense.entry
abbrev identity := Flare.Matrix.Dense.identity
abbrev transpose := Flare.Matrix.Dense.transpose

def multiply (rows inner columns : Nat) (a b : Array Float)
    : Except Error (Array Float) :=
  adapt (Flare.Matrix.Dense.multiply rows inner columns a b)

def solveSPD (n columns : Nat) (a b : Array Float) : Except Error (Array Float) :=
  adapt (Flare.Matrix.Dense.solveSPD n columns a b)

def add (a b : Array Float) : Except Error (Array Float) :=
  (Array.range a.size).mapM fun i => finite (a.getD i 0.0 + b.getD i 0.0)

def sub (a b : Array Float) : Except Error (Array Float) :=
  (Array.range a.size).mapM fun i => finite (a.getD i 0.0 - b.getD i 0.0)

def fromCols (rows leftColumns rightColumns : Nat) (a b : Array Float) : Array Float :=
  (Array.range (rows * (leftColumns + rightColumns))).map
    fun index =>
      let i := index / (leftColumns + rightColumns)
      let j := index % (leftColumns + rightColumns)
      if j < leftColumns then
        entry leftColumns a i j
      else
        entry rightColumns b i (j - leftColumns)

/-- Separately rounded products and subtractions in the supplied index order.
The core uses FLARE's runtime error type so its arithmetic schedule can be
compared directly with FLARE's proof-side extraction. -/
def subtractProductsCore (indices : List Nat) (left right : Nat → Float) (initial : Float)
    : Except Flare.Matrix.DenseError Float := do
  let mut s := initial
  for k in indices do
    let term ← Flare.Matrix.Dense.finite (left k * right k)
    s ← Flare.Matrix.Dense.finite (s - term)
  return s

def subtractProducts (indices : List Nat) (left right : Nat → Float) (initial : Float)
    : Except Error Float :=
  adapt (subtractProductsCore indices left right initial)

/-- Cholesky and substitution divide only after all residual subtractions. -/
def divideResidual (indices : List Nat) (left right : Nat → Float)
    (initial diagonal : Float)
    : Except Error Float := do
  let residual ← subtractProducts indices left right initial
  finite (residual / diagonal)

def positiveSqrt (pivot : Float) : Except Error Float := do
  unless 0.0 < pivot do
    throw .nonpositivePivot
  let diagonal ← finite pivot.sqrt
  unless 0.0 < diagonal do
    throw .nonpositivePivot
  return diagonal

/-- Direct Cholesky initialization/noise factorization. Only the lower triangle
is read. Positive computed pivots are required; failure is numerical rejection. -/
def cholesky (n : Nat) (a : Array Float) : Except Error (Array Float) := do
  let mut l := Array.replicate (n * n) 0.0
  for j in [:n] do
    let pivot ←
      subtractProducts (List.range j) (fun k => entry n l j k)
        (fun k => entry n l j k) (entry n a j j)
    let diagonal ← positiveSqrt pivot
    l := l.set! (j * n + j) diagonal
    for i in [j + 1:n] do
      let value ←
        divideResidual (List.range j) (fun k => entry n l i k)
          (fun k => entry n l j k) (entry n a i j) diagonal
      l := l.set! (i * n + j) value
  return l

/-- Ascending forward substitution with a separately rounded final division. -/
def forwardCholesky (n columns : Nat) (l b : Array Float)
    : Except Error (Array Float) := do
  let mut y := Array.replicate (n * columns) 0.0
  for i in [:n] do
    for j in [:columns] do
      let value ←
        divideResidual (List.range i) (fun k => entry n l i k)
          (fun k => entry columns y k j) (entry columns b i j) (entry n l i i)
      y := y.set! (i * columns + j) value
  return y

/-- Descending rows, ascending residual indices, then diagonal division. -/
def backwardCholesky (n columns : Nat) (l y : Array Float)
    : Except Error (Array Float) := do
  let mut x := Array.replicate (n * columns) 0.0
  for step in [:n] do
    let i := n - 1 - step
    for j in [:columns] do
      let value ←
        divideResidual (List.range' (i + 1) (n - (i + 1)))
          (fun k => entry n l k i) (fun k => entry columns x k j)
          (entry columns y i j) (entry n l i i)
      x := x.set! (i * columns + j) value
  return x

/-- Solve (L Lᵀ) X = B without materializing the Gram matrix. -/
def solveCholesky (n columns : Nat) (l b : Array Float) : Except Error (Array Float) := do
  backwardCholesky n columns l (← forwardCholesky n columns l b)

end Kalman.Implementation.LinearAlgebra
