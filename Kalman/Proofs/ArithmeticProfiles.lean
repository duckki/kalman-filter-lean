import Flare.Analysis.ErrorRecurrence
import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Implementation.CovarianceFilter

/-!
# Shared native operand profiles and error radii

Numerical domains for actual native arithmetic. These profiles bound exact
magnitudes of stored operands; they do not assume any desired error conclusion.
Intermediate arrays in a Joseph profile expose the implemented operation order. -/

namespace Kalman.Proofs.ArithmeticProfiles

open Kalman.Definitions
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation
open Flare.Binary64.Value

noncomputable section

/-! ----------------------------------------------------------------------
## Matrix-product and array-sum operand profiles
-------------------------------------------------------------------------- -/

structure ProductProfile (rows inner columns : Nat) (a b : Array Float) (M : ℝ)
    : Prop where
  inner_le : inner ≤ 32
  finite_left : a.all Float.isFinite = true
  finite_right : b.all Float.isFinite = true
  upper : M ≤ (2 : ℝ) ^ (990 : Int)
  lower : (2 : ℝ) ^ (-1022 : Int) ≤ M
  mass
    : ∀ i j,
        i < rows
        → j < columns
        → (∑ k ∈ Finset.range inner,
            |value (entry inner a i k) * value (entry columns b k j)|)
          ≤ M

structure SumProfile (a b : Array Float) (E : Int) (subtract : Bool) : Prop where
  exponent_lower : -1022 ≤ E
  exponent_upper : E ≤ 1022
  finite_left : a.all Float.isFinite = true
  finite_right : b.all Float.isFinite = true
  magnitude
    : ∀ i,
        i < a.size
        → |value (a.getD i 0.0)
            + (if subtract then -value (b.getD i 0.0) else value (b.getD i 0.0))|
          ≤ (2 : ℝ) ^ E

def productRadius (inner : Nat) (M : ℝ) : ℝ := inner * (2 : ℝ) ^ (-50 : Int) * M
def sumRadius (E : Int) : ℝ := (2 : ℝ) ^ (E - 52)

/-! ----------------------------------------------------------------------
## Finite-horizon radius recurrence
-------------------------------------------------------------------------- -/

/-- Finite-horizon composition budget. L bounds sensitivity of each exact
step and δ its proved local implementation error; neither is inferred here. -/
abbrev accumulatedRadius := Flare.Analysis.ErrorRecurrence.accumulatedRadius

/-! ----------------------------------------------------------------------
## Direct Joseph operand profile and evaluation radius
-------------------------------------------------------------------------- -/

/-- A posteriori numerical profile for the direct Joseph covariance kernel.
The gain is supplied to this kernel; its error relative to the optimal gain is
a separate solve/conditioning obligation. All products are the native kernels. -/
structure JosephProfile (input : Input.Model) (prior : Input.State)
    (k output : Array Float) where
  (kh w wp first kr second : Array Float)
  (massKH massWP massFirst massKR massSecond : ℝ)
  (exponentW exponentSum : Int)
  computeKH
    : multiply input.stateDimension input.measurementDimension input.stateDimension
        k input.observation
      = .ok kh
  computeW : sub (identity input.stateDimension) kh = .ok w
  computeWP
    : multiply input.stateDimension input.stateDimension input.stateDimension w
        prior.covariance
      = .ok wp
  computeFirst
    : multiply input.stateDimension input.stateDimension input.stateDimension
        wp (transpose input.stateDimension input.stateDimension w)
      = .ok first
  computeKR
    : multiply input.stateDimension input.measurementDimension input.measurementDimension
        k input.measurementNoise
      = .ok kr
  computeSecond
    : multiply input.stateDimension input.measurementDimension input.stateDimension
        kr (transpose input.stateDimension input.measurementDimension k)
      = .ok second
  computeSum : add first second = .ok output
  profileKH
    : ProductProfile input.stateDimension input.measurementDimension input.stateDimension
        k input.observation massKH
  profileW : SumProfile (identity input.stateDimension) kh exponentW true
  profileWP
    : ProductProfile input.stateDimension input.stateDimension input.stateDimension
        w prior.covariance massWP
  profileFirst
    : ProductProfile input.stateDimension input.stateDimension input.stateDimension
        wp (transpose input.stateDimension input.stateDimension w) massFirst
  profileKR
    : ProductProfile input.stateDimension input.measurementDimension
        input.measurementDimension k input.measurementNoise massKR
  profileSecond
    : ProductProfile input.stateDimension input.measurementDimension input.stateDimension
        kr (transpose input.stateDimension input.measurementDimension k) massSecond
  profileSum : SumProfile first second exponentSum false

/-- Complete Joseph evaluation allowance against the same stored gain. P, W,
and K bound entries of the exact decoded prior, I-KH, and gain respectively. -/
def josephRadius {input : Input.Model} {prior : Input.State} {k output : Array Float}
    (p : JosephProfile input prior k output) (P W K : ℝ)
    : ℝ :=
  let n : ℝ := input.stateDimension
  let m : ℝ := input.measurementDimension
  let ew := sumRadius p.exponentW + productRadius input.measurementDimension p.massKH
  let ewp := productRadius input.stateDimension p.massWP + n * ew * P
  sumRadius p.exponentSum
  + (productRadius input.stateDimension p.massFirst
      + n * (ewp * W + (n * W * P) * ew + ewp * ew))
  + (productRadius input.measurementDimension p.massSecond
      + m * productRadius input.measurementDimension p.massKR * K)

end
end Kalman.Proofs.ArithmeticProfiles
