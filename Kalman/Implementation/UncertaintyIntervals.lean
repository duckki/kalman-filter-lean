import Kalman.Implementation.LinearAlgebra

/-! Executable uncertainty endpoints, with separately rounded operations and
finite guards. Certified input ranges are stated in the correctness module.
The padding is exactly 2^-40; no FMA or floating-point mode change is used. -/

namespace Kalman.Implementation.UncertaintyIntervals

open Kalman.Definitions.Input Kalman.Implementation.LinearAlgebra

/-- Exact dyadic outward allowance, independent of the caller's error budgets. -/
def padding : Float := Float.ofBits 0x3d70000000000000

/-- The `2^-29` componentwise mean allowance of the stationary coupled
tracking certificate. Its applicability is proved in `FloatTrackingIntervals`. -/
def trackingMeanAllowance : Float := Float.ofBits 0x3e20000000000000

/-- Native conservative variance, radius and endpoints. -/
structure Interval where
  varianceUpper : Float
  radius : Float
  lower : Float
  upper : Float
deriving Repr

/-- Add supplied covariance and mean allowances, pay for native square-root
and arithmetic rounding, and return outward-padded finite endpoints. The
correctness theorem requires nonnegative finite allowances and multiplier. -/
def bounds (mean variance covarianceError meanError multiplier : Float)
    : Except Error Interval := do
  let v1 ← finite (variance + covarianceError)
  let inflated ← finite (v1 + padding)
  let root ← finite inflated.sqrt
  let scaled ← finite (multiplier * root)
  let r0 ← finite (scaled + meanError)
  let radius ← finite (r0 + padding)
  let lower0 ← finite (mean - radius)
  let upper0 ← finite (mean + radius)
  let lower ← finite (lower0 - padding)
  let upper ← finite (upper0 + padding)
  return ⟨inflated, radius, lower, upper⟩

end Kalman.Implementation.UncertaintyIntervals
