import Kalman.Implementation.LinearAlgebra

/-! Optional diagonal-variance allowance for the completed Joseph horizon
certificate. Add exactly 2^-29 in binary64, then apply the finite-result guard.
The extra margin beyond the 2^-30 certificate pays for this addition's rounding.
This helper does not change the filter state or evaluate interval endpoints. -/

namespace Kalman.Implementation.UncertaintyInflation

open Kalman.Definitions.Input Kalman.Implementation.LinearAlgebra

/-- Rounded conservative allowance, certified on the Joseph invariant range. -/
def inflateVariance (variance : Float) : Except Error Float :=
  finite (variance + 0.00000000186264514923095703125)

end Kalman.Implementation.UncertaintyInflation
