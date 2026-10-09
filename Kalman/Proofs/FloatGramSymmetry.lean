import Kalman.Proofs.FloatDenseError
import Flare.Matrix.GramSymmetry

/-! Two-state rounded Gram symmetry through Kalman's native error adapter.
The authoritative word-symmetry and Hermitian-decoding proofs live in FLARE. -/

namespace Kalman.Proofs.FloatGramSymmetry

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.Correctness.InputInterpretation

alias native_mul_comm := Flare.Binary64.Arithmetic.native_mul_comm

/-- The separately computed off-diagonal words are identical on every
successful finite two-state Gram multiplication. No magnitude or PD premise
is needed, so this also covers gradual underflow. -/
theorem multiply_gram_two_symmetric (a r : Array Float)
    (ha : a.all Float.isFinite = true)
    (hr : multiply 2 2 2 a (transpose 2 2 a) = .ok r)
    : entry 2 r 0 1 = entry 2 r 1 0 := by
  exact Flare.Matrix.GramSymmetry.multiply_gram_two_symmetric a r ha
    ((FloatDenseError.adapt_ok _ r).mp hr)

/-- Exact Real decoding of the successful rounded two-state Gram is Hermitian. -/
theorem multiply_gram_two_hermitian (a r : Array Float)
    (ha : a.all Float.isFinite = true)
    (hr : multiply 2 2 2 a (transpose 2 2 a) = .ok r)
    : (matrix 2 2 r).IsHermitian := by
  exact Flare.Matrix.GramSymmetry.multiply_gram_two_hermitian a r ha
    ((FloatDenseError.adapt_ok _ r).mp hr)

end Kalman.Proofs.FloatGramSymmetry
