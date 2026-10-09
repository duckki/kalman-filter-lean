# Floating-point foundation and library assessment

The 2026-10-04 source assessment selected **FLARE** for the native arithmetic
foundation. This file records the reviewed interfaces, exact model bridges,
and alternative libraries inspected at that time, including **FloatLib**.
No equivalence between these libraries is assumed.

## FLARE: adopted dependency

Source: [duckki/flare-lean](https://github.com/duckki/flare-lean).
The current Git dependency is pinned to
[`55fd803a36d424ee3428e9a3085ef87b7829ee79`](https://github.com/duckki/flare-lean/tree/55fd803a36d424ee3428e9a3085ef87b7829ee79),
using Lean/Mathlib 4.34.1 and leanfmt 0.4.5.

The initial assessment used `15c4847df7229c8346a8168cfd4551db0597fb0e`;
the 2026-10-05 proof recheck used `c7639ee9efb9b30c1c5ecae4f3a9dd6fe30ef0b0`.
The current revision adds reusable results extracted from Kalman with their
assumptions and constants preserved, and GPL-3.0-only licensing. Its
[theorem guide](https://github.com/duckki/flare-lean/blob/55fd803a36d424ee3428e9a3085ef87b7829ee79/docs/reference.md)
and [provenance record](https://github.com/duckki/flare-lean/blob/55fd803a36d424ee3428e9a3085ef87b7829ee79/docs/provenance.md)
describe those exports. FLARE's complete checks and Kalman's build, theorem
axiom audit, and native regressions validate the pinned source.

The relevant source interfaces were inspected directly:

| Interface | What it actually provides | Limit retained for Kalman |
| --- | --- | --- |
| `Flare.Binary64.Value.value` / `modelToReal` | Exact Real meaning through Lean's logical `Float.Model`; both signed zeros denote zero; NaN/infinity have no value in the option-valued interpretation | Totalized helper values need separate finiteness premises |
| `Flare.Binary64.Nearest.{add,sub,mul,div}_error_nearest` | Native scalar bounds including underflow allowance; magnitude hypotheses also establish finite output | Typical exact-result bound is $2^{1000}$; division requires a nonzero decoded divisor |
| `Flare.Binary64.Sqrt.sqrt_error_nearest` | A native square-root bound for finite, nonnegative decoded input | Domain premises must be discharged for each Cholesky/QR square root |
| `Flare.Matrix.Dense.multiply` and `Dense.solveSPD` | Executable native, separately rounded dense multiplication and LDLᵀ solve | Callers supply correct array shapes; factorization reads the lower triangle |
| `Flare.Matrix.Multiplication.multiply_accuracy` | Success, finite storage, and entrywise product error against the exact decoded product | At most 32 terms; $0\le E\le1016$ and exact products bounded by $2^E$; entry error at most `inner * 2^(E-45)` |
| `Flare.Matrix.SolveAccuracy.solveSPD_accuracy` | Successful solve and an a posteriori solution-error enclosure | Dimension at most 12, lower bound $A\succeq(3/16)I$, entries at most 1024, RHS magnitude/exponent restrictions, and actual intermediate residual terms |
| `Flare.Analysis.MatrixError`, `Conditioning`, `SchurComplement`, `GramBounds` | Real norm, conditioning, and perturbation tools | Mathematical results do not by themselves certify a new native QR loop |

For example, the nearest addition theorem bounds error by
$2^{-53}(|x+y|+2^{-1022})$ under its stated finite-input/range hypotheses.
This is a theorem about the actual native logical operations, rather than an
unproved rounding-law axiom. Its overflow profile is still a real restriction.

The Kalman `Dense` module reuses FLARE's multiplication and SPD-solve definitions
through an explicit error adapter. FLARE's theorem conclusions use its
`Matrix.Operations` adapter; the application proofs transfer successful
results across these adapters rather than merely cite a similarly named theorem.
The arithmetic schedule itself is unchanged. Kalman's Cholesky, triangular
factor solve, and Householder QR are new definitions; existing LDLᵀ theorems do
not automatically cover them.

The Kalman runtime supports dimensions up to 32 for exploration. That does not
extend FLARE's solve theorem from 12 to 32 or discharge its conditioning bounds.
The certified numerical profiles are narrower than the runtime API.

## FloatLib: newly announced alternative

Robert Joseph George, Will Adkisson, and Anima Anandkumar,
[“FloatLib: Verified Floating-Point Arithmetic in Lean”](https://arxiv.org/abs/2609.19352),
submitted 2026-09-16. Primary project announcement:
[LeanDojo FloatLib](https://leandojo.org/floatlib.html). Primary code:
[lean-dojo/FloatLib](https://github.com/lean-dojo/FloatLib).

Inspected revision: `1e83f09ed8c41a953cf8f93d26c210778177b94a`, 2026-09-30.
Its toolchain and Mathlib requirement are **4.34.0**, not 4.34.1. It was fetched
for inspection, but is not a dependency of this project's final Lake configuration.
Compatibility of its full build with this project's 4.34.1 pins was not established.

Source-level findings at that revision:

- [Native representation](https://github.com/lean-dojo/FloatLib/blob/1e83f09ed8c41a953cf8f93d26c210778177b94a/FloatLib/Floats/Formats/IEEE754/Native/Representation.lean)
  proves `ExecFloat.Binary.toFloat_ofFloat` for binary64. This is a representation
  round trip, not agreement of every native arithmetic operation.
- [Native addition/subtraction](https://github.com/lean-dojo/FloatLib/blob/1e83f09ed8c41a953cf8f93d26c210778177b94a/FloatLib/Floats/Formats/IEEE754/Native/AddSub.lean)
  has `toModel_ofFloat_add_of_isFinite`, `ofFloat_add_of_isFinite`, and corresponding
  subtraction bridges, with finite-input hypotheses. These concern Lean's logical
  native model; they do not verify external CPU instructions.
- [Executable error bounds](https://github.com/lean-dojo/FloatLib/blob/1e83f09ed8c41a953cf8f93d26c210778177b94a/FloatLib/Floats/Formats/BinaryInterchange/Analysis/Error.lean)
  prove `Model.abs_toReal_{add,sub,mul,div,sqrt,fma}_sub_le` with format-specific
  half-ULP bounds. Addition, subtraction, multiplication, division, and FMA require
  finite outputs; division also requires a nonzero divisor. Square root retains
  a nonnegative/sign-domain premise. These model theorems are substantive error
  results, not just equality of a backend to a specification.
- Its generic [reduction error layer](https://github.com/lean-dojo/FloatLib/blob/1e83f09ed8c41a953cf8f93d26c210778177b94a/FloatLib/Numerics/Reduction/Error.lean)
  is a candidate for future dot-product composition. This assessment did not
  audit a complete native binary64 multiplication/division bridge or Kalman/QR
  matrix-error theorem. Those would need checking before changing foundations.

FloatLib covers many formats and certified software backends. Its unchecked
host-FPU backend is a separate trust choice. Format breadth and conformance-test
counts do not establish a Kalman covariance error or positivity theorem.

## Other research candidates

[FLoPS](https://github.com/rutgers-apl/FLoPS), by Tung-Che Chang, Sehyeok Park,
Jay P. Lim, and Santosh Nagarakatte, formalizes P3109 representations and
operations; [arXiv:2602.15965](https://arxiv.org/abs/2602.15965) describes the work.
It is relevant background, but not the newly announced September FloatLib.
P3109 theory would require an explicit native IEEE binary64 bridge for this task.

[FloatSpec](https://github.com/Beneficial-AI-Foundation/FloatSpec), assessed in
the original project goal, remains another candidate. Its README status alone
was insufficient to select it over the directly inspected native/matrix FLARE
interfaces. No claim that either alternative is unsound follows from this choice.

## Use in the completed proofs

FLARE supplies scalar arithmetic and dense linear-algebra interfaces with the
domains listed above. The project supplies its program-specific Cholesky,
triangular-solve, scaled Householder QR, gain, mean, and full-filter proofs.
The original-input QR result derives all prefix conditions on its eight-row
domain; the two full-filter operating domains derive the reached kernel
profiles and uniform accumulated errors, including dense materialization.

These are completed results in [the numerical reference](../results.md), not
claims about every runtime dimension or every alternative floating-point
library. The wider-domain limitations and hardware/compiler boundary remain
explicit. See [development.md](../development.md#dependencies) for reproducible
dependency setup and the local-path lock limitation.

## Reusable results contributed to FLARE

The Kalman development contributed these general facts with their existing
assumptions and constants. FLARE has no dependency on Kalman's model or algorithms.

| FLARE module | Imported result and domain |
| --- | --- |
| `Analysis.EntrywiseError` | Absolute entrywise comparison, algebraic propagation, symmetric-matrix spectral margins, and right-system residual accuracy; arbitrary finite dimensions, with the bounds and conditioning premises in each statement |
| `Analysis.ErrorRecurrence` | Finite-horizon recurrence and nonexpansive budget; step-error recurrence and nonnegative sensitivity are premises |
| `Analysis.Householder` | Coordinate bound and exact column-Gram preservation for an exactly unit vector |
| `Binary64.Arithmetic` | Commutativity of logical native multiplication, including canonical exceptional results |
| `Binary64.SignMultiplication` | Exact real value of multiplication by ±1 on every finite binary64 value, including signed zero and subnormals |
| `Binary64.Sqrt` | Positive finite square root and squared residual `(2u+u²)x`, with `u=2⁻⁵³`, for any positive finite input |
| `Matrix.GramSymmetry` | Matching off-diagonal Float words and Hermitian decoding of successful two-state Gram multiplication from finite input; no scale or PD premise |

Kalman's aliases preserve the mathematical predicates. The rounded Gram
wrappers use the proved error-adapter equivalence for the identical native
`Dense.multiply` operation. Filter profiles and initialization-to-horizon
guarantees remain in Kalman. The source hashes and revision are recorded in
FLARE's `docs/extraction-manifest.json`.
