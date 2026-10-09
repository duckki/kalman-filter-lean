# Project layout and APIs

The public entry point is [Kalman.lean](../Kalman.lean). Runtime users can import
`Kalman.Implementation.CovarianceFilter` or
`Kalman.Implementation.SquareRootFilter` without loading proof infrastructure.
The [results reference](results.md) owns mathematical guarantees and numerical
bounds; this document explains storage, modules, and the execution interface.

## Directory map

```text
Kalman.lean                         Public specifications and proof interfaces
Kalman/Definitions/                 Source equations and decoded input
Kalman/Definitions/Theorems/         Main exact Real result statements
Kalman/Implementation/              Executable Float algorithms and helpers
Kalman/Implementation/Correctness/   Main native guarantees and decoding relations
Kalman/Proofs/                      Completed theorems
Kalman/Tests/                       Exact checks, native regressions, axiom audit
docs/                              Public specification and reference documents
docs/project-notes/                 Internal project background and proof-development history
```

Namespaces match module paths. Definitions are standalone; implementations may import
definitions. Neither layer imports project proofs or tests, including transitively.
Runtime algorithms also import no correctness modules. The top-level `Kalman.lean` can
expose all layers; `Kalman/` itself contains only domain-specific subdirectories.

## Review path

1. [Definitions/LinearModel.lean](../Kalman/Definitions/LinearModel.lean): exact
   model and state. The strict PD domain lives beside its theorem statements.
2. [Definitions/CovarianceRecursion.lean](../Kalman/Definitions/CovarianceRecursion.lean):
   prediction, posterior formulations, information correction, and trajectory.
3. [Definitions/FactorRecursion.lean](../Kalman/Definitions/FactorRecursion.lean):
   lower-factor interpretation, exact QR stage relations, and U-D storage.
4. [Definitions/Input.lean](../Kalman/Definitions/Input.lean): shared native
   arrays, validation, and errors.
5. [Implementation/LinearAlgebra.lean](../Kalman/Implementation/LinearAlgebra.lean): arithmetic
   adapters, Cholesky, LDLᵀ, and triangular solves.
6. [Implementation/CovarianceFilter.lean](../Kalman/Implementation/CovarianceFilter.lean):
   compact, subtractive, and direct Joseph filtering.
7. [Implementation/OrthogonalFactorization.lean](../Kalman/Implementation/OrthogonalFactorization.lean)
   and [SquareRootFilter.lean](../Kalman/Implementation/SquareRootFilter.lean):
   scaled Householder QR and factored Joseph filtering.
8. [Definitions/Theorems/](../Kalman/Definitions/Theorems),
   [Implementation/Correctness/](../Kalman/Implementation/Correctness),
   and [Proofs/](../Kalman/Proofs): main result statements, definitions needed to
   express them, and completed proofs.
9. [Tests/](../Kalman/Tests): executable validation and the proof audit.

## Storage and validation

`Definitions.Input.Model` owns dimensions and row-major arrays for $F,H,Q,R,z$.
`Input.State` stores mean and dense covariance; `Input.FactorState` stores mean
and a lower covariance factor as another representation of the same input.
The Real comparator decodes the original finite words exactly.

Checked APIs accept dimensions 1–32, require exact array shapes and finite
entries, and require symmetric noise arrays. Dense covariance is not repaired
or required to be symmetric, so conventional numerical failure remains visible.
Factor states additionally require zero upper triangle and positive diagonal.
Both zero signs are accepted; NaN and infinities are rejected.

Factorization checks reject nonpositive pivots and arithmetic kernels reject nonfinite
intermediates. A successful input validator alone does not establish the conditioning or
PD premises of an accuracy theorem. Full policy and rejection order are recorded in [the
decoded input contract](paper-and-spec.md#authoritative-decoded-input-contract).

## Native APIs

Covariance filtering exposes `predict input state`, `update form input prior`,
and `step form input state`, returning `Except Input.Error Input.State`.
`form` is `.compact`, `.subtractive`, or `.joseph`. Successful covariance updates
can still return an invalid covariance on some inputs; validation alone does not
guarantee positivity.

Square-root filtering starts with `fromCovariance input state`, then calls
`predict`, `update`, and `step` on `FactorState`, retaining factor storage between
steps. `SquareRootFilter.run inputs initial count` executes checked
time-varying steps and propagates the first prefix error. It imports no proof
infrastructure.

`materialize n factorState` optionally returns a rounded dense covariance; it is
not called by the filter. The complete two-state theorems prove this output's
accuracy and positivity separately from the exact Gram denoted by the factor.

`predict` and `update` share full model validation, including observation fields
unused by prediction. Unchecked helpers require their callers to supply valid
storage and finite operands; public comparisons use the checked operations.

## Arithmetic and proof interfaces

Native dot products visit ascending inner indices with separately rounded
multiply and add operations. Kernels use no FMA or exact rational execution.
Cholesky and LDLᵀ read the lower triangle; no implicit dense symmetry repair is
performed. The QR sign convention retains positive diagonal factors and writes
specified positive-zero tails. See [the operation choices](paper-and-spec.md).

Main exact Real statements are in `Definitions/Theorems/`; main native
statements and shared decoding relations are in `Implementation/Correctness/`.
Definitions needed to express a main result live beside that result. Profiles,
intermediate contracts, and auxiliary statements used only by proofs stay in
`Proofs/`. Importing a statement module alone does not prove its propositions.

The top levels stay small: six source-equation/input modules in `Definitions/` and four
executable modules in `Implementation/`. Reusable analysis is supplied by FLARE; Kalman
has no separate analysis layer. The statement modules load independently of the project
proof modules.

Each main result has a comment identifying its proof witness.
Section banners separate the guarantees and the definitions needed to read them.
Each result file uses one namespace matching its filename and one consolidated
`open` block. Names such as `HorizonDomain` and `DenseHorizonAccuracy` distinguish
the concepts without nested `Horizon` or `DenseOutput` namespaces. Family-specific
constants from another file remain qualified when that improves readability.
[The result catalogue](results.md#public-error-statements) records their domains
and exact bounds.

| Exact Real result | File in `Definitions/Theorems/` |
| --- | --- |
| Full-step covariance PD preservation and Joseph PD at any gain | [CovariancePositiveDefiniteness.lean](../Kalman/Definitions/Theorems/CovariancePositiveDefiniteness.lean) |
| Covariance formulas, complete information update, and exact square-root stages | [FormulationEquivalence.lean](../Kalman/Definitions/Theorems/FormulationEquivalence.lean) |
| Prediction/correction sensitivity and diagonal contraction, with the pure relations and domains they use | [RecursionSensitivity.lean](../Kalman/Definitions/Theorems/RecursionSensitivity.lean) |

`InformationFormAgrees` compares covariance and mean. `SquareRootStagesAgree`
compares the covariances denoted by exact QR factors. Shared perturbation
relations and their budgets are inside `RecursionSensitivity.lean`; proof-only invariant
helpers are in the corresponding proof modules.

| Native result or shared definitions | File in `Implementation/Correctness/` |
| --- | --- |
| Compact/subtractive negative-covariance certificates | [CovarianceCounterexamples.lean](../Kalman/Implementation/Correctness/CovarianceCounterexamples.lean) |
| Direct Joseph covariance-evaluation error | [JosephCovarianceEvaluation.lean](../Kalman/Implementation/Correctness/JosephCovarianceEvaluation.lean) |
| Retained-factor PD and rounded covariance accuracy, with shared factor/comparison relations | [SquareRootFilterProperties.lean](../Kalman/Implementation/Correctness/SquareRootFilterProperties.lean) |
| Correlated-family retained/dense horizon guarantees and their original-input domains | [CorrelatedNoiseFilterAccuracy.lean](../Kalman/Implementation/Correctness/CorrelatedNoiseFilterAccuracy.lean) |
| Fully observed diagonal retained/dense horizon guarantees and their original-input domains | [FullyObservedDiagonalFilterAccuracy.lean](../Kalman/Implementation/Correctness/FullyObservedDiagonalFilterAccuracy.lean) |
| Shared exact decoding, covariance input domain, and independent trace interpretation | [InputInterpretation.lean](../Kalman/Implementation/Correctness/InputInterpretation.lean) |

`CorrelatedNoiseFilterAccuracy.InitializedHorizonAccuracy` states the complete
original-input retained-factor guarantee. Its comment identifies
`FloatInputHorizon.initializedHorizonAccuracy` as the proof witness.
`CorrelatedNoiseFilterAccuracy.InitializedDenseHorizonAccuracy` separately
states the rounded dense guarantee. The diagonal family has corresponding
statements in `FullyObservedDiagonalFilterAccuracy`.

Elementary arithmetic and factorization packages are supporting facts rather
than headline Kalman results. [FloatErrorBounds.lean](../Kalman/Proofs/FloatErrorBounds.lean)
keeps their auxiliary statements with proof witnesses. Operand profiles live
in `Proofs/ArithmeticProfiles`, `CholeskyProfiles`, `QRProfiles`, and
`SquareRootProfiles`. `CorrelatedStages` and `DiagonalStages` hold local-stage
conditions and budgets. [FilterComposition.lean](../Kalman/Proofs/FilterComposition.lean)
holds the conditional step/horizon contracts and composition profiles.
`ErrorPropagation` and `OrthogonalStructure` expose aliases of FLARE results;
`FloatGramSymmetry` proves the bridge through Kalman's native error adapter. Their
numerical claims remain available through the completed proof modules.

All completed project theorems are included in the transitive axiom audit,
including private helpers. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. Counterexample executions use `decide +kernel`, not `native_decide`.
Lean's logical native binary64 model is the proof interface; compiled
hardware/runtime correspondence remains outside these proofs.

## Validation

Exact regression modules check source-equation transcription. The native suite
covers scalar failures, correlated and diagonal trajectories, high-precision
reference checkpoints, rank rejection, signed zeros, subnormals, and overflow.
Tests and proof certificates have separate roles: a regression tolerance does
not become a proved error bound. Commands and dependency versions are in
[development.md](development.md).
