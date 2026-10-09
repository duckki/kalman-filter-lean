# Build and validation

## Dependencies

The project uses `leanprover/lean4:v4.34.1` through [elan](https://github.com/leanprover/elan).
Mathlib is pinned to `v4.34.1`, commit
`d13f23b723b8a846827a245b89c10fc7d3f11612` in the Lake manifest.
FLARE is a Git dependency pinned to
[`55fd803a36d424ee3428e9a3085ef87b7829ee79`](https://github.com/duckki/flare-lean/tree/55fd803a36d424ee3428e9a3085ef87b7829ee79),
also on Lean/Mathlib 4.34.1. Lake fetches it automatically; no sibling checkout
is needed. The project also pins `leanfmt v0.4.5` directly at commit
`65d69c8dc2dfd0aa69fd4132d48f38b7af9a57ef`.

The numerical foundation, extracted reusable results, and imported native/model
bridges are recorded in
[the library assessment](references/floating-point-library-assessment.md).
Both Kalman and FLARE use GPL-3.0-only; their dependency licenses remain separate.

## Build

From the Kalman repository root:

```sh
lake update
lake exe cache get
make
```

`make` builds and runs the repository checks. `make build` (or `make b`) compiles
the public library, exact specification regressions, project-wide theorem axiom
audit, and native regression executable. `make test` runs the native executable.

Lake stores fetched dependencies and generated artifacts under `.lake/`.
The Git pin selects the reviewed FLARE source independently of any other local
checkout.

## Validation coverage

The specification checks exercise exact prediction, innovation, covariance
forms, information correction, and factor equations. The native suite checks
certified failure fixtures, factor/dense positivity differences, arithmetic
boundary cases, and both supported long-horizon operating profiles.
Independent reference checkpoints for 256-step correlated and diagonal runs
were reproduced at 120 and 160 decimal digits; the tests compare native output
at a `10⁻¹²` tolerance. That tolerance supplements the proved bounds and is not
itself a theorem.

The axiom audit covers every project theorem and allows only `propext`,
`Classical.choice`, and `Quot.sound`. It excludes admissions and project axioms.
Native agreement tests do not establish compiler/hardware refinement. The
complete domains and mathematical guarantees are in [results.md](results.md).

## Linting and repository checks

`make lint` runs `lake lint`: source hygiene checks, an incremental build with
Lean's extra linters and warnings treated as errors, and import checks using
Lean's dependency reader. It includes untracked Lean files, rejects orphan
modules and import cycles, and checks layer boundaries transitively.
Definitions cannot depend on implementations, proofs, or tests; runtime
implementations cannot depend on correctness, proofs, or tests. Correctness
statements load independently of proofs and tests. The build also runs the
existing specification checks and theorem axiom audit.

`make check` (or `make c`) additionally checks the tooling, formatting, and native
regressions. The [Makefile](../Makefile) and [lint driver](../scripts/lint.py)
contain the commands and boundary rules.

## Formatting

The directly pinned formatter is `leanfmt v0.4.5`, using its default width of
90 columns:

```sh
make fmt
make fmt-check
```

The [formatter wrapper](../scripts/fmt.py) selects all tracked and untracked Lean
sources, including nested proof directories and tooling. It restores any file
if the formatter changes non-whitespace content. `make fmt-check` checks without
writing; the wrapper also accepts `--jobs` to limit parallel workers.
