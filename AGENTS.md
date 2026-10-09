# Kalman development

- Keep source equations and attributed interpretations in `Kalman/Definitions/`.
  Record source locations and project choices in `docs/paper-and-spec.md`.
- Keep executable native `Float` algorithms in `Kalman/Implementation/`, with
  shared storage and arithmetic helpers there. Runtime modules must not import
  correctness, proofs, or test tooling, even transitively.
- Reserve `Kalman/Implementation/Correctness/` for noteworthy native filter
  guarantees and their shared decoding relations, grouped by verified result
  with section banners and proof-witness references on result statements.
  Put exact Real theorem statements in `Kalman/Definitions/Theorems/` and
  group them by result (positive definiteness, formulation equivalence, or
  sensitivity). Keep definitions needed to express these results beside their
  statements. Put profiles, intermediate contracts, and other definitions used
  only by proofs in `Kalman/Proofs/`, with their witnesses or proof support.
  Definitions and implementations must load without proof modules or tests,
  even transitively. Definitions must not depend on implementations;
  implementations may depend on definitions. Runtime modules must not import
  correctness.
  Keep the top level of `Kalman/Definitions/` limited to source equations and
  decoded input. Keep top-level implementation files limited to executable
  algorithms and runtime helpers. Put theorem-only definitions under
  `Definitions/Theorems/` and correctness-only definitions under
  `Implementation/Correctness/`; add only definitions needed by specifications
  or result statements. Put completed theorems in `Kalman/Proofs/`; never substitute
  `sorry`, `admit`, or project axioms for proofs.
  State the difference between an unproved contract and a completed theorem.
- Use domain-specific module names and namespaces matching their paths. Keep
  `Kalman/` free of files and use the root `Kalman.lean` as the public entry point.
  Give each main result file one namespace and one consolidated `open` block.
  Use descriptive declaration names and section banners instead of nested
  namespaces for domains, horizon results, or dense-output results.
- The decoded native input is owned by `Kalman/Definitions/Input`. Covariance
  matrices and covariance factors are different working representations of it.
  Interpret the same finite input values exactly when comparing with `Real`.
- Specify operation order, exceptional-value behavior, and any symmetry repair
  explicitly. A rounded dense Gram matrix needs a separate positivity argument.
- Keep meaningful executable regressions in `Kalman/Tests/`, and pin external
  libraries. Record the actual domain and native-model bridge of imported bounds.
- Format Lean with `make fmt`, using leanfmt's default width of 90 columns.
  Run `make check` for extra Lean linters, import boundaries, proof audits,
  formatter checks, tooling checks, and native regressions.
- Use Lean and Mathlib 4.34.1. Keep sibling projects unchanged. Do not add CI,
  ports, automation, or commits unless requested.
