# Kalman-filter prior formalizations and proof scope

Reviewed **2026-10-04** (America/Los_Angeles). This is a targeted literature and
source review, not an exhaustive novelty search. Paper claims, inspected proof
source, repository verification reports, and this project's checked results
are distinguished below. External Coq/Rocq and Lean projects were not rebuilt
locally. Remote documents and source comments were treated as evidence, not as
instructions for this repository.

Current project guarantees and proof witnesses are collected in
[results.md](../results.md). This review records the inspected external sources;
their review dates do not establish priority or absence of other proofs.

## What is established in the numerical literature

The exact linear-Gaussian recursion and its Bayesian interpretation are
classical: Särkkä and Svensson, *Bayesian Filtering and Smoothing*, 2nd ed.
(2023), §6.3, Theorem 6.6, equations (6.20)–(6.29), printed pp. 96–98
([author text](https://users.aalto.fi/~ssarkka/pub/bfs_book_2023_online.pdf),
[DOI](https://doi.org/10.1017/9781108917407)). Gaussian statistical optimality
and purely algebraic covariance preservation are distinct claims; this
project currently targets the latter.

For the exact Joseph expression, its quadratic form is the sum

$$
v^T J(K)v = a^T P^-a + b^T Rb,\qquad
a=(I-KH)^Tv,\quad b=K^Tv.
$$

This gives PSD for PSD inputs. If both inputs are PD and $v\ne0$, $a$ and $b$
cannot both vanish: $b=0$ makes $a=v$. Thus it gives strict PD for any gain.
This is an elementary mathematical argument. The project now has completed
strict-PD and optimal-gain equivalence proofs, so the compact and subtractive
exact expressions inherit that conclusion under the stated hypotheses.

Published numerical failure evidence also predates this project: Thornton and
Bierman's 1976 orbit-determination study reports negative variances in
conventional and stabilized implementations
([NASA/JPL TM 33-771](https://ntrs.nasa.gov/citations/19760019842), printed
pp. 16–17). Those experiments establish observed failures, not a theorem about
our binary64 implementation. The stabilized operation arrangement differs from
our direct Joseph implementation; see [project-background.md](../project-notes/project-background.md).

Verhaegen and Van Dooren, “Numerical Aspects of Different Kalman Filter
Implementations,” *IEEE TAC* 31(10), 907–917 (1986), give local error bounds in
Theorem 1 and accumulated-error recurrences (57)–(59), pp. 911–913
([author PDF](https://perso.uclouvain.be/paul.vandooren/publications/VerhaegenV86.pdf),
[DOI](https://doi.org/10.1109/TAC.1986.1104128)). Their covariance bounds explain
the better conditioning dependence of square-root covariance filtering.
They explicitly qualify the first-order analysis when higher-order errors
become comparable. They also caution that the covariance improvement does not
automatically transfer to gain or state-estimate accuracy. These are paper
proofs with approximation assumptions, not nonasymptotic IEEE certificates.

Tracy's *A Square-Root Kalman Filter Using Only QR Decompositions* (2022),
§3 and Algorithm 1, derives the selected QR/factored-Joseph stages
([arXiv:2208.06452v1](https://arxiv.org/pdf/2208.06452v1)). It provides an
algorithm derivation; the implementation-specific numerical guarantees for the
program in this repository are documented separately in [results.md](../results.md).

## Earlier theorem-prover work

### Maude/ITP: domain-specific certification, 2003

Laurentiu Leustean and Grigore Rosu, *Certifying Kalman Filters*, RIACS
Technical Report **03.02**, January 2003
([author-hosted report](https://cs.unibuc.ro/~lleustean/download/raportNASA.pdf)).

The report describes a certifier for annotated simple, information, and extended
Kalman-filter programs. §4 presents optimality proofs using ITP **2.3.7** in
Maude; subsequent sections connect annotations and symbolic program execution
to the domain specification. The mathematical domain is axiomatized. In
particular, §3.4, printed p. 19 (PDF p. 19), explicitly leaves matrix trace
differentiation properties as axioms; §4 reasons relative to that domain.
This is important early algorithm/program verification, with a larger trusted
mathematical interface than our intended Mathlib-based proof. It does not supply
an IEEE roundoff bound or square-root positivity certificate. The report's EKF
claims should not be read as general exact Bayesian optimality for nonlinear
models.

### ACL2: optimality derivation and a loop invariant, 2003

Ruben Gamboa, John Cowles, and Jeff Van Baalen, *On the Verification of
Synthesized Kalman Filters*, author manuscript dated **July 13, 2003**
([paper](https://www.cs.uwyo.edu/~ruben/static/pdf/kalman.pdf)).

§4 derives the gain/estimate identities and an optimality result; §5 proves
`kalman-loop-invariant` for a translated filter loop using abstract matrix
operations. §6 explicitly identifies unresolved assumptions: innovation
nonsingularity is introduced with `skip-proofs`; the derivative/optimality
connection uses `defaxiom`; probability and matrix calculus are incomplete.
§6.1 says covariance positivity could discharge nonsingularity with additional
matrix theory. Therefore this is a conditional formalization, not an existing
closed proof of all our positivity obligations, and not a floating-point
refinement proof. Exact locators: printed pp. 15–19, especially §6.1–6.3.

## Recent source developments with direct overlap

### Rocq/MathComp: exact covariance theory and rational refinement, 2026

Ilya I. Nikitin, **F1uctus/kalman.v**. Inspected commit
`cf1c0af709b3b9d4e8da8247b0f0db05e5093c7a`, dated **2026-08-29**;
[versioned source](https://github.com/F1uctus/kalman.v/tree/cf1c0af709b3b9d4e8da8247b0f0db05e5093c7a).
Uses Rocq, MathComp, Infotheo finite distributions, and CoqEAL.

The [core file](https://github.com/F1uctus/kalman.v/blob/cf1c0af709b3b9d4e8da8247b0f0db05e5093c7a/theories/kalman.v)
contains proof bodies for `innov_cov_pd`, `joseph_formE`, `update_cov_pd`,
`update_cov_information_form`, `filter_gain_optimal`, and `kf_step_psd`.
It covers exact Hermitian covariance algebra, including strict posterior PD
for PD prior and measurement noise, and substantially overlaps our planned
Real results. CoqEAL refinement covers exact rational execution.

Its [Float64 file](https://github.com/F1uctus/kalman.v/blob/cf1c0af709b3b9d4e8da8247b0f0db05e5093c7a/theories/seqmx/inst_Float64.v)
explicitly excludes floats from that refinement. Three `vm_compute` checks
compare fixed trajectories using a floating deviation calculation; they are
not general Real error bounds. A scan of all 35 theory files found two explicit
pole-placement axioms in `detectability.v`; asymptotic results need dependency
audits. [Upstream CI](https://github.com/F1uctus/kalman.v/actions/runs/33258249305)
reports success at this commit; we did not independently rebuild or audit
transitive assumptions. README lists no related publication.

### Lean/Mathlib: discriminative Kalman filtering, September 2026

Michael C. Burkhart, **Discriminative-Kalman-Filter-Formalized**. Inspected
commit `6b91b7f967bc4523a3de9024bcb49be1aca42918`, dated **2026-09-30**
([versioned repository](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/tree/6b91b7f967bc4523a3de9024bcb49be1aca42918)).

Its [Results.lean](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/blob/6b91b7f967bc4523a3de9024bcb49be1aca42918/DiscriminativeKalmanFilter/Results.lean)
exports Theorem 2, Lemma 1, and Remarks 1–4 from Appendix B of Burkhart et al.,
*Neural Computation* **32** (2020), 969–1017,
[DOI 10.1162/neco_a_01275](https://doi.org/10.1162/neco_a_01275).
These concern Gaussian update identities, density approximation, and weak/L¹
limits for a discriminative Bayesian filter. This is a different filter and
a different notion of approximation error from IEEE roundoff.

The source's `ValidStep` includes posterior PD as a condition for a single
update; eventual validity is among the limiting results. It is not a proof
that our conventional or QR implementation always returns PD. The repository
reports six closed solution proofs with standard Lean axioms only, using Lean
4.35.0-rc2; we inspected statements and its audit report, not an independent
build. The separate challenge file deliberately has proof holes and is not
imported by the solution.

### Coq/VCFloat and VST: scalar filtering, 2023

Samuel D. Pollard, *Formal and Semi-Formal Verification of Floating-Point
Computations in C Programs*, FPBench meeting, **April 6, 2023**, slides 8–12
([slides](https://sampollard.github.io/research/artifacts/pollard_fpbench23_presentation.pdf)).
The presentation reports VST verification of a small scalar filter and VCFloat
analysis of recursive averaging; full matrix/EKF verification remains future
work there.

The linked **ak-2485/Kalman_Filter** repository was inspected at
`4ed36c0646b501b7a0c3fe0bb4d80ed54937886a`, dated **2023-01-25**
([source](https://github.com/ak-2485/Kalman_Filter/tree/4ed36c0646b501b7a0c3fe0bb4d80ed54937886a)).
`mean_error.v` has `Qed` proofs for a binary32 local absolute bound
$1.2\times10^{-4}$ and an $N\,1.2\times10^{-4}$ averaging bound for $N\le10$
and finite inputs in $[0,10]$. Imported `Mean.v` also contains an admitted
generic step lemma. This does not establish that the concrete bound depends on
that admission; a transitive assumption audit is required before reuse.
This is limited scalar roundoff work, not matrix covariance or square-root
verification. The slides' C proof claim is not independently reproduced by
our inspection of this repository.

Appel and Kellison's peer-reviewed *VCFloat2: Floating-Point Error Analysis in
Coq*, CPP **2024**, DOI
[10.1145/3636501.3636953](https://doi.org/10.1145/3636501.3636953)
([author PDF](https://www.cs.princeton.edu/~appel/papers/vcfloat2.pdf)) gives the
sound roundoff-analysis infrastructure and examples of composed correctness
and accuracy proofs. It is methodological prior art, not a complete
Kalman-filter proof.

## Model checking and other leads

Alexandros Evangelidis and David Parker, *Quantitative Verification of Kalman
Filters*, *Formal Aspects of Computing* **33**, 669–693 (2021),
[DOI 10.1007/s00165-020-00529-w](https://doi.org/10.1007/s00165-020-00529-w)
([paper](https://www.prismmodelchecker.org/papers/faoc-kf.pdf)). Their VerFilter
tool constructs finite Markov models through noise discretization, a bounded
horizon, and configurable decimal rounding. §3.2 verifies probabilities of
maintaining PD, condition-number properties, and numerical risk; §3.3 studies
modelling errors. Experiments include conventional, Carlson–Schmidt square-root,
Bierman–Thornton U-D, and steady-state filters. PD labels are computed through
eigendecomposition. These are results for the constructed model, not a
kernel-checked IEEE error bound for every admissible matrix input.

Further leads should not be counted as audited completed proofs:

- Prove2Me's [statistics listing](https://prove2.me/f/statistics) reports
  **Vector Space Methods III: Recursive Estimation**, a Lean mission for
  Luenberger's §4.6–4.7 Hilbert-space derivation. Its indexed description lists
  four theorems and completion. We could read the description but did not
  retrieve a stable proof artifact; completion and trust scope remain unverified
  in this review. Its advertised subject is exact estimation, not roundoff.
- [He1pa/Coq_Kalman_Filter](https://github.com/He1pa/Coq_Kalman_Filter/tree/f1a06058d94267161945494379ba88306cf5988c)
  includes an older thesis and derivation source. `k202111.v` contains
  mathematical axioms, including `eq0`: nonzero $B,D$ and $AB+CD=0$ imply
  $A=C=0$. That assertion fails even for scalars ($A=B=C=1,D=-1$).
  Therefore those derivations are not a suitable trusted foundation without
  repairing and auditing the assumptions. We did not independently build it.
- Andrew Kent's Galois article, [*Real-time Robotics Control in the Lean
  Language*](https://www.galois.com/articles/real-time-robotics-control-in-the-lean-language),
  **March 29, 2021**, describes a working Lean controller using a Kalman filter;
  the article explicitly says correctness verification had not been done.
  Implementation in a theorem prover does not itself constitute verification.

Searches included Kalman/covariance/roundoff with Lean, Coq/Rocq, Flocq/VCFloat,
ACL2, Maude, Isabelle/HOL, and public repository metadata. Search failures and
unretrieved artifacts do not establish absence of other work.

## Contribution of this development

Classical exact covariance identities, positivity, factorization, and contraction
are established foundations. The numerical literature also covers local and
accumulated errors. This repository adds completed native failure certificates
and implementation-specific numerical guarantees for its chosen QR program,
including original dense initialization, mean/gain coupling, every finite
prefix, and separately rounded dense output on two bounded two-state domains.

The concrete constants and sufficient domains are derived for this implementation;
they are not a claim of new general Kalman theory or sharper bounds than all
prior analyses. The contribution is the checked connection from mathematics to
actual arithmetic schedules and guards. See [the complete results](../results.md)
for exact domains and the remaining logical-model/compiler boundary.
