# Kalman-filter prior formalizations and proof scope

Initial review **2026-10-04**; Pollard/VCFloat/Elaenia and Burkhart/DKF follow-ups
reviewed **2026-10-09** (America/Los_Angeles). This is a targeted literature and
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

### Lean/Mathlib: discriminative Kalman filtering, September–October 2026

Michael C. Burkhart, **Discriminative-Kalman-Filter-Formalized**. Inspected
commit `6b91b7f967bc4523a3de9024bcb49be1aca42918`, dated **2026-09-30**
([versioned repository](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/tree/6b91b7f967bc4523a3de9024bcb49be1aca42918)).

The source paper is Michael C. Burkhart, David M. Brandman, Brian Franco,
Leigh R. Hochberg, and Matthew T. Harrison, *The Discriminative Kalman Filter
for Bayesian Filtering with Nonlinear and Nongaussian Observation Models*,
*Neural Computation* **32**(5) (2020), 969–1017,
[DOI 10.1162/neco_a_01275](https://doi.org/10.1162/neco_a_01275).
A [free author-hosted published PDF](https://burkh4rt.github.io/pubs/Burkhart-et-al-2020-Neural-Comput.pdf)
is available; the [author manuscript](https://pmc.ncbi.nlm.nih.gov/articles/PMC8259355/)
is another access route. Page references below use the 49-page published PDF.

#### Algorithm and source locations

DKF uses stationary linear Gaussian state dynamics, with transition $A$,
process covariance $\Gamma$, and stationary covariance
$S=ASA^T+\Gamma$. It approximates the state distribution conditioned on an
observation by $p(Z_t\mid X_t)\approx\mathcal N(f(X_t),Q(X_t))$.
The observation model can be nonlinear and non-Gaussian. Equation (2.7),
printed p. 974 (PDF p. 6), gives

$$
\begin{aligned}
\nu_t &= A\mu_{t-1},\\
M_t &= A\Sigma_{t-1}A^T+\Gamma,\\
\Sigma_t &= \bigl(M_t^{-1}+Q(X_t)^{-1}-S^{-1}\bigr)^{-1},\\
\mu_t &= \Sigma_t\bigl(M_t^{-1}\nu_t+Q(X_t)^{-1}f(X_t)\bigr).
\end{aligned}
$$

The stationary-prior subtraction avoids counting that prior twice. The robust
variant, equation (2.8), printed p. 976 (PDF p. 8), omits $-S^{-1}$ from the
precision. Here $Q(X_t)$ is conditional state covariance and $S$ is stationary
covariance; these differ from this project's process covariance $Q$ and
innovation covariance $S$. Neither DKF variant is implemented in this repository.

#### Six completed Lean results

The public [Results.lean](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/blob/6b91b7f967bc4523a3de9024bcb49be1aca42918/DiscriminativeKalmanFilter/Results.lean)
exports the following Appendix B statements in arbitrary positive finite state
dimension. All computations in these statements are over Real numbers and
probability measures.

| Declaration | Published location | Verified result |
| --- | --- | --- |
| `theorem2` | Theorem 2, p. 1003 (PDF p. 35) | Under A1–A5, the supplied Gaussian approximants have the stated weak limits; their normalized update is eventually a valid Gaussian, concentrates at the limiting state, and has L¹ error tending to zero against the exact update. |
| `lemma1` | Lemma 1, pp. 1007–1010 | Proves the pointwise Gaussian update formula when the precision is valid, and derives eventual validity and concentration from weak convergence of the input Gaussian sequences. |
| `remark1` | Remark 1, p. 1003 | Identifies L¹ distance with the total variation **norm** of the difference of the associated measures. Under the probability-distance convention $\sup_B\lvert\mu(B)-\nu(B)\rvert$, the distance is half that norm. |
| `remark2` | Remark 2, p. 1003 | The posterior limits hold for every supplied pair of Gaussian approximants satisfying the hypotheses, rather than merely for some choice. |
| `remark3` | Remark 3, p. 1004 (PDF p. 36) | The robust update is a valid Gaussian at every index. Eventually its error satisfies the three-term bound (B.2); all three terms and the total L¹ error tend to zero. |
| `remark4` | Remark 4, p. 1004 | With random inputs and explicit measurability assumptions, the conclusions hold in probability and update-validity probability tends to one. |

For Theorem 2, $s_n,u_n$ are exact input densities and $s'_n,u'_n$ are their
Gaussian approximants. The exact posterior is the normalized density
$p_n=\mathrm{normalize}(u_n\,\tau s_n/p)$, where $\tau$ is Gaussian
prediction and $p$ is the stationary density. Exact updates must be valid at
every index. A1–A5 require: $s_n$ converges weakly to a probability measure;
the prior approximation error tends to zero in L¹; $u_n$ concentrates at a
state $b$; its Gaussian approximation error tends to zero in L¹; and the
**exact posterior $p_n$ also concentrates at $b$**. The theorem then proves
$\lVert p_n-p'_n\rVert_1\to0$. Exact posterior concentration is retained as a
hypothesis, not derived solely from observation concentration.

The single-step `ValidStep` condition includes posterior PD. Lemma 1 separately
**proves eventual PD** under its limiting assumptions; it does not assume
validity at every index. For the standard DKF, arbitrary learned positive-definite
$Q(X_t)$ alone is insufficient to ensure PD after subtracting $S^{-1}$.
The robust variant's positive precision sum supplies Gaussian validity at every
index for the Gaussian inputs in the theorem.

#### Scope, verification, and comparison

The paper's main-text Theorem 1, printed p. 975 (PDF p. 7), connects posterior
consistency at each fixed filtering time to increasingly informative,
higher-dimensional observations. The Lean development formalizes the Appendix B
sequence results. It does not formalize observation-model Bernstein–von Mises
conditions, conditional-density existence, or the induction over filtering time
used to reach Theorem 1. The limit is not a claim that errors vanish as filter
time increases. There is no finite-data convergence rate or native Float
roundoff certificate. See the versioned
[statement read-back](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/blob/6b91b7f967bc4523a3de9024bcb49be1aca42918/READBACK.md)
and [formalization metadata](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/blob/6b91b7f967bc4523a3de9024bcb49be1aca42918/formalization.yaml).

Palomar registered this exact commit on **2026-10-01** (the registry's UTC date), as
**PALOMAR-2026-10-01-000006**, version 1. Its
[registry record](https://data.palomar-registry.org/entries/PALOMAR-2026-10-01-000006-v1.json)
lists all six declarations and verification with NanoDa and con-ron;
the [verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/36780042299)
is linked there. The repository's September 30 README says nothing has been
submitted; that statement predates the registration. The recorded toolchain is
Lean **4.35.0-rc2**, with Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Source inspection covered the 41
non-challenge Lean files and the axiom report, which lists only `propext`,
`Classical.choice`, and `Quot.sound` for the six results. We did not rebuild
the project locally. The separate challenge file deliberately has theorem
holes and is not imported by the solution.

The formalization also repairs intermediate steps in the paper proof: full
quadratic completion avoids assuming $U^{-1}-S^{-1}$ is positive definite, and
the inverse-limit argument avoids inverting the potentially singular
$G^{-1}-S^{-1}$, where $G$ is predicted covariance. These changes preserve the
lemma's hypotheses and strengthen its proof justification. See the
[Gaussian update proof](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/blob/6b91b7f967bc4523a3de9024bcb49be1aca42918/DiscriminativeKalmanFilter/Proof/GaussianUpdate.lean)
and [matrix-limit proof](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/blob/6b91b7f967bc4523a3de9024bcb49be1aca42918/DiscriminativeKalmanFilter/Proof/MatrixLimits.lean).

The developments are complementary: DKF certifies statistical approximation of
posterior distributions; this repository certifies numerical discrepancy between
a native binary64 filter and its exact Real trajectory, with concrete bounds
and PD at every finite prefix in two operating domains. Combining learned
observation errors, statistical approximation, and native arithmetic in one
application is a possible future direction. The current theorems do not compose
automatically: a shared filter specification, a common error measure, and a
finite-precision operating domain would be needed.

### Coq/VCFloat and VST: original scalar examples, 2023

Samuel D. Pollard, *Formal and Semi-Formal Verification of Floating-Point
Computations in C Programs*, FPBench meeting, **April 6, 2023**, slides 8–12
([slides](https://sampollard.github.io/research/artifacts/pollard_fpbench23_presentation.pdf)).
The presentation reports VST verification of a small scalar filter and VCFloat
analysis of recursive averaging; full matrix/EKF verification remains future
work there.

The linked **ak-2485/Kalman_Filter** repository was inspected at
`4ed36c0646b501b7a0c3fe0bb4d80ed54937886a`, dated **2023-01-25**
([source](https://github.com/ak-2485/Kalman_Filter/tree/4ed36c0646b501b7a0c3fe0bb4d80ed54937886a)).
On 2026-10-09, this remained its latest default-branch commit. This older
repository is not the whole of the group's subsequent work; see Elaenia below.
`mean_error.v` has `Qed` proofs for a binary32 local absolute bound
$1.2\times10^{-4}$ and an $N\,1.2\times10^{-4}$ averaging bound for $N\le10$
and finite inputs in $[0,10]$. Imported `Mean.v` also contains an admitted
generic step lemma. This does not establish that the concrete bound depends on
that admission; a transitive assumption audit is required before reuse.
This artifact contains limited scalar roundoff work, not matrix covariance or
square-root verification. The gold-bar C proof described in the slides is
available in Elaenia's `gold_spec.v`, discussed below; it was not rebuilt here.

### Sandia Elaenia: C filter examples and matrix infrastructure, 2024 onward

Pollard's *Verification of Digital Numerics for High-Consequence Systems*,
FPTalks, **July 11, 2024**, slides **6–7**, directly follows up the 2023 talk
([slides](https://sampollard.github.io/research/artifacts/pollard_fptalks24_presentation.pdf),
[event program](https://fptalks.org/talks/fptalks24.html)). It reports examples
from 1D to 3D and VST proofs for some, while identifying LU decomposition and
floating-point reasoning as obstacles to the full application. For the larger
C EKF codebase, it describes building Frama-C annotations and judges VST
impractical. This is a progress report, not a claim that all those examples or
the production EKF have complete numerical proofs.

**sandialabs/elaenia**, *Automated Error Analysis of Numerical Software for
High-Consequence Systems*, was inspected at
`3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f`, dated **2026-06-27**
([versioned repository](https://github.com/sandialabs/elaenia/tree/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f)).
Its initial open-source release commit has committer date **2024-10-28**
([release commit](https://github.com/sandialabs/elaenia/commit/e15d90be3d5053a29c856461ba7f3431cb4a4995));
that commit's older author timestamp is not the public-release date. The
Kalman example paths have no later commits through the inspected revision.
Repository maintenance through 2026 therefore does not by itself establish
newer Kalman theorems.

The [Kalman example guide](https://github.com/sandialabs/elaenia/blob/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/05_kalman/kalman-readme.md)
credits Kellison's original work and lists gold-bar weighing, tank flow, kettle
temperature, a union-storage kettle variant, GPS tracking, and adaptive kettle
filtering. The GPS example tracks position, velocity, and acceleration in one
spatial dimension; three state components should not be confused with tracking
in three spatial dimensions.

| Inspected artifact | Proof source or specification | What the inspection establishes |
| --- | --- | --- |
| Gold-bar filter | [`gold_spec.v`](https://github.com/sandialabs/elaenia/blob/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/05_kalman/01_gold/gold_spec.v) | `body_update_p`, `body_update_state`, `body_update_gain`, and `body_main` end in `Qed`. The loop invariant follows the Float recursion over ten fixed measurements. |
| Kettle filter and union-storage variant | [`kettle_spec.v`](https://github.com/sandialabs/elaenia/blob/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/05_kalman/03_kettle/kettle_spec.v), [`kettle_union2_spec.v`](https://github.com/sandialabs/elaenia/blob/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/05_kalman/04_kettle_union/kettle_union2_spec.v) | Update-function and `body_main` proofs end in `Qed`; the loops use fourteen fixed measurements. Each file also contains four local VCFloat roundoff lemmas, with the bounds described below. |
| General matrix multiplication | [`Matrix_Algebra_spec.v`](https://github.com/sandialabs/elaenia/blob/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/04_matrices/lu/Matrix_Algebra_spec.v#L722) | `body_axb` ends in `Qed` and specifies agreement with `IRMatrix_mult`, whose arithmetic uses Float operations. The directory name `lu` does not establish an LU-decomposition proof or a Real matrix-error bound. |
| GPS, flow, and adaptive examples | [Example directory](https://github.com/sandialabs/elaenia/tree/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/05_kalman) | C implementations are present; GPS has basic ACSL preconditions. No corresponding full-filter Rocq proof or accumulated accuracy certificate was found in the inspected tree. |

The VST function specifications compare C execution with explicitly ordered
**floating-point** expressions. Their `body_main` postconditions return zero;
the loop invariants relate intermediate storage to Float recursions. This is
functional verification, with separation-logic memory reasoning, rather than
a Real trajectory-error or covariance-positivity theorem.

The kettle files' `Section fidelity` contains `update_p_del_var`,
`update_state_var`, `update_p_var`, and `update_gain_var`, all ending in `Qed`.
Each states `prove_roundoff_bound` with the same absolute-error allowance

$$
\left|\mathrm{decode}(\widehat f)-f_{\mathbb R}\right|
\le 1.7976931348623157\times10^{308}.
$$

Here $\widehat f$ is the binary64 result of one scalar update expression and
$f_{\mathbb R}$ evaluates that same expression exactly at the decoded inputs.
The input bounds are $p,r\in[1,1000]$, $p_{\rm del}\in[-100,100]$, and
$K,t,x,x_{\rm del},m,q\in[-1000,1000]$, using only the relevant variables for
each expression. The VCFloat predicate also asserts finite output. Exact
locators are [`kettle_spec.v`, lines 333–418](https://github.com/sandialabs/elaenia/blob/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/05_kalman/03_kettle/kettle_spec.v#L333)
and [`kettle_union2_spec.v`, lines 363–448](https://github.com/sandialabs/elaenia/blob/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/05_kalman/04_kettle_union/kettle_union2_spec.v#L363).
The predicate's meaning was checked in
[`vcfloat/Automate.v`, lines 1206–1215](https://github.com/VeriNum/vcfloat/blob/a203b287a84b0e3c9bec136823b5622ebfde6ad6/vcfloat/Automate.v#L1206).
These are completed local proof scripts with an extremely loose error bound,
not useful full-filter accuracy bounds. They neither accumulate error across
the loop nor establish covariance positivity.

Elaenia's [README](https://github.com/sandialabs/elaenia/blob/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/README.md)
describes a shift from a Frama-C plug-in toward extending NASA's ReFlow, and
includes C error-analysis tooling and proposed ACSL extensions. Sandia's
[July 14, 2025 project report](https://www.sandia.gov/research/news/assurance-of-high-consequence-systems/)
reports improved automated roundoff analysis and specification-language work;
it does not announce completion of the full EKF proof.

For the 2023 future-work list, the public follow-up therefore supports more
C examples, completed proofs of some Float recursions, and matrix/tooling
infrastructure. This review did not find a completed full matrix/EKF numerical
certificate, square-root accuracy/positivity proof, the proposed statistical
optimality result, or a verified performance transformation for that
application. This is a statement about the inspected public sources, not
unpublished or internal results.

### VCFloat2 and later error-analysis methods, 2024–2025

Appel and Kellison's peer-reviewed *VCFloat2: Floating-Point Error Analysis in
Coq*, CPP **2024**, DOI
[10.1145/3636501.3636953](https://doi.org/10.1145/3636501.3636953)
([author PDF](https://www.cs.princeton.edu/~appel/papers/vcfloat2.pdf)) gives the
sound roundoff-analysis infrastructure and examples of composed correctness
and accuracy proofs. It is methodological prior art, not a complete
Kalman-filter proof. The inspected library revision is
[`a203b287a84b0e3c9bec136823b5622ebfde6ad6`](https://github.com/VeriNum/vcfloat/tree/a203b287a84b0e3c9bec136823b5622ebfde6ad6),
dated **2026-09-23**; continued library maintenance is separate evidence from
completion of a filter application.

Anthony Dario and Samuel D. Pollard, *A Step-Function Abstract Domain for
Granular Floating-Point Error Analysis*, NSAD **2024**, **October 22**, DOI
[10.1145/3689609.3689997](https://doi.org/10.1145/3689609.3689997)
([author PDF](https://sampollard.github.io/research/artifacts/dario_fp_nsad24.pdf)),
§§3–5, develops an abstract interpreter for a subset of C with arrays,
conditionals, and arithmetic. Error bounds depend on value ranges, including
binade boundaries and unstable branches. Its evaluation compares with
Fluctuat; it is general analysis-tool research, not a completed Kalman theorem.
Elaenia contains the accompanying `fp-analysis` tool and Kalman-related inputs.

Max Fan, Ariel E. Kellison, and Samuel D. Pollard, *Mechanizing Olver's Error
Arithmetic*, VSS **2025**, *EPTCS* **432**, pp. **37–47**, DOI
[10.4204/EPTCS.432.6](https://doi.org/10.4204/EPTCS.432.6)
([paper](https://arxiv.org/abs/2510.13414),
[artifact](https://github.com/Athena-Types/mechanized-precision)), §§3–4,
mechanizes relative precision as a metric, conversions to relative error, and
compositional error rules in Rocq. Its worked application is an inner-product
bound. The formalization uses Flocq's unbounded-exponent model and assumes no
overflow or underflow; those limits matter when considering reuse for native
binary64. It does not provide a full Kalman or QR filter certificate.

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
actual arithmetic schedules and guards. The Pollard/Kellison comparison includes
Elaenia's C filter and matrix proofs, not only the older scalar-roundoff
repository. Those results and our Lean certificates verify different programs
and numerical guarantees; neither comparison establishes a first-ever claim.
See [the complete results](../results.md)
for exact domains and the remaining logical-model/compiler boundary.
