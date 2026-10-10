# Kalman filter in Lean

A formal numerical-software case study connecting exact Kalman mathematics to
executable binary64 arithmetic. The project certifies conventional numerical
failures and proves square-root filter accuracy and covariance positivity on
explicit operating domains. It uses **Lean and Mathlib 4.34.1** and
[FLARE](https://github.com/duckki/flare-lean).

## Exact reference

Let $x$ be the mean, $P$ the covariance, $z$ the measurement, $F$ the transition,
$H$ the observation matrix, and $Q,R$ the process and measurement covariances.
The Real-valued specification is

$$
\begin{array}{ll}
x^- = Fx, & \qquad P^- = FPF^T+Q,\\
y = z-Hx^-, & \qquad S = HP^-H^T+R,\\
K = P^-H^TS^{-1}, & \qquad x^+ = x^-+Ky.
\end{array}
$$

The posterior expressions

$$
\begin{aligned}
P^+ &= (I-KH)P^-\\
    &= P^- - K(HP^-)\\
    &= (I-KH)P^-(I-KH)^T+KRK^T\\
    &= \big[(P^-)^{-1}+H^TR^{-1}H\big]^{-1}
\end{aligned}
$$

are proved equivalent at the exact Kalman gain. Positive-definite initial $P$
and noise covariances $Q,R$ give positive-definite innovation and posterior
covariances at every finite step. Exact QR stage agreement and information-form
mean equivalence are also proved. See [the sources and specification](docs/paper-and-spec.md).

## Native implementations

- **Compact:** Evaluates $(I-KH)P^-$ directly. A certified one-step execution
  returns negative scalar covariance $-2^{-52}$. A separate nine-step trace has
  eight positive posteriors followed by a negative ninth, while its exact
  reference stays positive-definite.
- **Subtractive:** Evaluates $P^- - K(HP^-)$ with a different rounding order.
  The same one-step negative-variance example is certified.
- **Direct Joseph:** Evaluates the two congruence terms and adds them. Its
  completed local covariance-evaluation bound compares with the exact Joseph
  expression at the supplied stored gain. Complete filter accuracy is a
  separate obligation.
- **QR square-root:** Stores a lower triangular covariance factor $L$ with
  positive diagonal, denoting covariance $LL^T$. It uses QR for prediction,
  innovation, and a factored Joseph correction, with triangular solves for the
  gain. This implementation has the complete initialization-to-horizon proof.

The native information filter and U-D update are not implemented; information
form and U-D storage are part of the mathematical specification.

## Complete numerical guarantees

The full certificate covers **two operating profiles of the same QR square-root
implementation**, each with two states and two measurements. It compares with
one independently propagated Real trajectory initialized from the original
dense covariance and mean, using exactly the same finite input words.

**Correlated stable profile:** Transition entries satisfy $|F_{ij}|\le1/8$ and
observation entries $|H_{ij}|\le1/64$, with bounded correlated covariances and
measurements. At every finite prefix, the returned dense covariance has
entrywise error at most $2^{-25}+2^{-48}$ and the mean has componentwise error
at most $2^{-25}$, both below $3\times10^{-8}$.

**Fully observed diagonal profile:** $H=I$ and diagonal transition magnitudes
are at most one, including identity and near-identity dynamics, with bounded
diagonal covariances and measurements. Returned dense covariance error is at
most $5\,2^{-30}+2^{-48}$, below $4.7\times10^{-9}$; mean error is at most
$2^{-24}$, below $6\times10^{-8}$.

In both profiles, initialization and every native step succeed. The bounds
include accumulated rounding and do not grow with the horizon. The retained
factor and separately rounded dense output both denote strictly positive-definite
covariances; dense output is exactly symmetric without repair. These horizon
guarantees apply to the QR implementation. Regression agreement between other
implementations is separate from an accuracy proof.

[Results and numerical guarantees](docs/results.md) gives the complete original
input domains, exact constants, positivity floors, and completed theorem interfaces.

## Contribution and scope

The main contribution is a **formally checked numerical certificate for a
specific implementation of a classical filter**. The exact identities,
positivity principles, and advantages of square-root filtering are established
Kalman theory.

### Numerical analysis

**What the papers already establish:** Verhaegen and Van Dooren (1986),
Theorem 1 and recurrences (57)–(59), analyze local roundoff and its accumulation,
including covariance, gain, and state-estimate errors. Their analysis uses
first-order perturbations. Tracy (2022), §3 and Algorithm 1, derives the QR
square-root formulation used here.
([Numerical analysis paper](https://perso.uclouvain.be/paul.vandooren/publications/VerhaegenV86.pdf),
[QR algorithm paper](https://arxiv.org/pdf/2208.06452v1).)

**What we certify:** We instantiate established roundoff analysis for this
binary64 program and certify its concrete error bounds in Lean on two operating
domains.

### Formal verification

**What earlier formalizations cover:** The inspected
[Rocq/MathComp development](https://github.com/F1uctus/kalman.v/blob/cf1c0af709b3b9d4e8da8247b0f0db05e5093c7a/theories/kalman.v)
already proves overlapping exact covariance identities and positivity, with
exact rational refinement; its
[Float64 examples](https://github.com/F1uctus/kalman.v/blob/cf1c0af709b3b9d4e8da8247b0f0db05e5093c7a/theories/seqmx/inst_Float64.v)
are fixed computations rather than general roundoff bounds.
[Pollard and Kellison's Coq/VCFloat work](https://sampollard.github.io/research/artifacts/pollard_fpbench23_presentation.pdf)
includes scalar roundoff analysis;
[Sandia's Elaenia follow-up](https://github.com/sandialabs/elaenia/tree/3cdf32d9e10dfc1d8b66341a75f2f977e8ce114f/examples/05_kalman)
adds C filter examples and proofs of floating-point functional specifications.
[Burkhart's Lean discriminative-filter formalization](https://github.com/burkh4rt/Discriminative-Kalman-Filter-Formalized/blob/6b91b7f967bc4523a3de9024bcb49be1aca42918/DiscriminativeKalmanFilter/Results.lean)
concerns Gaussian identities and distributional approximation. See
[the prior-work review](docs/references/prior-formalizations.md) for the
versioned sources, theorem locations, and trust scopes.

**What this development adds:** A complete Lean proof connecting the executable
QR filter to its Real specification, including accumulated accuracy and
covariance positivity. Relative to the reviewed work, the added value is this
implementation-specific binary64 certificate.

The complete native filter domains are bounded two-state families. Wider
dimensions and dynamics require further analysis.

## Build and validation

Lake fetches FLARE from GitHub at the reviewed, pinned revision. Follow
[the dependency setup](docs/development.md#dependencies) before building:

```sh
make
```

The build includes exact specification checks and the project-wide theorem axiom
audit. The regression executable checks failure fixtures, arithmetic boundary
cases, and long trajectories against independent high-precision references.
See [build and validation](docs/development.md) for setup and proof boundaries.

## Documentation

- [Sources, equations, and adopted specification](docs/paper-and-spec.md)
- [Results, error bounds, domains, and proof interfaces](docs/results.md)
- [Project layout and runtime APIs](docs/project-layout.md)
- [Dependency setup, build, and validation](docs/development.md)
- [Prior formalizations and contribution scope](docs/references/prior-formalizations.md)
- [Floating-point foundation and library assessment](docs/references/floating-point-library-assessment.md)

## License

GPL-3.0-only. See [LICENSE](LICENSE). Third-party dependencies retain their own licenses.
