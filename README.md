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
\begin{aligned}
x^- &= Fx, & P^- &= FPF^T+Q,\\
y &= z-Hx^-, & S &= HP^-H^T+R,\\
K &= P^-H^TS^{-1}, & x^+ &= x^-+Ky.
\end{aligned}
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

**Kalman theory:** The equations and general stability principles are established.
The project does not claim a new general Kalman result.

**Numerical analysis:** Concrete bounds and sufficient operating conditions are
derived for this program, including covariance error changing the gain and then
the mean, initialization error, and rounded dense conversion.

**Formal verification:** The contribution is the complete checked connection
from exact mathematics to the specified native operation order and guards.
There are no admitted proofs or added project axioms. FLARE supplies the recorded
binary64 foundation; the proofs concern Lean's logical `Float` semantics.

The complete native filter domains are bounded two-state families. Wider
dimensions and dynamics require further analysis. These are roundoff guarantees
against the ideal filter, with physical model adequacy, statistical consistency,
and compiler/hardware refinement outside their scope.

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
