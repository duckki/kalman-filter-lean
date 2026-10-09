# Project background and research notes

Internal background and planning history. The research baseline and milestone
dates below are historical; proposed directions are ideas, not a committed
research agenda. Current public claims live in [results.md](../results.md).
Working instructions live in [AGENTS.md](../../AGENTS.md).

Research baseline: **2026-10-04** (America/Los_Angeles).
Status updated **2026-10-06**: exact Real contracts, one-step and nine-step
native failure certificates, initial-input QR success/error, and complete
native square-root accuracy from original dense inputs are proved for the
documented correlated two-state family. Both accumulated errors are `≤ 2⁻²⁵`
at every finite prefix, with native/ideal positive covariance and a separate
rounded dense-output accuracy/positivity guarantee. Its F/H entry caps are
`1/8` and `1/64`; broader original-input domains remain work in progress.
For fully observed diagonal dynamics up to identity, complete initialized
native filtering and rounded dense output are also proved from original inputs:
uniform covariance/mean errors `5·2⁻³⁰ + 2⁻⁴⁸` / `2⁻²⁴`, exact dense symmetry
and strict-PD floor `7/16 − 2⁻⁴⁷ ≥ 3/8`. The native initial variance interval is
`[1,3/2]`, with Q/R diagonals `[1,3/2]` and mean/measurement cap one. Broader
dimensions, noise scales and correlated near-identity dynamics remain extensions. See
[the public results](../results.md),
[the original-input horizon scope](../results.md#accumulated-horizon-accuracy-from-original-inputs)
and [the current roadmap](research-roadmap.md#implementation-roadmap-and-acceptance-criteria).

## 1. Intended result

Build a Lean project that connects an exact Real-valued Kalman covariance recursion to specified floating-point implementations. The eventual demonstration should establish all three of the following:

1. A conventional covariance implementation can accumulate roundoff across repeated updates and produce an invalid covariance, despite valid inputs and a positive-definite exact reference result.
2. The corresponding ideal matrix computation over `Real` preserves positive definiteness under explicit hypotheses.
3. A specified square-root implementation preserves the covariance structure and satisfies useful, explicit numerical error bounds. Strict positive definiteness must follow from a proved rank or error-margin condition throughout the supported execution domain.

The main output being verified is the **state-error covariance**, not the estimated state vector. Positivity does not establish that the physical model is accurate, that the filter is statistically consistent, or that the state estimate is close to reality. Mean-vector roundoff relative to the same ideal filter is now also covered; this is not a bound against physical truth.

This file records published evidence, mathematical deductions, and proposed proof obligations separately. The repository now proves the exact Real contracts and certifies a repeated-update negative covariance. The square-root success postcondition and dense materialization bounds are proved. The native QR factor's initial-input theorem derives success, a strictly PD exact output Gram with floor $M^2/16$, and entrywise error at most $M^2/128$ from explicit dimension, energy/rank and scale margins alone. See [the complete QR bound and domain](../results.md#initial-input-qr-success-and-error).

Initial column energy/rank margins now give intermediate magnitude and remaining
spectral bounds from the errors of preceding pivots, including concrete headroom
for up to eight rows. The next active source-tail witness is now derived from
the remaining rank margin and prior triangular structure: an entry of magnitude
at least $M/16$ meets the kernel's source floor for $M\ge2^{-896}$. The initial-input
induction is complete for $n\le d\le8$ and $2^{-896}\le M\le2^{900}$, row energies
at most $M^2/2$ and Gram floor $M^2/8$. Accuracy of the complete square-root recursion, including rounded prearrays,
prior/noise factors, gain and mean, is now proved under explicit operand domains.
The finite-horizon result and two-state uniform budget are documented in
[the numerical reference](../results.md#full-filter-over-a-finite-horizon).
See [the initial-input result](../results.md#initial-input-qr-success-and-error).

## 2. Clarify the property before choosing an algorithm

For a symmetric real matrix, write:

- $P \succeq 0$ (positive semidefinite, PSD) when $v^T P v \geq 0$ for every $v$.
- $P \succ 0$ (positive definite, PD) when $v^T P v > 0$ for every nonzero $v$.
- $P \prec 0$ (negative definite) when every nonzero quadratic form is negative.

The failure target is **loss of PSD**, preferably with an explicit nonzero vector $v$ for which $v^T \widehat P v < 0$. One negative diagonal entry supplies such a witness using a coordinate vector. A matrix with both positive and negative eigenvalues is indefinite; it is not negative definite. Requiring the entire output to be negative definite would unnecessarily strengthen the demonstration. Loss of symmetry and a zero eigenvalue should be reported separately.

Three different objects must remain distinct:

| Object | Meaning of positivity |
| --- | --- |
| Exact reference $P_k$ | A theorem about matrices over `Real`. |
| Stored finite floating-point factor $\widehat L_k$ | Decode its entries exactly into reals, then define $\widetilde P_k = \operatorname{decode}(\widehat L_k)\operatorname{decode}(\widehat L_k)^T$. This matrix is PSD; it is PD if the factor is nonsingular. |
| Materialized floating-point covariance $\widehat P_k = \mathrm{fl}(\widehat L_k\widehat L_k^T)$ | A separate rounded computation. Its decoded result needs its own symmetry and positivity analysis. |

Thus “always positive definite” means **for every supported execution satisfying stated input, range, conditioning, and precision hypotheses**. Factor storage alone gives PSD of the represented covariance; it does not prove nonsingularity or a small error relative to the exact recursion. These distinctions follow from the quadratic-form identities and are reflected in Mathlib's definitions [F1].

## 3. Ground facts and existing research

### Published failure evidence

Thornton and Bierman's 1976 NASA/JPL 19-state study found negative variances after four days for the conventional filter and ten for the stabilized filter. Across 607 measurement updates, the respective counts were **177** and **69**: printed pp. 16-17 (PDF pp. 25-26) [R1].

Crucially, its stabilized implementation used an **expanded arrangement** of Joseph's formula, equations (7a)-(7b), p. 9. The direct congruence arrangement, equation (8), p. 10, was excluded. The rejection of unconditional nonnegativity on p. 19 concerns the studied implementation [R1]; those failure counts cannot be transferred unchanged to direct Joseph evaluation.

These experiments used a UNIVAC 1108, with double-precision inner-product accumulation before rounding, pp. 12-13 [R1]. They are neither IEEE binary32 reproductions nor exact Real proofs. The repository needs its own witness.

### Published analysis and improved algorithms

Verhaegen and Van Dooren's SRCF uses orthogonal array triangularization, including Householder transformations: Section II.B, p. 908, equations (11)-(13) [R2].

A useful starting bound is Theorem 1, part 2, printed p. 911:

$$
\Delta_p \leq \epsilon_5
  \left(1+\frac{\sigma_1}{\sigma_p}\right)
  \frac{\|P_{k+1\mid k}\|_2}{\cos\phi_1}.
$$

Here $\Delta_p$ is local covariance error; $\sigma_1,\sigma_p$ are extreme singular values of the innovation factor $R_k^{e\,1/2}$; and $\cos\phi_1=\|S_{k+1}\|_2/\|[G_k\;S_{k+1}]\|_2$. Its $S_k$ is a covariance factor, unlike this document's innovation $S_k$. The conventional bound contains $(\sigma_1/\sigma_p)^2$. The $\epsilon_i$ are precision-scale constants. This conditioning-dependent first-order analysis, including accumulation in Section III, needs explicit remainder bounds for Lean certification [R2].

The 1987 follow-up clarifies which conventional multiplication order exhibits the loss-of-symmetry mechanism [R3]. Accordingly, the project must specify an operation sequence, not just a formula or the label “conventional filter.”

Bierman's U-D measurement update is another established candidate: it propagates $P=UDU^T$, with unit upper-triangular $U$ and diagonal $D$. The 1976 paper covers measurement updates rather than the complete prediction algorithm [R4]. It is a serious alternative, but its nonnegative diagonal invariant and numerical bounds also need implementation-level proofs.

Tracy's 2022 paper gives a compact QR-based square-root algorithm, with a Julia implementation, using QR for prediction, innovation, and a factored Joseph update [R5, L3]. It is useful as an approachable alternative; it supplies an algorithm derivation rather than the quantitative roundoff certificate needed here. Claims about doubled precision must not be substituted for such a certificate.

### Relationship to the supplied report

The attached *Formal Methods for Orbit Determination and Satellite GNC*, especially pp. 4-6 and 8, motivates studying roundoff and warns that covariance invariants alone do not establish navigation accuracy [C1]. Its recommendations are context, not instructions defining this repository's scope.

Two qualifications are necessary: its statement that Joseph form does not degrade covariance positivity needs finite-precision assumptions; its factorization argument concerns the covariance denoted by valid factors. Also, its FloatSpec maturity assessment is a dated claim that needs a fresh dependency audit; the inspected README now reports a different status [F2]. This project makes no claim that Kalman roundoff analysis is new, or that a complete literature review has established novelty of a particular Lean formalization.

### Prior formalizations and contribution scope

Kalman filtering has earlier Maude/ITP and ACL2 formalizations, and recent
Rocq/MathComp work already includes exact covariance positivity, Joseph-form
equivalence, information-form identities, and gain optimality. Lean work also
exists for discriminative Kalman filtering. Their assumptions and numerical
scope differ substantially. The dated, versioned review is in
[prior-formalizations.md](../references/prior-formalizations.md).

The completed Real theorems in this repository are known exact linear-algebra
consequences. The intended implementation contribution is the complete link
from specified native arithmetic to certified failure evidence and a useful
square-root error bound with explicit positivity conditions. No inspected
source supplies that full chain for the selected implementation; this is not
an exhaustive novelty claim.

## 4. Exact reference and theorem hypotheses

Start with the discrete-time linear model, finite state dimension $n\geq1$ and measurement dimension $m\geq1$. Let $F_k$ be the transition, $H_k$ the measurement matrix, and $Q_k,R_k$ the process and measurement covariances. The covariance recursion is:

$$
\begin{aligned}
P_k^- &= F_kP_{k-1}^+F_k^T+Q_k,\\
S_k &= H_kP_k^-H_k^T+R_k,\\
K_k &= P_k^-H_k^TS_k^{-1},\\
P_k^+ &= P_k^- - P_k^-H_k^TS_k^{-1}H_kP_k^-.
\end{aligned}
$$

This is the standard recursion, with notation adapted from the modern textbook reference [T1]. For the exact optimal gain, the last line also equals the compact update $(I-K_kH_k)P_k^-$ and the Joseph update

$$
P_k^+=(I-K_kH_k)P_k^-(I-K_kH_k)^T+K_kR_kK_k^T.
$$

The initial sufficient assumptions are $P_0^+\succ0$, $R_k\succ0$, and $Q_k\succ0$ at every prediction. They allow arbitrary, even singular, $F_k$. A later generalization can use $Q_k\succeq0$ with nonsingular $F_k$, or the weaker condition

$$
\ker(F_k^T)\cap\ker(Q_k)=\{0\}
$$

when $P_{k-1}^+\succ0$. This condition explains exactly when prediction can lose rank. Semidefinite noise by itself does not justify strict positivity.

The proposed exact proof establishes:

1. Prediction preserves PSD and is PD under the chosen sufficient condition.
2. $S_k\succ0$, so the innovation inverse is legitimate.
3. The compact, subtractive, and Joseph forms agree for the exact gain.
4. The posterior is PD, for example through
   $P_k^+=((P_k^-)^{-1}+H_k^TR_k^{-1}H_k)^{-1}$.
5. Induction preserves PD at every finite step.

As a separate algebraic result, Joseph form is PSD for any gain when $P_k^-\succeq0$ and $R_k\succeq0$; it is PD for any gain when both are PD. These exact deductions are now proved in Lean; they do not assert that a rounded dense evaluation has the same property. Probability-theoretic optimality can remain outside the first proof: covariance recursion correctness already supplies a meaningful exact reference.

## 5. Floating-point comparison and failure demonstration

The first comparison should use three implementations of the same model:

| Implementation | Role |
| --- | --- |
| Conventional direct covariance | Specify either $(I-\widehat K H)\widehat P^-$ or the subtractive form and its evaluation order. Find and certify a repeated-update failure. |
| Direct Joseph covariance | Compare how much it improves the example; do not promise universal PSD. |
| QR square-root covariance | Primary candidate for structure preservation and quantitative bounds. |

Choose IEEE binary64, round-to-nearest ties-to-even as the first concrete semantics, with unit roundoff $u=2^{-53}$; binary32 ($u=2^{-24}$) is a useful subsequent stress case. Define whether multiply-add is fused, how dot products accumulate, how solves operate, and how triangularization branches are evaluated. A generic relative-error model is useful for analysis, but it is insufficient to certify a particular IEEE execution.

Useful initial specifications are

$$
\mathrm{fl}(a\mathbin{\circ} b)
 = (a\mathbin{\circ} b)(1+\delta),\quad |\delta|\leq u,
\qquad \gamma_r=\frac{ru}{1-ru},\quad ru<1.
$$

Here $\circ$ ranges over addition, subtraction, multiplication, and division with a nonzero denominator. The relative model requires suitable range hypotheses. Either exclude underflow with proved intermediate bounds or include the corresponding absolute error terms. Handle overflow, non-finite values, and square roots separately. Rounding and error-analysis background is available in [N1, N2].

For fair comparisons, use the exact real decoding of the same machine-representable inputs as the reference. Account for input conversion and initial/noise factorization errors. Initially, exactly representable diagonal noise matrices with exactly representable factors can simplify this obligation. Do not compare algorithms against different silently rounded models.

The eventual repeated-update artifact must record inputs, precision, operation order, first failing step, and a certified negative quadratic form of the decoded covariance. Track covariance error and symmetry error over the whole run. Exact rational computation on a suitably chosen example, or certified intervals, must establish positivity of the reference and negativity of the failure witness. A rounded eigensolver and a higher-precision run are diagnostics rather than final proof evidence. Errors need not grow monotonically; Kalman recursions can also damp them.

A small mathematical sanity example already shows why strict PD needs care: with scalar $P^-=H=1$ and $R=2^{-54}$, binary64 rounds $1+R$ to $1$. The compact implementation therefore computes $\widehat K=1$ and $\widehat P^+=0$, whereas the exact posterior is $1/(2^{54}+1)>0$. This is an independently derived target for a future rounding proof. It shows a one-step loss of strict positivity, **not** a negative variance or accumulated failure. A separate nine-step negative-variance witness is now certified below.

This cancellation case is now an executable native regression. A second scalar fixture uses $F=0$, $Q=P=1$, $R=2^{-60}$, and $H$ decoded from binary64 word `0x3ffd8a8f075e6e3b`; compact and subtractive full steps return $-2^{-52}$, while Joseph and QR return positive results. The exact scalar posterior is $R/(H^2+R)>0$. Both conventional full-step outputs are now **kernel-certified** instances of `NegativeQuadraticWitness`. See [the fixture record](../paper-and-spec.md#reproducible-cancellation-fixtures).

A second certified experiment repeats one fixed scalar model nine times: $F=2^{23}$, $Q=2^{-47}$, $R=2^{-63}$, $H$ decoded from `0x3ffecc02dca65478`, initial $P=1$, and zero mean/measurements. All nine native compact calls succeed with finite output. The first eight posteriors are positive; the ninth is negative with covariance word `0xbc10000000008102`. `FloatTraceCounterexample` proves the exact reference is PD at every horizon and certifies every native transition. This demonstrates delayed loss under rounded propagation; it does not assert monotonically increasing absolute error. Native Joseph and retained QR stay positive on this regression, without establishing a universal dense Joseph guarantee.

## 6. Recommended square-root target

Implementation selection: the initial code uses **Tracy's three-QR Joseph arrangement** [R5, L3], with lower factors, explicit Householder QR, Cholesky noise initialization, and triangular gain solves. The block-array arrangement below remains a distinct research candidate. Neither arrangement inherits the other's numerical constants; the selected implementation is mapped in [paper-and-spec.md](../paper-and-spec.md#square-root-interpretation-and-implementation-choices).

Use an **array square-root covariance filter with Householder QR**, storing a triangular factor $L$ with $P=LL^T$. This is supported by the SRCF literature [R2] and concrete array implementations [L1, L2]. Prefer it as the first research target because it connects matrix identities, QR error analysis, rank preservation, and recurrence bounds.

The following separated prediction/measurement arrangement makes the covariance meaning explicit. It differs from the combined recursion in [R2]; that paper's constants require a new derivation for this sequence.

For prediction, with $Q=T_QT_Q^T$, triangularize

$$
A_{\mathrm{pred}}=[F L\;T_Q]
$$

by QR of its transpose, yielding $L^-$ with $L^-(L^-)^T=A_{\mathrm{pred}}A_{\mathrm{pred}}^T$.

For measurement, with $R=T_RT_R^T$, triangularize the transpose of

$$
M=
\begin{bmatrix}
T_R & H L^-\\
0 & L^-
\end{bmatrix},
\qquad
M U=
\begin{bmatrix}
T_S & 0\\
C & L^+
\end{bmatrix},\quad U^TU=I.
$$

The block Gram identity yields the innovation factor $T_S$, gain $K=CT_S^{-1}$, and posterior factor $L^+$. Use triangular solves rather than explicitly forming inverses. Factor diagonal signs are immaterial to PD; nonzero diagonal entries are what matter. The first implementation must freeze the exact QR algorithm and arithmetic sequence before its constants are proved.

Tracy's QR/Joseph arrangement [R5] is the initial implemented sequence. The block-array arrangement above and Bierman's U-D recursion [R4] remain separate candidates. Changing the chosen arrangement requires a new equivalence argument and error analysis. Calling a library's QR routine is useful for exploration, but does not establish a Lean proof of that routine's machine execution.

## 7. What a useful error and positivity theorem must say

### Local arithmetic bound

Prove a QR contract for each computed prearray, including errors incurred while constructing it. One useful contract has an exactly orthogonal real matrix $U$ and perturbation $\Delta A$ such that the decoded triangular result is the exact triangularization of $A+\Delta A$, with

$$
\|\Delta A\|_2\leq\eta(A,n,m,u).
$$

The final $\eta$ must have explicit constants derived for the chosen algorithm. An assumed “stable QR” contract is a possible intermediate result, but is not completion of the floating-point implementation proof. [N1, N2] provide the numerical-analysis background.

For any such contract, an independently derived bridge is

$$
\|(A+\Delta A)(A+\Delta A)^T-AA^T\|_2
\leq 2\|A\|_2\eta+\eta^2.
$$

Prediction can use this directly. Measurement additionally needs bounds for extracting the posterior through the block factorization, including the conditioning of the innovation block. A backward error for an arbitrary perturbed prearray is not automatically a backward error for physically structured $F,H,Q,R$; that stronger claim would need a separate proof.

### Accumulation over a finite horizon

Let $\mathcal R_k$ denote the exact prediction/update map from step $k$ to $k+1$, and let $\widetilde P_k$ be the covariance denoted by the computed factor. Define $E_k=\|\widetilde P_k-P_k\|_2$. Prove a local defect bound $\varepsilon_k$ relative to $\mathcal R_k(\widetilde P_k)$, and a Lipschitz bound $a_k$ for $\mathcal R_k$ on an explicit invariant domain. The proposed composition theorem is

$$
E_{k+1}\leq a_kE_k+\varepsilon_k,
\qquad
E_N\leq
E_0\prod_{j=0}^{N-1}a_j
+\sum_{i=0}^{N-1}\varepsilon_i
\prod_{j=i+1}^{N-1}a_j.
$$

This was the proposed linear theorem shape. The completed implementation theorem now uses explicit coupled covariance/mean radii and nonlinear correction sensitivity; it retains higher-order terms. The two-state coefficient check yields a uniform `2⁻²⁵` budget on its documented domain. These are project constants, not a bound copied from a paper. The local bounds and finite-horizon composition are complete under explicit operand certificates. Deriving the reached-prefix domain from original inputs for nontrivial dynamics remains part of the goal. An indefinite-horizon bound needs additional proved stability hypotheses; for example, uniform $a_k\leq a<1$ and $\varepsilon_k\leq\varepsilon$ imply $E_N\leq a^NE_0+\varepsilon(1-a^N)/(1-a)$. Detectability alone is not an explicit Euclidean-norm contraction constant.

### Strict positivity and dense output

PSD of $\widetilde P_k$ follows from its factor representation. Establish strict PD by either proving the decoded factor remains nonsingular, or proving

$$
P_k\succeq\alpha_k I,\quad \alpha_k>0,
\qquad E_k<\alpha_k.
$$

The latter gives $\widetilde P_k\succ0$. A local sufficient rank condition is $\eta<\sigma_{\min}(A)$ for a full-row-rank prearray under the stated exact QR perturbation contract. Show how input margins imply this condition; merely assuming the computed pivots are nonzero would leave the main obligation unproved.

If users need a materialized covariance, specify a symmetric reconstruction and prove its additional error bound $\rho_k$. A sufficient PD condition becomes $E_k+\rho_k<\alpha_k$. Symmetrization alone does not restore PSD. If unsupported inputs are rejected, distinguish “every successful result is PD” from the stronger theorem that admissible inputs always succeed.

An error bound counts as **good** when it is explicit, applies to the actual algorithm, stays below the positivity margin on a documented example family, and remains useful for repeated updates. A bare $O(u)$ statement, or a bound too large to imply anything on those examples, is insufficient.

## 8. Existing libraries and documentation to inspect

These are algorithm references and later comparison baselines, not formally verified dependencies. Source revisions below were inspected on the research date.

| Source | Inspected behavior | Project use |
| --- | --- | --- |
| FilterPy [L1] | `KalmanFilter.update` evaluates Joseph form. `SquareRootKalmanFilter` uses QR for prediction and a block measurement array; its gain calculation uses a pseudoinverse. | Convenient Joseph and factor baselines. Its ordinary filter should be labeled as the Joseph baseline. |
| pykalman [L2] | Standard `_filter_correct` uses $P^- - K(HP^-)$ and a pseudoinverse. The Cholesky variant uses QR prediction and a block QR correction. A Bierman variant is also present. | Particularly useful for comparing direct covariance and factored algorithms in one library. Pseudoinverse thresholds are part of behavior and need separate treatment. |
| QRKalmanFilter [L3] | Julia code accompanying Tracy's paper; stores an upper factor with $P=F^TF$, uses triangular division for the gain, and QR on factored Joseph terms. | Small paper/code pair for reviewing an alternative proof target. |

The pykalman documentation discusses numerical stability and both Cholesky and U-D variants [L2]. Its prose guarantee must be interpreted using the factor-versus-materialization distinction above. Examples and documentation are useful for learning behavior; the papers and actual operation sequence determine the proof obligations.

## 9. Lean scope, completion criteria, and remaining decisions

Mathlib already supplies `Matrix.PosDef`, `Matrix.PosSemidef`, congruence and addition lemmas, positive-definite inversion, and eigenvalue characterizations [F1]. This supports the Real-level development. It does not by itself certify floating-point QR or Kalman error accumulation.

FloatSpec is a candidate for rounding semantics [F2]. Its inspected README reports compilation without active `sorry`, `admit`, or project axioms, while explicitly distinguishing that syntactic audit from source-semantic review. Its roadmap still lists arithmetic and error-bound work. Neither the supplied report's older assessment nor the README alone establishes that the exact theorems needed here are available. The initial project now selects Lean/Mathlib **4.34.1** and the upgraded local **FLARE** library. The newly announced **FloatLib** (arXiv:2609.19352) was also inspected. Exact revisions, interfaces, restrictions, and the adoption rationale are in [the library assessment](../references/floating-point-library-assessment.md).

The initial completion criteria are:

1. A fixed arithmetic/model specification and documented admissible input domain.
2. Kernel-checked Real proofs of the covariance invariants and algorithm equivalence.
3. A reproducible repeated-update failure with a formally certified negative witness and positive exact reference.
4. A specified square-root operation sequence with proved local error constants, a finite-horizon bound, and conditional strict PD throughout that horizon.
5. A clear statement of whether output is a factor or dense matrix, with reconstruction covered if promised.
6. Useful instantiated bounds and proof builds free of unproved placeholders or added correctness axioms in the delivered theorem dependency chain.

These criteria are met for the documented two-state original-input domain.
A nine-step scalar counterexample is certified; minimality is not claimed.
The selected Householder schedule has explicit error constants. Original dense
initialization and time-varying correlated model inputs derive every reached
profile, successful execution, native/ideal positivity and accumulated
covariance/mean errors `≤ 2⁻²⁵` at every finite prefix. Optional rounded dense
output has its own symmetry, accuracy and strict-PD margin. General conditional
horizon theorems remain available outside that instantiated domain.

The remaining work concerns wider operating domains and tighter constants.
Fully observed diagonal transitions up to identity now have a completed Real
stability argument, native local prediction/innovation proofs, exact
returned QR diagonality and input-derived gain accuracy `2⁻²⁷` against the same
stored prior's ideal gain. The gain is exactly diagonal with diagonals in
`[3/8,13/16]`. Native mean correction now derives every operation/profile,
ideal local error `2⁻²⁵` and returned mean cap `9/8`, with input-derived
prediction-to-correction handoff. Complete local posterior correction now
also succeeds with output validation, covariance/mean errors `2⁻²⁹` / `2⁻²⁵`,
exact diagonal covariance floor `7/16`, diagonal cap `17/16`, and factor/mean
caps `9/8`. The completed exact Joseph identity makes gain error quadratic,
with contribution `2⁻⁵⁰`. Complete checked native steps now derive
covariance/mean errors `3·2⁻³⁰` / `5·2⁻²⁸` against the ideal full step from
the same incoming state and preserve the native invariant. Every finite native
prefix succeeds with diagonal strict-PD factor covariance and floor `7/16`.
Original dense initialization now derives that invariant and initial
covariance/mean errors `2⁻⁴²` / zero on variances `[1,3/2]`. Accumulated
accuracy against the independent ideal trajectory is now uniformly bounded by
`5·2⁻³⁰` / `2⁻²⁴` at every finite prefix, with identity and near-identity
witnesses. Rounded dense output now has covariance error `5·2⁻³⁰ + 2⁻⁴⁸`,
the same mean bound, exact symmetry and PD floor `7/16 − 2⁻⁴⁷ ≥ 3/8`.
The initialized fully observed diagonal filter milestone is complete.
Broader dimensions/scales and correlated near-identity dynamics follow.
Lower-dimensional examples should precede a reproduction of the full JPL case.
Extended/unscented filters, smoothing, orbit dynamics, hardware/compiler
refinement, model tuning and flight qualification are outside the first scope.

## 10. Exact source register

Unless stated otherwise, links and indicated content were reviewed on 2026-10-04. Printed page numbers and PDF viewer page numbers can differ.

### Texts and numerical research

- **[T1]** Simo Särkkä and Lennart Svensson. *Bayesian Filtering and Smoothing*, 2nd ed., Cambridge University Press, 2023. DOI: [10.1017/9781108917407](https://doi.org/10.1017/9781108917407). [Author-hosted text](https://users.aalto.fi/~ssarkka/pub/bfs_book_2023_online.pdf), Section 6.3, Theorem 6.6, equations (6.20)-(6.29), printed pp. 96-98 (PDF pp. 126-128). The equations and the discussion recommending factor methods on p. 98 were checked. This is the principal modern specification reference.
- **[T2]** R. E. Kalman. “A New Approach to Linear Filtering and Prediction Problems.” *Journal of Basic Engineering* **82**(1), 35-45, March 1960. DOI: [10.1115/1.3662552](https://doi.org/10.1115/1.3662552). Historical origin of the covariance recursion. Bibliographic details are corroborated by [R5]; publisher full text was inaccessible during this review. No implementation error bound is attributed to this paper.
- **[T3]** Greg Welch and Gary Bishop. *An Introduction to the Kalman Filter*. University of North Carolina at Chapel Hill, TR 95-041, updated July 24, 2006. [Canonical PDF address](https://www.cs.unc.edu/~welch/media/pdf/kalman_intro.pdf). A useful introductory tutorial, Sections 1-3, with prediction/update equations and a scalar example. Title, authors, and revision date were verified from the indexed report; direct retrieval returned 404, so equation/page-level claims in this document rely on [T1] instead.
- **[R1]** Catherine L. Thornton and Gerald J. Bierman. *A Numerical Comparison of Discrete Kalman Filtering Algorithms: An Orbit Determination Case Study*. JPL TM **33-771**, NASA-CR-148278, June 15, 1976. [NASA record](https://ntrs.nasa.gov/citations/19760019842); [full report](https://ntrs.nasa.gov/api/citations/19760019842/downloads/19760019842.pdf). Algorithms: Section II.C; failures: Section III.A. Related journal version: Bierman and Thornton, *Automatica* **13**(1), 23-35, 1977, DOI [10.1016/0005-1098(77)90006-1](https://doi.org/10.1016/0005-1098(77)90006-1). Evidence here uses the technical report.
- **[R2]** Michel Verhaegen and Paul Van Dooren. “Numerical Aspects of Different Kalman Filter Implementations.” *IEEE Transactions on Automatic Control* **31**(10), 907-917, October 1986. DOI: [10.1109/TAC.1986.1104128](https://doi.org/10.1109/TAC.1986.1104128). [Author-hosted PDF](https://perso.uclouvain.be/paul.vandooren/publications/VerhaegenV86.pdf). Exact locators: Section II.B, equations (11)-(13), p. 908; Section III, Theorem 1, pp. 911-912; accumulation discussion, equations (57)-(59), pp. 912-913. Read with [R3].
- **[R3]** M. H. Verhaegen. *Improved Understanding of the Loss-of-Symmetry Phenomenon in the Conventional Kalman Filter*. NASA Technical Memorandum **100041**, December 1987. [NASA record](https://ntrs.nasa.gov/citations/19880005327); [PDF](https://ntrs.nasa.gov/api/citations/19880005327/downloads/19880005327.pdf). Section II, Table I contrasts CKF1/CKF2; Section III treats their different error propagation. This correction prevents overgeneralizing the conventional-filter discussion in [R2].
- **[R4]** Gerald J. Bierman. “Measurement Updating Using the U-D Factorization.” *Automatica* **12**(4), 375-382, July 1976. DOI: [10.1016/0005-1098(76)90058-3](https://doi.org/10.1016/0005-1098(76)90058-3). [Publisher abstract](https://www.sciencedirect.com/science/article/pii/0005109876900583). Abstract and bibliographic details reviewed; full paper not retrieved. Use for the U-D measurement-update alternative, not an uninspected detailed error theorem.
- **[R5]** Kevin S. Tracy. “A Square-Root Kalman Filter Using Only QR Decompositions.” **arXiv:2208.06452v1**, submitted August 12, 2022 (PDF title-page date August 16, 2022). DOI: [10.48550/arXiv.2208.06452](https://doi.org/10.48550/arXiv.2208.06452). [Versioned paper](https://arxiv.org/pdf/2208.06452v1). Section 3 and Algorithm 1, pp. 2-4; prediction (20), innovation (26), gain (29)-(30), and factored Joseph update (36). Accompanying code: [L3].
- **[N1]** Nicholas J. Higham. *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002. DOI: [10.1137/1.9780898718027](https://doi.org/10.1137/1.9780898718027). [Publisher contents](https://epubs.siam.org/doi/book/10.1137/1.9780898718027). Relevant chapters: 2, floating-point arithmetic; 3, basic error analysis; 8, triangular systems; 19, QR factorization, pp. 353-380; 20, least squares. Contents and publisher excerpts reviewed; full Chapter 19 was not accessible. Use alongside the open analysis [N2], not as an unverified quotation of an exact theorem constant.
- **[N2]** L. Minah Yang, Alyson Fox, and Geoffrey Sanders. “Rounding Error Analysis of Mixed Precision Block Householder QR Algorithms.” **arXiv:1912.06217v3**, February 27, 2021. [Versioned text](https://arxiv.org/pdf/1912.06217v3). Section 2.1, equation (2.2) and Lemma 2.1 introduce the arithmetic model and $\gamma_r$; Section 3.1, Algorithm 3 and Theorem 3.4 give uniform-precision Householder QR analysis. Its simplified constants still need to be made explicit for this project's chosen algorithm. Mixed precision is outside the initial scope.

### Libraries and websites, with source snapshots

- **[L1]** Roger R. Labbe Jr., **FilterPy**. [Documentation](https://filterpy.readthedocs.io/en/latest/). Inspected commit: `3b51149ebcff0401ff1e10bf08ffca7b6bbc4a33`. [Direct covariance source](https://github.com/rlabbe/filterpy/blob/3b51149ebcff0401ff1e10bf08ffca7b6bbc4a33/filterpy/kalman/kalman_filter.py#L485), `KalmanFilter.update`, Joseph evaluation at lines 555-556; [square-root source](https://github.com/rlabbe/filterpy/blob/3b51149ebcff0401ff1e10bf08ffca7b6bbc4a33/filterpy/kalman/square_root.py#L172), measurement QR at line 208 and prediction QR at line 243. Source inspected; no execution or correctness audit performed. The generated docs display version 1.4.4, which should not be confused with the repository snapshot.
- **[L2]** **pykalman**. [Numerical-stability documentation](https://pykalman.readthedocs.io/en/latest/index.html#numerical-stability). Inspected commit: `d62e60be00bd028ecc7eea6a8bea02f583910428` (release commit for 0.11.2). [Standard source](https://github.com/pykalman/pykalman/blob/d62e60be00bd028ecc7eea6a8bea02f583910428/pykalman/standard.py#L233), correction at lines 295-297; [Cholesky source](https://github.com/pykalman/pykalman/blob/d62e60be00bd028ecc7eea6a8bea02f583910428/pykalman/sqrt/cholesky.py#L110), block QR at lines 159-183; [Bierman source](https://github.com/pykalman/pykalman/blob/d62e60be00bd028ecc7eea6a8bea02f583910428/pykalman/sqrt/bierman.py#L216). Source inspected; no execution or correctness audit performed. The retrieved documentation displays 0.10.1, so source and documentation versions differ.
- **[L3]** Kevin Tracy, **QRKalmanFilter**. Inspected commit: `ecb24c924d9b6bfc23d5e89d2e4b3f97f724432f`. [Julia implementation](https://github.com/kevin-tracy/QRKalmanFilter/blob/ecb24c924d9b6bfc23d5e89d2e4b3f97f724432f/QRkalman_filter.jl), functions `sqrkf_predict`, `sqrkf_innovate`, and `sqrkf_update`. Read with [R5]. Source inspected; no execution or correctness audit performed.

### Formalization resources and supplied context

- **[F1]** **Mathlib4**, inspected commit `99cd51ba858a791e7a4026bd4be036a1302dcfe0`. [Algebraic positive-definiteness source](https://github.com/leanprover-community/mathlib4/blob/99cd51ba858a791e7a4026bd4be036a1302dcfe0/Mathlib/LinearAlgebra/Matrix/PosDef.lean); [analytic source](https://github.com/leanprover-community/mathlib4/blob/99cd51ba858a791e7a4026bd4be036a1302dcfe0/Mathlib/Analysis/Matrix/PosDef.lean); [generated API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html). Relevant names include `Matrix.PosSemidef.add`, `Matrix.PosSemidef.conjTranspose_mul_mul_same`, `Matrix.PosDef.inv`, and `Matrix.IsHermitian.posDef_iff_eigenvalues_pos`. Source/API review only; no project build or proof effort estimate is established.
- **[F2]** Beneficial AI Foundation, **FloatSpec**, inspected commit `158263e983ec3925e02b10f5b312498bf414e0f1`. [Versioned README](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/README.md), “Current Progress” and “Roadmap.” It exposes library version 0.7.0. The review inspected the README and revision metadata; it did not independently validate its trust audit or certify suitability for QR analysis.
- **[C1]** User-supplied *Formal Methods for Orbit Determination and Satellite GNC*, subtitle *Where verification has paid off in this domain, where it has not, and what to try next*. Local file: [od_gnc_formal_methods_report.pdf](</Users/duckki/Library/CloudStorage/OneDrive-Personal/Work shared/od-gnc formalization discussion/od_gnc_formal_methods_report.pdf>). Nine pages; no named author or publication date in the document; PDF metadata records September 10, 2026. Reviewed as contextual material, especially pp. 4-6 and 8, not as independent authority for its historical or library-status claims.
