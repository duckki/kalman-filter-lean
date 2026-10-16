# Source equations and adopted specification

The source review was made on 2026-10-04. This document maps the implemented
definitions to exact source locations and labels project choices. Completed
guarantees and numerical domains are collected in [results.md](results.md).
The supplied formalization guide informed the repository organization; its
Ephemeris-specific examples do not define this filter's mathematical domain.

## Sources and declaration map

| Source | Exact location | Adopted definitions |
| --- | --- | --- |
| Särkkä and Svensson, *Bayesian Filtering and Smoothing*, 2nd ed. (2023), [author PDF](https://users.aalto.fi/~ssarkka/pub/bfs_book_2023_online.pdf), DOI [10.1017/9781108917407](https://doi.org/10.1017/9781108917407) | §6.3, Theorem 6.6, Eqs. (6.20)–(6.29), printed pp. 96–98 | `Definitions/LinearModel`, `CovarianceRecursion.predict`, `innovation`, `innovationCovariance`, `gain`, `update`, `step` |
| Thornton and Bierman, JPL Technical Memorandum 33-771 (1976), [NASA record](https://ntrs.nasa.gov/citations/19760019842) | Direct Joseph congruence: Eq. (8), printed p. 10; expanded stabilized form: Eqs. (7a)–(7b), p. 9 | `CovarianceRecursion.joseph`, native `.joseph`; vector-observation generalization stated explicitly |
| Tracy, “A Square-Root Kalman Filter Using Only QR Decompositions,” [arXiv:2208.06452v1](https://arxiv.org/pdf/2208.06452v1), submitted 2022-08-12 | §3, Algorithm 1, pp. 2–4; prediction (20), innovation (26), gain (29)–(30), correction (36) | `FactorRecursion` prearrays and `SquareRootStages`; native `SquareRootFilter` |
| Tracy's accompanying [Julia source](https://github.com/kevin-tracy/QRKalmanFilter/blob/ecb24c924d9b6bfc23d5e89d2e4b3f97f724432f/QRkalman_filter.jl) | Commit `ecb24c924d9b6bfc23d5e89d2e4b3f97f724432f`; `sqrkf_predict`, `sqrkf_innovate`, `sqrkf_update` | Algorithm cross-check; this project's implementation is independently written |
| Bierman, “Measurement Updating Using the U-D Factorization,” *Automatica* 12(4), 375–382 (1976), DOI [10.1016/0005-1098(76)90058-3](https://doi.org/10.1016/0005-1098(76)90058-3) | Published U-D measurement-update representation; abstract inspected, full algorithm not inspected | `FactorRecursion.UDFactor` storage interpretation only; no U-D runtime algorithm claimed |

`CovarianceRecursion.informationUpdate` is a project algebraic interpretation of the same
Gaussian correction in precision coordinates. Its equivalence to the covariance form is
proved in `Proofs/RealRecursion`, including the mean. It is not a transcription of a
separately audited information-filter implementation.

## Exact Real model

The specification uses `Matrix (Fin n) (Fin m) ℝ` and vectors `Fin n → ℝ`.
The model has transition $F$, observation $H$, and noise covariances $Q,R$.
State is mean $x$ and covariance $P$. There is no control input or deterministic
offset in this initial model; noises are interpreted as independent and zero mean.
The specification is algebraic; it does not formalize random variables or prove
the statistical optimality of the Kalman estimator.

For one observation $z$:

$$
\begin{aligned}
x^- &= Fx, & P^- &= FPF^T+Q,\\
y &= z-Hx^-, & S &= HP^-H^T+R,\\
K &= P^-H^TS^{-1}, & x^+ &= x^-+Ky.
\end{aligned}
$$

The three covariance expressions are stored separately for review:

$$
\begin{aligned}
P^+_{\rm compact} &= (I-KH)P^-,\\
P^+_{\rm subtractive} &= P^- - K(HP^-),\\
P^+_{\rm Joseph} &= WP^-W^T+KRK^T,\quad W=I-KH.
\end{aligned}
$$

They agree in exact arithmetic with the optimal gain and valid covariance
inputs. This equivalence is proved in Lean. Joseph also has meaning
for an arbitrary gain; both its PSD and strict-PD theorems cover arbitrary gains.

`CovarianceRecursion.trajectory` composes the exact steps over a finite list of
model/observation pairs, including the initial state in its trace. Models may vary with
time while dimensions remain fixed. This is a project representation of repeated source
steps, with a completed PD-preservation theorem and a certified nine-step Float
comparison.

The information correction is

$$
Y^+=(P^-)^{-1}+H^TR^{-1}H,\quad
P^+=(Y^+)^{-1},\quad
x^+=P^+\big((P^-)^{-1}x^-+H^TR^{-1}z\big).
$$

Mathlib's matrix inverse is total, including singular matrices. These definitions
therefore exist outside their intended domain, but the validity contracts require
the relevant covariance matrices to be PD. A total inverse is not a promise of
meaningful Kalman behavior on singular input.

The first strict domain requires $n,m>0$, $P\succ0$, $Q\succ0$, and $R\succ0$.
Strictly positive process noise allows singular $F$. The source's broader PSD
domain and weaker rank hypotheses are documented in
[the background notes](project-notes/project-background.md#4-exact-reference-and-theorem-hypotheses); they are
not silently substituted for this initial profile.

## Square-root interpretation and implementation choices

This implementation adopts Tracy's three-QR Joseph arrangement. It transposes
the source's upper-factor convention into lower factors $P=LL^T$. The block
array update described in
[the background notes](project-notes/project-background.md#6-recommended-square-root-target)
remains a separate research candidate.
Its published constants do not automatically apply to this implementation.

Given $Q=T_QT_Q^T$ and $R=T_RT_R^T$, the stages are:

$$
\begin{aligned}
A_{\rm pred} &= [FL\mspace{5mu}T_Q],\\
A_{\rm innov} &= [T_R\mspace{5mu}HL^-],\\
A_{\rm post} &= [(I-KH)L^-\mspace{5mu}KT_R].
\end{aligned}
$$

Each stage applies QR to $A^T$ and retains a lower factor $L=R_{\rm QR}^T$.
The ideal `QRGramFactor` relation explicitly requires an orthogonal right
transformation $U$ with $AU=[L\mspace{5mu}0]$, a lower triangular $L$, and a positive
diagonal sign convention. It specifies mathematical factorization without
choosing a canonical noncomputable QR algorithm.

The runtime `OrthogonalFactorization.gramFactor` is unpivoted Householder QR.
It scales each active column by its maximum magnitude, normalizes the reflector,
applies separately rounded dot products and rank-one updates, then makes the
retained factor diagonal positive by sign changes. Zero pivots and nonfinite
intermediates produce errors. Successful factorization of every valid Real
input is not claimed. The complete-loop theorem establishes a Gram residual bound under
prefix operand profiles; the initial-input theorem derives those profiles and success from
one original-input energy/rank and scale domain with at most eight tall QR rows.

The maximum-scaled column-norm kernel is `scaledColumnNorm`.
`FloatQRNorm.scaledColumnNorm_range_schedule` proves operation-order equivalence,
including failures. Its numerical theorem proves successful finite normalized norm
computation from at most 32 finite entries with one nonzero entry; the bounds use the same
stored inputs and explicit division/square/add/sqrt allowances. This is project numerical
analysis of a classical kernel, not a theorem attributed to Tracy's paper.

`householderReflector` performs the first-component subtraction, sum-of-squares, checked
sqrt, and in-place division. `FloatQRReflector.householderReflector_range_schedule` proves
equivalence for every operand, including failures. The sign rule chooses the norm opposite
to the first component, with both signed zeros choosing a negative norm. Its numerical
theorem bounds the first subtraction and the normalization of the exactly decoded stored
constructed vector, including a near-unit squared-norm bound.
`scaledColumn_reflector_accuracy` derives success of both local stages from the same
finite nonzero column inputs, for at most 32 distinct valid active indices. This is also
project analysis of our native schedule, not a bound taken from Tracy. The local bounds
and precise reference are in [results.md](results.md).

`applyReflector` performs each trailing-column dot, doubling, and mutable
rank-one update. `FloatQRApplication.applyReflector_range_schedule`
specifies the checked schedule for all values and failures.
`applyReflector_accuracy` bounds application of the same stored vector and
target column; `scaledColumn_applyReflector_accuracy` additionally propagates
construction error into an exact normalized stored-constructed-vector reference.
It derives three-stage success from finite nonzero source-column inputs and an
explicit target-column scale budget. This proof follows our source schedule and
FLARE's native nearest arithmetic/dot-step bounds; it is not a transfer of a
library or paper theorem for an entire Householder QR implementation.

`finishColumn` performs checked diagonal rescaling and intentional
positive-zero tail writes. `FloatQRFinish.finishColumn_range_schedule`
specifies the checked schedule for all operands and failures;
`active_range_cons` identifies its tail with the norm/reflector active range.
`scaledColumn_finish_accuracy` derives success from an original finite source
column of at most 32 distinct valid rows with maximum magnitude in
$[2^{-900},2^{900}]$. It proves a finite nonzero diagonal, squared-norm error
relative to the same stored input, and overwrite error relative to the same
stored reflector's exact application. Positive zeros are assigned, not computed
residuals. Its annihilation estimate and storage analysis are project proofs;
FLARE supplies the native product rounding bound. The retention result below
establishes retained-factor sign/copy analysis, and the complete-loop result composes the
whole-loop Gram error under prefix operand profiles.

`applyReflectorColumns` visits trailing columns in ascending order;
`qrIteration` combines the local kernels.
The range/iteration schedule theorems preserve both blocks for all values and
failures. `FloatQRIteration.applyReflectorColumns_accuracy` proves column
independence and an entrywise error allowance without a trailing-column-count
multiplier. `qrIteration_accuracy` composes all four local stages from the stored
iteration input, including copied prefixes and finite nonzero diagonal finishing.
Its exact unit reference normalizes the same stored constructed vector; its
uniform selected-panel radius is at most $2^{-17}M$ for at most 32 active rows
under `IterationProfile`. The proof reuses the preceding arithmetic bridges and
adds project storage/composition proofs. It does not establish preservation of
that input profile at later pivots or an ideal whole-matrix QR reference.

`retainFactor` performs the final sign/transpose conversion, with ascending checked copies
in `retainColumns` and `copyFactorColumn`. The schedule theorems specify the operation
order, including failures. `FloatQRRetain.retainFactor_accuracy` proves success from
finite stored entries and nonzero diagonals, exact signed-transpose and Gram identities
relative to the retained upper block, and strictly PD exact Gram. Multiplication by ±1 is
proved exact over the full finite binary64 domain from Lean 4.34.1's
multiplication/rounding model in `Flare.Binary64.SignMultiplication`, using canonical
unpack/pack lemmas. This sign convention implements the positive diagonal in our ideal
`QRGramFactor` relation. The source for the square-root arrangement remains Tracy's paper
above; these native-model and storage proofs are project proofs, not a numerical theorem
attributed to that paper. The complete-loop theorem composes whole-loop Gram error under
prefix profiles; the initial-input theorem derives an original-input success domain with
at most eight tall QR rows. Detailed bridge and scope are in [the retention
analysis](project-notes/proof-development.md#sixth-native-qr-slice-exact-retained-factor-conversion).

`qrIterations` and `triangularize` visit pivots in ascending order. `FloatQRTriangular`
proves exact structural postconditions of every successful loop: finite storage, preserved
earlier columns and assigned positive zeros below the diagonal, including extra tall rows.
`retainedUpper_gram_eq_full` identifies the retained block's Gram with the full stored
result's column Gram. `gramFactor_structure` combines it with exact retention, deriving a
strictly PD exact Gram for the raw factor call from its successful trace, without relying
on the filter's final validator. These are project storage/finite-sum proofs of this
program's classical triangular structure. They do not attribute a new stability bound to
Tracy or establish accuracy against the original prearray. The source arrangement remains
the Tracy QR stages above; the complete-loop theorem below adds numerical Gram error under
prefix profiles, and the initial-input theorem derives the supported domain. See [the
structural
postcondition](project-notes/proof-development.md#seventh-native-qr-slice-whole-loop-triangular-structure).

The project algebraic reference is
`Definitions.OrthogonalFactorization.reflect`, $C=(I-2uu^T)A$, where $u$ is the
exact normalization of the same stored constructed vector, embedded with zero
prefix rows. `Flare.Analysis.Householder.reflect_gram` proves the classical exact
Gram identity by finite-sum algebra; `OrthogonalStructure` exposes the same result here. This reference extends
`constructedAppliedValue`; it does not select ideal QR on the original
prearray. With the proved prior zeros, `FloatQRGram` extends the panel
error to the full reflection and bounds one actual iteration's column-Gram
change against its entire incoming stored matrix. These conservative constants
are project composition results, not paper stability constants. They preserve
all native operations and reuse the previous arithmetic bridge. Whole-loop
numerical composition is completed under prefix profiles by the complete-loop theorem
below; the initial-input theorem derives later source domains from the supported initial inputs.
See [the exact reference and radius](project-notes/proof-development.md#eighth-native-qr-slice-one-iteration-column-gram-error).

The complete-loop theorem composes the actual ascending loop's local Gram allowances using
the Real triangle inequality. `FloatQRComposition` propagates earlier nonzero diagonals
and triangular zeros, derives final retention success, and bounds the retained factor's
exact Gram against the exact Gram of the **original stored prearray**. The exact native
transpose bridge is `Flare.Matrix.Multiplication.transpose_matrix`; the sign/transpose
retention contributes zero additional error. These are project composition results with
conservative constants and the same preceding native arithmetic bridge, not stability
constants transferred from Tracy or a new QR algorithm. The `TriangularizationProfile`
requires operand conditions at every actual prefix; no final success or desired error is
assumed. The initial-input theorem discharges those conditions from its initial-input
domain. No native operation, rejection order or factor convention changes. See [the
accumulated bound and exact
scope](project-notes/proof-development.md#ninth-native-qr-slice-complete-factor-gram-error).

The prefix-enclosure theorem derives prefix magnitude and spectral bounds from initial
column energies and the initial column-Gram lower bound. `FloatQRDomain` uses
the preceding native Gram allowances, a project finite-sum diagonal-energy
argument, and FLARE's existing Real `perturbation_lower_bound` theorem. The
factor $w$ in the lost spectral margin comes from converting entrywise error
to a quadratic-form bound. No new native rounding estimate or paper constant
is imported. Profiles are needed only for preceding pivots; no next/future
profile is assumed in deriving its enclosure. The up-to-eight-row headroom
choice (column energy $M^2/2$, initial floor $M^2/8$, preserved floor $M^2/16$)
is a conservative project choice derived from the existing radius formula.
The source-tail theorem supplies the active-column witness used to close
the initial-input induction. No runtime arithmetic changes. See
[the prefix enclosure](project-notes/proof-development.md#tenth-native-qr-slice-prefix-magnitude-and-spectral-margins).

The source-tail theorem uses exact leading triangular-block invertibility to cancel
processed source rows by a linear combination of earlier columns. The source
coefficient is one; prior zeros leave the active tail unchanged. Mathlib's
determinant and exact `mulVec_surjective_iff_isUnit` consequences establish
that combination. FLARE's existing Real `quadratic_lower_bound` then proves
that the active tail retains at least the Gram floor in squared energy. For
at most eight rows and remaining floor $M^2/16$, this yields an active entry
of magnitude at least $M/16$. The project choice $M\ge2^{-896}$ meets the
already specified native source floor $2^{-900}$. This is a project exact-matrix
argument tied to the prior native bounds, not an imported whole-QR stability
constant. The native algorithm performs none of the proof's cancellation solve.
Only preceding profiles are assumed in this source-tail lemma. The initial-input theorem
closes the complete induction. See
[the source-tail statement and exact scope](project-notes/proof-development.md#eleventh-native-qr-slice-the-active-source-tail-witness).

The initial-input contracts are `InitialQRDomain` for the tall input and
`GramFactorInputDomain` for the original row prearray. The project chooses
$n\le d\le8$, $2^{-896}\le M\le2^{900}$, row energies at most $M^2/2$, and
Gram floor $M^2/8$. `FloatQRInitialDomain` uses strong induction to derive every
local profile and successful prefix, then applies the accumulated Gram theorem
and exact retention. The public `qrGramFactorInitialAccuracy` concludes success,
finite positive-diagonal lower output, exact Gram floor $M^2/16$, and error
at most the explicit Gram-radius sum, itself bounded by $M^2/128$. These
conservative sufficient margins are project consequences of the previous
constants, not a sharper stability theorem attributed to Tracy or another paper.

FLARE's `Multiplication.transpose_storage` and `transpose_matrix` provide exact
finite stored-transpose shape, finiteness and decoding, with no scale/dimension
cap or rounding error. Its `JacobiInitialization.identity_size`, `identity_finite`
and `identity_matrix` provide exact native identity storage and decoding in
every dimension; they prove a nonempty domain family through dimension eight
with $M=2$. No new native error estimate, external revision or runtime operation
is introduced. The theorem does not include rounded prearray construction or
full-filter propagation, and its PD claim concerns the factor's exact Real Gram.
See [the full input domain and bridge](results.md#initial-input-qr-success-and-error).

`FloatPrearray` proves exact copying and block-Gram assembly for the selected row-major
layout; it adds no arithmetic error. `FloatSquareRootError` composes the existing product,
noise-Cholesky and QR bounds for the entire prediction stage, including the mean product.
Its `PredictionProfile` still includes the noise operand profile and intermediate
operation equations, so this is a stage composition theorem, separate from an
original-model full-filter domain. The reference uses the decoded noise covariance and
incoming factor Gram; rounded noise factorization is included. See [prediction
bounds](results.md#prediction-stage-native-prearray-and-mean-accuracy).

Noise factors and the initial state factor use a direct native Cholesky loop.
These rounded factors introduce errors relative to the decoded $P,Q,R$;
`FloatCholeskyFactor.factor_backward_error` now bounds these errors under an
explicit a posteriori operand profile. The later original-input Cholesky and
horizon theorems derive that profile and propagate these factor errors through
the full filter for the stated two-state family.
The square-root gain uses
two triangular solves on the innovation factor, without materializing $S$.
Both solves subtract products in ascending residual-index order before dividing
by the stored diagonal; backward substitution visits rows in descending order.
Their shared checked residual helper preserves separately rounded products and
subtractions. The helper's error adapter is proved to preserve the native schedule,
including failures, in `Proofs/FloatResidualError.subtractProducts_schedule`.

The local arithmetic sources are the reviewed FLARE revision
`15c4847df7229c8346a8168cfd4551db0597fb0e`:
`Flare/Matrix/Substitution.lean`, theorem `subtractProducts_accuracy`;
`Flare/Binary64/Division.lean`, theorem `div_error_relative`;
`Flare/Binary64/Sqrt.lean`, theorem `sqrt_error_nearest`; and
`Flare/Analysis/NumericalBounds.lean`, theorem `residual_entrywise_bound`.
The runtime-to-model bridges and restricted domains are recorded in
[the numerical bounds](results.md). The completed two-pass solve bound
uses the exact Gram of the stored innovation factor; it does not silently replace
that factor's denotation by the ideal innovation covariance.

The primary square-root output is the stored factor. Its exact Real Gram matrix
and its optional `materialize` result are distinct. `materialize` performs an
additional native matrix product. Generic dense positivity needs a separate
margin; the original-input two-state horizon now derives that margin below.
The two-state native Gram symmetry proof unfolds the actual ascending two-term
multiply/add schedule. Swapping row indices commutes each rounded product but
does not reorder accumulation. Multiplication commutativity is proved from
Lean 4.34.1's native logical binary64 model, including signed zero and its
canonical exceptional results. Successful finite products therefore have
identical off-diagonal words, with no symmetry repair. The retained covariance
cap two derives absolute dot-product mass two and a conversion radius $2^{-48}$;
these are completed theorems. The dense horizon theorem separately derives its
PD composition from the same original input conditions.

The regressions include a tiny full-rank factor whose dense materialization
underflows to the zero matrix, making this distinction observable.

## Direct Joseph covariance evaluation domain

The direct Joseph stored-input evaluation theorem uses the existing
`CovarianceFilter.covarianceUnchecked .joseph` order: KH multiplication,
identity subtraction, WP multiplication, multiplication by transposed W,
KR multiplication, multiplication by transposed K, then addition. This is the
same direct Joseph expression attributed above; no runtime reassociation, FMA,
symmetry repair, or exceptional-value behavior is introduced. The sufficient
two-state stored-entry caps P/H/R/K = 4/1/(3/2)/1, derived product
mass 256, sum exponents 2 and 8, and error allowance 2^-34 are project choices,
not constants from the source literature. The comparator uses the same stored
gain and dense prior. Stored `W` is bounded by `7/2`, exact `I-KH` by three,
and stored `WP` and the first congruence term by 29 and 204. These sharper
intermediate bounds allow the prior cap of four (covering the reached `13/4`
prediction bound) without increasing the `2^-34` allowance.
This covariance-kernel theorem is separate from the completed computed-gain
and accumulated full-filter results below. It reuses the pinned FLARE nearest-arithmetic,
matrix multiplication, and native/model bridges already recorded here.

The companion `FloatJosephSolve` proof specializes the unchanged native LDLᵀ
solve to diagonal two-state coefficients in `[3/2,5]` and finite RHS entries
bounded by four. The first pivot is the original first diagonal word; the
second differs from its original diagonal value by at most `2^-49`. The lower
factor decodes to identity. FLARE forward/backward substitution equations and
rounding bounds then yield `2^-40` entrywise error against the original
coefficient matrix inverse times RHS, and exact decoded diagonal preservation
when RHS is diagonal. These intervals and allowances are project choices for
the completed Joseph gain proof, not a general conditioning theorem.
All storage lookups retain the runtime's zero-padding semantics; the result
does not need an additional array-shape premise. The existing native/model
bridge and signed-zero interpretation apply unchanged.

`FloatJosephGain.gain_stages` specializes the common dense correction gain
prefix to original diagonal prior variances `[15/16,13/4]`, original diagonal
measurement noise `[1,3/2]`, and stored observation decoding to identity. The
unchanged native order is HP, HPHᵀ, addition of original R, PHᵀ, RHS transpose,
LDLᵀ solve, then gain transpose. Product mass eight and sum exponent three
are derived from original operand bounds. Innovation error against original
`P+R` is at most `2^-44`; its diagonal entries lie in `[3/2,5]`. The sharp
solver theorem and an original-coefficient perturbation argument yield gain
error `2^-36` against original `P(P+R)⁻¹`, with native gain diagonal entries in
`[3/8,13/16]` and exact decoded off-diagonal zeros. These budgets are project
choices. No factorized or separately rounded R replaces the original words.
This prefix result does not by itself certify a complete filter horizon.

`FloatJosephStructure.stored_input_positive` additionally certifies the
rounded dense kernel's positivity on the stored-input domain when `H=I`,
`P,R,K` decode to diagonal matrices, and prior/noise diagonal entries are at
least `1/2`. For any supplied gain satisfying the entry bound, exact scalar
Joseph variance is at least `1/4`; diagonal preservation through every rounded
operation and the `2^-34` entrywise error imply a retained floor of `1/8` and
positive definiteness. These floors are project margins, not source constants.
The proof concerns the returned dense array directly, with no symmetry repair
or assumption that a rounded Gram is positive. The completed correction,
checked-step, and horizon results below additionally charge gain and prediction
error.

The complete `FloatJosephUpdate.update_accuracy` correction adds original
prior mean magnitude `19/16` and measurement magnitude one to the gain domain.
It composes actual gain/residual/mean stages and the covariance kernel, compares
with the exact optimal-gain update of the same stored incoming prior, and bounds
both covariance and mean errors by `2^-33`. The quadratic Joseph gain-error
identity charges at most `2^-50` for gain perturbation; mean gain perturbation
is charged linearly with residual magnitude at most three. The returned dense
covariance is diagonal with entries `[7/16,13/8]`, and returned mean magnitude
is at most `9/8`. These are propagated native storage conditions, not assumed
output errors. Finiteness, shapes, and positivity are proved without repairing
symmetry or reinterpreting a rounded dense covariance as an exact Gram.
Prediction and accumulated trajectory errors remain separate from this local
correction theorem.

`FloatJosephPrediction` charges both native dense covariance products and Q
addition, with product mass eight and sum exponent two. On the dense invariant
and shared original full-observation model domain, prediction covariance/mean
errors are `2^-42/2^-46`; returned variances `[15/16,13/4]` and mean magnitude
`19/16` discharge the complete correction domain. `FloatJosephFilter.step_accuracy`
includes the actual public model/state validation and all native prediction/
correction stages, preserves the dense invariant, and bounds both local errors
by `2^-32` against an exact full step from the same incoming stored state.
Exact correction sensitivity propagates the prediction discrepancy through
the optimal gain and mean; it is not omitted. The step result is complete,
and the horizon result below separately accumulates independent-trajectory
discrepancy.

The completed `FloatJosephHorizon.initialized_horizon_accuracy` result uses
the same original fully observed diagonal model/initialization domains as QR.
Initial/native input arrays have correct finite shapes, `n=m=2`, `H=I`,
diagonal F/Q/R and initial covariance, transition magnitudes at most one,
original initial/noise variances `[1,3/2]`, and original initial mean/every
measurement bounded by one. No reached execution, profile, reference-state
bound, or desired output error is an original-input hypothesis.

The correctness-side `josephRun` specifies repeated calls to the existing
checked runtime step without changing or duplicating its arithmetic. Native
initialization preserves the original dense words exactly, with zero initial
error. The independent exact matrix `exactRun` uses those same original words
and time-varying models, and has its own invariant. Local full-step error
`2^-32` and exact covariance/mean sensitivity coefficients `9/25` and `3/5,1/2`
close uniform covariance/mean budgets `2^-30/2^-29` at every finite prefix.
Native dense covariance entries remain `[7/16,13/8]`, hence strictly positive;
mean magnitude remains at most `9/8`. No rounded Gram or symmetry repair is
used. Identity and near-unit/sign-reversing original dynamics provide completed
nonempty-domain witnesses for every horizon. These allowances are sufficient
project certificates on a restricted shared family, not a general ranking of
Joseph and QR numerical accuracy.

## Authoritative decoded input contract

`Definitions/Input.Model` owns the one native input format. It contains state
and observation dimensions, row-major arrays for $F,H,Q,R$, and observation $z$.
`State` stores mean and dense covariance; `FactorState` stores mean and lower
factor as a different working representation of the same covariance.

Project policies:

- Dimensions are 1–32 inclusive. Shapes are exactly $n^2$, $mn$, $n^2$,
  $m^2$, and $m$; state mean has $n$ entries.
- All input entries must be finite native `Float` (IEEE binary64 in Lean).
  Both signed zeros are accepted; NaN and infinities are rejected.
- $Q$ and $R$ must compare exactly symmetric. The guards do not certify PD.
- Dense state covariance is not required to compare exactly symmetric. This
  lets conventional roundoff be observed without repairing or hiding it.
- Factor states require finite storage, an exactly zero upper triangle, and
  strictly positive native diagonal entries.
- Model checks precede state checks. Model rejection order is dimensions,
  shapes, finiteness, then noise symmetry; factor structure is checked last.

The Cholesky and FLARE LDLᵀ kernels read the lower triangle. For a rounded
asymmetric innovation, LDLᵀ therefore acts on its lower-triangle symmetric
interpretation. This is an explicit solver policy; no full covariance symmetry
repair is applied. The conventional forms can return a negative covariance.

Arithmetic checks reject every nonfinite product, sum, difference, quotient,
and square-root result in the implemented kernels. Positive computed pivots
are required by factorizations. Runtime acceptance does not discharge the Real
domain or error-theorem conditioning hypotheses.

Unchecked helpers require valid shapes and finite inputs from their callers.
They are implementation building blocks; the supported public APIs are the
checked `predict`, `update`, and `step` operations.

## Reproducible cancellation fixtures

The native executable tests record three scalar cases:

| Fixture | Inputs | Observed native behavior |
| --- | --- | --- |
| Loss of strict positivity | Prior $P=1$, $H=1$, $R=2^{-54}$ | Compact and subtractive correction return zero; Joseph returns $R$ and QR retains a positive factor. The exact posterior is $1/(2^{54}+1)>0$. |
| Negative variance | Initial $P=1$, $F=0$, $Q=1$, $H$ from binary64 word `0x3ffd8a8f075e6e3b`, $R=2^{-60}$ | Full-step compact and subtractive posterior is $-2^{-52}$; Joseph and QR return positive results. |
| Repeated failure | Initial $P=1$, $F=2^{23}$, $Q=2^{-47}$, $R=2^{-63}$, $H$ from `0x3ffecc02dca65478`, zero mean/measurements | Compact has eight positive posteriors then a negative ninth with word `0xbc10000000008102`; native Joseph and QR stay positive. |

In the second fixture $H\approx1.846327809128424$ and the predicted covariance
is exactly one. The exact scalar posterior is $R/(H^2+R)>0$ using the exact Real
meaning of those same input words. This algebraic observation and the native
test are accompanied by Lean-certified counterexamples to the complete
source recursion. `FloatTraceCounterexample` additionally certifies every
transition of the nine-step fixture, finite outputs, the positive prefix, and
strict PD of the exact iterated reference at every horizon. No monotone growth
of absolute error or minimal failing horizon is claimed. The separate 100-step
rectangular regression remains a benign agreement case.

## Numerical correction and propagation choices

The measurement-update proof follows the existing Tracy-based schedule in
`SquareRootFilter.updateUnchecked`. The exact comparator uses the original
decoded $R$ and the exact Gram of the incoming stored factor. Innovation QR,
rounded numerator and both triangular solves contribute to the gain error;
Joseph is then compared first at the computed gain, and then at the exact gain.
The mean proof includes projection, residual subtraction, increment and addition.
The project coefficients in `Proofs.SquareRootProfiles.Update` and
`Definitions.Theorems.RecursionSensitivity` keep all
cross terms. `RecursionSensitivity` accounts for the effect of an imperfect
prior on gain and residual. These are implementation-specific composed bounds,
not constants attributed to Tracy or a claim of new Kalman theory. FLARE's pinned
native model bridge and imported domains are unchanged. Original-input domains
for general Cholesky/solve execution remain a separate obligation; the
two-state Cholesky theorem below derives one sufficient family.

The completed `FloatFullFilter.step_accuracy` theorem now propagates an
independent incoming-state error through the entire checked square-root step.
Its local comparison never resets the ideal trajectory to rounded output.
`StepEnvironment` bounds the ideal predicted state, while the theorem derives
the larger native-prior magnitudes from the prediction allowance. The original
public square-root `StepWithin` contract is a corollary under these profiles.

## Finite-horizon accuracy and chosen operating budget

The exact comparator is initialized once and consumes exactly the original
finite native model/measurement words. `InputInterpretation.atDimensions` supplies
fixed Lean indices and is proved equal to native input when its metadata agrees.
The completed horizon theorem composes initialization, prediction and correction
errors without resetting the comparator at an intermediate rounded state.

The two-state `UniformStepParameters` budgets are project choices: F/H entry caps `1/32`,
product/noise masses `8`, solve mass `32`, diagonal floors `1/2`, QR budget `2`, original
R floor/bound `1`, and ideal predicted P/residual caps `2`. After tightening QR
normalization and source-annihilation estimates, full coefficient inequalities keep
covariance and mean errors at most `2⁻²⁵` for any finite length whose numerical domains
hold and whose initial errors also meet that tolerance. The earlier `2⁻²⁰` and original
`1/128` interfaces remain valid. The coefficient proofs retain cross terms and are
conservative bounds for this program, not constants attributed to Tracy or the classical
papers. All reached-prefix conditions are discharged for a reset model to prove
nonvacuity, including its retained negative-zero word. A general original-model invariant
for nontrivial dynamics is not claimed.

The new reflector bound uses native magnitude-scaled square/add errors relative to the
original constructed vector's squared norm; its positive norm floor absorbs underflow
allowances. The column-norm allowance now keeps the prefix count, and reflector
normalization keeps the active row count, using `(9k+5)2⁻⁵⁰` instead of a blanket `2⁻⁴⁰`.
The source estimate uses the relation between an individual component and that norm, and
charges the linear alpha defect only to the head; tail defects contribute their squares.
The iteration uses the larger of the source and trailing-application allowances, since
neither dominates at every length. Neither change modifies the executable program or
introduces a new caller assumption. These constants are derived here, rather than asserted
as an instantiation of a published QR algorithm.

The executable repeated-step driver lives in `Implementation/SquareRootFilter`.
`Implementation/Correctness/InputInterpretation.nativeRun` is only an alias to that
driver; the runtime module imports the checked filter and no correctness, proof or test
modules. The first failing prefix propagates its error, and no rounded dense covariance is
introduced by the driver.

## Original-input two-state Cholesky domain

`Implementation/Correctness/InputInterpretation.TwoStateCovarianceDomain` chooses finite
symmetric 2×2 stored covariances with diagonal values in `[1,2]` and off-diagonal
magnitude at most `1/4`. These constants and the resulting `2⁻⁴²` absolute entrywise
allowance are project choices/derivations, not paper requirements or new claims about
classical Cholesky theory. Symmetry is equality of decoded finite values, so opposite
signed zeros satisfy both the mathematical condition and the native guard.
Covariance/noise roles consume the same original dense input values.

`Proofs/FloatCholeskyDomain.cholesky_two_schedule` identifies the exact native
operation order, including its rejection paths: first square root, off-diagonal
division, one rounded multiplication and subtraction, then the second square
root. FLARE finite comparison, `Division.div_error` at exponent `-1`, and the
already proved residual/positive-square-root bounds derive all guards and the
final `FactorProfile 2 a l 8 (1/2) 2`. The original covariance has exact floor
`3/4`; the factor's exact Gram has floor `1/2` and error at most `2⁻⁴²` against
that original covariance. Checked initialization preserves the mean exactly.
The pinned FLARE bridge/trust boundary is unchanged, and runtime code is
unchanged. Dense Gram rounding still has its separate obligations.

This discharges the Cholesky component for a correlated input family. It does
not discharge all uniform-horizon conditions, including their original R floor
`1`, solve profiles and reached-prefix invariants. See
[the complete domain and proof interfaces](results.md#two-state-cholesky-from-original-inputs).

## Two-state substitution domain and original covariance solve

`Proofs/CholeskyProfiles.SolveDomain` chooses finite two-state stored lower factors
with zero upper entry, diagonal floor `1/2`, and entry magnitudes at most `2`.
The two RHS columns are finite and bounded entrywise by `1/8`. These constants
are sufficient operating choices. `FloatCholeskySolveDomain.solve_profile`
derives every field of `SolveProfile 2 2 l b y x 32 (1/2) 2`, including both
successful runs, from those operands. Forward rows ascend, backward rows
descend, and RHS columns ascend; every row performs the original separately
rounded products/subtractions followed by its checked division. Runtime code
and exceptional-value policy are unchanged.

With exact stored Gram floor `1/2`, solution discrepancy from `(LLᵀ)⁻¹B` is
at most `2⁻³⁷`, and output entries have magnitude at most `1`. Composing with
the original covariance domain above derives that floor and accounts for the
Cholesky discrepancy, proving the same allowance against **original** `A⁻¹B`.
The constants are implementation-specific finite estimates derived here, not
attributed to a paper. FLARE supplies the native binary64 residual/division
enclosures, inverse-entry and residual-to-solution lemmas with the previously
recorded bridge. This local theorem requires factor/RHS bounds at its call site;
the complete original-input horizon theorems derive them at every reached prefix
in their operating domains. See
[the public solve statements](results.md#two-state-triangular-solves-from-stored-inputs).

## QR factor and innovation solve domain bridge

`Proofs/FloatQRFactorDomain` uses the existing original prearray domain at
budget `M=2` to derive native two-state output factor bounds. The factor Gram
floor `1/4` and lower-positive structure imply both factor diagonals are at
least `1/2`; row-energy/QR-error bounds imply all factor entries are at most `2`.
For solve conditioning, the additional original prearray floor `2/3` is a
project headroom choice. Cholesky noise accuracy and PSD of the other stored
block derive this floor, and the QR perturbation leaves output Gram floor `1/2`.

The composed solve retains the `2⁻³⁷` error cap relative to the returned factor
Gram. Its separate original-prearray comparison includes QR discrepancy in a
`2⁻²⁰` convenience cap. These constants are project derivations, not attributed
paper constants, and the uniform filter radii continue using sharper allowances.
Runtime operation order, exceptional behavior, storage, and the pinned FLARE
bridge are unchanged. The formed observation-block energy and RHS bounds are
still explicit, as are their discrepancies from the original model. See
[the exact interfaces and domains](results.md#two-state-qr-factor-to-innovation-solve).

## Formed gain operating domain

`Proofs/CorrelatedStages.Gain.TwoStateDomain` chooses observation entry cap
`1/64`, prior-factor entry cap `2`, and exact stored covariance entry cap `2`.
The observation cap is stricter than the earlier uniform allowance `1/32` to leave
room for rounded products. The input-derived profiles now use the actual
original H cap `1/64` in their error propagation. `FloatGainDomain.formed_rhs` uses covariance-level
magnitudes and separately propagates both product errors, giving RHS entries
at most `1/16 + 5·2⁻⁴⁶`, hence below the existing solve cap `1/8`.

The two-pass solve then gives actual gain magnitude at most `1/3` on innovation Gram floor
`1/2`. `gain_profile` retains the uniform gain allowance `1` while exporting the sharper
actual magnitude. These are implementation-specific derived headroom choices, not new
paper claims. The native operation order, finite guards and copied transpose are
unchanged. The later innovation and original-input horizon theorems derive the reached
profiles and preserve the stored covariance bound. See [the public
statements](results.md#formed-two-state-gain-rhs-and-magnitude).

## Innovation prearray headroom from original noise

`Proofs/CorrelatedStages.Innovation` caps original noise diagonals by `3/2`
within the preceding Cholesky input domain. This is a project headroom choice:
the noise factor contributes row energy at most `3/2 + 2⁻⁴²`, and the rounded
observation block contributes at most `1/32`. `FloatInnovationDomain` derives
the full QR input domain and complete innovation/gain profiles from this local
stored-input domain. The earlier `UniformStepParameters` additionally require
`R=I`. The original-input horizon theorem below uses a floor of `3/4` and
R cap `3/2` to prove the same tolerance with correlated measurement noise.

Its composed accuracy theorem compares with original noise and the exact stored prior
covariance, using the existing implementation-specific stage radii. Native Cholesky,
product, QR and solve order and exception policy are unchanged. The posterior theorem
below supplies its local bounds; original-input trajectory preservation is supplied by the
invariant theorem below. See [the exact local domain and
statements](results.md#innovation-and-gain-from-a-stored-local-input-domain).

## Local mean correction headroom

`Proofs/CorrelatedStages.Mean` now admits predicted-mean magnitude `≤ 9/32` and
measurement magnitude `≤ 1`, both with finite two-component storage. These
are project operating choices, not paper assumptions or statistical confidence
bounds. The actual stored-gain cap `1/3` derives mean-stage headroom:
rounded projected measurement `≤ 1/64`, residual `≤ 33/32`, increment
`≤ 45/64`, and output mean `≤ 1`. The final sum has headroom since
`9/32 + 45/64 = 63/64`; the separate rounding allowance fits the remaining
`1/64`. This prepares stronger transition dynamics without increasing the
stored-gain evaluation error cap. The unchanged native order is `Hμ`, `z−Hμ`,
`K·residual`, then `μ+increment`, with separately rounded products/sums and
existing finite guards. There is no symmetry repair or changed runtime kernel.

`FloatMeanDomain` proves evaluation error `≤ 2⁻⁴⁵` against this expression at
the same stored gain. Its separate ideal correction comparison derives the
ideal gain cap `1/6` from original noise floor `3/4` and stored covariance cap
`2`; the ideal residual cap is `2`. The resulting closed `localMeanRadius`
includes gain/noise/QR/solve errors and is proved `≤ 2⁻²⁵`. These finite estimates
are derived for this implementation using the recorded FLARE bridge; they are
not attributed literature constants. Incoming state discrepancy against an
independent trajectory is still handled by the full-step sensitivity proof.
The posterior and full-step theorems below complete local discharge and
invariant composition.
See [the public local mean statements](results.md#mean-correction-from-stored-local-inputs).

## Original local prediction and correction handoff

`Proofs/CorrelatedStages.Prediction` chooses transition entry cap `1/8`,
incoming mean cap `1`, incoming factor entry/covariance caps `2`, and original
process-noise diagonals in `[1,3/2]` with off-diagonal magnitude `≤ 1/4`.
These reuse the prior headroom choices for process noise and leave room inside
the correction's predicted-mean cap `9/32`. Prediction does not require an
observation or measurement value; `CorrectionInputs` separately records those
static bounds when composing it with correction.

`FloatPredictionDomain` derives FL Gram energy through
`(FL)(FL)ᵀ = F(LLᵀ)Fᵀ`, then includes the native product error. This uses
the covariance cap and preserves the cancellation hidden by loose factor-entry
bounds. The program executes prediction QR on `[FL,T_Q]`; its order is unchanged.
Original process-noise accuracy
gives the stronger prediction prearray floor `11/16`; its diagonal cap `27/16`
leaves output covariance floor `2/3` and entry cap `7/4` after QR rounding.
The returned factor entries are bounded by `2` and the mean by `9/32`.

The closed covariance radius includes original Q factorization, transition
product and QR error, and is proved `≤ 2⁻²⁵`; the mean allowance is `2⁻⁴⁶`.
`prediction_correction_domain` derives all reached local correction input
conditions from these returned bounds and static measurement inputs. These
constants are project derivations with the recorded FLARE bridge. Runtime
operation order and finite guards are unchanged. See
[the prediction statements](results.md#prediction-from-stored-local-inputs).

## Posterior QR headroom and returned-state bounds

`Proofs/CorrelatedStages.Posterior` uses prediction's covariance floor `2/3`
and entry cap `7/4`. The original noise/observation bounds sharpen ideal gain
magnitude to `7/48`; the completed gain error cap `2⁻²⁰` leaves native stored
gain magnitude `≤ 1/6`. This tighter bound suffices for posterior row energy
without invoking an optimal-gain contraction identity. These constants are
project derivations for the recorded native algorithm, not literature claims.

`PosteriorStructure` bounds the exact `[ (I−KH)L, KT_R ]` reference at the
same stored gain, with floor `20/39` and diagonal cap `251/128`. The latter
uses row absolute masses `97/96` for `I−KH` and `1/3` for `K`, and the exact
noise-factor Gram cap `25/16`, including original-noise Cholesky error.
`FloatPosteriorPrearray` accounts for the actual separately rounded `KH`,
identity subtraction, `WL` and `KT_R` in their existing order. Its Gram
perturbation cap `2⁻³⁸` leaves QR input floor `1/2` and diagonal cap `63/32`.
Native QR rounding leaves returned covariance entry cap `2`, finite lower
factor entry cap `2` and strictly PD exact Gram. No symmetry repair is added.

`FloatPosteriorDomain.correction_accuracy_and_bounds` includes original noise,
computed gain and mean errors in both local ideal-correction budgets `≤ 2⁻²⁵`.
Its returned mean cap `1` supplies the next prediction's numerical assumptions.
The reference prior is still the exact current stored factor Gram; discrepancy
from an independently propagated ideal prior belongs to full-step sensitivity.
[The public statements](results.md#posterior-qr-from-reached-stored-inputs)
record this distinction. The checked-step invariant is now composed below;
accumulated horizon accuracy is composed below.

## Original-input full step and preserved nontrivial family

`Implementation/Correctness/CorrelatedNoiseFilterAccuracy.ModelDomain` collects dimensions `n=m=2`,
finite correctly shaped F with entry magnitude `≤ 1/8` and H `≤ 1/64`, finite measurement
magnitude `≤ 1`, and original Q/R in the Cholesky domain with diagonals
`[1,3/2]`, symmetric off-diagonal magnitude `≤ 1/4`. The retained
`StateInvariant` specifies a valid finite lower-positive factor and caps mean,
factor entries and exact covariance entries by `1`, `2`, `2`. Neither an
arithmetic profile nor an error bound is assumed. Dense initialization uses the
same covariance/noise headroom and finite mean magnitude `≤ 1`.

`FloatFilterInputDomain` derives every input validation check and complete
`StepProfile`. For exact prediction from the incoming stored state, covariance
entries are bounded by `7/4` and residual by `2`; original R has floor `3/4`
and entry cap `3/2`. This independently establishes `StepEnvironment` and the
full-step sensitivity reference. Including rounded prediction's effect on ideal
correction, both local full-step radii are proved `≤ 2⁻²⁵`.
`step_accuracy_and_invariant` also establishes the same returned operating caps,
so no reached numerical bound must be assumed for a following step.

`initialize_invariant` gives checked dense-to-factor success, error `≤ 2⁻⁴²`
and zero mean error from original input conditions. `initialized_run_invariant`
then proves success and PD exact retained covariance for all finite prefixes
of time-varying inputs in `ModelDomain`. This statement is broader than the
earlier uniform **accuracy** budget's identity-R condition. This prefix theorem
proves success and bounds; the accumulated-error theorem below additionally
compares with an independent ideal trajectory and includes correlated R.
A kernel-checked witness uses nonzero F, correlated Q and original covariance
`[[1,1/4],[1/4,3/2]]`, and mean `[1,−1]`. All constants are project choices;
native arithmetic, guards and FLARE's recorded model bridge are unchanged.

## Independent exact trajectory headroom

`RealFilterInvariant` uses the same ideal recursion and exact original input
values. The completed optimal-gain identity yields
`P − P⁺ = K S Kᵀ ⪰ 0` for the Real Joseph covariance. This is an algebraic
consequence of the source gain/correction equations already attributed above;
it is not a new numerical stability claim about the rounded gain.

Starting from the original dense covariance, the independent reference remains
PD with covariance entry cap `2` and mean cap `1`. Prediction supplies covariance
cap `7/4`, mean cap `1/4`, ideal gain cap `7/48` and residual cap `2`, leaving
ideal posterior mean cap `5/6`. Every `StepEnvironment` is thus derived with
floor `3/4`, predicted covariance cap `7/4`, original R cap `3/2` and residual cap
`2`. These are sufficient project headroom choices. Native roundoff or native
trajectory agreement is not used to assume the independent ideal bounds.

## Original-input accumulated accuracy with correlated noise

`Implementation/Correctness/CorrelatedNoiseFilterAccuracy.HorizonDomain` assembles only
original decoded input conditions. `FloatInputHorizon` connects dense initialization, the
preserved native invariant, every derived numerical profile, the independent ideal
invariant and the general horizon induction. Its public result bounds both
covariance-entry and mean-component discrepancies by `2⁻²⁵` at every finite prefix,
starting with the exact original dense covariance and mean. The initial `2⁻⁴²`
factorization error is included; the reference is not silently changed to the returned
initializer Gram.

The completed coefficient check uses the derived original-noise floor `3/4`,
predicted covariance cap `7/4`, R entry cap `3/2` and residual cap `2`. This
preserves the same `2⁻²⁵` accumulated tolerance with time-varying correlated Q/R.
The earlier identity-R uniform coefficients remain a special case. These are
implementation-specific sufficient constants, not constants attributed to a
paper. Higher-order and normal/subnormal contributions remain included.

A nonzero-F witness has correlated Q, R and original initial covariance
`[[1,1/4],[1/4,3/2]]` for arbitrary finite horizon. A second witness reaches
F entries `±1/8`. The theorem's F/H entry caps `1/8` and `1/64` are significant
operating restrictions. General near-identity navigation
dynamics, wider dimensions and broader scales require further invariants and
coefficient checks. The retained-factor theorem denotes its exact covariance;
the separately rounded dense result below now derives its own positivity margin.
A 256-step changing-noise native regression supplements the proof with seven
independent Decimal-oracle checkpoints reproduced at 120 and 160 digits.

## Rounded dense horizon output

`FloatDenseHorizon` adds no native arithmetic or symmetry repair. Cholesky's returned Gram
floor `1/2` supplies the zero-prefix floor `1/4`; the actual posterior QR budget `M=2`
supplies the same floor `M²/16=1/4` after every step. The covariance cap two bounds each
absolute dot-product mass by two, using `2|ab| ≤ a²+b²`. Native materialization therefore
has error `2⁻⁴⁸` per entry. The already proved native schedule symmetry and the two-state
perturbation bound give dense floor `1/4 − 2⁻⁴⁷ > 0`. The independent ideal covariance
comparison has radius `2⁻²⁵ + 2⁻⁴⁸`; unchanged mean words retain radius `2⁻²⁵`. All
initialization, native runs, profiles, symmetry and floors are derived from
`Implementation.Correctness.CorrelatedNoiseFilterAccuracy.HorizonDomain`, containing only
original finite input conditions.

These are project choices and consequences of the recorded FLARE multiplication
bound, native QR/Cholesky proofs and matrix perturbation theorem; they are not
constants quoted from Tracy or another paper. No new dependency or native-model
bridge is introduced. The generic tiny-factor underflow witness lies outside
the quarter-floor domain and remains a valid limit on universal dense positivity.

## Full observation and diagonal dynamics: Real specialization

`Definitions/DiagonalObservation` uses the already recorded Särkkä–Svensson
Theorem 6.6, Eqs. (6.20)–(6.29), printed pp. 96–98. The source model is
specialized to diagonal F/Q/R/P and H equal to identity. Prediction variance
`a=f²p+q`, optimal gain `a/(a+r)`, corrected variance `ar/(a+r)`, and corrected
mean `r/(a+r)·fx + a/(a+r)·z` are project algebraic specializations, proved equal
to the existing matrix recursion for all three covariance forms. Innovation
diagonals are positive, so no totalized singular inverse is used.

The independent Real domain chooses `|f|≤1`, Q/R diagonals in `[1,3/2]`,
initial variance in `[1/2,3/2]`, and mean/measurement magnitudes at most one.
Prediction variance `[1,3]`, posterior variance `[1/2,1]`, posterior mean cap
one, and every-prefix covariance floor `1/2` are completed proofs. These exact
results apply to any finite dimension, including identity dynamics;
they do not introduce a second native input owner. The implemented native
observable family is two-state. Its prediction/innovation budgets, returned QR
diagonality, complete correction and local joint roundoff allowance are derived
below, followed by independent ideal-trajectory accumulated accuracy and rounded
dense output. No new arithmetic library or
native bridge is imported.

## Full-observation joint sensitivity: project-derived constants

`Proofs/RealObservableSensitivity` derives exact perturbation identities from
the same Särkkä–Svensson specialization above. For prior variances `a,b≥1`,
gain difference is `r(a−b)/((a+r)(b+r))`; posterior variance difference is
`r/(a+r)·r/(b+r)·(a−b)`. Mean difference decomposes into
`r/(a+r)·f(x−y) + (k(a)−k(b))·(z−fy)`. These are exact identities, not
first-order truncations or a separate source algorithm.

In the chosen Real domain, each correction weight is at most `3/5`, the
gain-difference coefficient is at most `1/4`, and reference innovation has
magnitude at most two. Prediction variance sensitivity is at most one for
`|f|≤1`. The resulting full-step bounds are `eP⁺≤(9/25)eP` and
`eX⁺≤(3/5)eX+(1/2)eP` in maximum entry/component errors. Choosing joint
radius E with covariance error at most `E/2` and mean error at most E gives
strict contraction `17/20`, even at identity dynamics. This weights
covariance-to-mean coupling explicitly, rather than inferring mean stability
from covariance contraction alone.

These are sufficient project constants proved for the original matrix
specification in arbitrary finite dimension; they are not quoted paper
constants or a novelty claim about exact Kalman contraction. Two exact
trajectories have discrepancy at most `(17/20)^t E₀`. The perturbed-step
recurrence `δ+(17/20)E` and fixed budget `(20/3)δ` are also proved, conditional
on a supplied local joint-error bound δ. These Real lemmas alone assert no
native δ or complete native invariant. The existing Float
full-horizon domain and its binary64 bridge are unchanged. Native prediction
and innovation, the larger gain solve, posterior profiles and the complete
local joint-error certificate are proved below. Independent ideal-trajectory
accumulated accuracy and rounded dense output are completed below.

## Larger native prediction and innovation: project operating choices

`FloatObservablePrediction` and `FloatObservableInnovation` analyze the existing
Tracy (2022) §3/Algorithm 1 stages, in this project's lower-factor convention
and actual `[FL,T_Q]` / `[T_R,HL]` order. No source equation or native algorithm
is changed. The original decoded input remains owned by `Definitions/Input`;
the local incoming factor is its retained working representation.

The sufficient native prediction domain chooses two states, diagonal F with `|f|≤1`,
original diagonal Q variances in `[1,3/2]`, factor entries at most two, exact incoming
Gram diagonals at most `13/8`, and mean magnitude at most `9/8`. These slack caps are
project choices around the Real invariant, rather than paper constants. Incoming factors
may be correlated. Q's exact floor one, the proved Cholesky error `2⁻⁴²` and
covariance-aware FL energy derive prearray floor `63/64`, energy cap `51/16` and QR budget
`21/8`. Native prediction returns floor `15/16`, covariance diagonal cap `13/4`,
factor/mean caps `2` / `19/16` (the mean cap is tightened from the earlier `5/4`), and
local covariance/mean errors `2⁻²⁴` / `2⁻⁴⁶`.

H decoding to I and original diagonal R variances in `[1,3/2]` derive the
reached innovation's prearray floor `15/8`, energy cap `77/16` and budget
`25/8`. The actual innovation QR returns retained covariance floor `29/16`,
diagonal cap `39/8`, factor cap `9/4` and local Gram error `2⁻²³` against
the incoming retained covariance plus original R. These derive from the same
FLARE native multiplication, Cholesky and QR bounds already recorded. Prediction
includes original-Q factorization; innovation includes original-R factorization.
Neither stage allowance is an accumulated independent-trajectory bound.

`FloatDiagonalStorage` additionally uses the pinned FLARE
`Binary64.Zero.mul_zero`, `add_zero` and `div_zero` theorems. Their domain is
finite native operands, an exactly zero product/sum (or zero numerator and
nonzero divisor). They preserve decoded zero, including opposite signs;
they do not assert word equality of signed zeros. The extracted native loops
prove decoded diagonal preservation for two-state multiplication and Cholesky,
with no symmetry repair. `FloatQRDiagonal` now proves preservation through
the native QR loop and signed retention as well: transposed diagonal blocks
have column supports `{0,2}` and `{1,3}`, so their computed reflector dot is
exactly zero. A local exact subtraction-of-zeros lemma is proved from Lean
4.34.1’s unpacked binary64 model (and FLARE nearest-subtraction finiteness); it
adds no rounding assumption. Maximum scaling, division, head update, reflector
normalization, checked products/subtractions, source-zero writes and signed
retention follow the existing operation order. For any successful QR of two
finite diagonal 2×2 blocks, retained off-diagonals decode exactly to zero; no
magnitude cap or symmetry repair is needed. This conditional structural result
does not assert success for rank-deficient or overflowing input.

`FloatObservableDiagonal` combines it with the existing input-derived stage
success/error theorems when the incoming factor is diagonal. The exact Real
Gram of each returned factor is the diagonal matrix of squared factor diagonal
entries. Prediction and innovation keep their previously proved bounds and
floors. This supplies the diagonal covariance interpretation required by the
Real sensitivity interface; the larger posterior and full-step proofs below
complete the native correction invariant and local joint-error δ.

The 1,200-case native prediction/innovation grid uses analytically representable
small-dyadic polynomial references, including `F=I`, sign reversal, zero
transitions, correlated incoming factors at the `13/8` energy boundary and
signed zeros. Its `10⁻¹²` tolerance supplements the proofs. A separate
independent high-precision full-horizon regression is recorded below, alongside
completed checked correction and full-step results. Original dense
initialization and the accumulated Float theorem are completed below.

## Larger diagonal gain: project bounds and source bridge

`FloatDiagonalSolve` and `FloatObservableGain` continue the same Tracy (2022)
§3, gain equations (29)–(30) and Algorithm 1. In the existing lower-factor
convention the native schedule forms HL, forms PHT as `L * transpose(HL)`,
solves against transposed PHT with the retained innovation factor, then
transposes the solution into K. Forward rows ascend, backward rows descend;
residual products and subtractions are individually checked before division.
No inverse is formed by the runtime. Its exceptional-value and pivot behavior
is unchanged; no symmetry repair or fused arithmetic is introduced.

The larger stored solve domain chooses diagonal factor entries at least one
and at most `9/4`, and RHS magnitudes at most four. These are project sufficient
conditions. Zero off-diagonal factor values make every residual cross-product
exactly zero, permitting correlated RHSs while deriving residual mass 16,
forward cap five and solution cap six. The completed solve error `2⁻³⁹` is
relative to the exact Gram of those stored factor words and exact decoded RHS.
The proof uses the pinned FLARE residual/division bounds, native/model bridge
and exact-zero arithmetic already recorded above, plus the actual native
substitution schedules. Exact diagonal RHSs produce exact decoded diagonal
solutions, with either sign of zero allowed. No new imported library bound or
native arithmetic assumption is added.

For the original local innovation domain and a diagonal prior, the existing
innovation QR floor `29/16` and factor cap `9/4` derive that solve domain.
Formed PHT is decoded diagonal, has entry cap `7/2` and error `2⁻⁴³` from
the prior's exact Gram. Keeping the actual four/three-row QR constants at
budget `25/8` bounds the complete innovation profile radius by `9·2⁻³²`.
The exact same-stored-prior gain is diagonal with entries `p/(p+r)` in
`[5/13,13/17]`. A preliminary native error bound `2⁻²⁴` derives gain cap
`13/16` and diagonal floor `3/8`; substituting that derived cap tightens the
final gain error to `2⁻²⁷`. All these are checked project bounds for the frozen
native operation order, not constants claimed from Tracy or first-order paper
analysis. Gain error includes both formed products, original-R factorization,
innovation QR and the solves; it does not include independently accumulated
prior-state error.

The public theorem derives profiles and successful stage executions from the
local stored conditions. It does not assume a desired intermediate run or
accuracy statement. Fifty-four larger diagonal solve cases and 600 scalar-gain
comparisons supplement it, including cap endpoints, correlated RHSs, signed
zeros and subnormal solve entries. Their `10⁻¹²` comparison tolerance is a
regression choice. Posterior correction, original initialization, accumulated
accuracy and rounded dense output are completed below.

## Larger diagonal mean correction: headroom and interpretation

`FloatObservableMean` analyzes the existing mean update from the recorded
Särkkä–Svensson (2023) §6.3, Theorem 6.6 (printed pp. 96–98), as encoded in
`Definitions/CovarianceRecursion.update`. It uses Tracy (2022) §3/Algorithm 1's
computed gain in the existing runtime order: Hx product, z−Hx subtraction,
gain/residual product, then addition to x. The weighted scalar form
`(1−k)x+kz` is used only for the mathematical headroom argument and independent
regression reference; the native program still evaluates residual/increment.
There is no fused multiply-add, changed association, symmetry repair or new
exceptional-value behavior.

Prior mean cap `19/16`, measurement cap one and returned mean cap `9/8` are
project sufficient conditions around the existing Real invariant. The reached
prediction mean cap is tightened to `19/16`: exact diagonal F with magnitude
at most one gives exact mean cap `9/8`, and the proved product error `2⁻⁴⁶`
fits that margin. The actual gain range `[3/8,13/16]` gives exact corrected
mean cap `143/128`; native evaluation error `2⁻⁴⁴` fits the remaining `1/128`
headroom below `9/8`. Product mass eight and sum exponent two derive every
mean-stage profile and successful run from the local input conditions.

The final error `2⁻²⁵` compares with the ideal correction from the same stored
prior's exact decoded mean/factor Gram and original H/R/z. Gain error `2⁻²⁷`
is multiplied by the exact residual cap `35/16`. A completed diagonal-support
propagation lemma avoids the generic inner-dimension multiplier; the combined
bound is `2⁻⁴⁴+(35/16)·2⁻²⁷ ≤ 2⁻²⁵`. The stored rounded residual instead has
the larger cap `19/8`. These constants are proved for the frozen native schedule,
not attributed to a paper. The same pinned FLARE multiply/add/subtract bounds
and binary64 native/model bridge are used; no new library assumption is added.

`prediction_correction_domain` derives the reached correction domain from
original prediction/observation inputs, a diagonal incoming factor and bounded
finite measurement. It supplies the mean handoff for later complete-step work.
The 270 stored-gain cases and 600 reached prediction/gain/mean cases use the
weighted scalar reference at tolerance `10⁻¹²`, distinct from the proved
allowances. Posterior QR, complete local correction, full-step composition and
the complete native invariant are proved below. Original dense initialization
and independent ideal-trajectory accumulated accuracy follow below, together
with the separate rounded dense positivity/accuracy certificate.

## Larger diagonal posterior correction: source and bounds

`Definitions/DiagonalObservation.josephVariance` is the full-observation scalar
specialization of Thornton–Bierman (1976), Eq. (8), printed p. 10, as already
encoded in `CovarianceRecursion.joseph`. `RealObservablePosterior` proves
`J(p,r,k)=pr/(p+r)+(p+r)(k−p/(p+r))²` directly from that specification, including
the complete quadratic remainder. This is attributed project algebra, not a
new paper theorem or a quoted numerical constant.

`FloatObservablePosterior` analyzes the frozen runtime's factored Joseph
prearray `[(I−KH)L, KTR]`, corresponding to Tracy (2022), §3, Eq. (36), and
Algorithm 1, pp. 2–4. Its native order is KH multiplication, identity subtraction,
WL multiplication, KTR multiplication, concatenation, scaled Householder QR
and signed retention. It uses the existing original-R Cholesky and computed
gain; no reassociation, FMA, symmetry repair or exception behavior is changed.

Reached prior variances `[15/16,13/4]` and original R diagonals `[1,3/2]` yield
ideal posterior interval `[15/31,39/38]`. Gain error `2⁻²⁷` contributes at most
`2⁻⁵⁰` to exact Joseph covariance. Rounded prearray arithmetic has allowance
`2⁻³⁸` at the same stored gain/noise factor; including original-R factorization
and gain error gives `2⁻³⁶`. Derived rounded-prearray floor `15/32` and cap
`17/16` establish QR's initial domain at project budget `15/8`.
The actual four/three-row QR radius plus that allowance is capped at `2⁻²⁹`.
These are completed project bounds for this exact implementation/domain;
no sharpness or equivalence with literature's asymptotic constants is claimed.

The public local correction theorem derives native `updateUnchecked` success
and returned validation, covariance/mean errors `2⁻²⁹` / `2⁻²⁵` against the
ideal correction from the same stored prior and original H/R/z, exact diagonal
strict-PD covariance floor `7/16`, diagonal cap `17/16`, and factor/mean caps
`9/8`. Covariance means exact Real multiplication of the returned native factor.
Rounded dense output requires a separate theorem. The full-step joint δ is
proved below, together with original dense initialization, error against an
independent ideal trajectory and the separate rounded dense output result.

The proof reuses the recorded pinned FLARE nearest arithmetic/native-model
bridge, Cholesky bounds, zero arithmetic and QR/solve lemmas. The new native
subtraction lemma permits either signed-zero encoding. All conclusions are
kernel-checked without project axioms. Six hundred reached diagonal cases now
exercise complete correction and the scalar covariance reference; 216 local
boundary cases exercise variance/mean headroom and signed-zero/subnormal means.
Their `10⁻¹²` tolerance supplements the proof and is not its error allowance.

## Larger diagonal complete step: exact propagation and scope

`RealObservableCorrection` specializes the existing Särkkä–Svensson (2023)
Theorem 6.6 prediction/correction equations to diagonal priors and full
observation, permitting arbitrary unused F/Q during local correction. It proves
exact variance/mean differences including gain changes. Prior variance floor
`15/16`, R diagonals `[1,3/2]` and ideal predicted mean cap `9/8` are project
slack around the stored and exact prediction domains. Their sufficient
propagation coefficients `2/5` and `8/13,17/30` are completed project algebra,
not literature constants or first-order estimates.

`FloatObservablePrediction.prediction_accuracy_sharp` retains the actual
four/three-row QR constants at budget `21/8`, plus rounded FL and original-Q
Cholesky error, to give covariance cap `7·2⁻³²`. The sharp mean/correction APIs
retain stored-gain evaluation and gain discrepancy, giving `9·2⁻²⁹` mean
allowance. Older wider public allowances remain valid.

`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy` owns the static
original-input domain and retained native state invariant.
`FloatObservableFilter.step_accuracy_and_invariant` composes the frozen
prediction/innovation/solve/mean/factored-Joseph schedule without runtime changes. It
derives checked execution, all validators, local covariance/mean errors `3·2⁻³⁰` /
`5·2⁻²⁸` and joint δ=`5·2⁻²⁸` against the ideal full step from the same incoming stored
factor Gram/mean and original input words. The fixed-dimension ghost view changes metadata
only; its equality to the original native metadata is proved from the model domain.

Returned factor/mean bounds derive the native invariant for subsequent steps.
The actual trace driver succeeds at every finite prefix and retains decoded
diagonality and exact covariance floor `7/16`. Nonzero identity dynamics,
full observation and signed nonzero mean/measurements inhabit the domain.
These are completed kernel proofs. Original dense initialization is completed
below, followed by the independent Real trajectory comparison and the separate
rounded dense positivity/accuracy argument.

Six hundred reached diagonal grid cases now exercise public checked full steps.
A separate 256-step near-identity dyadic fixture includes changing Q/R endpoints,
identity/sign-reversing dynamics and alternating measurements. Seven independent
ideal scalar checkpoints generated at 120/160 decimal digits have identical
rounded references; native validation and retained caps are checked at all 257
prefixes, with exact final driver word agreement. The `10⁻¹²` comparison tolerance
is an executable regression choice, separate from proved local δ. No imported
floating-point library, arithmetic-model assumption or runtime schedule changed.

## Larger diagonal dense initialization: original comparator

`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.InitializationDomain`
specifies original dense `Input.State` words, with diagonal variances `[1,3/2]` and finite
mean magnitudes at most one. This is a sufficient native subset of the independently
proved Real initial interval `[1/2,3/2]`, rather than a change of covariance
representation or input owner. `FloatObservableInitialization` derives the checked
initializer and every validator, retained decoded diagonality, positive factor, native
invariant, initial covariance error `2⁻⁴²` and exactly zero mean error. The comparator
remains the original decoded covariance; the rounded Cholesky Gram never replaces it. The
existing pinned FLARE native/model bridge and recorded Cholesky backward bound are reused
without new assumptions or arithmetic changes. A 162-case initialization/first-step
regression supplements the proof.

## Larger diagonal accumulated accuracy: independent original-input trace

`RealObservableHorizon` identifies the stored full-observation diagonal model
with the previously attributed source specification at fixed dimensions.
`FloatObservableHorizon` then composes original dense initialization, actual
native steps and exact full-step sensitivity against one independently
propagated Real matrix trajectory. Every finite prefix succeeds and covariance/
mean errors stay at most `5·2⁻³⁰` / `2⁻²⁴`. Original initial variances remain
`[1,3/2]`; the wider Real half-to-one initial interval is not instantiated here.

The project-derived sufficient budgets use covariance coefficient `9/25` and
mean coefficients `3/5,1/2`, charging local errors `3·2⁻³⁰` / `5·2⁻²⁸` and
initial error `2⁻⁴²` / zero. No term is discarded and these are not constants
copied from a paper or a novelty claim about Kalman stability. Identity and
native `diag(1023/1024,−1)` models inhabit the domain for every finite horizon.
The existing high-precision regression now includes original dense variances
`5/4,3/2` and their rounded Cholesky initialization. The native/model bridge
and frozen runtime schedule are unchanged. The separately rounded dense output
certificate follows.

## Larger diagonal rounded dense output: separate spectral certificate

`FloatObservableDenseOutput` composes the complete original-input observable
horizon and actual checked dense multiplication. The retained factor Gram's
`7/16` floor, two-state entrywise conversion radius `2⁻⁴⁸` and exact native
symmetry imply rounded dense floor `7/16 − 2⁻⁴⁷ ≥ 3/8`. Covariance error against
the same independent original-input ideal trajectory is `5·2⁻³⁰ + 2⁻⁴⁸`; mean
error stays `2⁻²⁴` because mean words are copied. These are completed sufficient
project constants, separate from paper asymptotics and from Gram positivity.

The frozen multiplication schedule and existing FLARE bridge are reused. The
reusable materialization proof needs factor validation and covariance diagonal
cap two, with no mean cap, and preserves the earlier invariant APIs. Exact
off-diagonal word agreement supplies Hermitian decoding without symmetry repair.
A 108-case larger-mean/signed-zero grid and dense floor checks at all 257
near-identity regression prefixes supplement the kernel proofs. The complete
initialized fully observed diagonal native filter milestone is now closed.

### Optional Joseph uncertainty allowance

Project adaptation: `Implementation/UncertaintyInflation` offers one checked
binary64 addition of exactly `2^-29`. It is observational and does not alter
the filter recurrence. The completed diagonal Joseph covariance radius is
`2^-30`; the extra margin covers the allowance addition's own `2^-51` error.
`Definitions/Theorems/UncertaintyBounds` states deterministic covariance order
and ideal interval coverage; its proofs and the original-input horizon bridge
are in `Proofs/UncertaintyBounds` and `Proofs/FloatJosephUncertainty`. Statistical
coverage remains a caller premise. Square roots and interval endpoints in the
transfer theorem are exact Real operations, not an executable interval API.

### Matrix Joseph gain perturbation

`Definitions/Theorems/JosephGainSensitivity` specifies exact completion of the
square and its semidefinite-order consequence. `Proofs/JosephGainSensitivity`
proves both for arbitrary dimensions from the already established innovation
invertibility and stationarity identities. Its entrywise quadratic allowance
is `m^2 * Smax * epsilon^2`. It compares two exact Joseph evaluations with the
same original prior/noise/observation and the exact optimal gain as reference;
it does not absorb native evaluation error or imply native conservatism.

### Position-only Joseph correction envelope

Project specialization of the existing linear observation/update equations:
two state components (position and velocity), one observation, and original
observation storage exactly `[1, 0]`. `Definitions/Theorems/JosephPositionCorrection`
records the position row, exact symmetric-part interpretation, and an exact
quantitative Joseph floor. The original stored prior can be correlated.
`Implementation/Correctness/JosephPositionCorrection` states the normalized
original-input envelope and the complete checked local guarantee. The prior
floor is an original mathematical premise; model validation only supplies the
existing storage/finite/noise-symmetry checks and assumes no filter execution.

`Proofs/FloatJosephPositionArithmetic`, `FloatJosephPositionGain`,
`FloatJosephPositionKernel`, `FloatJosephPositionMean`, and
`FloatJosephPositionCorrection` discharge all actual rectangular native
arithmetic stages. The scalar innovation uses the existing unchanged LDL
solver. There is no new gain algorithm or covariance symmetry repair. Its
comparator uses the optimal exact gain from the same original finite words.
The output's exact symmetric part has a certified floor, while raw output
asymmetry is bounded separately. This interpretation does not claim exact
stored symmetry. The theorem is local, with explicit conditioning/scale bounds;
no physically calibrated sensor or prediction/horizon extension is implied.

### Optional stored symmetry for the position-only Joseph correction

`Implementation/SymmetricJosephFilter.update` is an opt-in wrapper around the
checked Joseph correction. After successful correction it copies lower-triangle
covariance words to the upper triangle using the pinned FLARE `mirrorLower`
kernel. It performs no additional arithmetic, preserves all mean and diagonal
words, and propagates correction errors. This project storage choice is separate
from the attributed Joseph equations and leaves the original runtime unchanged.

`Proofs/FloatSymmetricJosephCorrection.mirror_accuracy` lifts FLARE's
`MatrixFormation.mirrorLower_accuracy` to state comparisons in any dimension.
Against a Hermitian exact reference it preserves both componentwise radii.
`update_accuracy` instantiates the complete original-input correlated-prior
correction theorem: mean/covariance errors remain `2^-28`, and the repaired
stored covariance is Hermitian with floor `1/8`, hence positive definite.
The positivity proof pays for entrywise error from the exact Joseph `1/4`
floor; it does not treat mirroring as a general positivity repair.

All 72 independent original-word position-correction references also exercise
the wrapper. Regressions check exact copied words, signed zero, positive stored
determinants, shape rejection and nonpositive-innovation rejection. This result
remains a local correction certificate; coupled prediction and domain closure
require separate results.

### Coupled constant-velocity prediction

`Definitions/Theorems/ConstantVelocity.transition` specializes the attributed
linear prediction to `[[1, dt], [0, 1]]`. This is a project model choice, not a
new source equation. `Implementation/Correctness/ConstantVelocityPrediction`
records an original-word envelope: finite `|dt| <= 1`, covariance/process entry
caps two, mean cap one, PSD prior/process covariance, and ordinary validation.
`Proofs/FloatConstantVelocityPrediction.prediction_stages` derives every actual
dense product, addition and guard. Covariance/mean local error radii are
`2^-36` / `2^-41` against the exact prediction of those same input words.

`SymmetricJosephFilter.predict` repairs the prediction storage too;
`predict_accuracy` proves finiteness, shape, Hermitian decoding, and unchanged
radii. The runtime `step` composes repaired prediction and correction, and
`run` propagates the first checked error. These executable drivers do not yet
claim domain closure merely from their existence. Thirty-six independent
Fraction references cover three nonzero time increments, correlated priors,
two process-noise scales and two initial means. As with the correction, the
normalized bounds are sufficient project constants, not physical sensor units.

### Closed coupled tracking envelope

The first closed position-only tracking family fixes `dt = 1/4`,
`Q = diag(5/16, 1/8)`, `R = 1`, and the correlated initial covariance
`[[1/2, 1/4], [1/4, 1]]`. Exact prediction gives
`[[1, 1/2], [1/2, 9/8]]`; correction has gain `[1/2, 1/4]` and returns the
initial covariance. `Definitions/Theorems/ConstantVelocityTracking` records
these project choices. `Proofs/ConstantVelocityTracking` proves this cycle from
the source equations and proves weighted mean nonexpansiveness: position error
radius `r` and velocity error radius `4*r` are preserved by an exact full step.

`Proofs/FloatConstantVelocityStorage` proves exact original-word decoding and
the same covariance/gain cycle through the actual binary64 dense kernels and
scalar LDL solve, by kernel reduction. It introduces no native evaluation axiom.
`FloatConstantVelocityTracking` combines these results with the general local
prediction and mean-error proofs. The complete checked step succeeds from the
original envelope and has weighted local mean radius `2^-36` and zero covariance
error in this family. Prediction itself derives every premise of the existing
correlated position-correction domain, including the prior `1/2` floor.

With original measurements bounded by `2^-24`, the envelope
`1/8 + t*(2^-25 + 2^-36)` is preserved up to `t = 2^20` and stays below `3/16`.
Its stored posterior covariance has floor `1/4`; means and measurements may
vary. The original envelope is proved nonempty. These are completed local and
domain-preservation results. This is a stationary-covariance family, not a
certificate for arbitrary correlated initial covariances or arbitrary sensor
scales. A 1,024-step varying-measurement regression checks all covariance-word
prefixes and nine independently propagated Fraction references. The original-
input accumulated horizon comparison is a separate result.
