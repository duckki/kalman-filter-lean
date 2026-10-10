# Research roadmap and milestone history

Internal background and planning history. The research baseline and milestone
dates below are historical; proposed directions are ideas, not a committed
research agenda. Current public claims live in [results.md](../results.md).
Working instructions live in [AGENTS.md](../../AGENTS.md).

Status: **2026-10-06**. The adopted implementation direction has produced
complete conditional step and finite-horizon accuracy proofs, an explicit
two-state budget, a fully discharged reset-model domain, and an original-input nontrivial
execution/PD invariant and full accumulated accuracy from original inputs. The remaining
research directions below are proposals. See [results.md](../results.md)
for the exact scope of completed claims.

## What is already known on paper

Verhaegen and Van Dooren (1986), *Numerical Aspects of Different Kalman Filter
Implementations*, IEEE TAC 31(10), 907–917, DOI
[10.1109/TAC.1986.1104128](https://doi.org/10.1109/TAC.1986.1104128), give local
error bounds in Theorem 1 and accumulation recurrences (57)–(59). Their §III
analysis is first order; the discussion on printed p. 912 warns that improved
covariance accuracy need not improve gain or state accuracy
([author PDF](https://perso.uclouvain.be/paul.vandooren/publications/VerhaegenV86.pdf)).

Tracy (2022), *A Square-Root Kalman Filter Using Only QR Decompositions*,
[arXiv:2208.06452v1](https://arxiv.org/pdf/2208.06452v1), §3 and Algorithm 1,
derives the QR/factored-Joseph stages used here. It does not certify our scaled
Householder program's binary64 error or rejection behavior.

Bougerol (1993), *Kalman Filtering with Random Coefficients and Contractions*,
SIAM J. Control Optim. 31(4), 942–959, DOI
[10.1137/0331041](https://doi.org/10.1137/0331041), §1.2, Theorem 1.7, provides
Riemannian-metric contraction results for exact Riccati maps, with additional
conditions governing strict contraction
([paper](https://www.cmap.polytechnique.fr/~gaubert/COURSM2/DENJOY/FURTHERREADING/BougerolKalmanFilteringRandomCoeffsContractions.pdf)).

These are foundations to formalize or extend. Calling positivity, QR stability,
or contraction itself a new result would misstate the contribution. The
[prior formalization review](../references/prior-formalizations.md) also documents
exact matrix theory, scalar roundoff proofs, C filter and matrix functional
proofs, and finite-model verification. Its 2026-10-09 Pollard/Elaenia follow-up
distinguishes those C proofs and local error-analysis lemmas from accumulated
filter accuracy and positivity. The inspected sources do not supply the full
certificate for our selected implementation; this is not an exhaustive
novelty or priority claim.

## Completed principal goal: derive the full domain from original inputs

### Implementation roadmap and acceptance criteria

Keep this table current at each completed slice and commit the proof and its
scope documentation together. Items marked planned are not completed theorems.

| Slice | Status | Acceptance criterion |
| --- | --- | --- |
| Original-input initialization | Complete (`798dbfa`) | Two-state correlated covariance inputs derive native Cholesky success, factor structure and backward error `≤ 2⁻⁴²`. |
| Stored-input triangular solves | Complete (`a8506c8`) | Factor/RHS bounds derive both substitution passes and their profiles; Cholesky plus solve has error `≤ 2⁻³⁷` against original `A⁻¹B`. |
| QR factor to innovation solve | Complete (`664088f`) | Native QR output derives the solve factor domain. Cholesky noise derives prearray floor `2/3`, leaving innovation Gram floor `1/2` after QR error. Composed solve error is `≤ 2⁻³⁷` against the retained Gram and `≤ 2⁻²⁰` against the original prearray Gram; energy/RHS bounds remain explicit. |
| Formed RHS and gain | Complete (`ccc62dc`) | Stored observation/factor bounds derive both rounded products and a transposed RHS inside `1/8`. A stored covariance bound `2` and observation cap `1/64` leave rounding headroom; actual gain magnitude `≤ 1/3` and the existing gain profile are derived. |
| Innovation prearray/profile | Complete (`b0f6dca`) | Original noise diagonals capped by `3/2` leave row-energy room for the rounded observation block. Every innovation and gain profile is derived from a stored local stage domain, with accuracy against original noise and the stored prior covariance. |
| Mean correction/profile | Complete (`3f6a022`) | Predicted mean cap `1/16`, measurement cap `1` and derived gain cap `1/3` imply all four native mean operations/profiles, finite output bounded by `1`, evaluation error `≤ 2⁻⁴⁵` at the stored gain, and error `≤ 2⁻²⁵` against the ideal local correction including gain error. |
| Prediction/profile and correction handoff | Complete (`eadb5f1`) | Original process-noise diagonals in `[1,3/2]`, transition cap `1/64` and incoming mean cap `1` derive all prediction profiles, successful validated output, covariance error `≤ 2⁻²⁵` and mean error `≤ 2⁻⁴⁶`. Returned mean cap `1/16`, factor entry cap `2`, covariance entry cap `7/4` and floor `2/3` establish the local correction domain. |
| Posterior/profile and returned-state bounds | Complete (`0a180ff`) | Derive all remaining correction profiles, rounded prearray floor `1/2` and diagonal cap `63/32`, native success and both local ideal-correction errors `≤ 2⁻²⁵`. Returned PD exact covariance/factor entries are bounded by `2` and mean by `1`. |
| One complete input-derived step | Complete (`e9d1afd`) | Derive every validation, stage profile and exact reference environment; checked `step` succeeds with covariance/mean error `≤ 2⁻²⁵` against the exact full step from the incoming stored state and preserves returned bounds. |
| Nontrivial invariant family | Complete (`e9d1afd`) | Original dense initialization derives the retained-state invariant with covariance error `≤ 2⁻⁴²` and zero mean error. All finite prefixes succeed and preserve bounded PD exact covariance, including time-varying correlated Q/R. A nonzero/correlated dense-input witness is proved. |
| Independent ideal trajectory invariant | Complete (`51bfc8a`) | Original dense inputs derive PD exact covariance and covariance/mean caps `2`/`1` at all finite prefixes. Every reference environment is derived with floor `3/4`, predicted covariance cap `7/4`, noise cap `3/2` and residual cap `2`; no native error premise. |
| Complete input-derived horizon accuracy | Complete (`329e2a4`) | Original dense initialization and original time-varying model bounds derive all native profiles and ideal environments. Both accumulated errors `≤ 2⁻²⁵`, successful execution, native/ideal PD covariance and the stored invariant hold at every finite prefix, including correlated Q/R. |
| Mean headroom for stronger dynamics | Complete (`dd0e8d7`) | The local correction admits predicted mean cap `9/32` while preserving stored output cap `1`, evaluation error `2⁻⁴⁵` and ideal local error `2⁻²⁵`. Recomputed projected/residual/increment caps are `1/64`, `33/32`, `45/64`. |
| Broader stable dynamics | Complete (`b8a5d4f`) | Transition entry cap `1/8`, H cap `1/64`. Covariance-aware FL energy derives native QR margins; predicted mean cap `9/32`, native/ideal invariants, every profile and uniform covariance/mean error `2⁻²⁵` are proved. The propagation uses the actual H cap `1/64`; a signed transition-boundary witness is proved. |
| Dense conversion success, symmetry and error | Complete (`37cdf61`) | Retained two-state invariant derives materialization success, error `≤ 2⁻⁴⁸`, unchanged mean words and exact off-diagonal word agreement without repair, including underflow. |
| Dense output over the original-input horizon | Complete (`2e6ce6f`) | Initialization/QR derive retained floor `1/4` at every prefix. Same original-input horizon domain gives finite exactly symmetric dense output with floor `1/4 − 2⁻⁴⁷ > 0`, accumulated covariance error `≤ 2⁻²⁵ + 2⁻⁴⁸` and mean error `≤ 2⁻²⁵`. |
| Observable Real invariant | Complete (`3cca098`) | `H=I`, diagonal F with entries up to magnitude `1`, diagonal Q/R in `[1,3/2]`, initial variance in `[1/2,3/2]`, and bounded mean/measurements. Scalar formulas agree with every matrix covariance form. Prediction variance `[1,3]`, corrected variance `[1/2,1]`, mean cap `1`; every prefix has PD floor `1/2`. Real proofs cover arbitrary finite dimension; an identity-F witness is proved. |
| Observable correction and joint sensitivity | Complete (`afdce8e`) | Full matrix-step covariance/mean error coefficients `9/25` and `3/5,1/2`, including gain changes. Covariance weighted by two gives joint contraction `17/20` and geometric forgetting for exact time-varying trajectories. A supplied local joint error `δ` closes uniform budget `(20/3)δ`; no native full-step δ is proved here. |
| Native diagonal multiplication and Cholesky | Complete (`9e7aab2`) | Actual finite two-state multiplication and Cholesky preserve decoded off-diagonal zero in their domains, including either signed-zero word. |
| Observable native prediction and innovation | Complete (`9e7aab2`) | Local stored-domain diagonal `|f|≤1` derives prediction profiles/success, covariance/mean errors `2⁻²⁴` / `2⁻⁴⁶`, covariance floor `15/16` and reached full-observation innovation domain. HL/R/innovation QR then derive success, original-R-plus-stored-P error `2⁻²³`, floor `29/16`, factor cap `9/4`. Native identity inputs inhabit the domain. |
| Observable returned QR diagonal structure | Complete (`a0123d0`) | Successful native QR of two finite diagonal 2×2 blocks preserves decoded diagonality without a magnitude cap. Original local domains and a diagonal incoming factor derive successful diagonal prediction/innovation with the existing bounds; exact Real Grams are diagonal matrices of squared factor diagonals. Signed zeros are permitted; 12 scale cases supplement the proof. |
| Observable gain products and solve | Complete (`61e3530`) | Stored diagonal factors with diagonals ≥1 and entry cap `9/4`, and RHS entry cap four derive both solve passes and error `2⁻³⁹` against the stored Gram. The original local innovation domain plus diagonal prior derives every gain profile and actual gain solve, formed PHT cap `7/2` and error `2⁻⁴³`, decoded diagonal gain with entries `[3/8,13/16]`, and error `2⁻²⁷` against the ideal gain of the same stored prior and original H/R. Innovation profile radius is tightened to `9·2⁻³²`. No stage run or desired error is an input premise. |
| Observable mean correction and headroom | Complete (`03bc020`) | Tighten reached prediction mean cap to `19/16`. Original local innovation/diagonal/vector inputs derive gain and every mean profile/run; evaluation error at the stored gain `2⁻⁴⁴`, ideal local correction error `2⁻²⁵`, returned mean cap `9/8`. Exact diagonal support removes the inner-dimension factor in gain-error propagation; the original prediction domain and bounded measurement derive the reached correction domain. |
| Observable posterior correction | Complete (`4f5d34c`) | Original local innovation/diagonal/vector inputs derive complete measurement correction and returned validation. Exact quadratic Joseph gain identity gives gain contribution `2⁻⁵⁰`; posterior covariance/mean errors `2⁻²⁹` / `2⁻²⁵`. Derived prearray QR budget `15/8`, decoded diagonal returned factor, strict-PD covariance floor `7/16`, diagonal cap `17/16` and factor/mean caps `9/8`. No stage run or desired error is an original input premise. |
| Observable complete step and native invariant | Complete (`8ebf6c1`) | Original model and stored-state bounds derive all validation/stages, checked step success, covariance/mean error `3·2⁻³⁰` / `5·2⁻²⁸` against the ideal full step from the same incoming state, joint δ=`5·2⁻²⁸`, and returned invariant. Sharp prediction cap `7·2⁻³²` and correction mean cap `9·2⁻²⁹` leave composition headroom. Every finite native prefix succeeds and stays diagonal/strictly PD with floor `7/16`; a nonzero identity-dynamics inhabitant is proved. |
| Observable dense initialization | Complete (`406a2fa`) | Original finite decoded diagonal covariance entries `[1,3/2]` and finite mean magnitudes at most one derive checked initialization, native invariant, initial covariance/mean error `2⁻⁴²` / zero, and independent Real initial invariant. The comparator is the original covariance words. |
| Observable accumulated accuracy | Complete (`d7a8a86`) | Original dense initialization and time-varying models alone derive native success, invariant and covariance/mean errors `5·2⁻³⁰` / `2⁻²⁴` against one independent ideal trajectory at every finite prefix. Exact covariance/mean coefficients `9/25` and `3/5,1/2` close separate budgets. Identity and near-identity/sign-reversal witnesses are proved; the 256-step high-precision regression now includes nonexact-square-root original initialization. |
| Observable rounded dense output | Complete (`FloatObservableDenseOutput`) | Original horizon inputs derive every dense prefix: success, finite validation, exact off-diagonal word agreement, copied mean words, covariance/mean errors `5·2⁻³⁰ + 2⁻⁴⁸` / `2⁻²⁴`, and strict-PD floor `7/16 − 2⁻⁴⁷ ≥ 3/8`. Materialization uses only factor validity and covariance diagonal cap; the larger mean cap is covered. |
| Broader practical domains | Planned | Extend dimensions/noise scales, derive scale-dependent bounds, and consider runtime certificates with verified bound-calculation arithmetic. |

Latest slice validation: full `lake build` (3,510 jobs), all 1,189 project-theorem axiom checks,
the complete native regression suite (including 216 stored-gain mean cases and
324 original-noise mean corrections and 648 original-input predictions with
correction handoff, 324 posterior prearray/QR/Joseph cases and 2,592 checked
steps with time-varying correlated Q/R, and a 256-step correlated horizon with
seven independent reference checkpoints reproduced at 120/160 decimal digits,
dense symmetry/mean-word/eighth-floor checks at all 257 prefixes, and six dense
scale/correlation/signed-zero cases, plus 1,200 larger-dynamics native
prediction/innovation cases (including 600 independent scalar-gain/mean/posterior and full-step comparisons),
270 stored diagonal gain mean cases, 216 local posterior/mean boundary cases,
162 original dense initialization and first-step cases, 108 larger-mean-cap
dense materialization cases,
a 256-step near-identity diagonal horizon with seven independent 120/160-digit
checkpoints and retained invariant checks at all 257 prefixes, 54 larger diagonal
solve cases and 12 diagonal QR scale cases from the smallest
subnormal to `10³⁰⁰`, plus rank rejection), the analytic fully observed two-state
exact check across all covariance forms, formatter checks and 199 local
documentation links/anchors pass.
No runtime arithmetic or sibling-project source changes are part of these slices.

The earlier `UniformStepParameters` fix decoded measurement noise `R ⪰ I`
and `|Rᵢⱼ| ≤ 1`, forcing symmetric R to identity. The new original-input coefficient
check uses floor `3/4` and R cap `3/2`, and closes the same `2⁻²⁵` tolerance with
correlated measurement noise. This broader accuracy condition is now proved.

The principal original-input deliverable is complete: initialization, every
reached native profile, the independent ideal reference bounds and accumulated
uniform errors are derived for the documented nonzero two-state family. Both
exact covariances stay PD at every finite prefix. Optional rounded dense output
now also succeeds, is exactly symmetric without repair and has a separately
derived floor `1/4 − 2⁻⁴⁷`. Its extra entrywise error is only `2⁻⁴⁸`.

The posterior slice is complete. Prediction supplies the reached input domain;
ideal gain cap `7/48` plus gain error `2⁻²⁰` gives stored gain cap `1/6`.
The sharper row-mass estimate closes QR energy/rank headroom without an
optimal-gain contraction identity. Returned mean/factor/covariance caps `1`,
`2`, `2` now supply the next prediction's numerical assumptions.

Checked-step success, invariant preservation and accumulated ideal-trajectory
accuracy are complete. The two uniform errors remain `≤ 2⁻²⁵` for arbitrary
finite horizon from original dense initialization. The full accuracy domain
has a nonzero transition and correlated Q/R/initial-covariance witness.

The stronger transition slice is complete: F entries may reach `1/8`, eight
times the preceding original-input cap. Rounded FL Gram energy is derived from
the covariance identity rather than loose individual factor products. Predicted
mean cap `9/32` fits the enlarged correction domain. Exact reference prediction
has mean cap `1/4`, and correction returns at most `5/6`. All native profiles,
native/ideal invariants and the same accumulated `2⁻²⁵` errors are proved.
Tightening the propagation's H allowance from `1/32` to the actual original
cap `1/64` closes those coefficients without changing the runtime algorithm.

The dense-output slice is complete: all its success, symmetry, accuracy and
positivity conditions follow from the original-input horizon domain. The
existing tiny-factor underflow witness still refutes unconditional dense PD
outside this family. The full-observation Real invariant is now proved, with
diagonal transition magnitudes up to one, including identity. Its scalar
specialization agrees with the existing matrix recursion; no new native format
or algorithm is introduced. The coupled correction contraction is now proved:
covariance error coefficient `9/25`, mean coefficients `3/5,1/2`, and a
joint coefficient `17/20` with covariance weighted by two. This includes exact
gain changes. It gives geometric forgetting for exact trajectories and a
conditional uniform roundoff interface `(20/3)δ` once a native local allowance
δ is proved. Native prediction and innovation now meet their larger budgets:
`21/8` and `25/8`, with retained floors `15/16` and `29/16`. Their original
local stored domains derive all stage runs and numerical conditions. The new
1,200-case regression grid checks identity/sign-reversing/reset dynamics,
correlations and signed-zero inputs. These remain local stage results.
Returned QR diagonal preservation is now proved for two finite diagonal blocks,
including signed zeros, with no magnitude cap on successful runs. Prediction
and innovation inherit exact diagonal factor/Real covariance structure from
diagonal incoming factors. Twelve independent scaled 3-4-5 cases exercise
subnormal, tiny, unit and huge inputs. Larger gain solves and mean profiles
are now derived, with gain error `2⁻²⁷`, mean correction error `2⁻²⁵` and returned
mean cap `9/8`. Posterior correction is now complete: the exact Joseph gain
perturbation is quadratic, all native posterior stages/QR succeed, covariance
error is `2⁻²⁹`, and returned diagonal covariance has floor `7/16` and cap
`17/16`. Factor and mean caps `9/8` fit the next prediction domain. Complete
checked steps now preserve that native invariant, with covariance/mean bounds
`3·2⁻³⁰` / `5·2⁻²⁸` and joint δ=`5·2⁻²⁸` against the same-state ideal full step.
Every finite native prefix succeeds and retains strict-PD covariance. Original
dense initialization now derives that invariant and covariance/mean errors
`2⁻⁴²` / zero for initial diagonal variances `[1,3/2]` and mean cap one.
The independent Real matrix trace and the actual native driver are now connected
by `FloatObservableHorizon.initialized_horizon_accuracy`: covariance/mean
errors `5·2⁻³⁰` / `2⁻²⁴` stay uniform at every finite prefix. Separate component
budgets use the stronger covariance contraction instead of widening both to
`(20/3)δ`. Identity and near-identity/sign-reversing original models inhabit
this horizon domain. Rounded dense output is now complete, with covariance
error `5·2⁻³⁰ + 2⁻⁴⁸`, exact symmetry and strict-PD floor
`7/16 − 2⁻⁴⁷ ≥ 3/8`. The initialized fully observed diagonal filter milestone
is closed; broader dimensions, noise scales and correlated near-identity
dynamics require new bounds.
Correlations and broader dimensions/scales can follow after this first observable
family. See [the exact contraction and conditional scope](../results.md#fully-observed-diagonal-real-sensitivity).

The QR supporting milestone is now complete on an explicit eight-row initial
domain: `OrthogonalFactorization.gramFactor` succeeds and meets a Gram bound
following the actual scaled norms, reflectors, signs, zero writes, diagonal
rescaling and rounding order. Classical QR analysis guides this work; applying
it to this precise program is a formal software contribution. Prediction
prearray rounding for $[\widehat{FL}\;T_Q]$, its QR composition and the discrepancy
from ideal prior/noise covariances are now proved under explicit profiles.
Innovation, gain, posterior and mean propagation complete the full step.

The first supporting slice is now complete: maximum-scaled column-norm success
and error for at most 32 finite active entries, including normalized-component
underflow. It also proves the stored vector's values and preserves the original
execution schedule. The second slice now proves Householder construction and
normalization success, first-subtraction error, and finite near-unit output.
Its local operand conditions are derived from the preceding norm stage, for
distinct valid active indices. The third slice now proves one-column application
success, error relative to the same stored vector, and composition with the
preceding construction error under a target-column scale budget. The fourth
slice now proves source-column finishing: finite nonzero rescaled diagonal,
squared-norm accuracy, and a bound for intentional zero writes compared with the
same stored reflector's action. It derives the needed profile from original
source entries with scale in $[2^{-900},2^{900}]$. The fifth slice now composes
one full iteration, including column independence, copied prefixes, and an
error bound against an exactly unit stored-constructed-vector reference. The
sixth slice now proves exact retained-factor sign/copy conversion and positive
exact Gram from finite stored entries and nonzero diagonals, with no magnitude
or dimension cap. The seventh slice now proves the triangular-zero invariant
through the complete successful loop and identifies the retained Gram with the
full stored QR result's column Gram. The eighth slice bounds each complete
iteration's exact column-Gram change against its incoming stored matrix using
that invariant and the existing local profile. The ninth slice sums those
allowances over the actual pivot loop, propagates nonzero diagonals, and derives
success and strict-PD exact output Gram with error against the original stored
prearray. The tenth slice derives prefix entry bounds and remaining spectral
margins from initial column energy/rank bounds and the errors of preceding
pivots, with a concrete sufficient headroom choice for up to eight rows.
The eleventh slice now turns the remaining rank margin and prior triangular
structure into the active source-tail witness, with $M\ge2^{-896}$ meeting the
kernel's floor. The twelfth slice closes the prefix-profile induction and exports
the full initial-input factor result: $n\le d\le8$, $2^{-896}\le M\le2^{900}$,
row energy $\le M^2/2$ and Gram floor $M^2/8$ imply success, output floor
$M^2/16$, and entrywise Gram error $\le M^2/128$.
See [the proved local bound](proof-development.md#first-native-qr-slice-the-scaled-column-norm).
The [reflector bound](proof-development.md#second-native-qr-slice-reflector-construction-and-normalization)
uses the exactly decoded stored constructed vector as its normalization reference.
The [application bound](proof-development.md#third-native-qr-slice-application-to-one-column)
also uses that reference for its three-stage comparison.
The [source-column finishing bound](proof-development.md#fourth-native-qr-slice-source-column-zeros-and-diagonal-rescaling)
accounts for intentional zero writes, rather than assuming exact annihilation.
The [full-iteration bound](proof-development.md#fifth-native-qr-slice-one-complete-iteration)
derives all stages' success from the iteration input and makes its original-matrix
reference explicit. The initial-input result below establishes the profile
invariant across pivots in its stated domain.

The [retention result](proof-development.md#sixth-native-qr-slice-exact-retained-factor-conversion)
adds zero conversion error relative to the stored upper block. The
[whole-loop structural result](proof-development.md#seventh-native-qr-slice-whole-loop-triangular-structure)
now identifies that block's Gram with the full tall stored result's column Gram,
conditional on successful execution. The
[one-iteration Gram result](proof-development.md#eighth-native-qr-slice-one-iteration-column-gram-error)
provides the local numerical allowance. The
[complete factor result](proof-development.md#ninth-native-qr-slice-complete-factor-gram-error)
now sums it and connects the retained factor to the original prearray, under
explicit operand profiles at every actual prefix. The
[prefix enclosure](proof-development.md#tenth-native-qr-slice-prefix-magnitude-and-spectral-margins)
now derives magnitudes and remaining rank margins without assuming future
profiles. The [source-tail witness](proof-development.md#eleventh-native-qr-slice-the-active-source-tail-witness)
now turns that margin and triangular structure into a sufficiently large
source entry. The [initial-input result](../results.md#initial-input-qr-success-and-error)
assembles all next-pivot conditions and closes that induction. No intermediate
profile, successful run or final validator is assumed in its statement.
Prearray construction, prior/noise discrepancy, innovation, gain, posterior
and mean propagation are now composed into complete checked-step and
finite-horizon accuracy theorems. A uniform two-state `2⁻²⁵` budget and a
fully discharged reset-model domain are proved. The original-input
nontrivial horizon now closes both native profiles and accumulated accuracy.
Wider dynamics, dimensions and tighter scale-dependent constants remain targets.
See [the complete horizon statement](../results.md#full-filter-over-a-finite-horizon).

## Further directions

| Direction | Concrete proposed result | Why it is interesting |
| --- | --- | --- |
| Certified runtime error budgets | A checked certificate accepts only when covariance/gain/mean error is below requested tolerances; otherwise it reports that certification failed. Prove soundness of both the numerical enclosures and the arithmetic used to calculate their bounds. | Converts conditional profiles into evidence obtainable for actual runs; may be less conservative than one global input bound. It certifies numerical discrepancy, not the correctness of a physical noise model. |
| Long-run stability | On a proved invariant operating domain, establish a strict contraction factor q < 1 and a uniform local error δ, then prove E_t ≤ q^t E_0 + δ(1-q^t)/(1-q), in a specified metric. | Answers whether rounding error stays bounded indefinitely. Exact contraction is known; obtaining useful constants, a preserved domain, and a complete native bridge is the substantive goal. Covariance contraction alone does not prove the analogous mean bound. |
| Certified precision or algorithm selection | A policy chooses an implementation or precision using sound error/conditioning certificates, and every accepted choice meets the same tolerance. If repair is used, include its covariance perturbation in the budget. | Produces a decision rule rather than a claim that square-root/Joseph is always more accurate. A new policy or materially sharper bound could be numerical research, subject to a dedicated novelty review. |

Runtime certification has prior art in validated numerics and interval filtering;
for example, the publisher describes
[*Interval Kalman filter enhanced by positive definite upper bounds*](https://www.sciencedirect.com/science/article/pii/S2405896317306407)
as providing covariance upper bounds under model uncertainty. That problem is
distinct from certifying this program's IEEE rounding error. The proposed
contribution must specify what is newly mechanized or changed, rather than claim
the general idea of a certified filter.

## What could count as new numerical research

A complete Lean proof of a known stability theorem is valuable verification,
but is not automatically a new numerical-analysis theorem. Candidates for a
further contribution include a substantially tighter finite-precision bound,
weaker scale/rank assumptions, a certified recovery or precision policy, or a
counterexample family that exposes a missing assumption in a published claim.
We have not established that any such candidate is absent from the literature.

Native QR error and a conditional complete finite-horizon theorem are now
proved. A correlated two-state Cholesky family now derives success, positive
factor structure and a `2⁻⁴²` backward bound from original stored entries alone;
[checked initialization inherits that allowance](../results.md#two-state-cholesky-from-original-inputs).
Two-state triangular solves now derive success and all row profiles from finite
stored factor/RHS bounds. Their composition with Cholesky proves error at most
`2⁻³⁷` against original `A⁻¹B`, including factorization rounding; see
[the solve domain](../results.md#two-state-triangular-solves-from-stored-inputs).
Preservation of the full stage bounds for a nontrivial operating family is
complete. The innovation factor-to-solve bridge is
proved, including noise-derived conditioning. Formed RHS bounds and the gain
profile are now derived from a stored observation/prior-factor domain.
Innovation prearray energy and innovation/gain/mean profiles are now discharged
locally. Prediction now derives its profiles and establishes that reached local
correction domain. Posterior stage discharge, preservation of the returned
state domain and accumulated independent-trajectory accuracy are complete. See
[the QR/solve bridge](../results.md#two-state-qr-factor-to-innovation-solve).
The further research targets are wider original-input domains, runtime domain
certificates, sharper constants and useful long-run guarantees for stronger dynamics.
Keep each theorem tied
to the existing implementation and logical binary64 semantics. Compiler/hardware
refinement is an additional, separate trust-boundary goal. Universal PD for a
rounded dense output is already ruled out by the certified underflow fixture;
it requires a quantitative margin or a changed representation/algorithm.
