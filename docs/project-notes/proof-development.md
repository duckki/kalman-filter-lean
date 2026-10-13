# Proof development notes

Internal implementation history, preserved during the documentation reorganization
on 2026-10-08. The passages below record the order in which supporting proofs and
profiles were developed; statements about remaining work may describe an earlier
stage. Use [the public results](../results.md) for current guarantees.
Repository working instructions remain in [AGENTS.md](../../AGENTS.md).

## QR proof development sequence

## First native QR slice: the scaled column norm

`Proofs.QRProfiles.ColumnProfile` requires at most 32 visited
indices, valid vector indices, finite supplied entries, and at least one nonzero
decoded entry. It assumes neither successful execution nor bounds on computed
quotients. `FloatQRNorm.scaledColumnNorm_accuracy` proves success of the actual
`scaledColumnNorm` helper now called by QR.

Let $s$ be the computed maximum absolute entry, $q_i=x_i/s$ in exact Real
arithmetic, $T=\sum_iq_i^2$, $k$ the number of visited indices, and $u=2^{-53}$.
Maximum selection and absolute value are exact, so $s>0$, $|q_i|\le1$, and
$1\le T\le k$. The returned vector is finite, contains the actual native
divisions at visited indices, and contains zero elsewhere; each visited entry
differs from $q_i$ by at most $2^{-51}$. The separately rounded square/add loop
has absolute error at most $a_k=k(k+20)2^{-52}$.

For the returned **normalized** norm $\widehat r$, the completed theorem gives

$$
|\widehat r^2-T|\le e_k,\qquad
|\widehat r-\sqrt T|\le e_k,\qquad
e_k=a_k+(2u+u^2)(k+a_k)\le2^{-38}.
$$

The bound is conservative and dimensionless. It includes gradual underflow of
small normalized components and permits subnormal or extremely large finite
column entries. It is not a bound on a later native multiplication by the scale.
It does not establish Householder orthogonality, reflector application accuracy,
whole-QR Gram/backward error, or a full-filter success domain. QR can have more
than 32 active entries; this slice only covers the stated local domain.

`scaledColumnNorm_range_schedule` proves equality with the original interleaved
QR range loop for all operands, including rejected computations. Zero scale
causes `nonpositivePivot`; exceptional division, square, addition, or sqrt
results cause `nonfiniteComputation`. With nonfinite source entries, maximum
selection can also leave a zero scale, causing the earlier pivot rejection.
The arithmetic bridge uses the reviewed FLARE `Order.abs_value`, `max_value`,
`Division.div_error`, `Arithmetic.mul_error`, `Arithmetic.add_error_relative`,
and `Sqrt.sqrt_error_nearest` results. The relative addition theorem requires
finite stored operands and exact sum magnitude at most $2^{1000}$; this loop
derives a bound below 64 and includes its explicit $2^{-1022}$ underflow term. Those decode the same stored binary64 values;
the norm and storage composition is proved in this project.


## Second native QR slice: reflector construction and normalization

`FloatQRReflector.householderReflector_accuracy` completes the public
`Proofs.QRProfiles.ReflectorAccuracy` statement for the actual
`householderReflector` helper now called by QR. Its local `ReflectorProfile`
requires a duplicate-free list of at most 32 valid active indices, the first
index in that list, finite vector storage with active magnitudes at most 2,
and a finite supplied column norm $r$ with $1/2\le r\le6$.
`scaledColumn_reflector_accuracy` derives every one of these operand conditions
from the preceding input-only `ColumnProfile`, plus distinct indices and a valid
first index. The caller need not assume either stage succeeds or satisfies its
error bound.

Let $v_i$ denote exact decoding of the stored scaled column, and let $\alpha$
be the native signed choice: $+r$ when the first component is negative, $-r$
otherwise. Negation and this finite comparison are exact. Both signed zeros
take the $-r$ branch. Thus

$$|v_f-\alpha|=|v_f|+r.$$

Let $b$ be the stored vector after the separately rounded first subtraction;
other components are copied unchanged. The completed statement gives

$$|b_f-(v_f-\alpha)|\le2^{-49},\qquad |b_f|\ge1/4.$$

For $S=\sum_{i\in I}b_i^2$, the proof derives $S\ge1/16$ and active magnitudes
at most 9. `sumSquares_relative_accuracy` proves that the actual square/add
loop has error at most $k2^{-49}S$, where $k=|I|$. It uses FLARE's magnitude-scaled
native multiplication/addition bounds with their underflow terms. The established
floor $S\ge1/16$ absorbs those terms; no individual component must be normal.
Its native square root $\widehat\rho$ is finite, at least $1/8$, and satisfies
$|\widehat\rho^2-S|\le(k+1)2^{-49}S$. These are derived properties of the intermediate
values, not additional caller assumptions.

For the returned stored vector $w$, the public theorem proves finite storage,
unchanged array size and inactive components, and

$$
\left|w_i-\frac{b_i}{\sqrt S}\right|\le r_k\quad(i\in I),\qquad
\left|\sum_{i\in I}w_i^2-1\right|\le r_k,\qquad r_k=(9k+5)2^{-50}.
$$

These dimensionless allowances are conservative. For four active rows,
$r_4=41\cdot2^{-50}\approx3.64\times10^{-14}$, about 25 times smaller than
the preceding $2^{-40}$ allowance. `reflectorRadius_le` retains that older cap
for $k\le32$. The proof keeps the actual row count and squared-norm discrepancy
relative to $S$. Nonnegative prefix-plus-next-term energy reduces the square/add
accumulation allowance; the normalization quotient magnitude is bounded by 2. The component
reference normalizes the **exact decoding of the stored constructed vector**.
The first subtraction has its own bound above. This does not yet bound error
against the ideal reflector of the original unrounded column, orthogonality of
a rounded dense reflector matrix. The following slice supplies native application
error and its composition with the stored constructed-vector error.

`householderReflector_range_schedule` proves equality with the previous inline
QR range block for all operands and failures. Divisions read the mutable vector
and overwrite in order; repeated indices would divide repeatedly, which is why
the numerical theorem requires distinct indices. Exceptional subtraction,
square, addition, sqrt, or division results cause `nonfiniteComputation`; a
nonpositive computed normalization norm causes `nonpositivePivot`.

The bridge uses the same reviewed FLARE binary64 operations as the norm slice,
plus `Order.lt_iff`, `neg_value`, and `Arithmetic.sub_error`. Finite subnormal
operands and gradual underflow remain covered by those scalar bounds. The
construction, accumulation, normalization, storage, and two-stage composition
proofs are in this project. The ninth slice below completes whole-QR Gram error
under prefix profiles; prearrays with more than 32 active entries remain outside
this local numerical domain.


## Third native QR slice: application to one column

`FloatQRApplication.applyReflector_accuracy` completes the public
`Proofs.QRProfiles.ApplicationAccuracy` statement for the
`applyReflector` helper now used for each trailing QR column. Its
`ApplicationProfile` requires at most 32 distinct valid active row indices,
finite correctly shaped matrix/vector storage, a valid target column, active
stored-vector magnitudes at most 2, and an active target-column bound $M$ with
$2^{-1022}\le M\le2^{900}$. No successful run, dot-product error, or final error
is assumed. The vector need not be assumed exactly unit.

Let $w_i$ and $x_i$ be exact decoding of the supplied stored vector and the
target column **before the writes**, $k$ the active length, and
$D=\sum_{i\in I}w_ix_i$. The reference is

$$y_i=x_i-2w_iD.$$

The proof establishes success with finite output, unchanged storage size and
every unselected flat matrix slot copied exactly. At every active row,

$$
|\widehat y_i-y_i|\le (k+1)2^{-42}M\le2^{-36}M.
$$

For $k=32$, the sharper formula is $33\cdot 2^{-42}M$, about
$7.50\times10^{-12}M$. This is an absolute stored-operand bound, not a relative
error bound on $y_i$; cancellation may make $y_i$ zero or very small.

The checked dot loop has error at most $k2^{-44}M$. It instantiates FLARE's
`Matrix.Multiplication.dot_nearest_step` with the derived total term budget
$64M\le2^{990}$. The proof derives finite doubling and each subsequent product
and subtraction, using `Binary64.Nearest.mul_error_nearest` and
`sub_error_nearest`. Each such scalar rounding contribution is bounded by
$2^{-44}M$. The imported operations include the $2^{-1022}$ underflow allowance;
the caller's lower bound on $M$ absorbs it. The upper bound leaves headroom for
all derived intermediate magnitudes and is sufficient, not maximal.

`scaledColumn_applyReflector_accuracy` also completes the three-stage public
`ColumnApplicationAccuracy` statement. Starting from a finite nonzero source
column's `ColumnProfile`, distinct valid indices and a selected first index,
plus `TargetColumnProfile` for the target matrix, it derives success of the
column norm, reflector construction, and application. In particular, the
returned reflector's near-unit result supplies the magnitude bound used above.
These are inputs to the local QR stages, not yet a domain for a whole QR run.

For the stored constructed vector $b$ from the second slice, let
$u_i=b_i/\sqrt{\sum_j b_j^2}$. Its exact normalized application is
$z_i=x_i-2u_i\sum_j u_jx_j$. The additional completed bound is

$$
|\widehat y_i-z_i|\le
\big((k+1)2^{-42}+6kr_k\big)M\le2^{-18}M.
$$

This allowance propagates the earlier component budget
$|w_i-u_i|\le r_k$; it does not assume an exactly normalized native vector.
It is deliberately conservative, and the preceding reflector budget dominates
it. The reference still uses the **stored constructed** vector, not the ideal
unrounded source column's reflector. Neither bound establishes whole-QR
Gram/backward error or a full-filter success/rank domain. The fourth slice below
separately covers the source-column overwrite.

`applyReflector_range_schedule` proves equality with the previous inline QR
block for every operand and failure: all dot products precede doubling; each
update then reads the mutable matrix, multiplies, subtracts, checks, and writes
in index order. Repeated indices would update repeatedly and are excluded from
the numerical profile. Every exceptional arithmetic intermediate causes
`nonfiniteComputation`; this stage has no pivot check or symmetry repair.
The native-model bridge and array-write proofs cover the actual helper; no
library theorem about a different full QR algorithm is imported.


## Fourth native QR slice: source-column zeros and diagonal rescaling

`FloatQRFinish.scaledColumn_finish_accuracy` completes the public
`Proofs.QRProfiles.SourceColumnAccuracy` statement. It
connects the actual `scaledColumnNorm`, `householderReflector`, and `finishColumn`
calls, deriving success from `SourceColumnProfile` on the original stored source
column. The profile requires finite correctly shaped matrix storage, a valid
column, and at most 32 distinct valid active rows, written as $I=f::\mathrm{tail}$.
Every active entry has magnitude at most $2^{900}$, and at least one has magnitude
at least $2^{-900}$. Consequently the exactly selected maximum scale satisfies
$2^{-900}\le s\le2^{900}$. These are input conditions; success, reflector accuracy,
and zero-write error are conclusions.

Let $x_i$ decode the same stored source column, $s$ the selected stored scale,
$\alpha$ the stored signed norm choice, and $w$ the returned stored reflector.
The finish helper computes the checked native product
$d=\mathrm{fl}(\alpha s)$, writes it at $f$, and writes **positive zero** at
all tail indices. It does not compute those residuals and discover them to be
zero. The completed conclusions include finite output, unchanged storage size,
exact preservation of every unvisited Float value, and

$$
|d-\alpha s|\le2^{-49}s,\qquad s/4\le|d|\le7s.
$$

The actual native comparison `0.0 < diagonal.abs` is also proved true for this
completed column. This establishes a local nonzero pivot, not that every later
QR pivot has a sufficient rank margin. Both signed-zero first entries retain
the existing negative-norm sign choice; the finishing stage adds no sign repair.

The squared diagonal accurately represents the original column's exact squared
norm:

$$
\left|d^2-\sum_{i\in I}x_i^2\right|\le2^{-37}s^2.
$$

Here both the square and sum in the reference are Real computations. They are
not a rounded native dense Gram or a computed Float square, which might overflow
at the upper end of the domain.

The forced writes also approximate the **same stored reflector's** exact action
on that original column, $y_i=x_i-2w_i\sum_jw_jx_j$. With
$\widehat y_f=d$ and $\widehat y_i=0$ for tail rows,

$$
|\widehat y_i-y_i|\le
\left(2^{-49}+c_k+6kr_k\right)s\le2^{-18}s,\qquad k=|I|\le32.
$$

The derivation accounts for forced-zero error rather than assuming it away.
Put $q_i=x_i/s$ and let $b$ be the exactly decoded stored constructed vector.
Rounded division and first subtraction give
$|b_i-q_i+\alpha\mathbf{1}_{i=f}|\le2^{-48}$;
$S=\sum b_i^2\ge1/16$, $|b_i|\le9$, and
$|\alpha^2-\sum q_i^2|\le e_k$ with the actual column-norm allowance above.
The completed Real lemma `source_reflection_residual` derives the dimensionless
annihilation allowance

$$
c_k=2^{-48}+4\left(2^{-44}+k(2^{-48})^2+e_k\right).
$$

Only the head contributes the linear alpha defect; tail defects enter as their
squares. This replaces a linear defect charged to all 32 rows and a blanket norm
allowance. The factor 4 follows from $|b_i|/S\le4$. The preceding component error
$|w_i-b_i/\sqrt S|\le r_k$ contributes $6kr_ks$, and rescaling rounding contributes
$2^{-49}s$. At four rows, $c_4\approx3.20\times10^{-13}$, replacing the previous
$2^{-35}\approx2.91\times10^{-11}$ cap. These are still conservative bounds.

`finishColumn_range_schedule` proves equivalence to the old checked product,
diagonal write, and ascending tail-zero range block for every operand and
failure. `active_range_cons` relates the actual QR active range to the head/tail
list used in the numerical proof. An exceptional product rejects with
`nonfiniteComputation` before any returned writes. `zeroColumn_storage` also
covers repeated zero writes; reflector construction requires distinct rows.
No symmetry repair is introduced.

The new imported arithmetic step is FLARE
`Binary64.Nearest.mul_error_nearest`, applied to the same stored binary64
operands with exact product magnitude at most $2^{1000}$. Its allowance
$2^{-53}(|\alpha s|+2^{-1022})$ is absorbed into $2^{-49}s$ using
$|\alpha|\le6$ and the stated scale floor. The native-to-model bridge is the
existing FLARE bridge for Lean 4.34.1 Float multiplication; no different QR
implementation is substituted. The Real sum algebra and array-write proofs
are project proofs. Inputs outside this sufficient scale domain are not covered
by this theorem, even when the runtime happens to succeed. The fifth slice
below composes one entire iteration, the sixth proves exact retention, and the
ninth completes whole-QR Gram error under prefix profiles, and the twelfth
derives the eight-row initial-input QR domain. The original-input horizon theorem
below derives a complete-filter success domain for its stated two-state family.


## Fifth native QR slice: one complete iteration

`FloatQRIteration.qrIteration_accuracy` completes the public
`Proofs.QRProfiles.IterationAccuracy` statement for the
`qrIteration` helper now called by `gramFactor`. For a pivot $f$, its active rows
are $I=[f,h)$, its trailing columns are $J=[f+1,w)$, and $k=h-f\le32$.
`IterationProfile` requires a valid pivot in both dimensions, finite correctly
shaped matrix storage, an entry magnitude cap $M$ over rows $I$ and columns
$[f,w)$ with $2^{-900}\le M\le2^{900}$, and one source-column entry with magnitude
at least $2^{-900}$. The reference matrix $X$ is exact decoding of the stored
input to this iteration, **before any writes**. No successful execution or
intermediate-error conclusion is assumed.

The proof derives successful norm computation, reflector construction,
application to every trailing column, and source-column finishing. The result
is finite and has unchanged storage size. Every flat slot outside the selected
rows/columns is preserved as the same Float value, including earlier columns
and prefix rows. The source scale satisfies $2^{-900}\le s\le M$; the diagonal retains the
fourth slice's magnitude lower bound $s/4$, true native absolute-value pivot
comparison, and squared-norm error $2^{-37}s^2$. The source tail contains assigned
positive zeros.

For the returned stored reflector $w$, put
$Y_{ij}=X_{ij}-2w_i\sum_{r\in I}w_rX_{rj}$. The completed panel theorem
`applyReflectorColumns_accuracy` gives, for every $j\in J$ and $i\in I$,

$$
|\widehat X_{ij}-Y_{ij}|\le(k+1)2^{-42}M\le2^{-36}M.
$$

Distinct target columns are essential: each column application preserves all
other valid columns, so the next application reads its original target. There
is **no multiplier for the number of trailing columns** in this entrywise bound.
The generic panel theorem allows any finite list of distinct valid target
columns; the 32-term limit concerns active rows. Repeated columns are excluded
from the numerical profile but retain their repeated-update native behavior.
Finishing then preserves every trailing result. Including the source column,

$$
|\widehat X_{ij}-Y_{ij}|\le
\max\lbrace 2^{-49}+c_k+6kr_k,\space (k+1)2^{-42}\rbrace M\le2^{-18}M,
\qquad i\in I,\space j\in[f,w).
$$

There is also a comparison with the exactly normalized stored constructed
vector $u_i=b_i/\sqrt S$, $S=\sum_{r\in I}b_r^2>0$.
`constructedUnitComponent_unit` proves $\sum_{r\in I}u_r^2=1$ exactly; the native
$w$ still has only the preceding near-unit guarantee. With
$Z_{ij}=X_{ij}-2u_i\sum_{r\in I}u_rX_{rj}$,

$$
|\widehat X_{ij}-Z_{ij}|\le
\mathrm{iterationRadius}(k,M)
=\left(\max\lbrace 2^{-49}+c_k+6kr_k,\space (k+1)2^{-42}\rbrace +6kr_k\right)M\le2^{-17}M.
$$

The final bound adds $6kr_kM$ to the larger of the source and trailing-column allowances.
Neither allowance is assumed to dominate the other at every active length. It is
conservative, dominated by the earlier component-normalization budget, and
absolute relative to the input magnitude cap $M$, not relative to a potentially
cancelled output entry. The unit reference uses the **stored constructed**
vector, not the ideal reflector computed without rounding from the original
source. These bounds concern the selected panel. Earlier columns are copied;
identifying that copying with a full-matrix Householder action requires the
previous-column triangular-zero invariant, established by the seventh slice
below. The eighth slice completes the full-matrix comparison and local Gram
bound; the ninth composes those allowances across every actual pivot under
explicit prefix operand profiles.

`applyReflectorColumns_range_schedule` preserves the ascending trailing-column
range loop, including every early rejection. `qrIteration_schedule` preserves
the previous complete iteration block for every operand and failure: the source
is read first; trailing columns update the current matrix in ascending order;
then finishing checks the rescaled product and writes the source diagonal/zeros.
The extraction adds no runtime checks, sign repair, or symmetry repair. A failed
stage returns its existing error and no successful output.

No new external arithmetic theorem or library is imported in this slice. The
proof composes the four preceding native-model bounds, proves column/storage
independence, and matches their existential results through deterministic
execution equality. It does not assume a newly supplied intermediate profile.
`IterationProfile` describes the current stored iteration input; it does not
prove that an initial full-rank matrix maintains the source witness and entry cap
at later pivots. The ninth slice completes multi-iteration Gram propagation;
the twelfth derives the supported initial-input domain. The filter-level sections
below compose the accumulated errors. The final sign/copy conversion is proved in the sixth
slice below.


## Sixth native QR slice: exact retained-factor conversion

`FloatQRRetain.retainFactor_accuracy` completes the public
`Proofs.QRProfiles.RetentionAccuracy` statement for the
`retainFactor` helper now called by `gramFactor`. `RetentionProfile` requires
finite stored entries and a nonzero decoded value on every retained diagonal.
It does **not** assume execution success, output positivity or accuracy. Unlike
the arithmetic QR slices, retention needs no dimension cap, scale floor or
magnitude headroom. Its multiplication theorems include every finite binary64
value, including signed zero, subnormals and the largest finite magnitude.

Let $U$ be the upper triangle of the retained square block of the stored QR
result, decoded exactly and set to zero below its diagonal. Put
$d_j=-1$ when the decoded diagonal is negative and $d_j=1$ otherwise, and
$D=\mathrm{diag}(d)$. The theorem produces a successful, finite output
of size $n^2$, with assigned positive zeros above its diagonal and

$$
L=U^T D,\qquad L_{jj}=|U_{jj}|>0,\qquad
LL^T=U^T U\succ0.
$$

These identities are **exact**: the retained sign/copy stage adds zero entrywise
or Gram error. `retained_factor_interpretation` proves the signed transpose
identity, and `retained_factor_gram` proves Gram preservation using $DD^T=I$.
The strict-PD conclusion follows from the proved positive-diagonal lower
structure and `FactorStructure.lowerPositive_gram_posDef`. It is derived from
retention inputs, without requiring a successful output-validation premise.

The reference $U$ is the **stored upper block**, not the original prearray or
the ideal QR factor. Off-triangle and extra tall rows are omitted by this
reference. The seventh slice below proves the triangular-zero invariant and
identifies $U^T U$ with the full stored QR result's Gram. Comparing it with the
original prearray still needs multi-iteration error propagation, now completed under prefix profiles by the
ninth slice. Neither comparison is silently included in this retention theorem. Missing
storage reads use the runtime's positive-zero default; the profile has no shape
premise, although the QR caller supplies the proper rectangular shape. A missing
diagonal cannot satisfy its nonzero premise.

`one_mul_value` and `neg_one_mul_value` prove the exact multiplication identities
from Lean 4.34.1's `Float.Model.UnpackedFloat.mul` and `roundWithAccuracy`.
Multiplying the canonical mantissa by $2^{52}$ and then shifting it back drops
only zero bits. The project proof shows both rounding stages are exact and
uses FLARE's `Model.Rounding.unpack_finite_shape`,
`Model.Conversion.unpack_pack_normal`, `Model.Rounding.unpack_pack_subnormal`
and native interpretation/order bridges. Thus this is a completed native-model
proof over the full finite domain, not an assumed rounding law, a native test,
or an application of a bounded-magnitude error inequality. Signed-zero bit
behavior is kept by the executable multiplication; both decode to real zero.

`retainFactor_schedule` and `gramFactor_retention_schedule` preserve the old
ascending diagonal-check, sign-choice, multiplication/check and transpose/write
block for all operands and failures. Zero and NaN diagonals fail the original
absolute-value pivot guard. An infinite diagonal passes that guard but its
checked product rejects; exceptional off-diagonal products also reject.
There is no new symmetry repair or rounded dense covariance formation.
`copyFactorColumn_storage` and `retainColumns_storage` also prove untouched
entries are preserved, including repeated writes from the fixed source.

Native regressions check independent analytic signed-copy and small Gram
references, positive-zero storage, both signed zeros, minimum subnormal and
maximum finite entries on both sign branches, a 33-dimensional retention case,
duplicate writes, empty output, missing diagonals and exceptional-value rejection
order. These tests supplement the logical proofs; they do not establish a
compiler/hardware refinement or universal PD of a rounded dense Gram matrix.


## Seventh native QR slice: whole-loop triangular structure

`FloatQRTriangular.triangularize_structure` completes the public
`Proofs.QRProfiles.TriangularizationStructure` postcondition.
For a stored $h\times w$ matrix with $w\le h$, finite correctly shaped input and
a **successful** `triangularize` call suffice. The result has the same shape,
finite entries and assigned positive zeros at every position $i>j$, including
all extra tall rows $i\ge w$. This is a conditional structural theorem: it does
not prove that the loop succeeds from full rank or PD of the original input.
There is no dimension cap, magnitude headroom or numerical `IterationProfile`
assumption in this result.

`ProcessedColumns h w k` records the exact native positive-zero entries below
the diagonal in columns $j<k$. The proof follows the successful checked-write
paths of `reflectorUpdates`, `applyReflector`, the trailing-column panel and
`finishColumn`. These storage lemmas require no rounding estimates or reflector
accuracy premise. `qrIteration_earlierColumn` proves each earlier column is
copied as the same Float value at **every row**. `qrIteration_processed` combines
those copies with the new source-tail zero assignments. Induction over the
actual ascending pivot list then establishes the full invariant in
`qrIterations_processed`. Empty pivot ranges are included.

Let $R$ denote the exact decoding of the full stored $h\times w$ result and
$U$ its retained upper $w\times w$ block. The completed
`retainedUpper_gram_eq_full` theorem gives

$$
U^TU=R^TR.
$$

The proof identifies every entry in the top block and proves that all omitted
tall-row terms are exactly zero. It introduces no arithmetic rounding allowance.
Combined with the sixth slice, this yields a public proof witness
`gramFactor_structure` for `SuccessfulGramFactorStructure`: if the finite,
correctly shaped $n\times p$ prearray has $n\le p$ and its native factor call
succeeds, there is a finite triangular $p\times n$ stored result $R$ such that

$$
L\text{ is lower triangular with }L_{jj}>0,\qquad LL^T=R^TR\succ0.
$$

The diagonal guard in the successful retention trace supplies the nonzero
stored diagonals required by `RetentionProfile`; it is not a separately assumed
rank margin. The proof does not require the filter's final factor validator.
This strengthens the raw factor kernel's structural guarantee, while the
previous successful checked-step theorem remains available.

The reference remains the **computed stored QR result**. This is not yet a bound
within this structural theorem for $R^TR-AA^T$, where $A$ is the decoded
original prearray; the ninth slice adds that bound under prefix profiles. This
structural theorem does not prove rank preservation or an input success domain;
the twelfth supplies those numerical conclusions under explicit initial margins.
No rounded dense Gram is formed by `gramFactor`; strict PD here is for the exact
Real denotation of the stored factor. The separate materialization error and
positivity-margin obligations still apply.

`triangularize_range_schedule` preserves the previous ascending pivot range on
all inputs and failures. The updated `gramFactor_retention_schedule` preserves
the entire previous factor call after extracting `qrIterations`/`triangularize`.
No operation ordering, finite check, zero assignment, sign policy or rejection
order is changed. No new external arithmetic theorem is imported: this slice
uses the existing finite/order bridge and kernel-checked storage, loop and Real
finite-sum proofs. The binary64/library revision and hardware boundary are the
same as the preceding slices.

Native regressions cover an independent analytic tall result and Gram,
preservation of earlier columns by later pivots, positive-zero tails and tall
rows, agreement of retained/full stored Grams, a 33-dimensional identity,
empty pivot ranges, first/later singular pivots and exceptional trailing entries.
The Gram comparisons in those tests are rounded native products; the exact
identity is supplied by the theorem, not inferred from test agreement.


## Eighth native QR slice: one-iteration column-Gram error

`FloatQRGram.qrIteration_orthogonal_accuracy` completes the public
`IterationOrthogonalAccuracy` contract. `qrIteration_gram_accuracy` completes
`IterationGramAccuracy`; the review entry point
`FloatErrorBounds.qrIterationGramAccuracy` witnesses `QRIterationGramAccuracy`.
These are completed numerical theorems, with success as a conclusion.

The domain is an incoming finite, correctly shaped $h\times w$ stored matrix,
pivot $p<h$ and $p<w$, and its existing `IterationProfile`: $k=h-p\le32$ active
rows, active panel magnitudes at most $M$, $2^{-900}\le M\le2^{900}$, and at least
one active source entry of magnitude at least $2^{-900}$. Additionally,
`ProcessedColumns h w p` requires assigned positive zeros below the diagonal
in every earlier column. No error or execution success is assumed. At pivot
zero the prior-zero premise is vacuous. At later pivots the seventh slice proves
that structure, but the numerical profile still needs separate justification.
Entries in the copied prefix may exceed $M$; only the active panel is bounded.

Let $A$ be the exact decoding of the entire incoming stored matrix and $B$ the
entire returned matrix. The proof embeds the exactly normalized **stored
constructed** vector as a full-height vector $u$, setting rows before the pivot
to zero. `iterationUnitVector_unit` proves $\sum_i u_i^2=1$.
`Definitions.OrthogonalFactorization.reflect` records the project algebraic
reference $C=(I-2uu^T)A$; `OrthogonalStructure.reflect_gram` proves
$C^TC=A^TA$. The reference is not the reflector selected by ideal QR on the
original prearray. Exact unit normalization is enough for Gram preservation.

The previous selected-panel bound extends to

$$
|B_{ij}-C_{ij}|\le e_k(M),\qquad
 e_k(M)=\mathrm{iterationRadius}(k,M)\le2^{-17}M.
$$

Prefix rows are copied by the native loop and unchanged by the reference.
Earlier columns have zero active tails, so they too agree with the full
reflection. These facts are why the prior-zero premise matters: applying a
later pivot while copying an earlier column with a nonzero active tail can
change cross-column Grams even in exact arithmetic.

The unit-component bound gives $|C_{ij}|\le(1+2k)M$ on active rows. A product
perturbation estimate, with exactly unchanged prefix rows, then gives

$$
\left|(B^TB-A^TA)_{ij}\right|\le g_k(M),\qquad
 g_k(M)=k\left[2(1+2k)M e_k(M)+e_k(M)^2\right].
$$

`iterationGramRadius` names this radius. `iterationGramRadius_le` supplies the
simple conservative cap $g_k(M)\le2^{-4}M^2$ for $k\le32$ and $M\ge0$.
The dimension-dependent formula is more informative; neither bound is a
relative error or a sharp classical backward-stability constant. There is no
trailing-column-count factor. The inequality concerns the **exact Real Gram**
of the stored arrays; it does not evaluate a rounded native dense Gram.

The new proof uses no new external arithmetic estimate. It composes the
previous native iteration bound, its existing binary64/FLARE bridge, the
proved storage invariant, and exact Real finite-sum algebra. It changes no
runtime operation, check, sign policy or zero assignment. Native regressions
compare a later pivot with an independent correlated analytic Gram and include
a contrasting input with invalid prior zeros. The native Gram products in the
regressions supplement the theorem and do not replace its exact interpretation.

This is a **one-iteration** bound against that iteration's incoming stored
matrix. The ninth slice below now sums the Gram changes over the actual complete
pivot loop under explicit prefix operand profiles. The twelfth slice derives
those profiles from initial conditions for the eight-row domain. Full Kalman
trajectory accuracy and PD of an optional rounded dense output remain separate.


## Ninth native QR slice: complete factor Gram error

`FloatQRComposition.qrIterations_prefix_accuracy` completes `QRPrefixAccuracy`.
`triangularize_gram_accuracy` completes `TriangularizationGramAccuracy`, and
`gramFactor_accuracy` completes `GramFactorAccuracy`. The public review entry
point `FloatErrorBounds.qrGramFactorAccuracy` witnesses `QRGramFactorAccuracy`.
These theorems prove successful execution, finite storage and the error bound;
they do not assume successful final factorization or the desired error.

The domain is `TriangularizationProfile h w a budget`: finite correctly shaped
$h\times w$ input, $w\le h$, and an `IterationProfile` with budget $M_p$ for
every actual ascending-loop prefix before pivot $p<w$. The profile states:
**if the first $p$ iterations return a stored matrix, that matrix satisfies the
local operand conditions for pivot $p$.** It does not assume that a prefix or
the final loop succeeds. Induction derives every prefix's success from these
conditions, beginning with the unchanged input at $p=0$.

This is a **run-dependent operand profile**, not a theorem discharging all
later profiles from initial rank or PD. The supplied conditions retain the
same numerical domain: each active height $k_p=h-p$ is at most 32, each
$2^{-900}\le M_p\le2^{900}$ bounds the incoming active panel, and each source
column has an active entry of magnitude at least $2^{-900}$. For a nonempty
full loop, the first profile requires $h\le32$. Empty loops are included
without that cap. Profiles contain no Gram-error conclusions or final-output
validation. The twelfth slice below constructs that evidence from initial
energy/rank and scale margins for up to eight rows.

The proof propagates `ProcessedColumns` and every earlier stored nonzero
source diagonal along the actual ascending schedule. Nonzero diagonal
finishing follows from the existing local numerical theorem, and later
iterations copy earlier columns. Thus the final `RetentionProfile` is a
conclusion, and the exact sign/transpose stage succeeds without an assumed
retention result or final validator.

Let $A_0$ be the exact decoding of the original tall input and $R$ the full
stored final triangular result. With $g_k(M)$ from the eighth slice,

$$
\left|(R^TR-A_0^TA_0)_{ij}\right|
 \le G_{h,w}(M),\qquad
G_{h,w}(M)=\sum_{p=0}^{w-1}g_{h-p}(M_p).
$$

`qrGramRadius h w budget` names this sum. The proof composes the actual
consecutive Gram comparisons with the Real triangle inequality. There is no
additional amplification or trailing-column-count factor. Under nonnegative
budgets bounded by $B$ and active heights at most 32, `qrGramRadius_le` supplies
the conservative cap $G_{h,w}(M)\le w\cdot 2^{-4}B^2$. The explicit sum is more
informative than that coarse cap. These are absolute entry bounds, not sharp
relative or normwise Householder backward-stability constants.

For a finite correctly shaped original $n\times d$ prearray $A$, the factor
witness requires this profile for its **actual native transpose** with
$h=d,w=n$. FLARE's already-used exact finite transpose interpretation identifies
$A_0=A^T$. Combining the accumulated bound with the completed exact retention
identity gives the returned native factor $L$:

$$
L\text{ is lower triangular with }L_{jj}>0,\qquad LL^T\succ0,\qquad
\left|(LL^T-AA^T)_{ij}\right|\le G_{d,n}(M).
$$

The reference is now the **same original stored prearray**, rather than the
computed QR result. Retention adds zero error. This is a complete raw-factor
Gram residual bound under explicit prefix profiles. It does not include errors
in constructing that prearray, deriving a Kalman gain, or propagating prior,
process-noise and measurement-noise factors. The ideal full-filter comparison
remains separate. Strict PD refers to the exact Real denotation of the stored
factor; an optional rounded dense Gram still needs materialization error and
its own positivity margin.

`qrIterations_append` proves the schedule split used by the induction, including
all early failures. No runtime operation, arithmetic order, exceptional-value
policy, sign convention or zero assignment changes. No new external rounding
estimate is imported: this slice composes the previously proved native local
bounds, exact retention and transpose interpretation, and project Real
entrywise composition. The binary64/library revision and hardware boundary are
unchanged.

Native regressions compare every prefix and the final retained factor with an
independent correlated $3\times5$ prearray Gram at scales $1,2^{20},2^{-20}$,
check persistence of nonzero diagonals, and cover an empty pivot range. The
native Gram products in those regressions are rounded; the universal error and
strict-PD conclusions come from the theorems, not from test agreement.


## Tenth native QR slice: prefix magnitude and spectral margins

`FloatQRDomain.qrIterations_prefix_enclosure` completes `PrefixEnclosure` for
the actual stored result after $p$ pivots. `InitialGramBounds h w a S α` refers
only to the exact decoding $A_0$ of the original stored tall input:

$$
\sum_{i=0}^{h-1}(A_0)_{ij}^2\le S\quad\text{for every column }j,
\qquad A_0^T A_0\succeq\alpha I.
$$

Let $A_p$ decode the current stored prefix and
$G_p=\texttt{qrGramRadius}\space h\space p\space \texttt{budget}$. The completed theorem gives

$$
(A_p)_{ij}^2\le S+G_p,\qquad
A_p^T A_p\succeq(\alpha-wG_p)I.
$$

The first bound uses the diagonal part of the proved Gram error: every entry's
square is bounded by its column's squared norm. The second uses the existing
Real perturbation theorem
`Flare.Analysis.NumericalBounds.perturbation_lower_bound`. A symmetric $w\times w$
entrywise perturbation of radius $G_p$ consumes at most $wG_p$ of a uniform
spectral lower bound. `ErrorPropagation.lower_bound_of_error` exposes this
quantitative statement, even when the remaining lower bound is nonpositive.
The exact column Gram is symmetric by construction; no symmetry repair or
rounded dense Gram computation is involved.

The proof requires finite initial storage and `IterationProfile` only for
the **preceding** pivots $q<p$, conditional on their actual stored prefix
results. `FloatQRComposition.qrIterations_prefix_accuracy_of_profiles` proves
prefix success, structure and Gram error from exactly those conditions. The
enclosure theorem also takes the actual prefix result to identify its storage;
that result's existence is already supplied by the prefix accuracy theorem.
Neither result requires a profile for the next pivot or any later pivot. This
avoids assuming the condition we are trying to establish in an induction over
the supported domain. At $p=0$ the preceding-profile condition is empty.

The consequences are public completed theorems:

- `prefixEnclosure_magnitude`: if $M\ge0$ and $S+G_p\le M^2$, every current
  entry satisfies $|(A_p)_{ij}|\le M$. In particular, this discharges the
  next iteration's panel-magnitude component; `prefixEnclosure_panel_magnitude`
  supplies exactly its Nat-indexed form.
- `prefixEnclosure_posDef`: if $wG_p<\alpha$, the current exact column Gram
  is strictly PD, giving a full-column-rank certificate.

There is also a concrete conservative budget for $w\le h\le8$, $p\le w$,
and constant nonnegative budget $M$:

$$
g_k(M)\le2^{-10}M^2\quad(k\le8),\qquad
G_p\le2^{-7}M^2.
$$

`iterationGramRadius_le_eight` and `qrGramRadius_le_eight` prove these constants
from the explicit local formulas. `prefixEnclosure_budget_eight` then proves
that initial column energies at most $M^2/2$ and initial Gram floor $M^2/8$
preserve entry magnitude $M$ and Gram floor $M^2/16$. The same conclusion
applies to every certified prefix, including the final one. These conditions
can hold simultaneously: with $M=2$, distinct unit columns embedded in a tall
matrix of zeros have energy 1 and Gram $I$. They are sufficient headroom choices, not optimal conditioning
limits. If $M>0$, the preserved floor is strictly positive.

This enclosure theorem uses profiles for preceding iterations. It discharges
the magnitude component of the next profile and preserves a quantitative rank
margin. The eleventh slice derives the source-tail witness from that margin,
processed-column zeros and the nonzero leading triangular block; the twelfth
closes the induction under explicit initial shape/scale conditions. Full column
rank alone is not substituted for the required quantitative margins.

This slice changes no runtime algorithms or external library revisions. Its
new estimates are Real finite-sum/perturbation consequences of the preceding
native bounds. The native-model bridge and compiler/hardware boundary remain
as documented above. The proof audit checks all new public theorems; existing
native regressions continue to cover the unchanged execution schedule.


## Eleventh native QR slice: the active source-tail witness

`FloatQRSourceTail` supplies the missing quantitative source-entry consequence
of the previous slice's rank margin. The exact argument applies to any Real
$h\times w$ matrix $A$ with $w\le h$ and pivot $p<w$. It requires:

- every previously processed column $j<p$ has zeros below its diagonal;
- every previously processed diagonal is nonzero;
- $A^TA\succeq\beta I$, with $\beta\ge0$.

`source_tail_combination` proves that there is a coefficient vector $x$ with
$x_p=1$ such that

$$
(Ax)_i=0\quad(i<p),\qquad (Ax)_i=A_{ip}\quad(i\ge p).
$$

The proof completes the earlier leading triangular block with an identity
block, proves its determinant nonzero, and uses exact linear-system
surjectivity to cancel the processed rows. The resulting coefficients for
columns $j\ge p$ are zero before adding the source column. Prior triangular
zeros make those earlier columns vanish in active rows. This is an exact
existence proof; the native algorithm does not execute this solve or cancellation.
No computed inverse or cancellation accuracy is assumed.

Since $x_p=1$, $\sum_jx_j^2\ge1$. The existing Real quadratic-form lower-bound
theorem then gives `source_tail_energy_lower`:

$$
\beta\le\sum_{i=p}^{h-1}A_{ip}^2.
$$

`source_tail_entry_witness` proves that if $\tau\ge0$ and $h\tau^2<\beta$,
some active row $i\ge p$ has $|A_{ip}|\ge\tau$. The use of $h$ rather than
$h-p$ is a conservative convenience. This proves a quantitative entry bound,
not just nonzero rank.

For $w\le h\le8$, remaining Gram floor $M^2/16$ and $M>0$,
`source_witness_eight` gives exactly decoded native storage indices satisfying

$$
\exists i,\quad p\le i<h,\qquad
\left|\mathrm{value}(\mathrm{entry}(w,\mathrm{current},i,p))\right|
 \ge M/16.
$$

`qrIterations_prefix_source_witness_eight` connects this to the actual stored
result after $p$ native pivots. Its hypotheses are finite initial storage,
$w\le h\le8$, $p<w$, initial column energies at most $M^2/2$, initial Gram
floor $M^2/8$, **only preceding** operand profiles for the same constant
budget $M$, and the actual prefix-result identity. Prefix accuracy establishes
that result's existence, zeros and nonzero earlier diagonals; the tenth slice
supplies its remaining Gram floor. Under the additional scale condition
$M\ge2^{-896}$, the theorem concludes the exact `IterationProfile.source_witness`
predicate:

$$
\exists i,\quad p\le i<h,\qquad
\left|\mathrm{value}(\mathrm{entry}(w,\mathrm{current},i,p))\right|
 \ge2^{-900}.
$$

Thus both numerical parts needed for the next profile—panel magnitude and
source witness—now have completed derivations from initial margins and
preceding profiles. No profile for the next or later pivot, final successful
run, final validator, or desired Gram-error conclusion is assumed. At $p=0$
there are no preceding profile, zero or nonzero-diagonal obligations.

The twelfth slice below assembles the next complete `IterationProfile`, including
storage/dimension conditions and upper scale limit $M\le2^{900}$, closes the
induction over all pivots, and applies the full-factor theorem. The source witness
proved here supplies that induction's remaining numerical condition. The complete
Kalman trajectory bound is proved in the horizon sections below.

The proof combines project exact triangular/determinant algebra, Mathlib
linear-system surjectivity, and FLARE's existing Real
`NumericalBounds.quadratic_lower_bound`. It imports no new floating-point error
estimate and changes no runtime arithmetic, exceptional-value policy, zero
assignments, library revision or native-model bridge. All statements are
exported through `Kalman.lean` and required by the project axiom audit.

Native regressions check a correlated $3\times8$ prearray (an eight-row tall
QR input) at scales $1,2^{-897},2^{899}$. With $M$ twice the scale, the latter
two exercise the proposed lower and upper budget endpoints $2^{-896},2^{900}$.
Every prefix checks the active source threshold $M/16$, panel budget, finite
storage, prior zeros and nonzero leading diagonals; the retained factor stays
finite with positive diagonals. The unscaled fixture's independent exact Gram
reference is

$$
\begin{pmatrix}
9/8&1/2&1/16\\1/2&9/8&1/16\\1/16&1/16&9/8
\end{pmatrix}.
$$

At the extreme scales, a native dense Gram product would underflow or overflow,
so the new tests inspect the factor representation and active stored entries
directly. These are execution regressions, not certificates establishing the
universal initial-domain hypotheses or compiler/hardware refinement.


## Conditional profile proof history

The separately exported `Kalman.Proofs.FloatQRNorm.scaledColumnNorm_accuracy`
is a proof witness for
`Proofs.QRProfiles.ColumnNormAccuracy`. Its input-only
`ColumnProfile` yields a finite vector, positive finite normalized norm, and a
dimensionless norm/squared-norm radius at most $2^{-38}$ for at most 32 terms.
The radius's formula and exact arithmetic schedule are documented in
[the numerical reference](#first-native-qr-slice-the-scaled-column-norm).

`Kalman.Proofs.FloatQRReflector.householderReflector_accuracy` completes the
public `ReflectorAccuracy` statement: cancellation-free sign choice,
first-subtraction error at most $2^{-49}$, finite successful normalization,
and component/near-unit bounds at most $(9k+5)2^{-50}\le2^{-40}$ for active length
$k\le32$. At four rows this is about $3.64\times10^{-14}$. The component reference is
the exactly decoded stored constructed vector divided by its exact Real norm.
`scaledColumn_reflector_accuracy` derives the local operand conditions from
the original finite, nonzero column inputs, assuming distinct valid active
indices and a selected first index. These conservative bounds prepare the
reflector-application composition; they do not certify whole QR or an exactly
orthogonal stored reflector. See
[the precise domain and reference](#second-native-qr-slice-reflector-construction-and-normalization).

`Kalman.Proofs.FloatQRApplication.applyReflector_accuracy` completes
`ApplicationAccuracy`: one-column native application succeeds, is finite,
preserves unselected matrix slots, and differs from the exact application of
the same stored vector by at most $(k+1)2^{-42}M\le2^{-36}M$. The column budget
is $2^{-1022}\le M\le2^{900}$, with at most 32 distinct active indices and vector
magnitudes at most 2. `scaledColumn_applyReflector_accuracy` derives the vector
conditions from the preceding stages and propagates their component error;
the normalized stored-constructed-vector comparison has radius at most
$2^{-18}M$. Its conservative reference and derivation are detailed in
[the application bound](#third-native-qr-slice-application-to-one-column).

`Kalman.Proofs.FloatQRFinish.scaledColumn_finish_accuracy` completes
`SourceColumnAccuracy`: the original stored source column yields successful norm,
reflector construction, and finishing calls. For at most 32 distinct valid rows
with maximum scale $2^{-900}\le s\le2^{900}$, its diagonal is finite, has magnitude
at least $s/4$, and passes the actual native absolute-value pivot comparison.
Its squared value differs from the same input's exact squared norm by at most
$2^{-37}s^2$. The diagonal/positive-zero overwrite differs from the same stored
reflector's exact application by at most $2^{-18}s$ per active row. The theorem
preserves every unvisited stored value; it does not establish the domains of
subsequent QR columns. See
[the source-column bound](#fourth-native-qr-slice-source-column-zeros-and-diagonal-rescaling).

`Kalman.Proofs.FloatQRIteration.qrIteration_accuracy` completes
`IterationAccuracy` for a whole iteration. Under an input-only `IterationProfile`,
all four stages succeed and return finite storage, a nonzero source diagonal,
and exact copies outside the selected panel. Its bounds use the same original
stored iteration input: at most $2^{-36}M$ for trailing columns against the
stored reflector, $2^{-18}M$ over the whole selected panel, and $2^{-17}M$ against
the exactly unit normalized stored constructed vector. The proof establishes
column independence, so the entrywise bound has no trailing-column-count factor.
The source-witness floor and cap concern this iteration's input, not an entire
QR trajectory. See
[the iteration bound](#fifth-native-qr-slice-one-complete-iteration).

`Kalman.Proofs.FloatQRRetain.retainFactor_accuracy` completes `RetentionAccuracy`:
finite stored QR entries and nonzero decoded diagonals suffice for success,
finite correctly sized output and positive-diagonal lower structure. Its exact
signed-transpose and Gram identities add **zero conversion error** relative to
the retained upper block, and its exact Gram is strictly PD. No dimension or
magnitude cap is needed. This does not compare with the original prearray or
establish PD of a rounded dense matrix. See
[the retention domain and native bridge](#sixth-native-qr-slice-exact-retained-factor-conversion).

`Kalman.Proofs.FloatQRTriangular.triangularize_structure` completes the
`TriangularizationStructure` postcondition for every successful loop on finite,
correctly shaped tall/square input. `ProcessedColumns` is preserved and extended
at each pivot, so the extra tall rows are assigned zeros. `gramFactor_structure`
completes `SuccessfulGramFactorStructure`: any successful raw factor call has a
positive-diagonal lower output with exact Gram $LL^T=R^TR$, using the **full
stored** QR result $R$. No numerical magnitude/dimension cap is needed for this
conditional structural guarantee. It does not compare with the original prearray
or promise successful execution. See
[the loop invariant and Gram identity](#seventh-native-qr-slice-whole-loop-triangular-structure).

`Kalman.Proofs.FloatErrorBounds.qrIterationGramAccuracy` completes the public
`QRIterationGramAccuracy` statement. Under `IterationProfile` and the incoming
`ProcessedColumns` invariant it proves success and bounds the exact full
column-Gram change by $k[2(1+2k)M e_k(M)+e_k(M)^2]$, where $k$ is the active row
count and $e_k(M)$ is the proved iteration radius. The reference is the same
incoming stored matrix, with no column-count factor; copied prefix entries
need no global $M$ cap. `qrIteration_orthogonal_accuracy` and `reflect_gram`
provide the full-matrix comparison and exact Gram preservation that justify
this result. The ninth slice below completes whole-loop numerical composition
under explicit prefix profiles; the twelfth derives those profiles from initial
inputs for up to eight rows. See [the local Gram bound](#eighth-native-qr-slice-one-iteration-column-gram-error).

`Kalman.Proofs.FloatErrorBounds.qrGramFactorAccuracy` completes
`QRGramFactorAccuracy` for the whole native factor call. Correctly shaped finite
original input and a `TriangularizationProfile` for its actual transpose suffice:
the returned finite positive-diagonal lower factor succeeds, denotes a strictly
PD Gram, and has absolute Gram error at most the sum of all proved local Gram
allowances against the **same original stored prearray**. Retention adds zero
error. The prefix profile requires each reached iteration's numerical operand
conditions, without assuming a final successful run or error bound. This is a
completed full-factor Gram residual theorem under run-dependent profiles. The
twelfth slice derives those profiles on the supported initial-input domain. See
[the accumulated radius and profile semantics](#ninth-native-qr-slice-complete-factor-gram-error).

`Kalman.Proofs.FloatQRDomain.qrIterations_prefix_enclosure` now derives
intermediate entry bounds and a remaining spectral floor from original column
energy/rank bounds and the proved errors of preceding pivots. It uses
`qrIterations_prefix_accuracy_of_profiles`, which needs no future-pivot
conditions. `prefixEnclosure_budget_eight` gives a concrete sufficient headroom
choice for up to eight rows: energy at most $M^2/2$ and initial Gram floor
$M^2/8$ preserve magnitude $M$ and Gram floor $M^2/16$. This discharges the next
panel magnitude, conditional on preceding profiles. See
[the completed enclosure and remaining domain gap](#tenth-native-qr-slice-prefix-magnitude-and-spectral-margins).

`Kalman.Proofs.FloatQRSourceTail.qrIterations_prefix_source_witness_eight` now
derives the next active source witness from those same initial bounds and
preceding profiles, with $M\ge2^{-896}$. Exact cancellation of processed rows,
using earlier columns, preserves the active tail; the Gram floor then bounds
its energy from below. For at most eight rows this forces an entry of magnitude
at least $M/16\ge2^{-900}$. No next/future profile or final success is assumed.
The twelfth slice below assembles the complete profile and closes the pivot
induction. See
[the source-tail proof and scale condition](#eleventh-native-qr-slice-the-active-source-tail-witness).

`Kalman.Proofs.FloatErrorBounds.qrGramFactorInitialAccuracy` completes
`QRInitialGramFactorAccuracy` from `GramFactorInputDomain`, containing only
original storage, dimension, energy, rank and scale conditions. It concludes
success, finite lower-positive output, strictly PD exact Gram with floor
$M^2/16$, and both the explicit accumulated error and the cap $M^2/128$.
`FloatQRInitialDomain.triangularizationProfile_eight` derives all pivot profiles
by strong induction. `identity_input_domain` proves every stored identity through
dimension eight meets the domain with $M=2$. No execution or output certificate
is assumed. See [the initial-input theorem and limitations](../results.md#initial-input-qr-success-and-error).

An **a posteriori profile** bounds operands and intermediate values associated
with an actual run. `FactorProfile`, `SolveProfile`, and `JosephProfile` also
record successful computations. Their error bounds are derived by proofs; none
of those profiles assumes the desired factor, solution, or covariance error.
The original-input horizon theorem establishes every such profile for its
documented nontrivial two-state family.

The product, sum, residual/division, local Cholesky diagonal, LDLᵀ, materialization,
and local QR numerical witnesses establish successful execution from their
stated operand hypotheses. Even these local
success theorems do not show that a Kalman trajectory stays in their domains.
The seventh QR slice instead assumes successful execution and derives structural
postconditions for the whole loop; it is not another input-only success theorem.
The ninth QR slice derives full factor success and error from operand profiles
at every actual prefix. The tenth derives prefix magnitude and spectral bounds
from initial bounds and preceding profiles; the eleventh adds the quantitative
active-tail source witness. The twelfth closes the profile/success induction
on the eight-row initial-input domain. The full-filter horizon proofs provide
the Kalman-specific step sensitivity and local-error budgets, and the
original-input theorem derives their assumptions for its two-state family.

All delivered proofs are checked without admissions or added project axioms.
The axiom-audit count includes private/generated helper theorems, not that many
independent mathematical claims. The formal execution model is Lean 4.34.1's
logical native binary64 semantics; hardware/compiler refinement is outside the
current proof scope. Native regression agreement is useful validation, separate
from these completed proofs.

## Implementation proof catalogue history

## Completed theorems

All five original exact propositions have completed proofs. Their statements
are grouped in `Definitions/Theorems/CovariancePositiveDefiniteness` and
`Definitions/Theorems/FormulationEquivalence`:

| Module / theorem | Actual guarantee |
| --- | --- |
| `RealRecursion.covarianceFormulationsAgree` | Compact, subtractive, and Joseph agree at the optimal gain for PD prior and measurement noise. Compact/subtractive agree for every gain. |
| `RealRecursion.josephPositiveDefinite` | Joseph is strictly PD for **any** gain when the prior and measurement noise are PD. |
| `RealRecursion.stepPositiveDefinite` | Every formulation preserves strict PD in the specified full-step domain. Prediction only needs PSD prior and PD process noise. |
| `RealRecursion.informationFormAgrees` | Both covariance and mean agree with the information update; all matrix inverses are justified. |
| `FactorStructure.squareRootStagesAgree` | The exact orthogonal QR relations denote the predicted and Joseph-corrected covariances. |
| `RealRecursion.trajectory_posDef` | Every state in a finite, time-varying-model trace is PD when the initial covariance and both noise covariances are PD. |
| `FactorStructure` | Positive-diagonal lower factors are invertible; covariance factors and positive U-D factors denote PD matrices. |

The five original `CovarianceStructure` lemmas remain available. The axiom audit
checks **every** project theorem, including private helpers, and requires the five
completed Real contract theorems. It permits only `propext`, `Classical.choice`,
and `Quot.sound` in transitive dependencies. There are no project axioms or
admitted proofs; the counterexamples use `decide +kernel`, not `native_decide`.

The fully observed diagonal family has a separate completed **Real** foundation:
`Definitions/DiagonalObservation` specializes to diagonal F/Q/R/P and H equal
to identity. `RealDiagonalObservation` proves equality to the matrix recursion
for all covariance forms. `Definitions/Theorems/RecursionSensitivity` states the exact
domain; `RealObservableInvariant` derives every-prefix covariance floor `1/2`
and mean cap `1` with `|f|≤1`, including identity dynamics. Prediction variance
lies in `[1,3]`, posterior variance in `[1/2,1]`.
`RealObservableSensitivity` derives covariance error coefficient `9/25` and
mean coefficients `3/5` and `1/2`, including the changed gain. Covariance
weighted by two gives joint contraction `17/20` and geometric forgetting of
initial error for two exact trajectories. A supplied local joint allowance `δ`
closes uniform budget `(20/3)δ`; this is a conditional Real interface, not a
new Float bound for the complete step.

The larger family's local native foundation is now proved too.
`Correctness/InputInterpretation.DecodedDiagonal` permits decoded off-diagonal signed zeros;
`FloatDiagonalStorage` proves native two-state multiplication and Cholesky
preserve them. `Proofs/DiagonalStages.Prediction` states stored factor,
diagonal-transition/noise and full-observation conditions.
`FloatObservablePrediction` derives every prediction profile, success,
covariance/mean errors `2⁻²⁴` / `2⁻⁴⁶`, retained covariance floor `15/16` and the
reached innovation domain. `FloatObservableInnovation` derives HL, original-R
Cholesky and innovation QR success with error `2⁻²³`, retained floor `29/16`
and factor entry cap `9/4`. Both use the existing runtime operation order and
binary64 bridge. `FloatQRDiagonal` now proves decoded diagonal retention for
any successful QR of two finite diagonal 2×2 blocks, without a magnitude cap.
`FloatObservableDiagonal` derives diagonal prediction/innovation factors with
the existing success/error bounds, given a diagonal incoming factor.
`FloatDiagonalStorage.gram_diagonal` connects these factors to exactly diagonal
Real covariances. `Proofs/CholeskyProfiles.DiagonalSolve` states the larger factor/RHS
domain; `FloatDiagonalSolve` derives both actual substitution passes and error
`2⁻³⁹` against the supplied factor's exact Gram. `FloatObservableGain` derives
the formed RHS and gain profiles from the reached local innovation domain and
a diagonal prior. Actual gain diagonals lie in `[3/8,13/16]`, off-diagonals decode
exactly to zero, and gain error is `2⁻²⁷` against the ideal gain of the same
stored prior and original H/R. The innovation profile radius is tightened to
`9·2⁻³²` by retaining the actual four/three-row QR constants.
`Proofs/DiagonalStages.Mean` admits prior mean cap `19/16` and measurement
cap one. `FloatObservableMean` derives every mean operation/profile, stored-gain
evaluation error `2⁻⁴⁴`, ideal local mean correction error `2⁻²⁵` and returned
mean cap `9/8`. `prediction_correction_domain` derives that whole local domain
from the original prediction/observation/measurement conditions; the prediction
mean cap is tightened to `19/16`. Exact diagonal gain support removes the
dimension factor when propagating gain error through the residual.
`Definitions/DiagonalObservation.josephVariance` specifies scalar Joseph
covariance; `RealObservablePosterior` proves its exact quadratic gain-error
identity and reached ideal variance interval `[15/31,39/38]`.
`Proofs/DiagonalStages.Posterior.localCovarianceRadius` records posterior
QR plus prearray allowance; `FloatObservablePosterior` derives all posterior
arithmetic, the original-R/optimal-gain reference, QR domain at budget `15/8`,
and decoded diagonal preservation. `correction_accuracy_and_bounds` proves
complete `updateUnchecked` success and output validation with covariance/mean
errors `2⁻²⁹` / `2⁻²⁵`, covariance floor `7/16`, diagonal cap `17/16`, and
factor/mean caps `9/8`. The sharp APIs tighten prediction covariance to
`7·2⁻³²` and local correction mean to `9·2⁻²⁹`, retaining older allowances.
`Implementation/Correctness/FullyObservedDiagonalFilterAccuracy` defines static original model bounds,
the incoming/returned native state invariant, and the exact same-word full-step
comparator. `RealObservableCorrection` includes changed-gain correction
sensitivity around the rounded/ideal prediction. `FloatObservableFilter`
derives all validation and reached domains, checked full-step error
`3·2⁻³⁰` / `5·2⁻²⁸`, joint δ=`5·2⁻²⁸`, invariant preservation and successful
strict-PD execution at every finite native prefix. A nonzero identity-dynamics
inhabitant is proved. `FloatObservableInitialization` derives the native
invariant and initial `2⁻⁴²` / zero errors from original dense covariance.
`FloatObservableHorizon` proves every-prefix accumulated errors `5·2⁻³⁰` /
`2⁻²⁴` against the independently propagated original-input Real trace, and
`FloatObservableDenseOutput` adds dense error `2⁻⁴⁸`, exact symmetry and
strict-PD floor `7/16 − 2⁻⁴⁷ ≥ 3/8`. These domains contain no successful
run, reached profile, reference-state bound or unknown output-error premise.

## Completed native results

`FloatCounterexamples` certifies successful compact and subtractive full steps
with covariance exactly `-2^-52`, valid finite output, and a negative quadratic
form, while the same decoded Real input gives a PD posterior. These instantiate
`NegativeQuadraticWitness`, including its strict-domain hypotheses. The compact
fixture also has a proved absolute-error lower bound greater than $2^{-52}$;
the direct Joseph fixture has a certified positive dense output.

`FloatTraceCounterexample` certifies every transition of a nine-step compact
filter on one fixed scalar model. The first eight posterior variances are
positive; the ninth is negative. Every output is finite and valid, and the exact
iterated reference is PD for every horizon. This is delayed failure under repeated
rounded propagation; absolute error need not increase monotonically.

`FloatFactorValidity.successfulStepPositiveDefinite` proves the square-root
success contract. The checked `step` now validates its output before returning it;
validation of finite entries, triangular zeros, and positive native diagonals is
translated to Real using FLARE's comparison theorems. Thus a successful retained
factor denotes a strictly PD exact Gram. This proves an enforced postcondition,
not successful execution on every valid Real input or closeness of QR to exact QR.

`FloatDenseError` bounds the actual ascending, separately rounded native product
and native addition/subtraction, including finite successful execution under the
stated range profiles. `FloatSolveError` transfers FLARE's LDLᵀ residual-based
solve enclosure through the exact adapter; its dimension/conditioning domain is
narrower than the API's accepted domain.

`FloatJosephError.joseph_evaluation_error` composes all five products and both sums
of the actual direct Joseph covariance kernel. `Proofs.ArithmeticProfiles.JosephProfile`
records successful intermediate computations and bounds **operand magnitudes**,
without assuming the desired error conclusion. Its reference uses the stored
prior, noise, observation, and gain; gain and prediction errors are separate.

`FloatMaterialization.materialization_accuracy` bounds optional dense $LL^T$
formation relative to the exact Gram of stored entries. `ErrorPropagation` proves
entrywise propagation through products/sums and a strict-PD margin theorem for
symmetric dense outputs. See [the constants and domains](../results.md).

`FloatGramSymmetry` proves identical off-diagonal words and Hermitian Real
decoding for every successful finite native two-state Gram product, by the
actual ascending two-term schedule. `FloatMaterialization.two_state_accuracy`
derives conversion success, finite shape, unchanged mean and error `≤ 2⁻⁴⁸`
from the retained-state invariant. `Implementation/Correctness/CorrelatedNoiseFilterAccuracy` states the new
relations; `FloatDenseHorizon.initialized_dense_horizon_accuracy` is their
completed original-input witness. It derives retained floor `1/4` and rounded
dense floor `1/4 − 2⁻⁴⁷ > 0` at every finite prefix, covariance error
`≤ 2⁻²⁵ + 2⁻⁴⁸` and mean error `≤ 2⁻²⁵` against the independent ideal trajectory.
There is no native symmetry repair or stronger original-input premise.

`FloatResidualError` proves the shared checked residual loop, final diagonal
division, and a local Cholesky square-root error with a sufficient pivot margin.
`FloatCholeskyFactor` tracks the native column writes and proves whole-factor
Gram backward error under `Proofs.CholeskyProfiles.FactorProfile`.
`FloatCholeskyDomain` derives that profile, successful execution and a `2⁻⁴²`
Gram backward bound from finite symmetric two-state covariance entries with
diagonals in `[1,2]` and off-diagonal magnitude at most `1/4`. It also proves
input/output Gram floors `3/4` and `1/2`, respectively, and checked initialization
with zero mean error. The domain definition is `Implementation/Correctness/InputInterpretation.TwoStateCovarianceDomain`;
[its complete scope](../results.md#two-state-cholesky-from-original-inputs)
is narrower than all mathematically PD inputs.
`FloatCholeskySolve` connects both native substitution passes to their returned
arrays and proves residual/solution bounds against the exact Gram of the supplied
stored factor. Its `Proofs.CholeskyProfiles.SolveProfile` is an a posteriori operand
profile; original-model success and conditioning bounds are separate obligations.
`FloatCholeskySolveDomain.solve_profile` now derives that profile with constants
`32,1/2,2` from finite two-state lower-factor/RHS bounds for two RHS columns.
Its `solve_accuracy` gives error at most `2⁻³⁷` against the stored Gram solve
when that Gram has floor `1/2`, and bounds the solution entries by `1`.
`factor_and_solve_accuracy` composes the original-input Cholesky domain and
compares directly with original `A⁻¹B`, including factorization rounding, with
the same allowance. See [the precise domain](../results.md#two-state-triangular-solves-from-stored-inputs).

`FloatQRFactorDomain` derives the same solve factor domain from two-row native
QR output at budget `2`. A Cholesky noise block derives additional prearray
spectral headroom, giving the innovation Gram floor `1/2` after rounding.
`innovation_factor_and_solve_accuracy` composes QR and substitution success and
profiles; `qr_original_factor_and_solve_accuracy` includes QR discrepancy
against the original stored prearray Gram. Formed prearray energy and RHS bounds
remain caller obligations. See [the bridge scope](../results.md#two-state-qr-factor-to-innovation-solve).

`Proofs/CorrelatedStages.Gain` states a sufficient stored observation/prior-factor
domain, including a bound on the exact stored covariance. `FloatGainDomain`
derives both gain products and profiles, the actual transposed RHS domain, and
gain magnitude `1/3`. `gain_profile` assembles the existing uniform profile
without a gain execution/profile premise; the reached innovation profile and
preserved stored covariance domain remain explicit. See
[the constants and remaining obligations](../results.md#formed-two-state-gain-rhs-and-magnitude).

`Proofs/CorrelatedStages.Innovation` adds original noise diagonal headroom
`≤ 3/2` to that stored gain-input domain. `FloatInnovationDomain` derives the
innovation prearray's energy/rank domain, all innovation/gain profiles, and their
accuracy against original noise plus the exact stored prior Gram. No intermediate
innovation profile remains a premise of the composed theorem. The posterior
result below adds prediction margins; see
[the local stage scope](../results.md#innovation-and-gain-from-a-stored-local-input-domain).

`Proofs/CorrelatedStages.Mean` adds finite two-component vector storage,
predicted-mean cap `9/32` and measurement cap `1`. `FloatMeanDomain` derives
all four `MeanProfile` operations with product masses `8` and sum exponents `2`.
It proves finite output magnitude `≤ 1` and evaluation error `≤ 2⁻⁴⁵` at the
stored gain. `correction_profiles` derives innovation/gain/mean together;
`correction_accuracy` compares with the ideal local Kalman correction using
the original noise and exact stored prior Gram. Its closed allowance
`localMeanRadius` is proved `≤ 2⁻²⁵`, including computed-gain discrepancy.
No ideal gain/residual bound or intermediate profile is assumed in that
statement. See [the local mean theorem](../results.md#mean-correction-from-stored-local-inputs).

`Proofs/CorrelatedStages.Prediction.TransitionInputs` permits transition entries
up to `1/8`, separately from the observation/gain domain. It adds process-noise diagonal
headroom, and bounds the incoming mean by `1`. `FloatPredictionDomain`
derives every `PredictionProfile` field, preserving the actual `[FL,T_Q]`
prearray order. `prediction_accuracy` proves successful validated output,
covariance error `≤ 2⁻²⁵`, mean error `≤ 2⁻⁴⁶`, output mean cap `9/32`,
factor entry cap `2`, covariance entry cap `7/4` and floor `2/3`.
`prediction_correction_domain` turns these bounds plus static measurement
inputs into the full local mean-correction domain. See [the prediction domain](../results.md#prediction-from-stored-local-inputs).

`Proofs/CorrelatedStages.Posterior` adds prediction's exact stored covariance
floor `2/3` and entry cap `7/4`. `PosteriorStructure` proves exact stored-gain
prearray margins. `FloatPosteriorPrearray` derives the four arithmetic profiles,
rounded Gram error `≤ 2⁻³⁸`, floor `1/2` and diagonal cap `63/32`.
`FloatPosteriorDomain` derives all correction profiles, native success, both
local ideal-correction error budgets `≤ 2⁻²⁵`, and returned mean/factor/covariance
caps `1`, `2`, `2`. The covariance is the exact Gram of retained words and is PD.
`prediction_posterior_domain` supplies every local condition after prediction;
the checked-step invariant below composes them. See
[the posterior theorem](../results.md#posterior-qr-from-reached-stored-inputs).

`Implementation/Correctness/CorrelatedNoiseFilterAccuracy` separates static `ModelDomain`, retained-word
`StateInvariant`, original dense `InitializationDomain` and derived arithmetic
`StepParameters`. `FloatFilterInputDomain` proves model validation, every
full-step profile, exact reference environment, checked full-step error budgets
`≤ 2⁻²⁵` and invariant preservation. `initialize_invariant` derives the input
invariant from the original dense covariance with error `≤ 2⁻⁴²` and zero mean
error. `initialized_run_invariant` composes this with the actual trajectory driver
for any finite length and time-varying models, including correlated Q/R.
The prefix theorem proves success/PD/bounded storage; the accumulated accuracy
result below connects it to the independent ideal trajectory. See
[the full original-input statements](../results.md#full-step-accuracy-and-invariant-from-original-inputs).

`ReferenceInvariant` in `Implementation/Correctness/CorrelatedNoiseFilterAccuracy` gives the independent
ideal state's PD covariance, entry cap `2` and mean cap `1`.
`RealFilterInvariant` proves original initialization and exact-step preservation,
then induction through `exactRun`. Exact optimal covariance decrease supplies
the corrected covariance cap. Its `reference_environment` derives all exact
conditioning/magnitude fields at every prefix; no native error or state bound
is substituted for an ideal-trajectory premise. See
[the reference invariant](../results.md#independent-ideal-trajectory-invariant).

`Implementation/Correctness/CorrelatedNoiseFilterAccuracy.HorizonDomain` collects original initialization and
finite-horizon model conditions, with no reached-state/profile/error premises.
`FloatInputHorizon` derives every reached profile and independently proved
reference environment, closes the covariance/mean coefficient expressions at
`uniformBudget = 2⁻²⁵`, and assembles the existing general `HorizonDomain`.
`initialized_horizon_accuracy` proves checked initialization and successful
execution, both accumulated errors `≤ 2⁻²⁵`, stored-state invariant and native/
ideal PD covariance at every finite prefix. Its reference starts at the original
dense covariance and mean. Correlated Q/R are supported by the derived floor
`3/4` and R cap `3/2`; a nonzero/correlated witness inhabits this full domain.
See [the public original-input horizon](../results.md#accumulated-horizon-accuracy-from-original-inputs).

`FloatQRNorm.scaledColumnNorm_accuracy` completes the first local QR bound:
finite nonzero inputs and at most 32 visited entries imply successful maximum
scaling, finite stored normalized entries, and a positive finite norm with an
explicit absolute error. `scaledColumnNorm_range_schedule` proves that extracting
this helper preserved the original range loop, including rejected runs. This
supplies a building block for reflector analysis. The statement and input domain
live in `Proofs.QRProfiles`.

`FloatQRReflector.householderReflector_accuracy` completes the next local bound:
opposite-sign choice and subtraction, sum of squares, positive finite native
sqrt, and in-place normalization. It proves subtraction error at most $2^{-49}$
and component/near-unit error at most $(9k+5)2^{-50}$ (still below $2^{-40}$ for
$k\le32$), relative to the exactly decoded
stored constructed vector. `scaledColumn_reflector_accuracy` derives all local
conditions from finite nonzero original column inputs, for at most 32 distinct
valid indices and a selected first component. The range schedule theorem covers
exceptional operands too.

`FloatQRApplication.applyReflector_accuracy` completes one-column application:
the actual dot, doubling, product/subtraction, and mutable writes succeed on
`ApplicationProfile`, preserve unselected slots, and have entry error at most
$(k+1)2^{-42}M\le2^{-36}M$ against the same stored vector's exact application.
`scaledColumn_applyReflector_accuracy` completes `ColumnApplicationAccuracy`,
deriving all three stages' success from the original local column inputs and
`TargetColumnProfile`, and propagating stored-reflector error into a normalized
constructed-vector comparison with radius at most $2^{-18}M$. The precise budget
is documented in [results.md](../results.md).

`FloatQRFinish.scaledColumn_finish_accuracy` completes `SourceColumnAccuracy`:
the norm, reflector, and checked source-column overwrite succeed from the
original stored input under `SourceColumnProfile`. Its scale lies in
$[2^{-900},2^{900}]$, with at most 32 distinct valid active rows. It proves
finite nonzero diagonal rescaling, the actual native pivot comparison, squared
norm error at most $2^{-37}s^2$, and overwrite error at most $2^{-18}s$ relative
to the same stored reflector's exact action. `finishColumn_range_schedule`
preserves the old product/write/zero loop for all operands and failures, and
`active_range_cons` identifies the original QR active range. The whole-QR
composition and retained-factor sign/copy analysis are completed below.

`FloatQRIteration.applyReflectorColumns_accuracy` completes `ColumnPanelAccuracy`
for a distinct-column list under `ColumnPanelProfile`. The original target column
and exact reference are preserved until that column is visited; the per-entry
radius is independent of the column count. `qrIteration_accuracy` completes
`IterationAccuracy` by composing the norm, reflector, whole trailing panel, and
source finishing calls now used by `gramFactor`. `IterationProfile` describes
finite correctly shaped input, a valid pivot, at most 32 active rows, an active
panel cap $2^{-900}\le M\le2^{900}$, and a source entry of magnitude at least
$2^{-900}$. The result has finite storage, copied prefixes, and selected-panel
error at most $2^{-17}M$ against the exactly unit normalized stored constructed
vector. The stored-vector comparison retains the sharper trailing-column bound.
Range/iteration schedule proofs cover failures too. The twelfth slice below
derives later-pivot profiles from initial inputs for the eight-row domain.
Retained sign/copy conversion and whole-QR Gram error are also completed below.

`FloatQRRetain.retainFactor_accuracy` completes `RetentionAccuracy` for the final
signed transpose/copy stage of `gramFactor`. Its input-only `RetentionProfile`
requires finite stored entries and nonzero decoded diagonals; it has no shape,
dimension-cap or magnitude-headroom premise. Missing reads follow native defaults,
and the nonzero condition excludes a missing diagonal. The theorem derives
successful finite output, correct output size, positive-zero upper triangle,
exact absolute diagonal, exact signed-transpose/Gram identities relative to
`retainedUpper`, and strict PD of the output's exact Gram. `one_mul_value` and
`neg_one_mul_value` prove exact sign multiplication for the full finite binary64
range directly from the rounding model and FLARE canonical unpack/pack results.
Schedule theorems preserve all original values and early rejections. See
[the zero conversion error and scope](#sixth-native-qr-slice-exact-retained-factor-conversion).
The seventh slice below completes whole tall-matrix Gram identification.
The ninth slice completes multi-iteration Gram error under prefix profiles;
the twelfth derives later-pivot domains from supported initial inputs.

`FloatQRTriangular.triangularize_structure` completes `TriangularizationStructure`
conditional on a successful call, finite input, correct storage shape and
width ≤ height. `ProcessedColumns` records assigned positive zeros below the
diagonal in completed columns. Successful checked-write storage lemmas and
`qrIteration_earlierColumn` require no arithmetic error estimate; each iteration
extends the invariant, and `qrIterations_processed` carries it over the actual
ascending list. Extra tall rows consequently contain assigned zeros.
`retainedUpper_gram_eq_full` proves that these omitted rows contribute exactly
zero to the full stored result's column Gram. `gramFactor_structure` completes
`SuccessfulGramFactorStructure`, deriving positive lower output, finite correct
storage, exact full stored QR Gram equality and strict PD from a successful raw
factor call. Its retention nonzero-diagonal profile follows from the actual
successful guard trace. It needs no final factor-validator premise, numerical
magnitude cap or dimension cap. Its success premise remains explicit; it does
not discharge an original-input success domain or bound original-prearray error.
See [the structural scope](#seventh-native-qr-slice-whole-loop-triangular-structure).

`FloatQRGram.qrIteration_orthogonal_accuracy` completes
`IterationOrthogonalAccuracy`, extending the selected-panel estimate to the
whole matrix using prior triangular zeros. Its exact reference embeds the
normalized stored constructed vector with zeros before the pivot;
`OrthogonalStructure.reflect_gram` proves exact column-Gram preservation.
`qrIteration_gram_accuracy` completes `IterationGramAccuracy`, with the review
entry point `FloatErrorBounds.qrIterationGramAccuracy`. It proves successful
finite execution and absolute column-Gram error from the local input profile
plus prior zeros, with radius `iterationGramRadius`. Only active rows contribute;
there is no column-count factor or global magnitude restriction on the copied
prefix. This is one iteration against its incoming stored matrix; the ninth
slice below composes it across the full loop. The twelfth derives the supported
original-input success domain. See
[the explicit radius and domain](#eighth-native-qr-slice-one-iteration-column-gram-error).

`FloatQRComposition.qrIterations_prefix_accuracy` completes `QRPrefixAccuracy`
for any prefix up to the width. `TriangularizationProfile` supplies the local
operand profile for each actual successful prefix, without assuming final
success, final validation or error. The proof derives all prefix executions,
triangular zeros, earlier nonzero diagonal preservation and an accumulated
column-Gram bound. `triangularize_gram_accuracy` completes
`TriangularizationGramAccuracy` and establishes the final `RetentionProfile`.
`gramFactor_accuracy` completes `GramFactorAccuracy`; the public review entry
point is `FloatErrorBounds.qrGramFactorAccuracy`. Its returned finite lower
factor has positive diagonal, strictly PD exact Gram, and error at most
`qrGramRadius columns rows budget` against the exact Gram of the same original
stored prearray. The transpose bridge is exact, retention adds zero error,
and consecutive Gram allowances sum without amplification. The domain still
requires profiles at every actual prefix; the twelfth slice below derives them
from one initial energy/rank and scale condition for up to eight rows. See
[the complete factor bound](#ninth-native-qr-slice-complete-factor-gram-error).

`FloatQRDomain.qrIterations_prefix_enclosure` completes `PrefixEnclosure` from
`InitialGramBounds` and operand profiles only for preceding pivots. It derives
every current entry's squared magnitude bound `S + qrGramRadius` and a remaining
Gram lower bound `α - width * qrGramRadius`. The generalized
`qrIterations_prefix_accuracy_of_profiles` supplies success and error without
conditions on future pivots. Public consequences discharge the panel magnitude
when this fits `M²`, and certify strict PD when the remaining margin is positive.
For up to eight rows, constant budget `M`, initial column energy `M²/2`, and
initial Gram floor `M²/8`, the derived bounds preserve magnitude `M` and Gram
floor `M²/16`. These still require preceding profiles. See
[the prefix domain bounds](#tenth-native-qr-slice-prefix-magnitude-and-spectral-margins).

`FloatQRSourceTail.source_tail_combination` proves exact cancellation of the
processed rows using earlier columns while preserving the active source tail.
`source_tail_energy_lower` derives a quantitative tail-energy floor from the
Gram lower bound. `source_witness_eight` forces an active entry of magnitude
at least `M/16` from Gram floor `M²/16`, prior zeros and nonzero diagonals.
`qrIterations_prefix_source_witness_eight` applies this to the actual prefix
and meets the `2⁻⁹⁰⁰` source floor when `M ≥ 2⁻⁸⁹⁶`. It needs only preceding
profiles, not the next pivot's profile or final success. The twelfth slice below
assembles the complete next profile and closes the initial-input induction. See
[the source-tail witness](#eleventh-native-qr-slice-the-active-source-tail-witness).

`FloatQRInitialDomain.triangularizationProfile_eight` derives all intermediate
profiles by strong induction from `InitialQRDomain`: finite correct storage,
tall dimensions at most eight, budget `2⁻⁸⁹⁶ ≤ M ≤ 2⁹⁰⁰`, column energies
`≤ M²/2`, and column-Gram floor `M²/8`. It yields successful bounded prefix
and full-loop execution through `qrIterations_prefix_accuracy_initial` and
`triangularize_accuracy_initial`. `inputDomain_transpose` converts
`GramFactorInputDomain` on the original row prearray using exact finite native
transpose interpretation. `gramFactor_initial_accuracy` completes
`InitialGramFactorAccuracy`, exported publicly as
`FloatErrorBounds.qrGramFactorInitialAccuracy`: success, finite lower-positive
factor, strictly PD exact Gram with floor `M²/16`, and error against the original
input Gram at most both `qrGramRadius` and `M²/128`. No intermediate profile,
run success or validator is a premise. `identity_input_domain` proves native
identities through dimension eight satisfy the domain with `M = 2`. See
[the precise sufficient domain and limitations](../results.md#initial-input-qr-success-and-error).

`Proofs/SquareRootProfiles.Error` defines `PredictionProfile`, explicit covariance
and mean radii, and `FactorAccuracy`. `FloatPrearray` proves native block copying
and exact block-Gram addition. `FloatSquareRootError.prediction_accuracy` proves
the entire prediction stage's successful validated output and both errors,
including the noise factorization discrepancy. `FloatFactorValidity.factor_validate_complete`
derives executable validation from shape, finiteness and exact lower positivity.
`RealErrorBounds` supplies gain-residual and Joseph gain-perturbation propagation.
The original-input prediction and horizon theorems derive that stage profile
for their documented family. See
[the completed prediction bound](../results.md#prediction-stage-native-prearray-and-mean-accuracy).

`Proofs/SquareRootProfiles.Update` records the innovation, gain, mean and posterior
operand domains and their radii. `FloatSquareRootUpdate.update_accuracy` proves
complete native correction success, validation, covariance and mean error.
`gain_accuracy` compares with the ideal gain and includes both innovation and
numerator error. `Definitions/Theorems/RecursionSensitivity` and `RecursionSensitivity` provide
nonlinear incoming-state propagation constants and completed exact prediction,
gain and correction sensitivity proofs. These are public through `Kalman`.

`Proofs/FilterComposition` defines `StepProfile`, independent
`StepEnvironment` reference bounds and both propagated radii.
`FloatFullFilter.step_accuracy` proves the complete checked native step's
success, output validity and accuracy against an independently supplied ideal
incoming state. `stepWithin` proves the public square-root covariance contract.
Incoming covariance and mean errors are included; no exact gain is assumed.

`FloatFilterInitialization.fromCovariance_accuracy` relates the checked
initializer to the original decoded covariance and mean; its allowance may
seed the horizon rather than changing the comparator to the factor Gram.
`Proofs/FilterComposition.Horizon` defines time-varying native/exact runs,
`HorizonOperands` and budgeted `HorizonDomain`. `FloatFilterHorizon.finite_horizon_accuracy`
proves success, covariance/mean errors and both PD properties at every prefix.
`initialized_horizon_accuracy` also covers initializer-plus-filter execution
against the original decoded covariance, deriving the initial error from its
Cholesky profile.
`Proofs/FilterComposition.Budget` defines explicit two-state allowances;
`FloatFilterBudget.refined_uniform_horizon_accuracy` keeps both errors at most
`2⁻²⁵` on any finite horizon meeting those reached-prefix domains and initial
accuracy budget. The original `1/128` API remains available.
Its coefficient caps are completed kernel proofs. `FloatFilterDomain.uniform_domain_nonempty`
discharges every condition for a reset model at every finite horizon; this is a
simple nonvacuity witness, not a proof of general original-input invariance for
nontrivial dynamics. `refined_uniform_domain_nonempty` also proves that witness
meets the tighter tolerance. All APIs are exported through `Kalman` and required by the
project-wide axiom audit. See [the complete scope](../results.md#full-filter-over-a-finite-horizon).

## Remaining numerical obligations

The square-root full-step comparison is proved under operand profiles. The
conventional covariance full-step bound remains outside this result. Two-state
Cholesky and solve input domains are completed above. The original-input horizon
theorem derives all reached-prefix conditions and accumulated accuracy for a
nontrivial two-state family. Wider dynamics, noise scales and dimensions remain
open, alongside tighter uniform constants.
Rounded dense materialization has those premises derived for the same two-state
original-input family. Generic conversion outside it keeps its own error and
positivity margin, and tiny-factor underflow still refutes universal dense PD.

U-D and information-form Float implementations remain outside the implemented
algorithms; their exact Real interpretations and relevant identities are proved.
Hardware/compiler correspondence with Lean's logical binary64 model remains an
external trust boundary.

## Validation

The exact checks evaluate small prediction, innovation, covariance-form, and
Gram examples. The native executable checks analytic scalar and correlated 2×2
posterior values, 100 repeated steps with a rectangular observation, 400
small-gain covariance/mean steps with alternating measurements, 2,592 checked
steps with varying correlated Q/R, and a 256-step original-input horizon with
seven ideal reference checkpoints reproduced at 120/160 decimal digits. All
257 prefixes include exact dense off-diagonal/mean word checks and an eighth
spectral-floor regression. Six additional dense cases cover correlations,
signed zero, large scales, subnormal products and full underflow. It also
checks the retained signed-zero reset witness, QR scaling,
reflector sign/signed-zero choices, analytic column reflection, inactive storage,
application scale extremes and repeated-index operation order, full-loop
triangular zeros, retained/full stored Gram agreement, later-pivot analytic Grams
and invalid-prior-zero contrasts, complete original-prearray Gram references
at three power-of-two scales, rank rejection, mixed observations with correlated noise, one-step and nine-step roundoff fixtures,
and validation/overflow failures. A tiny positive factor also materializes to a
zero dense covariance through underflow, exercising the factor/dense distinction.
Neither native agreement nor the benign repeated run replaces an error proof.

The larger fully observed diagonal family now has original dense initialization
in `Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.InitializationDomain` and `FloatObservableInitialization`. Original
covariance variances `[1,3/2]` and mean cap one derive checked initialization,
the native invariant and initial covariance/mean errors `2⁻⁴²` / zero against
the original input words. The independent Real initial invariant is also
derived; no native factor or successful run is an original-domain premise.

`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.HorizonDomain` and `FloatObservableHorizon` now complete the
larger family's initialized accumulated accuracy. The original inputs alone
derive every native prefix and covariance/mean errors `5·2⁻³⁰` / `2⁻²⁴` against
the independent matrix `exactRun`. `RealObservableHorizon` derives its original
model mapping and invariant. Identity and near-identity/sign-reversal witnesses
are completed; the separate rounded dense conversion theorem follows.

`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy` and `FloatObservableDenseOutput` complete separately
rounded dense conversion at every observable prefix. The original horizon
domain derives finite output, exact off-diagonal word equality, copied mean
words, covariance/mean errors `5·2⁻³⁰ + 2⁻⁴⁸` / `2⁻²⁴`, and strict-PD floor
`7/16 − 2⁻⁴⁷ ≥ 3/8`. General materialization helpers now require only factor
validity and covariance diagonal cap two, accommodating native mean cap `9/8`.
