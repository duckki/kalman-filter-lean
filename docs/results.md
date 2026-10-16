# Results and numerical guarantees

This is the public reference for completed Real and native numerical results.
Each theorem is a completed proof in `Kalman/Proofs/`; a proposition definition
alone is not a proof. The implementation,
operation order, and original input interpretation are specified in
[paper-and-spec.md](paper-and-spec.md).

## Reading the guarantees

All numerical errors below are **absolute and entrywise** for matrices, or
componentwise for means. Native arrays are decoded exactly into Real values.
The ideal trajectory starts at the original dense covariance and mean and uses
the original finite $F,H,Q,R,z$ words at every step. It is not restarted from
an intermediate rounded state.

Three covariance objects are kept distinct:

- $P_t$: the independently propagated ideal Real covariance.
- $C_t^{\mathrm{factor}}=\mathrm{decode}(L_t)\mathrm{decode}(L_t)^T$:
  the exact covariance denoted by the retained native factor.
- $C_t^{\mathrm{dense}}$: exact decoding of the separately rounded native
  multiplication used to return a dense covariance.

A matrix floor $A\succeq\alpha I$, with $\alpha>0$, establishes strict positive
definiteness. Factor positivity and dense-output positivity are separate claims.

## Exact Real results

The exact specification covers arbitrary finite state and observation dimensions.
The strict full-step domain has positive dimensions, initial $P\succ0$, and
process/measurement covariances $Q,R\succ0$; $F$ may be singular.

| Proof witness | Conclusion |
| --- | --- |
| `RealRecursion.covarianceFormulationsAgree` | Compact, subtractive, and Joseph agree at the optimal gain; compact/subtractive agree at every gain. |
| `RealRecursion.josephPositiveDefinite` | Joseph is strictly PD at any gain when prior and measurement noise are PD. |
| `RealRecursion.stepPositiveDefinite` / `trajectory_posDef` | Every formulation preserves strict PD over one step and every finite time-varying trace. |
| `RealRecursion.informationFormAgrees` | Information-form covariance and mean agree with the covariance update, with inverses justified. |
| `FactorStructure.squareRootStagesAgree` | Exact orthogonal QR stage relations denote prediction and Joseph correction. |
| `FactorStructure` | Lower positive-diagonal factors and positive U-D factors denote PD covariances. |

See [RealRecursion.lean](../Kalman/Proofs/RealRecursion.lean) and
[FactorStructure.lean](../Kalman/Proofs/FactorStructure.lean). These are algebraic
claims; statistical optimality is not part of the current specification.

## Certified native failures

[FloatCounterexamples.lean](../Kalman/Proofs/FloatCounterexamples.lean) proves
actual compact and subtractive full steps return scalar covariance $-2^{-52}$
from the same valid finite words whose exact Real step is PD. The compact
forward error is greater than $2^{-52}$. The direct Joseph output in that
particular fixture is also certified positive.

[FloatTraceCounterexample.lean](../Kalman/Proofs/FloatTraceCounterexample.lean)
certifies every native transition of a fixed-model nine-step compact trace:
eight positive posterior variances, then a negative ninth, while the exact trace
is PD for every horizon. This is delayed loss of positivity; it does not claim
monotone absolute-error growth. Fixture words and equations are recorded in
[the specification](paper-and-spec.md#reproducible-cancellation-fixtures).

## Complete filter guarantees

The complete native theorems cover **the QR square-root implementation** under
two original-input domains. Both use $n=m=2$, correctly shaped finite storage,
initial mean and every measurement bounded componentwise by one, and original
initial/noise covariance diagonals in $[1,3/2]$. Models may vary with time.

**Correlated stable domain:** $|F_{ij}|\le1/8$, $|H_{ij}|\le1/64$; original
initial covariance and $Q,R$ are symmetric, with off-diagonal magnitude at most
$1/4$. Every finite native prefix succeeds, and both retained and ideal
covariances are PD. See
[the original-input horizon theorem](#accumulated-horizon-accuracy-from-original-inputs).

**Fully observed diagonal domain:** $H=I$; $F,Q,R$ and the original initial
covariance are diagonal, with $|F_{ii}|\le1$. This includes identity and
near-identity/sign-reversing transitions. Every finite prefix succeeds and stays
diagonal. The native initial variance interval is $[1,3/2]$; the separate Real
invariant admits the wider interval $[1/2,3/2]$. See
[the initialized observable horizon](#fully-observed-diagonal-accumulated-accuracy-from-original-inputs).

Let $E_P$ bound every covariance-entry difference from $P_t$ and $E_x$ bound
every mean-component difference from the independent ideal mean.

| Domain | Retained-factor $E_P$ | Returned dense $E_P$ | $E_x$ | Returned dense floor |
| --- | --- | --- | --- | --- |
| Correlated stable | $2^{-25}$ | $2^{-25}+2^{-48}$ | $2^{-25}$ | $1/4-2^{-47}>0$ |
| Fully observed diagonal | $5\cdot 2^{-30}$ | $5\cdot 2^{-30}+2^{-48}$ | $2^{-24}$ | $7/16-2^{-47}\ge3/8$ |

These bounds hold at **every prefix of any finite horizon**, including
initialization, and do not grow with the number of steps. No reached arithmetic
profile, successful trace, reference-state bound, or desired output error is an
original-input premise. Higher-order and normal/subnormal terms are included.

Returned dense output is finite, has exactly matching off-diagonal Float words,
and copies mean words unchanged. Symmetry is proved without repair, and PD is
derived from a quantitative retained floor and the materialization error.
The complete witnesses are `FloatInputHorizon.initialized_horizon_accuracy`,
`FloatDenseHorizon.initialized_dense_horizon_accuracy`,
`FloatObservableHorizon.initialized_horizon_accuracy`, and
`FloatObservableDenseOutput.initialized_dense_horizon_accuracy`.

## Scope and trust

The direct Joseph theorem below bounds its covariance-evaluation kernel at a
supplied stored gain. It does not include prediction/gain error or prove a
complete native Joseph horizon. Compact and subtractive have certified failure
examples and shared arithmetic bounds, not the QR accuracy certificate.

General component theorems may use conditional profiles or successful runs;
the two original-input filter domains discharge all of their reached premises.
The runtime API's larger dimension range is not a wider accuracy theorem.
Tiny-factor underflow refutes unconditional PD of rounded dense Gram output.

The foundation is Lean 4.34.1's logical binary64 semantics and the reviewed
FLARE revision recorded in [development.md](development.md#dependencies).
The axiom audit permits only standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`). Completed proofs have no admissions or added project axioms.
Hardware/compiler refinement, statistical consistency, and physical navigation
accuracy are outside these numerical guarantees. The distinction between known
Kalman mathematics and this implementation-specific contribution is discussed
in [the prior-work review](references/prior-formalizations.md).

## Reusable numerical foundation

General entrywise propagation, matrix positivity margins, right-system residual
accuracy, error recurrences, Householder Gram preservation, exact native sign
multiplication, positive square-root residuals, and two-state rounded Gram
symmetry are now proved in FLARE. Kalman retains its specification relations and
small compatibility or native-error adapters; the authoritative general proofs
are in FLARE. [The library assessment](references/floating-point-library-assessment.md)
identifies the imported modules and their domains.

## Reference navigation

- [Public proof interface catalogue](#public-error-statements)
- [Native arithmetic kernels](#native-kernels),
  [Cholesky and solves](#cholesky-residuals-and-triangular-solves), and
  [direct Joseph evaluation](#composed-direct-joseph-evaluation)
- [Initial-input QR success and error](#initial-input-qr-success-and-error)
- [Correlated local stages](#two-state-qr-factor-to-innovation-solve) and
  [original-input accumulated accuracy](#accumulated-horizon-accuracy-from-original-inputs)
- [Conditional full-filter composition](#full-filter-over-a-finite-horizon)
- [Observable exact sensitivity](#fully-observed-diagonal-real-sensitivity),
  [native stages](#native-prediction-and-innovation-at-diagonal-transition-magnitude-one),
  and [dense horizon output](#fully-observed-diagonal-rounded-dense-horizon-output)

## Public error statements

Import `Kalman` for the complete public interface. Exact Real proposition definitions are
grouped by result in `Definitions/Theorems/`, and native accuracy statements in
`Implementation/Correctness/`. Every result statement names its proof witness in its
comment. [The result-file map](project-layout.md#arithmetic-and-proof-interfaces)
identifies the file for each guarantee and the shared-definition exceptions. Importing a
statement module alone does not prove its propositions.

The main closed propositions are listed below. Exact statements use namespace
`Kalman.Definitions.Theorems`; native statements use
`Kalman.Implementation.Correctness`. Those prefixes are omitted here.

- `CovariancePositiveDefiniteness.StepPositiveDefinite` and `JosephPositiveDefinite`.
- `FormulationEquivalence.CovarianceFormulationsAgree`, `InformationFormAgrees`,
  and `SquareRootStagesAgree`. The information-form statement includes both
  covariance and mean; the square-root statement compares represented covariances.
- `RecursionSensitivity.PredictionSensitivity`, `CorrectionSensitivity`,
  `DiagonalStepSensitivity`, `DiagonalJointContraction`, and `DiagonalHorizonContraction`.
- `CovarianceCounterexamples.CompactCanReturnNegativeCovariance` and
  `SubtractiveCanReturnNegativeCovariance`.
- `CorrelatedNoiseFilterAccuracy.InitializedHorizonAccuracy` and
  `InitializedDenseHorizonAccuracy` for the correlated original-input domain.
- `FullyObservedDiagonalFilterAccuracy.InitializedHorizonAccuracy` and
  `InitializedDenseHorizonAccuracy` for the fully observed diagonal domain.

Auxiliary product, sum, residual, Cholesky, solve, and QR statement packages
live with their witnesses in
[`Proofs/FloatErrorBounds.lean`](../Kalman/Proofs/FloatErrorBounds.lean).
They support the main results rather than forming separate headline interfaces.
Definitions needed by the main guarantees live beside those guarantees;
technical profiles and radii stay on the proof side. Conditional composition
contracts are in `Proofs.FilterComposition`. For example, `MatrixProductAccuracy`
uses `Proofs.ArithmeticProfiles.productRadius inner M = inner · 2⁻⁵⁰ · M`; its witness
requires input shapes and `ProductProfile`, not arbitrary arrays.
`JosephCovarianceEvaluation` and `SquareRootFilterProperties` retain the direct Joseph and retained/
materialized covariance guarantees that explain the algorithm comparison.
The named horizon witnesses below package the existing complete theorems without
changing their domains or numerical bounds.

| Proof witness (in `Kalman.Proofs`) | Conclusion and domain |
| --- | --- |
| `RealDiagonalObservation.predict_eq` / `gain_eq` / `update_eq` / `step_eq` | Fully observed diagonal scalar formulas equal the existing matrix specification; all covariance forms covered and inverses justified |
| `RealObservableInvariant.prediction_invariant` / `update_invariant` / `step_invariant` | Real full-observation diagonal domain with $\lvert f\rvert\le1$: prediction variance `[1,3]`, posterior variance `[1/2,1]`, mean cap `1` |
| `RealObservableInvariant.run_invariant` / `horizon_covariance_floor` / `identity_domain_nonempty` | Every Real prefix preserves the invariant and covariance floor `1/2`; identity dynamics inhabit the domain. These are Real theorems |
| `RealObservableSensitivity.gain_difference` / `covariance_difference` / `mean_difference` | Exact rational perturbation identities, including the covariance-dependent gain's contribution to mean error |
| `RealObservableSensitivity.step_sensitivity` | Real fully observed diagonal step: covariance error `≤ (9/25)eP`, mean error `≤ (3/5)eX + (1/2)eP`; nonnegative actual diagonal covariance, bounded reference and common model/measurement |
| `RealObservableSensitivity.joint_step_contraction` / `horizon_contraction` | Covariance weighted by two gives joint contraction `17/20`, including `F=I`; two exact trajectories have joint error `≤ (17/20)^t E₀` at every finite prefix |
| `RealObservableSensitivity.joint_step_with_local_error` / `joint_uniform_budget` | Conditional Real implications: a supplied local joint bound `δ` gives recurrence `δ+(17/20)E` and invariant budget `(20/3)δ`. The native local and initialized-horizon instantiations are listed separately below |
| `FloatDiagonalStorage.multiply_diagonal_two` / `cholesky_diagonal_two` | Actual finite native two-state products and Cholesky preserve decoded diagonal zeros under their stated domains, including either zero sign |
| `FloatDiagonalStorage.gram_diagonal` | Exact Real Gram of a decoded diagonal factor equals the diagonal matrix of its squared diagonal entries; no rounded dense product |
| `FloatQRDiagonal.triangularize_disjoint_two` / `gramFactor_diagonal_two` | Actual successful QR of finite disjoint-support 4×2 columns retains decoded R₀₁ zero; signed retention of two diagonal 2×2 blocks returns a diagonal factor, without a magnitude cap |
| `FloatObservableDiagonal.prediction_innovation_diagonal` / `innovation_accuracy_diagonal` | Original local domains plus a diagonal incoming factor derive successful diagonal prediction/innovation, exact diagonal Real Grams, and the existing local errors/floors; no full correction or horizon claim |
| `FloatObservablePrediction.prediction_profile` / `prearray_domain` | Local stored domain with diagonal $\lvert f\rvert\le1$ derives every prediction profile; actual prearray floor `63/64`, row energy cap `51/16`, QR budget `21/8` |
| `FloatObservablePrediction.prediction_accuracy` / `prediction_innovation_domain` | Native prediction success/valid factor, covariance/mean errors `2⁻²⁴` / `2⁻⁴⁶` against exact local prediction, mean/factor caps `19/16` / `2`, covariance diagonal cap `13/4`, floor `15/16`, and reached innovation domain |
| `FloatObservablePrediction.identity_domain_nonempty` | Native identity-transition/observation inputs inhabit the original local domains; no full correction or horizon conclusion |
| `FloatObservableInnovation.prearray_domain` / `factor_accuracy` | Full-observation HL/R/innovation QR succeed; original-R-plus-stored-P error `2⁻²³`, exact retained floor `29/16`, covariance diagonal cap `39/8`, factor entry cap `9/4` |
| `FloatDiagonalStorage.transpose_diagonal` | Transposing finite native diagonal storage preserves decoded diagonal zeros |
| `FloatDiagonalSolve.solve_profile` / `solve_accuracy` / `solve_diagonal` | Shaped finite diagonal factor with diagonals ≥1 and entry cap `9/4`, RHS cap four: both passes succeed, error `2⁻³⁹` against stored `Gram(L)⁻¹B`; diagonal RHS additionally yields diagonal solution |
| `FloatObservableGain.solve_factor_domain` / `formed_rhs` / `innovation_profile` | Original local innovation domain plus diagonal prior derives larger solve domain and profiles, rounded PHT cap `7/2`, error `2⁻⁴³` against the same prior's exact Gram, and exact diagonal RHS |
| `FloatObservableGain.innovation_radius_cap` | Chosen input-derived innovation profile at QR budget `25/8`: complete original-R-plus-stored-P radius `≤9·2⁻³²`, retaining exact four/three-row QR constants |
| `FloatObservableGain.ideal_gain_diagonal` / `ideal_gain_bounds` | Exact same-stored-prior gain equals scalar `p/(p+r)` and diagonals lie in `[5/13,13/17]` |
| `FloatObservableGain.gain_accuracy` | Actual formed gain solve succeeds, decoded gain is diagonal with diagonals `[3/8,13/16]`, error `≤2⁻²⁷` against original H/R and the same stored prior's ideal gain. No intermediate run/error premise |
| `ErrorPropagation.within_diagonal_mul_right` | Exact diagonal support propagates gain discrepancy through an exact bounded residual with coefficient `Z`, avoiding the inner-dimension factor |
| `FloatObservableMean.convex_mean_bound` / `mean_stages` / `mean_profile` | Stored diagonal gain `[3/8,13/16]`, prior mean cap `19/16`, measurement cap one: all four native operations/profiles derived, output mean cap `9/8`, evaluation error `2⁻⁴⁴` at the same stored gain |
| `FloatObservableMean.correction_accuracy` | Original local innovation, diagonal prior and vector inputs derive gain and mean profiles/runs, returned mean cap `9/8`, and local ideal correction error `2⁻²⁵`. No run/error premise; this local theorem compares the same stored prior, while the separate horizon theorem below uses an independent trajectory |
| `RealObservablePosterior.joseph_gain_difference` / `joseph_gain_accuracy` | Exact scalar Joseph difference is `(p+r)(k−p/(p+r))²`; gain error `2⁻²⁷` contributes at most `2⁻⁵⁰` on the reached variance/noise intervals |
| `FloatObservablePosterior.prearray_accuracy` / `prearray_domain` | All native KH/sub/WL/KTR profiles/runs derived; prearray error `2⁻³⁶` includes original-R Cholesky and gain discrepancy. Exact rounded-prearray floor `15/32` and cap `17/16` derive posterior QR budget `15/8` |
| `FloatObservablePosterior.factor_accuracy` | Original local innovation domain and diagonal prior derive finite positive diagonal QR factor, decoded diagonal support, strict-PD exact covariance floor `7/16`, diagonal cap `17/16`, factor cap `9/8` and local covariance error `2⁻²⁹` |
| `FloatObservablePosterior.correction_accuracy_and_bounds` | Original local innovation/diagonal/vector inputs derive `updateUnchecked` success, returned validation, covariance/mean error `2⁻²⁹` / `2⁻²⁵` against the ideal correction of the same stored prior and original H/R/z, with returned factor/mean caps `9/8`. The separate horizon theorem below composes accuracy against an independent trajectory |
| `FloatObservablePrediction.prediction_accuracy_sharp` | Same derived native prediction and returned margins with covariance/mean errors `7·2⁻³²` / `2⁻⁴⁶`; older `2⁻²⁴` allowance remains available |
| `FloatObservableMean.mean_accuracy_sharp` / `FloatObservablePosterior.correction_accuracy_and_bounds_sharp` | Same local correction with sharpened mean allowance `9·2⁻²⁹`; covariance allowance stays `2⁻²⁹` |
| `RealObservableCorrection.update_sensitivity` | Full observation with both prior variance floors `15/16`, R diagonals `[1,3/2]`, exact reference mean cap `9/8`: covariance/mean coefficients `2/5` and `8/13,17/30`, including gain changes |
| `FloatObservableFilter.step_accuracy_and_invariant` | Original model and stored-state domain derive checked full-step success, covariance/mean errors `3·2⁻³⁰` / `5·2⁻²⁸` against the same incoming state's ideal full step, joint δ=`5·2⁻²⁸`, diagonal strict-PD exact covariance and returned native invariant |
| `FloatObservableFilter.run_invariant` / `identity_domain_nonempty` | Every finite native prefix succeeds and preserves diagonal strict-PD covariance floor `7/16` and stored caps; a nonzero identity-dynamics domain inhabitant is proved. Independent ideal-trajectory accuracy is supplied by the separate initialized horizon theorem below |
| `FloatObservableInitialization.initialize_invariant` / `exact_initial_invariant` / `identity_domain_nonempty` | Original dense diagonal covariance `[1,3/2]` and finite mean cap one derive checked initialization, native invariant, covariance/mean errors `2⁻⁴²` / zero against the original covariance/mean words, and independent Real initial invariant; signed nonzero-mean identity covariance is an inhabitant |
| `RealObservableHorizon.model_diagonal` / `model_domain` / `run_invariant` | Original stored model equals the source full-observation diagonal specification, and original dense initialization/models derive the independent ideal trace invariant and covariance floor `1/2` |
| `FloatObservableHorizon.step_accumulated_accuracy` / `initialized_horizon_accuracy` | Original dense initialization and original time-varying models alone derive every native prefix, retained invariant, both PD covariances, and uniform errors `5·2⁻³⁰` / `2⁻²⁴` against one independent ideal trajectory |
| `FloatObservableHorizon.identity_domain_nonempty` / `near_identity_domain_nonempty` | Identity and native `diag(1023/1024,−1)` dynamics with original dense covariance and signed nonzero means inhabit the complete accuracy domain for every finite horizon |
| `FloatMaterialization.two_state_accuracy_of_diagonal_cap` | Factor validity and Gram diagonal cap two alone derive native dense conversion error `2⁻⁴⁸`, finite output, copied mean words, exact off-diagonal word agreement and Hermitian decoding, without a mean magnitude premise |
| `FloatObservableDenseOutput.materialization_positive` / `initialized_dense_horizon_accuracy` | Original observable horizon inputs derive every rounded dense prefix, covariance/mean errors `5·2⁻³⁰ + 2⁻⁴⁸` / `2⁻²⁴`, and strict-PD dense floor `7/16 − 2⁻⁴⁷ ≥ 3/8`; native factor and independent ideal covariance also remain PD |
| `FloatObservableMean.prediction_correction_domain` | Original prediction/observation domains, diagonal incoming factor and bounded finite measurement derive successful prediction and the whole reached local mean-correction domain, including mean cap `19/16` |
| `FloatGramSymmetry.multiply_gram_two_symmetric` / `multiply_gram_two_hermitian` | Every successful finite native two-state Gram has identical off-diagonal words and Hermitian Real decoding; no symmetry repair or PD premise |
| `FloatMaterialization.two_state_accuracy` | Stored-state invariant derives materialization success, finite shape, covariance error `≤ 2⁻⁴⁸` and unchanged mean words |
| `FloatDenseHorizon.initialization_covariance_floor` / `step_covariance_floor` / `run_covariance_floor` | Initialization and original model/state bounds derive retained covariance floor `1/4` at every finite prefix |
| `FloatDenseHorizon.materialization_positive` | Stored invariant and retained floor derive successful dense conversion and dense floor `1/4 − 2⁻⁴⁷ > 0`, with symmetry/error premises discharged |
| `FloatDenseHorizon.initialized_dense_horizon_accuracy` | Original-input horizon domain alone derives every dense prefix: success, finite shape, exact off-diagonal word agreement, unchanged mean, PD floor and covariance/mean errors `≤ 2⁻²⁵ + 2⁻⁴⁸` / `2⁻²⁵` against the independent ideal trajectory |
| `FloatFilterInitialization.fromCovariance_accuracy` | Checked covariance-to-factor conversion, valid storage, initial covariance error and zero mean error, under the Cholesky profile |
| `FloatCholeskyDomain.cholesky_accuracy` | Original-input two-state Cholesky success, finite lower-positive factor, exact Gram floor `1/2` and error at most `2⁻⁴²`; no execution or intermediate-profile premise |
| `FloatCholeskyDomain.fromCovariance_accuracy` | Checked initialization from that covariance-entry domain, with covariance error at most `2⁻⁴²` and zero mean error; other model/state validation remains explicit |
| `FloatCholeskySolveDomain.solve_profile` | Both two-state substitution passes, finite storage, row masses and the uniform `32,1/2,2` solve profile derived from stored factor/RHS bounds |
| `FloatCholeskySolveDomain.solve_accuracy` | Error at most `2⁻³⁷` against the supplied factor's exact Gram solve, and output magnitude at most `1`, with a `1/2` spectral floor |
| `FloatCholeskySolveDomain.factor_and_solve_accuracy` | Original-input covariance factorization and solve both succeed; error at most `2⁻³⁷` against original `A⁻¹B`, including Cholesky rounding |
| `FloatQRFactorDomain.factor_domain_of_qr` | Original two-row prearray domain at budget `2` derives the QR output's stored-factor solve domain |
| `FloatQRFactorDomain.innovation_factor_and_solve_accuracy` | Noise factor derives innovation spectral headroom; prearray/RHS domains imply QR and both solves succeed, with error `≤ 2⁻³⁷` against the returned factor Gram |
| `FloatQRFactorDomain.qr_original_factor_and_solve_accuracy` | Includes QR rounding in an error cap `≤ 2⁻²⁰` against the original stored prearray Gram solve |
| `FloatGainDomain.formed_rhs` | Stored observation/factor/covariance bounds derive both products, their profiles, discrepancy `≤ 5·2⁻⁴⁶` and the transposed RHS domain |
| `FloatGainDomain.formed_gain` | Conditioned stored innovation factor and formed RHS derive solve success, solve error `≤ 2⁻³⁷` and gain magnitude `≤ 1/3` |
| `FloatGainDomain.gain_profile` | Existing innovation profile plus the stored input domain derive all fields of the uniform gain profile; innovation energy and prior-factor domain preservation remain explicit |
| `FloatInnovationDomain.prearray_domain` | Original noise and stored observation/prior-factor bounds derive innovation QR shape, finite storage, row-energy and rank conditions |
| `FloatInnovationDomain.innovation_and_gain_profiles` | Every innovation/gain profile field and stage run is derived from the local stored-input domain |
| `FloatInnovationDomain.innovation_and_gain_accuracy` | Innovation and gain discrepancy against original noise/model and the exact stored prior Gram, with explicit stage radii and no intermediate-profile premise |
| `FloatMeanDomain.mean_stages` / `mean_profile` | Four native mean operations/profiles derived from stored vector/matrix bounds; finite output magnitude `≤ 1` and error `≤ 2⁻⁴⁵` at the same stored gain |
| `FloatMeanDomain.correction_profiles` | Innovation, gain and mean profiles derived together from the local input domain; no intermediate profile or execution premise |
| `FloatMeanDomain.ideal_mean_operand_bounds` | Original noise floor `3/4`, ideal gain magnitude `≤ 1/6` and ideal residual magnitude `≤ 2` derived locally |
| `FloatMeanDomain.correction_accuracy` / `local_mean_radius_cap` | Mean discrepancy from the ideal local Kalman correction, including gain error, bounded by the closed `Proofs.CorrelatedStages.Mean.localMeanRadius ≤ 2⁻²⁵` |
| `FloatMeanDomain.input_domain_nonempty` | Local domain admits nonzero observation/mean, correlated prior and endpoint measurements |
| `FloatPredictionDomain.prediction_profile` | Every Cholesky/product/mean/QR prediction profile derived from original local process-noise, transition and stored-state bounds |
| `FloatPredictionDomain.transition_product` / `transition_gram_bound` | Original transition cap `1/8` derives the native FL product and its Gram energy from the incoming covariance cap; includes rounded product error |
| `FloatPredictionDomain.prearray_margins` / `factor_output_bounds` | Actual `[FL,T_Q]` prearray floor `11/16` and diagonal cap `27/16`; returned stored covariance floor `2/3`, entry cap `7/4` and solve factor domain |
| `FloatPredictionDomain.prediction_accuracy` / `local_covariance_radius_cap` | Successful validated prediction with covariance error `≤ localCovarianceRadius ≤ 2⁻²⁵`, mean error `≤ 2⁻⁴⁶` and returned correction headroom |
| `FloatPredictionDomain.prediction_correction_domain` | Predicted output meets the complete `Proofs.CorrelatedStages.Mean.TwoStateDomain`, given only original local prediction/static correction inputs |
| `FloatPredictionDomain.input_domain_nonempty` | Nonzero transition/observation, correlated initial factor, endpoint initial mean and measurements witness the combined local family |
| `PosteriorStructure.prearray_reference_bounds` | Exact stored-gain Joseph prearray floor `20/39` and diagonal cap `251/128` |
| `FloatPosteriorPrearray.arithmetic_stages` / `prearray_domain` | All four native posterior arithmetic stages derived from stored operands; prearray Gram error `≤ 2⁻³⁸`, QR floor `1/2` and diagonal cap `63/32` |
| `FloatPosteriorDomain.prediction_posterior_domain` / `input_domain_nonempty` | Prediction derives all posterior input margins from original local inputs, including a nonzero/correlated witness |
| `FloatPosteriorDomain.correction_profiles` | All innovation/gain/mean/posterior profiles derived together with no intermediate execution/profile premise |
| `FloatPosteriorDomain.posterior_output_bounds` | QR retained factor meets the solve factor domain and exact covariance entry cap `2` |
| `FloatPosteriorDomain.correction_accuracy_and_bounds` | Complete local correction succeeds; covariance and mean error `≤ 2⁻²⁵`, PD exact covariance and returned caps for next prediction |
| `FloatFilterInputDomain.input_validate` / `prediction_domain` | Static original model bounds and stored-state invariant derive validation and the complete prediction input domain |
| `FloatFilterInputDomain.step_profile` / `step_environment` | All full-step arithmetic profiles/constants and exact reference conditioning/magnitudes derived from original inputs |
| `FloatFilterInputDomain.initialize_invariant` | Original dense initialization succeeds, has covariance error `≤ 2⁻⁴²` and zero mean error, and establishes the retained-state invariant |
| `FloatFilterInputDomain.step_accuracy_and_invariant` | Checked full step succeeds, preserves the invariant and has covariance/mean error `≤ 2⁻²⁵` against an exact full step from the incoming stored state |
| `FloatFilterInputDomain.run_invariant` / `initialized_run_invariant` | Every finite native prefix succeeds and preserves bounded PD exact covariance from only original input conditions; no accumulated accuracy claim |
| `FloatFilterInputDomain.input_domain_nonempty` | Nonzero transition, correlated original process/initial covariance and endpoint mean witness the dense-input family |
| `RealFilterInvariant.update_covariance_decrease` | Exact optimal Joseph correction removes a PSD covariance term |
| `RealFilterInvariant.initial_invariant` / `step_invariant` / `run_invariant` | Independent original-dense Real trajectory remains PD with covariance/mean entry caps `2`/`1` at every finite prefix |
| `RealFilterInvariant.prediction_bounds` / `reference_environment` | Ideal prediction/gain/residual headroom and every independent reference environment derived from original inputs |
| `FloatInputHorizon.propagated_radius_caps` | Derived correlated-noise environment and native profile constants preserve accumulated covariance/mean budget `2⁻²⁵` |
| `FloatInputHorizon.reached_profile` | Every reached full-step profile and its constants derived from original inputs and the preserved state invariant |
| `FloatInputHorizon.initialized_horizon_accuracy` | Original dense initialization and original time-varying model bounds alone give success, both accumulated errors `≤ 2⁻²⁵`, native/ideal PD covariance and stored-state invariant at every finite prefix |
| `FloatInputHorizon.domain_nonempty` | Nonzero transition and correlated Q, R and original initial covariance inhabit the full accuracy domain for any finite horizon |
| `FloatInputHorizon.boundary_domain_nonempty` | Positive and negative F entries at the widened `1/8` cap inhabit that same original-input horizon domain with correlated Q/R |
| `FloatSquareRootError.prediction_accuracy` | Native prediction success, validated output, covariance and mean radii |
| `FloatSquareRootUpdate.update_accuracy` | Complete measurement correction including gain error, both noise/prearray discrepancies and all mean operations |
| `FloatFullFilter.step_accuracy` | Checked full-step success and covariance/mean errors against an independently supplied exact prior, including incoming discrepancies |
| `FloatFullFilter.stepWithin` | Completed original public square-root covariance comparison from the same initial factor |
| `FloatFilterHorizon.initialized_horizon_accuracy` | Complete initializer-plus-filter execution and accuracy against the original decoded covariance/mean; initializer error seeds the horizon budget |
| `FloatFilterHorizon.finite_horizon_accuracy` | Every time-varying finite prefix succeeds and meets both budgets; represented and ideal covariances are PD, under `HorizonDomain` |
| `FloatFilterBudget.uniform_horizon_accuracy` | Both absolute errors at most `1/128` for every prefix of any finite horizon under `UniformHorizonDomain` |
| `FloatFilterBudget.tight_uniform_horizon_accuracy` | Earlier `2⁻²⁰` interface retained, with initial errors at most `2⁻²⁰` |
| `FloatFilterBudget.refined_uniform_horizon_accuracy` | Both absolute errors at most `2⁻²⁵`, with the same stage allowances and initial errors at most `2⁻²⁵`; represented and reference covariances remain PD |
| `FloatFilterDomain.uniform_domain_nonempty` / `supported_horizon` | Fully discharged reset-model domain and its full-horizon accuracy/PD result |
| `FloatFilterDomain.refined_uniform_domain_nonempty` | The same reset model meets every condition of the tighter horizon theorem |

Every error below is **absolute and entrywise**: the inequality holds for every
matrix entry, or every visited array entry. $A,B,L,K$ denote exact Real decoding
of the stored native arrays, not automatically the ideal filter's corresponding
quantities. Correct storage shapes are explicit in the product and solve APIs;
the Joseph statement concerns its covariance kernel with a supplied gain.

| Public proof witness in `Kalman.Proofs.FloatErrorBounds` | Proved conclusion | Required domain and reference |
| --- | --- | --- |
| `matrixProductAccuracy` | $\lvert \widehat C_{ij}-(AB)_{ij}\rvert \le k2^{-50}M$; execution succeeds with finite, correctly shaped output | Finite stored operands; correct shapes; $k\le32$; every dot-product absolute term mass is at most $M$; $2^{-1022}\le M\le2^{990}$ |
| `arraySumAccuracy` | Addition/subtraction error at most $2^{E-52}$; execution succeeds with finite output | Equal array sizes, finite operands, exact stored-operand result magnitude at most $2^E$, $-1022\le E\le1022$ |
| `residualAccuracy` | Ordered $b-\sum a_tc_t$ error at most $e_k=k2^{-48}M$; execution succeeds and is finite | At most 32 terms; finite operands; $\lvert b\rvert +\sum\lvert a_tc_t\rvert +2^{-1022}\le M\le2^{990}$ |
| `residualDivisionAccuracy` | $\lvert xd-(b-\sum a_tc_t)\rvert \le r_k$ after the native residual loop and division; execution succeeds and is finite | Residual profile; finite diagonal $0<\delta\le d$, $\lvert d\rvert \le D$; $(M+e_k)/\delta\le2^{1000}$ |
| `choleskyDiagonalAccuracy` | $\lvert d^2-p_0\rvert \le c_k$ for the computed diagonal; both pivot checks succeed | Residual profile for the diagonal row and strict exact residual margin $e_k<p_0$ |
| `choleskyGramAccuracy` | $\lvert (LL^T-A)_{ij}\rvert \le c_n+r_n$ for the actual returned factor | Successful native run, symmetric finite input, correct storage, and `FactorProfile`; diagonal floor and quotient domain as below |
| `choleskySolveAccuracy` | $\lvert X_{ij}-((LL^T)^{-1}B)_{ij}\rvert \le n(1+nD)r_n/\alpha$ | `SolveProfile` for both successful passes; correct finite storage; $(LL^T-\alpha I)\succeq0$, $\alpha>0$; reference is the stored factor's exact Gram |
| `ldlSolveAccuracy` | Solution error in column $j$ at most $\frac{n}{3/16}\sum_i\mathrm{residualBound}(i,j)$; execution succeeds with finite output | $n\le12$, stored coefficient magnitude $\le1024$, $(A-\frac3{16}I)\succeq0$, finite correctly shaped arrays, RHS magnitude $\le2^B$ for $0\le B\le512$ |
| `josephCovarianceAccuracy` | $\lvert \widehat J_{ij}-J(P,H,R,K)_{ij}\rvert \le e_J$; all five products and both sums are covered | `JosephProfile` records successful computations and operand budgets; $e_J$ is the public `Proofs.ArithmeticProfiles.josephRadius`; reference uses the same stored gain, with separate entry bounds on $P,I-KH,K$ |
| `FloatJosephDomain.stored_input_accuracy` | All covariance-kernel operations succeed with finite 2×2 output and entrywise error at most $2^{-34}$ | Stored finite $P,H,R,K$ entry bounds $2,1,3/2,1$; no intermediate execution or profile premise; same stored gain comparator |
| `qrGramFactorInitialAccuracy` | Execution succeeds with finite lower-positive $L$; exact $LL^T\succeq(M^2/16)I$ is PD; $`\lvert(LL^T-AA^T)_{ij}\rvert\le G_{d,n}(M)\le M^2/128`$ | Original finite $n\times d$ array, $n\le d\le8$, $2^{-896}\le M\le2^{900}$, row energies $\le M^2/2$, $AA^T\succeq(M^2/8)I$; no run or intermediate profile assumption |
| `factorMaterializationAccuracy` | Dense $LL^T$ formation error at most $n2^{-50}M$; checked output is valid | Valid retained factor, $1\le n\le32$, finite storage, Gram dot-product mass $\le M$, $2^{-1022}\le M\le2^{990}$ |

`FloatQRInitialDomain.gramFactor_initial_refined_accuracy` additionally proves
the smaller cap $M^2/2^{25}$ on the same original QR input domain, preserving
native success, finite lower-positive storage and the $M^2/16$ spectral floor.
The earlier $M^2/2^{20}$ interface and $M^2/128$ public contract remain available.

For the Cholesky rows, let $u=2^{-53}$ and

$$e_n=n2^{-48}M,\qquad
r_n=e_n+D2^{-50}\left(\frac{M+e_n}{\delta}+2^{-1022}\right),\qquad
c_n=e_n+(2u+u^2)(M+e_n).$$

The profiles require $n\le32$, positive stored diagonals at least $\delta>0$,
the quotient budget $(M+e_n)/\delta\le2^{1000}$, and row term-mass budgets of the
residual kind above. For factorization, $D$ bounds the diagonal magnitude; for
substitution, $D$ bounds every factor entry. The underflow allowance is explicit.
These are conservative proved allowances; no tightness claim is made.

For example, a 32-term matrix product has a bound $2^{-45}M$, about
$2.84\times10^{-14}M$, **when its profile holds**. $M$ bounds absolute term mass,
not the final product entry. Cancellation can make the result much smaller than
$M$, so this is not a blanket relative-error claim.

`denseCovariancePositiveDefinite` additionally proves that a symmetric output is
PD when its reference satisfies $(P-\alpha I)\succeq0$ and its proved entrywise
error $\varepsilon$ satisfies $n\varepsilon<\alpha$. It does not supply symmetry
or that spectral margin. A certified example has $L=2^{-600}$ and a PD exact Gram
$2^{-1200}$, yet its rounded dense materialization is zero.


## Detailed numerical reference

### Native kernels

`FloatDenseError.multiply_entrywise_accuracy` proves successful finite execution
of the actual ascending dot-product loop with separately rounded products/sums.
For an inner dimension $k\le32$, let

$$M_{ij}\space \ge\space \sum_{t=0}^{k-1}|\mathrm{decode}(a_{it})\mathrm{decode}(b_{tj})|,
\qquad 2^{-1022}\le M_{ij}\le2^{990}.$$

For finite operands, its entrywise error is

$$|\mathrm{decode}(\widehat C_{ij})-(AB)_{ij}|
\space \le\space k\cdot 2^{-50}M_{ij}.$$

The lower allowance includes gradual underflow; there is no assumption that
every exact term is normal. The theorem is transferred from FLARE
`Matrix.Multiplication.multiply_entrywise_accuracy` through the native error
adapter. Missing array entries are totalized to zero; public filter comparisons
also require the appropriate storage shapes.

`FloatDenseError.add_accuracy` and `sub_accuracy` prove the actual checked array
operations succeed and remain finite when every exact sum/difference of stored
operands has magnitude at most $2^E$, with $-1022\le E\le1022$. Their absolute
entrywise allowance is $2^{E-52}$. This is meaningful through cancellation and
does not assume a relative error with a nonzero exact result.

`FloatSolveError.solve_accuracy` transfers FLARE's actual LDLᵀ solve enclosure:
dimension $n\le12$, finite operands, coefficient magnitude at most 1024, a proved
floor $(A-\frac3{16}I)\succeq0$, and right-hand-side magnitude at most $2^B$ with
$0\le B\le512$. For the actual factors and substitution arrays, the error in
column $j$ is at most

$$\frac{n}{3/16}\sum_i\mathrm{residualBound}(i,j).$$

`residualBound` is FLARE's explicit arithmetic allowance computed mathematically
from the actual intermediate magnitudes, not an assumed solution-error bound.
This enclosure is relative to the **stored coefficient and right-hand-side
matrices**. The PSD floor includes symmetry of the stored coefficient matrix;
the dense Kalman API does not enforce this floor or repair innovation symmetry.
An ideal innovation being PD does not automatically establish this profile.


### Cholesky residuals and triangular solves

`FloatResidualError.residual_accuracy` covers the shared native loop that starts
from a stored value and subtracts separately rounded products in the specified
index order. Its core is definitionally equal to FLARE
`Matrix.Substitution.subtractProducts`; `subtractProducts_schedule` also proves
that adapting the error type preserves every original finite check, including
on rejected runs. Runtime imports do not include FLARE's proof extraction.

For at most $k\le32$ visited indices, finite operands, and

$$|b|+\sum_t|a_tc_t|+2^{-1022}\le M\le2^{990},$$

the native residual succeeds, remains finite, and differs from
$b-\sum_t a_tc_t$ by at most $e_k=k2^{-48}M$. The same ordered kernel is used
by Cholesky and both triangular substitution passes.

`FloatResidualError.divideResidual_accuracy` includes the final native division.
For a finite diagonal $d$ with $0<\delta\le d$ and $|d|\le D$, require
$(M+e_k)/\delta\le2^{1000}$. The returned value $x$ satisfies

$$\left|xd-\left(b-\sum_t a_tc_t\right)\right|\le
r_k=e_k+D2^{-50}\left(\frac{M+e_k}{\delta}+2^{-1022}\right).$$

This is a residual bound; it includes subnormal operands and gradual underflow.
The division bridge uses FLARE `Binary64.Division.div_error_relative`, which
proves finite native division with the stated quotient domain. It is applied
**after** the residual subtractions, as required by this implementation.

`FloatResidualError.choleskyDiagonal_accuracy` proves a local Cholesky pivot
result. If the exact stored-operand residual $p_0$ satisfies $e_k<p_0$, the
positive-pivot and positive-square-root checks succeed. With $u=2^{-53}$, the
returned diagonal $d$ obeys

$$|d^2-p_0|\le e_k+(2u+u^2)(M+e_k).$$

The square-root bound comes from FLARE `Binary64.Sqrt.sqrt_error_nearest`,
including positive subnormal inputs. The strict residual-margin lemma is local;
it does not itself supply a success domain from the original covariance alone.

`FloatCholeskyFactor.cholesky_equations` tracks every column write and proves
that each cell of the returned factor equals its actual residual/square-root or
residual/division computation on the final stored prefixes. It also proves the
returned shape and exactly zero upper triangle, without assuming the Cholesky
equations as a postcondition.

`Proofs.CholeskyProfiles.FactorProfile` records a successful native factorization,
symmetry of the decoded input, finite factor storage, the row term-mass budgets,
the diagonal floor/bound, and the quotient domain above. It contains no assumed
factor error. `FloatCholeskyFactor.factor_backward_error` proves the whole-factor
entrywise enclosure

$$|(LL^T-A)_{ij}|\le
c_n+r_n,\qquad c_n=e_n+(2u+u^2)(M+e_n),\quad u=2^{-53}.$$

Here $A$ is the exact decoding of the stored input array. Symmetry is needed
to extend the lower-triangle analysis to the full matrix, since the kernel reads
only the lower triangle. This is an **a posteriori** backward-error theorem;
successful execution and operand budgets from a general original covariance
domain are not conclusions of this theorem. The two-state domain below derives
those profiles.
Noise and initialization factors can use this bound once their profiles have
been established.

`FloatCholeskySolve.forward_equations` and `backward_equations` prove the storage
connection: every successful returned entry equals its native row kernel
evaluated on the appropriate earlier/later rows of the final array. The proof
tracks every array write, rather than presuming the substitution equations.

`Proofs.CholeskyProfiles.SolveProfile` records the two actual successful passes,
lower positive factor structure, finite factor entries, term-mass profiles for
their returned row operands, diagonal floor $\delta$, entry bound $D\ge0$, and
$(M+e_n)/\delta\le2^{1000}$ for $n\le32$. It is an **a posteriori** profile,
with no assumed residual or solution-error conclusion. It does not supply those
operand bounds or successful execution from an arbitrary original model.

Under that profile, `FloatCholeskySolve.solve_residual` proves, entrywise,

$$|(LL^T X-B)_{ij}|\le(1+nD)r_n.$$

For a supplied spectral floor $(LL^T-\alpha I)\succeq0$, $\alpha>0$,
`FloatCholeskySolve.solve_accuracy` proves

$$|X_{ij}-((LL^T)^{-1}B)_{ij}|\le\frac{n(1+nD)r_n}{\alpha}.$$

The Real residual-to-solution theorem is FLARE
`Analysis.NumericalBounds.residual_entrywise_bound`. Here $L$ denotes the
**exact decoding of the stored factor**, and $B$ the stored right-hand side.
The complete update theorem below propagates innovation-factor QR error and
right-hand-side formation error when comparing the computed gain to its ideal
value.


### Two-state Cholesky from original inputs

[`Proofs/CholeskyProfiles.lean`](../Kalman/Proofs/CholeskyProfiles.lean)
defines `InputDomain.TwoStateDomain` using only the original stored array: exactly four finite
binary64 entries, equal **decoded** off-diagonal values, diagonal values in
$[1,2]$, and off-diagonal magnitude at most $1/4$. Both signed zeros are allowed,
including opposite zero words across the diagonal. These numerical constants
are sufficient project operating choices; they are not necessary conditions for
Cholesky and are not attributed to a paper. No positive-definiteness premise,
successful execution, factor, pivot condition or intermediate profile is assumed.

[`FloatCholeskyDomain`](../Kalman/Proofs/FloatCholeskyDomain.lean) proves:

- `input_lower_bound` and `input_positive`: the original exact decoded covariance
  satisfies $A\succeq(3/4)I$ and is strictly PD.
- `input_symmetric`: the native initializer's symmetry guard accepts those finite
  values, including mixed signed zeros.
- `cholesky_profile`: the actual native kernel succeeds with finite correctly
  shaped $L$, an exactly zero upper triangle, diagonal values in $[3/4,2]$ and
  $|L_{10}|\le1/2$. Every field of `FactorProfile 2 a l 8 (1/2) 2`, including its
  execution equation, is derived.
- `cholesky_accuracy`: the exact Gram of that returned factor is strictly PD,
  satisfies $LL^T\succeq(1/2)I$, and meets
  $$|(LL^T-A)_{ij}|\le c_2+r_2\le2^{-42}
    \approx2.27\times10^{-13}.$$
- `fromCovariance_accuracy`: when the model metadata has two states and its
  ordinary model/state validation succeeds, checked initialization succeeds,
  preserves the original mean, and satisfies `FactorAccuracy 2⁻⁴² 0` against the
  **original decoded dense covariance and mean**. No assumed Cholesky run remains.
- `correlated_domain_nonempty`: the domain premises are proved for the original
  array `#[1.0, 0.25, 0.25, 2.0]`.

The schedule theorem exposes the actual two-column computation: checked square
root of $A_{00}$, checked division $A_{10}/d_0$, separately rounded square and
subtraction for the second pivot, then its checked square root. The first
diagonal's squared-error estimate gives $d_0\ge3/4$; the exact quotient is at most
$1/3$ in magnitude. FLARE's native division enclosure at exponent $-1$ bounds
the stored off-diagonal by $1/2$. Thus the exact second residual is at least
$1-1/4=3/4$, exceeding the residual roundoff allowance. Both pivot checks and all
finite-result guards follow. The exact input floor and whole-factor error then
give the output Gram floor. Imported arithmetic and finite-comparison bounds
use the same pinned logical-native binary64 bridge described above; no new
hardware or compiler refinement is asserted.

This bound concerns exact Real multiplication of the **stored factor entries**.
Optional native dense materialization has its additional rounding/symmetry/PD
argument [completed for the horizon family](#rounded-dense-output-over-the-original-input-horizon).
The 54 native regressions exercise diagonal endpoints/interiors,
both correlation endpoints and all four signed-zero pairings, comparing a
rounded reconstruction directly with the original covariance and checking
the initializer's storage. They supplement the universal domain proof.

The profile constants match the existing two-state **noise-factor allowances**,
and this initializer error fits well inside the $2^{-25}$ horizon budget.
The domain's $3/4$ input floor does not establish the uniform horizon theorem's
separate measurement-noise floor $1$. The stored-input solve theorem below derives two-state
success from its stored factor/RHS conditions; discharge of other stage domains
and their preservation for nontrivial dynamics remain separate obligations.


### Two-state triangular solves from stored inputs

[`Proofs/CholeskyProfiles.lean`](../Kalman/Proofs/CholeskyProfiles.lean)
defines conditions on the **stored operands entering the solve**. `FactorDomain`
requires four finite lower-factor entries, a zero decoded upper entry, diagonals
at least $1/2$, and all entry magnitudes at most $2$. `RightHandSideDomain`
requires four finite entries, each with magnitude at most $1/8$: this local domain has
two states and **two RHS columns**. Either signed zero is accepted. No native
run, intermediate array, row profile or approximation is a premise. These
constants are sufficient project choices, not general requirements for a solve.

[`FloatCholeskySolveDomain`](../Kalman/Proofs/FloatCholeskySolveDomain.lean)
exports the proof witnesses:

- `solve_profile`: both native substitution passes succeed with correctly shaped
  finite outputs. Forward entries are bounded by $3$ and backward entries by
  $30$. All fields of `SolveProfile 2 2 l b y x 32 (1/2) 2`, including execution,
  are derived from the input operands.
- `solve_accuracy`: if the supplied factor's exact Gram additionally satisfies
  $LL^T\succeq(1/2)I$, the actual two-pass output obeys

  $$
  |\widehat X_{ij}-((LL^T)^{-1}B)_{ij}|\le2^{-37}
  \approx7.28\times10^{-12},\qquad |\widehat X_{ij}|\le1.
  $$

  The spectral floor is a conditioning premise about the stored factor, not an
  execution/error premise. The reference uses the original stored RHS values.
- `factor_domain_of_cholesky`: every factor returned from the preceding
  original-covariance Cholesky domain satisfies these factor conditions.
- `factor_and_solve_accuracy`: on that original covariance domain and the RHS
  domain above, **both factorization and solve succeed**, with finite correctly
  shaped output, and

  $$
  |\widehat X_{ij}-(A^{-1}B)_{ij}|\le2^{-37},\qquad |\widehat X_{ij}|\le1.
  $$

  Here $A$ and $B$ decode the **original input arrays**. Cholesky error is
  included; the exact comparator is not replaced by the rounded factor's Gram.

The proof follows the existing operation order, with ascending forward rows,
descending backward rows, ascending RHS columns, separately rounded products
and subtractions, and a final checked division for each entry. The sufficient
per-column enclosures are $|y_0|\le1/2$, $|y_1|\le3$, $|x_1|\le7$ and
$|x_0|\le30$. These give all row masses below $32$ and all quotient range
conditions. The imported binary64 residual/division bounds and their native
schedule bridge are unchanged. In particular,
$$r_2\le25\cdot 2^{-46},\quad
 \frac{2(1+2\cdot2)r_2}{1/2}\le2^{-37}.$$
For the original covariance, its $3/4$ spectral floor, the Cholesky allowance
$2^{-42}$ and the proved output bound $1$ give residual radius
$(1+2\cdot2)r_2+2\cdot 2^{-42}$; multiplying by $2/(3/4)$ still fits $2^{-37}$.
These finite allowances retain factorization and substitution error.

The 162 stored-factor boundary/interior/signed-zero native regressions compare
solutions with an independent analytic 2×2 Gram inverse. The preceding 54
covariance-domain cases now also exercise factor-and-solve against the analytic
inverse of the original covariance. These executable checks supplement the
universal Lean theorems; they do not supply a spectral floor for every tested
factor. Runtime code is unchanged.

This discharges two-state solve profiles from quantitative stored input bounds.
It does not establish those factor/RHS bounds for every reached Kalman prefix.
The Cholesky-plus-solve theorem derives its conditioning floor from the original
covariance; the innovation QR analysis establishes its own floor and operands.
The original-input horizon theorem below derives and preserves these conditions
for its nontrivial two-state operating family.


### Composed direct Joseph evaluation

`Proofs.ArithmeticProfiles.JosephProfile` records the actual intermediate arrays and
successful operation equations of `covarianceUnchecked .joseph`. Its profiles
bound their operand magnitudes as above; they contain no presumed approximation
to the desired answer. This is an a posteriori profile, not a theorem supplying
uniform bounds from an arbitrary original model.

Let $P,H,R,K$ be the exact decoding of the **stored** inputs to this kernel,
$W=I-KH$, and choose entrywise magnitude bounds $B_P,B_W,B_K\ge0$. Let
$d_{KH},d_{WP},d_1,d_{KR},d_2$ be the native product allowances, and $s_W,s_+$
the subtraction/addition allowances. The proved radius is

$$
\begin{aligned}
e_W&=s_W+d_{KH},\\
e_{WP}&=d_{WP}+n e_W B_P,\\
e_1&=d_1+n\big(e_{WP}B_W+nB_WB_Pe_W+e_{WP}e_W\big),\\
e_2&=d_2+m d_{KR}B_K,\\
e_J&=s_++e_1+e_2.
\end{aligned}
$$

`FloatJosephError.joseph_evaluation_error` proves successful execution of the
specified kernel and entrywise error at most $e_J$ relative to
$WPW^T+KRK^T$. All five products and both sums are included. The gain may be
rounded: the reference uses that same stored gain. Comparing against the ideal
Kalman gain requires solve conditioning and error propagation in addition.

`FloatJosephDomain.covariance_stages` now derives the complete profile from
stored operands on an explicit two-state/two-measurement domain. Original
arrays have four finite entries each, with entry magnitudes
$|P_{ij}|\le2$, $|H_{ij}|\le1$, $|R_{ij}|\le3/2$, and
$|K_{ij}|\le1$. No intermediate run, profile, or desired error is assumed.
Correlated inputs, full observation $H=I$, and signed gains are permitted. Neither positivity nor
optimality of the supplied gain is required for this evaluation bound.

All five products have derived mass allowance 256. The subtraction and final
addition use exponents 2 and 8, respectively; the reached magnitude caps for
$W,WP,WPW^T,KR,KRK^T$ are $4,17,137,4,9$. Substituting the actual
profile constants into the complete radius above gives
$e_J\le2^{-34}$ (approximately $5.9\times10^{-11}$).
`FloatJosephDomain.stored_input_accuracy` proves native kernel success,
finite output of the correct shape, and this absolute entrywise error.
The result statement and domain are in
`Implementation/Correctness/JosephCovarianceEvaluation.lean`; a nonzero-gain,
nonzero-observation, correlated-prior witness proves the domain is inhabited.

This is a completed stored-gain covariance-evaluation result, not a complete
Joseph filter certificate. Prediction, the actual LDLᵀ gain solve, mean error,
returned covariance structure, and accumulated independent-trajectory accuracy
remain to be composed and discharged for a Joseph operating invariant.
Forty native cases compare against an independent exact-rational expanded
Joseph polynomial in `Tests/JosephReference.py`; the `10^-14` regression
tolerance is separate from the proved allowance. They include correlated
priors/noise, full observation, boundary and non-dyadic gain words, signed zeros,
and a subnormal gain.
The runtime schedule, symmetry handling, and pinned floating-point foundation
are unchanged.

`ErrorPropagation.within_mul` proves, for operand errors $e_A,e_B$ and ideal
entry bounds $B_A,B_B$, the product propagation allowance
$k(e_AB_B+B_Ae_B+e_Ae_B)$. Addition, subtraction, transpose, and enclosure
composition are also proved. These are mathematical composition tools; they
do not themselves instantiate a uniform Kalman horizon bound.
`finite_horizon_bound` composes a certified recurrence $e_{t+1}\le Le_t+\delta$
with its recursively defined budget. `nonexpansive_budget` proves the linear
allowance $e_0+t\delta$ for $0\le L\le1$; no Kalman sensitivity constant is
silently assumed.


### Retained factors and optional dense output

`FloatFactorValidity.successfulStepPositiveDefinite` proves that every successful
checked square-root step returns finite, lower triangular storage with positive
decoded diagonal, hence an invertible factor and a PD **exact Gram denotation**.
The output validation enforces this postcondition. It does not prove a success
domain, QR backward stability, or accuracy against the exact filter.

`FloatMaterialization.materialization_accuracy` applies the native multiplication
bound to optional $LL^T$ materialization. For $1\le n\le32$ and a common dot-product
mass $M$ in the same range, its entrywise error relative to the exact stored-factor
Gram is at most $n2^{-50}M$.

`FloatMaterialization.two_state_accuracy` derives successful finite
materialization from `Implementation.Correctness.CorrelatedNoiseFilterAccuracy.StateInvariant`, with entrywise error
**at most $2^{-48}$** relative to the exact retained Gram and unchanged mean
words. `two_state_dot_mass` derives $M=2$ from the covariance diagonal cap,
using $2|ab|\le a^2+b^2$. This is tighter than using factor-entry caps alone.
`FloatGramSymmetry.multiply_gram_two_symmetric` proves that the separately
computed off-diagonal Float words agree exactly on every successful finite
two-state Gram product, including signed zero and gradual underflow. Its
Hermitian corollary applies to exact Real decoding. The proof unfolds the
actual checked ascending two-term schedule and proves multiplication
commutativity in Lean 4.34.1's native Float logical model. There is no symmetry
repair or extra runtime operation.

`ErrorPropagation.posDef_of_error_margin` gives the additional dense guarantee:
if the reference satisfies $(P-\alpha I)\succeq0$, the rounded output is symmetric,
and the entrywise radius $e$ satisfies $ne<\alpha$, the rounded output is PD.
This theorem retains both symmetry and a quantitative margin as explicit premises.
`FloatDenseHorizon.initialized_dense_horizon_accuracy` now discharges those
conditions for the original-input horizon family. Its completed dense result
is [stated below](#rounded-dense-output-over-the-original-input-horizon).
`Implementation.Correctness.CorrelatedNoiseFilterAccuracy.DenseHorizonAccuracy` names the relation; the theorem supplies its witness.

The certified underflow example stores $L=2^{-600}$. Its exact Gram is PD, but
native dense materialization rounds $2^{-1200}$ to zero. Thus output-factor PD
cannot be promoted to unconditional rounded-dense PD.


### Initial-input QR success and error

`FloatErrorBounds.qrGramFactorInitialAccuracy` completes the public
`QRInitialGramFactorAccuracy` statement. It needs only
`Proofs.QRProfiles.GramFactorInputDomain n d a M`, stated on the **original
stored prearray** $A\in\mathbb R^{n\times d}$:

- Correct storage size $nd$ and finite binary64 entries, decoded exactly.
- $n\le d\le8$ and $2^{-896}\le M\le2^{900}$.
- Each original row has energy $\sum_j A_{ij}^2\le M^2/2$.
- Original Gram floor $AA^T\succeq(M^2/8)I$.

These are sufficient quantitative conditions, not a promise for every full-rank
matrix. No intermediate operand profile, prefix execution, final success,
validator result or error bound is a hypothesis. Empty dimensions are included;
strict PD in dimension zero is vacuous. For nonempty inputs, the scale margin
makes the Gram floors strictly positive.

The theorem guarantees that the actual `gramFactor n d a` returns a finite,
correctly shaped lower factor $L$ with positive diagonals and

$$
LL^T\succeq\frac{M^2}{16}I\succ0,\qquad
\left|(LL^T-AA^T)_{ij}\right|
\le G_{d,n}(M)\le\frac{M^2}{128}.
$$

The comparison uses the same finite native input values as the reference.
Both the accumulated allowance `qrGramRadius d n (fun _ => M)` and its uniform
cap are exported in the conclusion. With $k_p=d-p$,

$$
G_{d,n}(M)=\sum_{p=0}^{n-1}
k_p\left[2(1+2k_p)M e_{k_p}(M)+e_{k_p}(M)^2\right],\qquad
e_k(M)=\mathrm{iterationRadius}(k,M).
$$

`FloatQRInitialDomain.iterationProfile_of_previous` assembles all next-pivot
conditions from initial bounds and preceding profiles. Storage and finiteness
come from preceding native success; the prefix enclosure supplies the magnitude cap,
and the active-tail proof supplies the active source witness. Strong induction in
`triangularizationProfile_eight` eliminates those preceding-profile assumptions.
`qrIterations_prefix_accuracy_initial` and `triangularize_accuracy_initial`
therefore supply success and error for every prefix and the full tall loop.
The tall-input contract is `InitialQRDomain h w a M`, with $w\le h\le8$,
column energy at most $M^2/2$, and column-Gram floor $M^2/8$.

`inputDomain_transpose` proves that the actual finite native transpose satisfies
that tall domain. FLARE's exact `transpose_storage` and `transpose_matrix`
bridges introduce no rounding allowance. `gramFactor_initial_accuracy` then
combines the loop bound with exact retention. The output Gram floor follows
from the input floor and the entrywise perturbation bound:
$M^2/8-nG_{d,n}(M)\ge M^2/16$. Retention adds zero error; successive Gram
allowances sum without additional amplification.

With dimension-sensitive norm/reflector and head-only annihilation accounting,
`qrGramRadius_le_eight_refined` proves $G_{d,n}(M)\le M^2/2^{25}$.
`gramFactor_initial_refined_accuracy` concludes this smaller error together with
the same successful finite lower-positive factor, PD Gram and $M^2/16$ floor.
Its original-input domain is unchanged. The previous $M^2/2^{20}$ and $M^2/128$
interfaces remain proved. For local consumers, `constructedApplicationRadius_le_tight`
and `sourceWriteRadius_le_tight` give $2^{-32}M$ caps, and
`iterationRadius_le_tight` gives $2^{-31}M$, for at most 32 active terms.

`identity_input_domain` is a completed nonvacuity theorem: every stored native
identity of dimension $n\le8$ meets the original-input domain with $M=2$.
It reuses FLARE's exact `JacobiInitialization.identity_size`, `identity_finite`
and `identity_matrix` lemmas, valid for every dimension. They concern exact
storage and decoding, not a new arithmetic error estimate or a changed
library/native bridge.

The runtime algorithm, operation order, exceptional-value behavior, positive-zero
writes and sign policy are unchanged. No new external library or native-model
bridge is introduced; the reviewed FLARE relative square/add bounds are reused.
These conservative project constants mechanize the selected program's analysis;
they are not claimed as sharp classical backward-stability constants or new
Kalman theory. The theorem concerns the raw QR factor kernel. It excludes errors
in constructing a Kalman prearray, prior/noise factorization, gain and mean
calculation, and recursion over time. Strict PD concerns the **exact Real Gram of
the stored factor**; rounded dense materialization requires a separate margin,
proved for the two complete filter domains below.
At the scale endpoints an actual native dense Gram can underflow or overflow.

Native regressions retain the correlated eight-row and extreme-scale cases and
add scaled identities in dimensions zero through eight at scales
$1,2^{-897},2^{899}$. They exercise all eight pivots and both budget endpoints,
checking success, finite positive diagonals and the independent exact identity
factor reference without a dense Gram product. Regression agreement supplements
the kernel proofs; hardware/compiler refinement remains outside their scope.


### Two-state QR factor to innovation solve

Proof witnesses are in
[`FloatQRFactorDomain.lean`](../Kalman/Proofs/FloatQRFactorDomain.lean).
For a two-row prearray `A` satisfying `GramFactorInputDomain 2 d A 2`, with
`2 ≤ d ≤ 8`, row energies at most `2` and original Gram floor at least `1/2`,
`factor_domain_of_qr` derives the solve's stored-factor domain from its native
QR output: finite shape, zero upper entry, diagonals in `[1/2,2]`, and all entry
magnitudes at most `2`. The second diagonal bound uses a quadratic form of the
exact lower-positive Gram; checking only its diagonal entries would not suffice.

The generic retained Gram floor is `1/4`. `qr_solve_floor` requires extra
**original prearray** headroom `AAᵀ ⪰ (2/3)I` and includes the QR entrywise
error `≤ 2⁻²³` to derive `LLᵀ ⪰ (1/2)I`. This is a separate conditioning
argument, not a consequence of positivity alone.

`innovation_prearray_lower` derives that extra headroom for `[T_R, HL]` when
`T_R` is the native Cholesky output of the documented two-state covariance
input domain. Its Gram has floor at least `3/4 − 2·2⁻⁴²`, and the other stored
block contributes an exact PSD Gram. This theorem does not assume the rounded
`HL` equals its exact product. The separate prearray domain still supplies
finite storage and row-energy bounds.

For two finite RHS columns bounded entrywise by `1/8`,
`qr_factor_and_solve_accuracy` derives QR and both substitution runs, all solve
profiles, solution magnitude `≤ 1`, and error `≤ 2⁻³⁷` against `(LLᵀ)⁻¹B`.
`innovation_factor_and_solve_accuracy` obtains the needed spectral headroom
from the noise block. `qr_original_factor_and_solve_accuracy` additionally
includes QR perturbation and proves error `≤ 2⁻²⁰` against **original**
`(AAᵀ)⁻¹B`. This convenience cap is deliberately conservative; it does not
replace the sharper stage radii in the `2⁻²⁵` uniform filter theorem.

The original prearray consists of stored assembled blocks. Comparing with
original noise covariance and the ideal observation product requires their
existing error propagation proofs. The later gain and original-input horizon
theorems derive the formed `HL` energy and RHS conditions. No runtime
arithmetic or imported binary64 model bridge changes here. The native regressions
exercise 108 QR-plus-solve cases with correlated noise, three observation blocks
and nonzero/signed-zero RHS inputs, using independent analytic 2×2 inverses.


### Formed two-state gain RHS and magnitude

[`CorrelatedStages.Gain.TwoStateDomain`](../Kalman/Proofs/CorrelatedStages.lean)
defines finite 2×2 stored observation `H` and prior factor `L`, with
`|Hᵢⱼ| ≤ 1/64`, `|Lᵢⱼ| ≤ 2`, and exact stored covariance
`|(LLᵀ)ᵢⱼ| ≤ 2`. This is a domain on **reached stored operands**; the original
model/initial-state invariant must still establish it at each filter prefix.

Proof witnesses are in
[`FloatGainDomain.lean`](../Kalman/Proofs/FloatGainDomain.lean).
`formed_rhs` derives both mass-eight product profiles and actual successful
native runs for `HL` and `L(HL)ᵀ`. It includes both rounded product errors:

$$
|\widehat{P H^T}_{ij}-(LL^TH^T)_{ij}| \le 5\cdot \mathrm{productRadius}(2,8)
=5\cdot2^{-46}.
$$

Every formed RHS entry is at most `1/16 + 5·2⁻⁴⁶ < 1/8` in magnitude.
Native transpose copies the finite entries exactly, deriving the existing
`RightHandSideDomain`. The covariance-level estimate is essential: multiplying
the loose individual factor bounds twice would exceed the target RHS cap.

`formed_gain` combines this domain with an innovation factor satisfying the
stored solve domain and exact Gram floor `1/2`. It derives both solve passes
and their full profiles, preserves solution error `≤ 2⁻³⁷` against that stored
Gram solve, and proves every returned gain entry has magnitude `≤ 1/3`.
`gain_profile` assembles `GainProfile` from an existing two-state innovation
profile at QR budget `2`, the original noise Cholesky input domain, and this
stored observation/prior-factor domain. Its fields retain uniform constants
`productMass=8`, `solveMass=32`, `solveFloor=1/2`, `solveBound=2`, `gainBound=1`;
the stronger actual `1/3` bound is a separate conclusion. The existing
`FloatSquareRootUpdate.gain_accuracy` supplies the comparison with the ideal
Kalman gain, including observation-product and noise/innovation rounding.

`input_domain_nonempty` proves a nonzero observation and correlated prior
factor belong to the stored domain. The native regressions add 162 formed-gain
cases using independent covariance/innovation formulas, positive diagonal
boundaries, signed-zero upper entries, and nonzero observations at the admitted
cap. Runtime arithmetic and the FLARE bridge are unchanged. The local
innovation, mean, prediction and posterior domains are discharged below. The
original-input horizon theorem derives and preserves every reached profile.


### Innovation and gain from a stored local input domain

[`CorrelatedStages.Innovation.TwoStateDomain`](../Kalman/Proofs/CorrelatedStages.lean)
combines the two-state dimensions, the preceding stored observation/prior-factor
domain, and the original noise Cholesky domain with a stricter noise diagonal
cap `3/2`. Noise diagonals therefore lie in `[1,3/2]`, and off-diagonal
magnitude is at most `1/4`. This local stage domain permits correlated noise.
The earlier `UniformStepParameters` require `R=I`; the original-input horizon
theorem uses different coefficient bounds and admits correlated R.

Proof witnesses are in
[`FloatInnovationDomain.lean`](../Kalman/Proofs/FloatInnovationDomain.lean).
`observation_block_bound` includes the rounded `HL` product error and bounds
every stored entry by `1/8`. `prearray_domain` derives finite shape and the
full original QR input domain for `[T_R, HL]` at budget `2`. Each row's energy
is at most `3/2 + 2⁻⁴² + 1/32 < 2`; Cholesky noise error and the exact PSD
observation-block Gram derive the rank floor. No prearray energy, successful
QR run or intermediate QR profile is a premise.

`innovation_profile` consequently derives every `InnovationProfile` field,
including actual Cholesky, product and QR executions, with the existing uniform
parameters `8,1/2,2,8,2,1/64,2`. `innovation_and_gain_profiles` also derives
the complete gain profile and actual gain magnitude `≤ 1/3`, without an
intermediate innovation or gain profile assumption.

`innovation_and_gain_accuracy` applies the existing error propagation proofs
to those derived profiles. Its innovation reference uses the **original decoded
noise covariance** and the exact Gram of the stored prior factor; its gain
reference is the corresponding ideal Kalman gain. The explicit allowances are
`innovationRadius innovation` and `gainRadius gain (3/4)`, accounting for noise
factorization, both rounded products, QR and both solve passes. The full-step
and horizon theorems below also include prior-factor error relative to the
independent ideal trajectory.

`input_domain_nonempty` proves the local domain contains a nonzero observation
and correlated prior with identity noise. Another 108 native cases cover noise
diagonal endpoints, both signs of correlation, formed-block energy, RHS and
gain bounds, and an independent gain formula using original noise. The later
posterior and full-step results derive the remaining domains and preserve the
state invariant. Runtime arithmetic and the imported native-model bridge are
unchanged.


### Mean correction from stored local inputs

[`CorrelatedStages.Mean.TwoStateDomain`](../Kalman/Proofs/CorrelatedStages.lean)
extends the preceding local innovation/gain domain with finite vectors of
length two, predicted-mean components bounded by `9/32`, and measurement
components bounded by `1`. Its domain has no arithmetic execution/profile,
desired error or ideal gain/residual bound as a premise. These are sufficient
operating bounds with slack, not universal Kalman assumptions.

Proof witnesses are in
[`FloatMeanDomain.lean`](../Kalman/Proofs/FloatMeanDomain.lean).
`mean_stages` derives the actual four-stage schedule:

| Operation | Derived profile | Stored output magnitude |
| --- | --- | --- |
| `projected = Hμ` | Product mass `8` | `≤ 1/64` |
| `residual = z−projected` | Sum exponent `2`, subtraction | `≤ 33/32` |
| `increment = K·residual` | Product mass `8` | `≤ 45/64` |
| `mean = μ+increment` | Sum exponent `2`, addition | `≤ 1` |

Every operation succeeds, and each returned vector has length two and finite
entries. `mean_profile` assembles the existing `MeanProfile` with those
parameters. `correction_profiles` derives innovation/gain/mean together from
the combined input domain. The stronger actual gain cap `1/3` is used to
derive headroom, while the existing uniform gain-profile cap remains `1`.

The **same-stored-gain evaluation error** is at most `2⁻⁴⁵` (about
`2.84×10⁻¹⁴`) against the exact expression `μ + K(z−Hμ)`, where each operand
denotes its exactly decoded stored word. Writing `e = productRadius 2 8 = 2⁻⁴⁶`
and `s = sumRadius 2 = 2⁻⁵⁰`, the propagated allowance is
`s + e + 2·(1/3)·(s+e) ≤ 2⁻⁴⁵`. This comparison excludes gain error.

The **ideal local correction error** is the separate `correction_accuracy`
theorem. `ideal_mean_operand_bounds` derives original-noise floor `3/4`,
ideal gain magnitude `≤ 1/6`, and ideal residual magnitude `≤ 2`. Consequently
the existing gain/mean error proof applies without those additional premises.
The reference uses original noise/model/measurement and the exact Gram of the
stored prior factor. Let `eI` be the existing innovation radius specialized to
parameters `8,1/2,2,8,2,1/64,2`, and let

```
eK = 2 · (5·divisionRadius 2 32 (1/2) 2 + 5·e + 2·eI) / (3/4).
localMeanRadius = s + e + 2·(2·eK + (1/6)·(s+e) + eK·(s+e)).
```

This closed allowance is defined in `Proofs.CorrelatedStages.Mean` and proved
`≤ 2⁻²⁵` (about `2.98×10⁻⁸`), retaining higher-order terms and the binary64
normal/subnormal allowance. The theorem bounds every mean component by this
allowance and also proves finite output magnitude `≤ 1`.
It does not assume an exact computed gain or silently replace original noise
by its stored Cholesky Gram.

`input_domain_nonempty` certifies nonzero observation, correlated prior,
predicted mean `[1/16,−1/16]`, and measurement `[1,−1]`. The native regressions
add 216 stored-gain evaluation cases, including the wider `±9/32` endpoints,
signed zero, subnormal inputs,
and cancellation, plus 324 actual mean corrections with original
correlated noise and independently computed ideal-gain references. These
regressions are executable checks; they do not replace the Lean proof.
Posterior profiles and trajectory invariant preservation are proved below.
This local `2⁻²⁵` result does not by itself establish accumulated accuracy
against the independently propagated original-input ideal trajectory.


### Prediction from stored local inputs

[`CorrelatedStages.Prediction.TwoStateDomain`](../Kalman/Proofs/CorrelatedStages.lean)
states a sufficient stored prediction domain: state dimension two, transition
entries `≤ 1/8` in magnitude, factor entries and exact stored covariance entries
`≤ 2`, finite incoming mean of length two with components `≤ 1`, and original
process noise in the Cholesky domain with diagonals capped by `3/2`.
`CorrectionInputs` separately records the two-state observation/noise/measurement
bounds from the preceding local correction domain.

Proof witnesses are in
[`FloatPredictionDomain.lean`](../Kalman/Proofs/FloatPredictionDomain.lean).
`transition_product` derives the FL mass-eight profile, execution and error.
`transition_gram_bound` uses the exact identity
`(FL)(FL)ᵀ = F(LLᵀ)Fᵀ` and incoming covariance cap `2`, bounding the original
transition-block Gram entries by `1/8`. It then includes the rounded FL error
`2·(2·e·(1/2)+e²)`. Separate factor-entry bounds alone would give row energy
`1/2` and exhaust the QR budget after adding the noise cap and roundoff.
`prearray_domain` derives every QR input condition in the actual `[FL,T_Q]`
order from these bounds and original Q. `prearray_swap_domain` remains a
separate exact block-order lemma. `mean_stage` derives the actual `Fμ` product
and output magnitude `≤ 9/32` from exact bound `1/4` plus rounding slack.
`prediction_profile` derives all fields of `PredictionProfile` with constants
`8,1/2,2,8,8,2,1/8,2`; no intermediate execution/profile is assumed.

`prearray_margins` retains a stronger exact prearray floor `11/16` and diagonal
cap `27/16`. `factor_output_bounds` includes QR error and derives returned
covariance floor `2/3`, covariance entry cap `7/4`, factor diagonal floor `1/2`
and factor entry cap `2`. The covariance entry cap follows from its diagonal
bound and the PSD two-coordinate Cauchy inequality, not from a separately
rounded dense Gram. These margins leave room for posterior QR analysis.

`prediction_accuracy` derives actual `predictUnchecked` success and a validated
factor, including finite correctly shaped mean/factor storage. The reference is
ideal Real prediction from the exact incoming stored-factor Gram and mean,
using **original decoded process noise Q**. Its covariance radius is

```
localCovarianceRadius = qrGramRadius 4 2 (fun _ => 2)
  + 2·(2·e·(2·(1/8)·2) + e²)
  + diagonalRadius 2 8 + divisionRadius 2 8 (1/2) 2,
where e = productRadius 2 8 = 2⁻⁴⁶.
```

`local_covariance_radius_cap` proves that allowance `≤ 2⁻²⁵`; the mean error
is `≤ 2⁻⁴⁶` (about `1.42×10⁻¹⁴`). Higher-order terms and the binary64
normal/subnormal allowance remain included. Incoming state discrepancy against
an independent ideal trajectory is the separate full-step sensitivity term.

`prediction_correction_domain` combines the returned mean/factor/covariance
bounds with `CorrectionInputs` to prove the entire reached
`Proofs.CorrelatedStages.Mean.TwoStateDomain`. Thus innovation, gain and mean profiles can
be derived after prediction with no additional predicted-state bound premise.
`input_domain_nonempty` certifies nonzero transition/observation, a correlated
incoming factor, mean `[1,−1]` and endpoint measurements. Another 648 native
cases cover process-noise endpoints and both signs of correlation, transition
and mean endpoints, output validation, independent scalar prediction formulas,
and execution of the subsequent correction. They are regressions, not a proof
that posterior QR preserves the next step's domain.
The posterior result below derives the remaining profiles and returned bounds.
The checked-step invariant and accumulated original-input horizon accuracy are
composed below.


### Posterior QR from reached stored inputs

[`CorrelatedStages.Posterior.TwoStateDomain`](../Kalman/Proofs/CorrelatedStages.lean)
adds prediction's exact stored covariance floor `2/3` and entry cap `7/4` to
the local mean-correction domain. All values decode the same finite input words.
[`FloatPosteriorDomain.prediction_posterior_domain`](../Kalman/Proofs/FloatPosteriorDomain.lean)
derives this reached domain from original prediction/static correction inputs;
`input_domain_nonempty` supplies a nonzero transition and correlated-state witness.

The completed local theorems use these project constants:

| Quantity | Proved bound |
| --- | --- |
| Ideal gain magnitude | `7/48` |
| Gain error against the ideal local gain | `2⁻²⁰` |
| Actual stored gain magnitude | `1/6` |
| Exact stored noise-factor Gram entries | `25/16` |
| Exact `[ (I−KH)L, KT_R ]` Gram floor / diagonal cap | `20/39` / `251/128` |
| Rounded prearray Gram discrepancy at the same stored gain | `2⁻³⁸` |
| Rounded prearray Gram floor / diagonal cap | `1/2` / `63/32` |
| Returned exact covariance entries / factor entries / mean magnitude | `2` / `2` / `1` |
| Covariance and mean discrepancy against the ideal local correction | each `2⁻²⁵` (about `2.98×10⁻⁸`) |

[`PosteriorStructure.prearray_reference_bounds`](../Kalman/Proofs/PosteriorStructure.lean)
uses row absolute masses `97/96` for `I−KH` and `1/3` for `K`. The sharper
stored-gain bound leaves sufficient energy without an optimal-gain contraction
identity. [`FloatPosteriorPrearray.arithmetic_stages`](../Kalman/Proofs/FloatPosteriorPrearray.lean)
derives successful native `KH`, identity subtraction, `WL` and `KT_R` and their
mass-eight products/exponent-two subtraction. `prearray_domain` proves QR's
initial energy/rank conditions after their actual rounding errors.

`FloatPosteriorDomain.correction_profiles` derives innovation, gain, mean and
posterior profiles together. `correction_accuracy_and_bounds` concludes native
`updateUnchecked` success, validated lower-positive output, strictly PD exact
stored-factor covariance, both error budgets and all returned caps above. No
successful intermediate run, profile or gain/error bound is an input premise.
The local error reference is the ideal Joseph correction using **original decoded R**,
original H/z and the exact incoming stored-factor Gram/mean. Original-noise
Cholesky, innovation QR, gain solve, posterior QR and mean errors are included,
with higher-order and normal/subnormal terms retained.

These are local absolute entrywise roundoff allowances. They are not statistical
confidence bounds or complete trajectory error from an independent ideal prior.
That discrepancy is included by the accumulated horizon theorem below.
Positivity concerns the exact Gram of retained words; rounded dense materialization
has its own positivity margin in the dense horizon theorem below. The FLARE native
binary64 bridge is unchanged.

Another 324 native cases exercise noise endpoints/correlation, signed-zero and
near-bound stored gain, rounded prearray margins, QR and returned caps, and an
independent scalar Joseph formula using original R. The previous 324 predictions
also check returned correction validation and covariance/factor caps. These tests
support execution regressions; the universal statements above are Lean theorems.


### Full-step accuracy and invariant from original inputs

[`Implementation/Correctness/CorrelatedNoiseFilterAccuracy.lean`](../Kalman/Implementation/Correctness/CorrelatedNoiseFilterAccuracy.lean)
collects the original two-state operating family:

- `ModelDomain`: `n=m=2`, finite shaped F with entry magnitude `≤ 1/8` and H `≤ 1/64`,
  finite shaped measurement with magnitude `≤ 1`, symmetric original Q/R
  with diagonals in `[1,3/2]` and off-diagonal magnitude `≤ 1/4`.
- `StateInvariant`: valid retained lower factor, mean magnitude `≤ 1`,
  factor entries `≤ 2` and exact retained covariance entries `≤ 2`.
- `InitializationDomain`: original dense covariance in the same noise domain,
  with a finite two-component mean of magnitude `≤ 1`.

All proof witnesses are in
[`FloatFilterInputDomain.lean`](../Kalman/Proofs/FloatFilterInputDomain.lean).
`input_validate` derives all model guards, including native noise symmetry.
`prediction_domain` derives the prediction stage input domain.
`step_profile` derives **every** prediction, innovation, gain, mean and posterior
profile and the fixed constants recorded in `StepParameters`.
`step_environment` derives the exact reference's original noise floor `3/4`,
noise entry cap `3/2`, predicted covariance cap `7/4` and residual cap `2`.

`step_accuracy_and_invariant` concludes:

```text
∃ output, SquareRootFilter.step input initial = .ok output
  ∧ FactorAccuracy 2⁻²⁵ 2⁻²⁵ output
      (ideal Joseph step using the original model words and incoming stored state)
  ∧ StateInvariant output
  ∧ (exact stored-factor covariance of output).PosDef.
```

This full step includes the sensitivity of ideal correction to rounded
prediction, as well as original Q/R factorization, imperfect gain and all mean
and QR errors. No intermediate profile, successful step or output/error bound
is a premise. Both tolerances are absolute entrywise bounds, each about
`2.98×10⁻⁸`; higher-order and normal/subnormal terms are retained.

`initialize_invariant` proves checked dense initialization, covariance error
`≤ 2⁻⁴²`, zero mean error and establishment of `StateInvariant` from original
inputs. `run_invariant` and `initialized_run_invariant` then prove successful
execution, invariant bounds and PD exact covariance at **every finite prefix**,
for time-varying models in this family. Both Q and R may be correlated for these
execution/PD statements. An explicit nonzero F and correlated Q/initial
covariance witness proves that the dense-input domain is inhabited.

The full-step reference starts with the incoming stored factor Gram and mean.
The prefix invariant theorem alone does not bound accumulated discrepancy from an
independently propagated ideal trajectory starting at the original dense
covariance. The accumulated horizon theorem below connects these derived profiles/invariants
to that independent accuracy reference. Its floor `3/4` and noise cap `3/2`
coefficient check admits correlated R; the earlier identity-R coefficients remain
available as a separate special case. Rounded
dense Gram positivity remains a separate statement. These are deterministic
implementation bounds, not estimation confidence or literature constants.

Another 2,592 native checked steps exercise time-varying correlated Q/R,
endpoint means/measurements, initialization, every returned cap, driver agreement
and a separately evaluated native Joseph trajectory. Their `10⁻¹²` comparison
tolerance is a regression criterion, not a replacement for the proved allowance.


### Independent ideal trajectory invariant

[`CorrelatedStages.ReferenceInvariant`](../Kalman/Proofs/CorrelatedStages.lean)
specifies PD covariance with entry magnitude `≤ 2` and mean magnitude `≤ 1`.
[`RealFilterInvariant.lean`](../Kalman/Proofs/RealFilterInvariant.lean) derives
it from the original dense `InitializationDomain` and preserves it along the
independently computed `exactRun`, for every finite prefix of time-varying
original `ModelDomain` inputs. No native state, floating-point error, reached
profile or ideal-trajectory bound is an input premise.

`update_covariance_decrease` proves the exact optimal Joseph correction removes
`K S Kᵀ`, a PSD term. This yields posterior diagonal cap `7/4`; PSD coordinate
bounds then give the same cap for all covariance entries. Prediction gives mean
cap `1/4`, original noise floor `3/4`, ideal gain cap `7/48` and residual cap `2`.
Consequently the ideal posterior mean is bounded by `5/6 ≤ 1`.
These exact identities use the ideal optimal gain, not the computed native gain.

`reference_environment` derives each `StepEnvironment` with noise floor `3/4`, predicted
covariance cap `7/4`, original noise entry cap `3/2` and residual cap `2`. Both Q and R
may be correlated within the original domain. This closes the independent-reference
conditions used by the accumulated accuracy theorem below.


### Accumulated horizon accuracy from original inputs

[`Implementation/Correctness/CorrelatedNoiseFilterAccuracy.HorizonDomain`](../Kalman/Implementation/Correctness/CorrelatedNoiseFilterAccuracy.lean)
contains only the original initialization-model domain, original dense initial-state
domain, and `ModelDomain` for each input before the chosen horizon. Its conditions are:

| Original data | Conditions |
| --- | --- |
| Dimensions and storage | `n=m=2`; correctly shaped finite words |
| F / H | Entry magnitude `≤ 1/8` / `≤ 1/64` |
| Original Q/R | Symmetric; diagonal in `[1,3/2]`; off-diagonal magnitude `≤ 1/4` |
| Original dense initial covariance | Same symmetric covariance headroom as Q/R |
| Initial mean / each measurement | Component magnitude `≤ 1` |

All models and measurements may vary with time. Q and R may both be correlated.
The initialization model may differ from the subsequent time-varying models.
The small transition bound is a substantive stability restriction; broader
practical dynamics have not been discharged by this theorem.

The F allowance is now eight times the preceding `1/64` domain. The native
prediction uses the covariance-aware FL Gram bound above and mean cap `9/32`.
The independent reference mean cap after prediction is `1/4`. The propagation
profiles use the actual original H cap `1/64` rather than the earlier loose
`1/32` allowance. These checked changes preserve the same accumulated tolerance
with stronger transitions; they change no native operation order or guards.

[`FloatInputHorizon.initialized_horizon_accuracy`](../Kalman/Proofs/FloatInputHorizon.lean)
proves, for every finite horizon N:

```text
∃ retained, fromCovariance initializationInput originalState = .ok retained
  ∧ ∀ t ≤ N, ∃ output,
      SquareRootFilter.run inputs retained t = .ok output
      ∧ FactorAccuracy 2⁻²⁵ 2⁻²⁵ output
          (exactRun inputs (exact original dense covariance and mean) t)
      ∧ StateInvariant output
      ∧ (exact retained-factor covariance of output).PosDef
      ∧ (independent ideal covariance at t).PosDef.
```

Here `2⁻²⁵ ≈ 2.98×10⁻⁸` bounds each covariance entry and each mean component
in absolute value, at every prefix including zero. It does not grow with N.
The reference uses exactly the same original finite model/measurement words;
its initial covariance is the original dense input, not the initializer's Gram.
The initializer's `2⁻⁴²` covariance error and zero mean error are included.

`reached_profile` derives every native profile from original inputs and the
preserved state invariant. `RealFilterInvariant` independently derives all
exact trajectory environments. `propagated_radius_caps` closes the two step
radius expressions at incoming covariance/mean allowance `2⁻²⁵`, using noise
floor `3/4`, predicted reference covariance cap `7/4`, original R cap `3/2`
and residual cap `2`. It includes incoming error, original Q/R factorization,
prediction, innovation, imperfect gain, mean correction and posterior QR, with
higher-order and normal/subnormal terms retained. The general horizon induction
then yields the public result. No reached native run, arithmetic profile,
ideal-trajectory bound or output error is a premise of `Domain` or that result.

`domain_nonempty` supplies nonzero F and correlated Q, R and original initial
covariance `[[1,1/4],[1/4,3/2]]` for every finite horizon. Thus the completed
accuracy result is supported beyond the previous reset-model witness. It is
still a deterministic implementation roundoff guarantee in the documented
units, not an estimation confidence bound or general stability claim.
The retained-factor theorem above concerns its exact Gram. The completed dense
horizon theorem below separately derives materialization error and positivity
from the same original-input conditions.
The FLARE native binary64 model bridge and reviewed dependency head are unchanged.
`boundary_domain_nonempty` additionally reaches F entries `±1/8` with the same
correlated original Q/R and initial covariance, for every finite horizon.

The new 256-step native regression uses changing correlated Q/R and endpoint
measurements, checks every returned cap and driver bit agreement, and compares
seven prefixes with an independent ideal Joseph oracle generated by
[`HorizonReference.py`](../Kalman/Tests/HorizonReference.py). The oracle's rounded
reference values agree at 120 and 160 decimal digits; it separately checks the
Joseph/subtractive algebraic identity numerically. The `10⁻¹²` native comparison
is a regression tolerance; the universal allowance above is proved in Lean.


### Rounded dense output over the original-input horizon

[`Implementation/Correctness/CorrelatedNoiseFilterAccuracy.lean`](../Kalman/Implementation/Correctness/CorrelatedNoiseFilterAccuracy.lean)
states the dense comparison relation and constants.
[`FloatDenseHorizon.initialized_dense_horizon_accuracy`](../Kalman/Proofs/FloatDenseHorizon.lean)
is its proof witness. Its **only domain premise** is the same
`Implementation.Correctness.CorrelatedNoiseFilterAccuracy.HorizonDomain` used above:
original dense initialization and original time-varying two-state input bounds. No new
successful run, materialization, symmetry, spectral floor or output accuracy is assumed.

For every $t\le N$, including zero, the checked native driver returns a factor,
and the unchanged native `SquareRootFilter.materialize 2 factor` returns a
finite correctly shaped dense state. Let $G_t=\widehat L_t\widehat L_t^T$ denote
the exact Gram of the retained Float words, $\widehat P_t$ the exact decoding
of the separately rounded dense output, and $P_t,x_t$ the independent ideal
trajectory initialized at the original dense covariance and mean. Then:

$$
G_t\succeq\tfrac14 I,\qquad
\max_{ij}|\widehat P_{t,ij}-G_{t,ij}|\le2^{-48},
$$

$$
\widehat P_t\succeq(\tfrac14-2^{-47})I\succ0,\qquad
\max_{ij}|\widehat P_{t,ij}-P_{t,ij}|\le2^{-25}+2^{-48},\qquad
\max_i|\widehat x_{t,i}-x_{t,i}|\le2^{-25}.
$$

The separately computed off-diagonal **Float words agree exactly**, without
mirroring or averaging. Mean words are copied unchanged. Both dense output and
ideal covariance are PD. The floor is also at least $1/8$, proved by
`denseFloor_ge_eighth`. The tiny added covariance allowance is approximately
$3.55\times10^{-15}$; it does not grow with the horizon, and the total remains
approximately $2.98\times10^{-8}$ in the documented units.

`initialization_covariance_floor` carries the Cholesky half floor to the common
quarter floor. `step_covariance_floor` derives a fresh quarter floor from the
actual posterior QR result, using budget $M=2$ and its $M^2/16$ theorem.
`run_covariance_floor` handles the zero prefix and every subsequent native step.
`FloatMaterialization.two_state_accuracy` derives $M=2$ dot-product mass from
the covariance diagonal cap, so the native multiplication bound is
$2\cdot2^{-50}\cdot2=2^{-48}$, including gradual underflow.
`FloatGramSymmetry` proves symmetry of the actual accumulation schedule.
The perturbation theorem then charges $n e=2^{-47}$ against the retained floor;
the triangle inequality adds materialization error to the existing horizon error.

These constants are project-specific sufficient bounds, not paper constants
or physical estimation guarantees. The result remains restricted to the
original two-state operating family with $|F_{ij}|\le1/8$ and $|H_{ij}|\le1/64$.
The generic underflow counterexample remains valid: a positive factor with no
quarter spectral floor can materialize to a singular matrix. Native regressions
check symmetry/mean-word preservation across six scale/correlation/signed-zero
cases, plus symmetry and an eighth-floor check at all 257 prefixes of the
256-step high-precision horizon. These supplement the proofs.


### Prediction stage: native prearray and mean accuracy

`FloatPrearray.fromCols_gram` proves that native horizontal copying has exactly
the sum of the two decoded blocks' Grams. It includes empty blocks and performs
no rounded matrix addition. `gram_within` converts a rectangular entry error $e$
against a reference bounded by $B$ to Gram error $d(2eB+e^2)$ for $d$ columns.

`FloatSquareRootError.prediction_accuracy` covers the entire existing
`predictUnchecked` stage: process-noise Cholesky, rounded $FL$, prearray copying,
QR, and the mean product. It proves success and a valid returned factor. With
$e=\mathrm{productRadius}(n,M_{FL})$, its absolute covariance allowance is

$$
G_{2n,n}(M_{QR})+n\bigl(2e\cdot nB_FB_L+e^2\bigr)
+\mathrm{diagonalRadius}(n,M_Q)
+\mathrm{divisionRadius}(n,M_Q,\delta_Q,D_Q).
$$

The mean allowance is `productRadius n meanMass`. Both comparisons use exact prediction
from the same decoded initial factor and input noise covariance. Noise-factor discrepancy
is included. `Implementation.Correctness.SquareRootFilterProperties.FactorAccuracy` states
validated storage, covariance error and componentwise mean error.

This completed theorem uses `PredictionProfile`: the noise Cholesky operand
profile, product/mean budgets, intermediate operation equations, the initial QR
domain on the assembled prearray, and original transition/factor entry bounds.
That generic theorem does **not itself discharge these conditions from one original-model domain**
or compare a rounded incoming covariance with an earlier ideal trajectory.
The local two-state prediction domain above now discharges them in its stated
range. Innovation, gain, posterior and trajectory composition are completed below.

`factor_validate_complete` proves that finite correctly shaped storage with a
lower-positive exact interpretation passes the native factor checks. Stage
accuracy therefore concludes output validation. Exact gain-residual and Joseph
gain-perturbation lemmas in `RealErrorBounds` support the correction stage; they reuse
FLARE's existing Real residual theorem and introduce no new native arithmetic
assumption or library revision.


### Measurement update and exact-recursion sensitivity

`FloatSquareRootUpdate.update_accuracy` proves the complete native measurement
update, including successful execution and final validation, against exact
correction from the same decoded prior. It covers measurement-noise Cholesky,
rounded $HL$ and $L(HL)^T$, innovation QR, both gain-solve passes, all four mean
operations, rounded $KH$ and $I-KH$, both Joseph prearray products, and posterior
QR. Its operands are recorded in `InnovationProfile`, `GainProfile`,
`MeanProfile` and `PosteriorProfile`; these are domain witnesses, not assumed
error conclusions. Cholesky and solve profiles still record intermediate
execution and operand bounds.

Write $e_I$ for `innovationRadius`, $e_{HL}$ and $e_C$ for the corresponding
product radii, $B_L$ for the stored prior-factor bound, and $B_{\widehat K}$ for
the computed gain bound. If the **original decoded measurement covariance** has
floor $\alpha>0$, the gain allowance is

$$
e_K=\frac{m}{\alpha}\left[(1+mD_S)
\mathrm{divisionRadius}(m,M_S,\delta_S,D_S)
+e_C+nB_Le_{HL}+mB_{\widehat K}e_I\right].
$$

`gain_accuracy` compares with the ideal $PH^TS^{-1}$, including innovation-factor
and numerator discrepancies. It does not assume an exact computed gain. The
floor is transferred from the original measurement noise through the exact
innovation covariance; no inverse of a perturbed innovation is silently used.

Let $e_z=\mathrm{sumRadius}(E_z)+\mathrm{productRadius}(n,M_{H\mu})$,
and let $K,Z$ bound the ideal gain and residual. The mean allowance is

$$
\mathrm{sumRadius}(E_\mu)+\mathrm{productRadius}(m,M_{Kz})
+m(e_KZ+Ke_z+e_Ke_z).
$$

`posterior_evaluation_accuracy` first bounds Joseph evaluation at the actual
stored gain by `posteriorEvaluationRadius`, including both noise and prearray
errors. `update_accuracy` adds the exact gain-perturbation allowance

$$
n^2P\bigl[2(me_KH)(1+mKH)+(me_KH)^2\bigr]
+m^2R(2e_KK+e_K^2).
$$

Here $P,R,H$ bound ideal prior, original noise and observation entries.
All cross terms remain; these are finite inequalities, not first-order estimates.

`RecursionSensitivity.predict_sensitivity` propagates incoming covariance and
mean errors $(e_P,e_\mu)$ to $(n^2F^2e_P,nFe_\mu)$ before local rounding is added.
`gain_sensitivity` and `update_sensitivity` account for the prior's effect on
both the optimal gain and the innovation. Their explicit nonlinear coefficients
are `correctionGainRadius`, `correctionCovarianceRadius` and
`correctionMeanRadius` in `Definitions/Theorems/RecursionSensitivity`. They prepare composition
against one ideal trajectory, rather than restarting the reference at a rounded
prior. The full-step and horizon theorems below compose them.


### Complete checked square-root step

`FloatFullFilter.step_accuracy` proves the complete checked native filter step
against an **independently supplied exact incoming state**. Both initial
covariance and mean discrepancies are carried through prediction and correction.
`stepWithin` supplies the previously open public `Proofs.SquareRootProfiles.StepWithin`
comparison relation when the initial reference is the exact Gram of the initial factor.

For incoming errors $(E_P,E_\mu)$, first form

$$
\widetilde E_P=e_{\mathrm{predict},P}+n^2B_F^2E_P,
\qquad
\widetilde E_\mu=e_{\mathrm{predict},\mu}+nB_FE_\mu.
$$

With ideal predicted covariance and innovation bounds $P,Z$, the native prior
has bounds $P+\widetilde E_P$ and $Z+nH\widetilde E_\mu$. Its exact optimal gain
is bounded by $m n(P+\widetilde E_P)H/\alpha$. The final allowances
`stepCovarianceRadius` and `stepMeanRadius` add the local update bounds at these
magnitudes to `correctionCovarianceRadius` and `correctionMeanRadius` evaluated
at the propagated prediction errors. This includes every implemented arithmetic
stage, prior error and both noise-factor discrepancies.

`StepProfile` records all stage operands and QR input domains. `StepEnvironment`
records independent ideal magnitudes, PSD process noise and a strictly positive
original measurement-noise floor. Input validation and valid initial factor are
explicit. Success, output validation and both final errors are conclusions.
The Cholesky/solve profiles and intermediate operation equations are still
operand-domain premises; the theorem is **not** a model-only success guarantee.
It changes neither the runtime program nor the pinned FLARE bridge.


### Full filter over a finite horizon

`FloatFilterHorizon.finite_horizon_accuracy` proves **successful native execution,
covariance and mean accuracy, and strict PD of both covariances at every prefix**
$t\le T$. Models and measurements may vary with time, at fixed dimensions. The
native recursion is the executable `Implementation/SquareRootFilter.run`,
aliased as `InputInterpretation.nativeRun`; its comparator `exactRun` starts
once from the supplied exact initial state. Every original input word is decoded
exactly. `atDimensions` only supplies type indices; the domain requires them to
agree with the original native metadata, and `atDimensions_eq` proves equality.

`HorizonOperands` records validation, initial/reference positivity, PD process
noise, ideal reference magnitude/floor bounds, and the stage profiles at reached
prefixes. `HorizonDomain` adds initial accuracy and inequalities comparing the
**explicit step-radius expressions** with the chosen next budgets. No final-run
success or actual trajectory error is assumed. Induction first proves a prefix
successful, then uses its operand witness to prove the next. The domain remains
a reached-prefix numerical certificate. The original-input horizon theorem
derives this certificate for the two-state family documented above.

`FloatFilterInitialization.fromCovariance_accuracy` covers the checked
covariance-to-factor initializer: it proves successful conversion and valid
factor storage, covariance allowance `diagonalRadius n M + divisionRadius n M δ D`
against the **original decoded covariance**, and zero mean discrepancy. Its
Cholesky operand profile is explicit in that general theorem; the new
[two-state input-only initializer](#two-state-cholesky-from-original-inputs)
derives it on its stated entry domain. This allowance can seed the horizon's
initial covariance radius, so initialization error need not be hidden by changing
the exact reference to the factor's Gram. `initialized_horizon_accuracy` proves
the **initializer-plus-filter pipeline** directly: it derives initial accuracy
from the Cholesky theorem and an inequality fitting its explicit allowance into
the initial budget, then concludes successful execution and both errors/PD
properties for every prefix. Initial accuracy is not an additional premise in
this pipeline theorem.


### Instantiated uniform two-state bound

`FloatFilterBudget.refined_uniform_covariance_cap` and `refined_uniform_mean_cap`
prove that incoming errors in $[0,2^{-25}]$ map back into the same interval under the following
fixed numerical allowances. Equality of budget fields fixes upper allowances;
it does not require matrix entries to equal their bounds.

| Quantity in `UniformStepParameters` | Allowance |
| --- | --- |
| State and measurement dimensions | $n=m=2$ |
| Transition and observation entry bounds | $1/32$ each |
| Incoming prediction/innovation factor entries; measurement-noise factor entries | $2$ |
| All rounded product term-mass budgets, including mean operations | $8$ |
| Noise Cholesky row mass, diagonal floor and diagonal bound | $8,\mspace{5mu}1/2,\mspace{5mu}2$ |
| Gain solve row mass, diagonal floor and factor entry bound | $32,\mspace{5mu}1/2,\mspace{5mu}2$ |
| Computed gain entry bound | $1$ |
| Sum/subtraction exponents | $E=2$, exact stored-operand magnitude at most $4$ |
| All three QR budgets | $M=2$: four-column prearray, row energies $\le2$, Gram floor $\ge1/2$ |
| Original measurement-noise floor and entry bound | $\alpha=1$, $R=1$ |
| Ideal predicted covariance and innovation entry bounds | $P=2$, $Z=2$ |

Every profile also has the shape, finiteness, operation-order, execution and
range conditions specified in its definition. `uniform_parameters_radii`
connects these allowances to the actual full-step radii. The closed coefficient
proofs retain cross terms and underflow allowances; no first-order truncation or
floating numerical estimate is used in the proof.

`refined_uniform_horizon_accuracy` consequently proves, for **any finite horizon**
whose reached-prefix witnesses satisfy `UniformHorizonDomain` with budget
$2^{-25}$, including initial errors at most that budget,

$$
\left|(\widetilde P_t-P_t)_{ij}\right|\le2^{-25},\qquad
\left|\widetilde\mu_{t,i}-\mu_{t,i}\right|\le2^{-25}
\quad(0\le t\le T).
$$

Here $\widetilde P_t$ is the exact Gram of the stored native factor and
$\widetilde\mu_t$ its exactly decoded mean. Both represented and reference
covariances are strictly PD at every prefix. The budget is absolute in the
chosen units, about $2.98\times10^{-8}$, and independent of horizon length under these
uniform domain conditions. It is conservative, dominated by QR proof constants;
it is neither a universal relative-error bound nor a sharp paper stability
constant. The coefficient calculation alone does not establish a preserved
original-input domain; the separate original-input horizon proof does so for
its stated two-state family. The original
`uniform_horizon_accuracy` API with initial/final budget `1/128` remains proved;
`UniformHorizonDomain` keeps that default budget for compatibility.

The refinement changes no runtime arithmetic or stage operand allowances. It
keeps the active row count in column-norm and reflector bounds, reduces the
nonnegative square/add accumulation error, and charges the linear annihilation
defect only to the head. For the four-column/two-pivot QR budget $M=2$, the explicit
Gram radius is approximately $8.3475\times10^{-10}$, down from the preceding
$3.1346\times10^{-8}$. The full-horizon tolerance improves another 32-fold, or
262,144-fold from the original $1/128$. The `tight_uniform_horizon_accuracy`
interface at $2^{-20}$ and the original $1/128$ interface both remain proved;
each requires initial accuracy at its own tolerance. The new tolerance also
has its own tighter initial-accuracy premise. These are improvements in proved
worst-case allowances, not changes in measured error or machine-precision
optimality. Generic component-to-action/Gram estimates and gain/recursion
propagation still leave room for tightening.

`FloatFilterDomain.uniform_domain_nonempty` and `refined_uniform_domain_nonempty`
supply a **fully discharged
original-input member** for every finite horizon: two-state reset dynamics
$F=H=0$, $Q=R=I$, zero initial mean, identity initial covariance, and measurement
$(1,0)$. All native operation certificates are checked with `decide +kernel`.
The retained factor stores a negative zero below its diagonal; the witness
preserves that exact native word and proves its Real meaning is zero. All
Cholesky, solve, QR, validation, magnitude and reference conditions are proved.
`native_trace_certificate` and `exact_trace_certificate` show the states remain
constant; `supported_horizon` instantiates the general accuracy/PD theorem.

This reset case establishes nonvacuity. Its exact roundoff discrepancy is zero;
it does not demonstrate a sharp bound on a realistic correlated model. The
uniform theorem covers other certified operands. The original-input horizon
theorem above establishes admissibility and accuracy for a nonzero-transition
family with correlated Q/R and initial covariance.


### Fully observed diagonal Real invariant

[`Definitions/DiagonalObservation.lean`](../Kalman/Definitions/DiagonalObservation.lean)
specializes the existing exact recursion to $H=I$ and diagonal $F,Q,R,P$.
For one component, prediction and correction are:

$$
a=f^2p+q,\quad k=\frac{a}{a+r},\quad
p^+=\frac{ar}{a+r},\quad
x^+=\frac{r}{a+r}fx+\frac{a}{a+r}z.
$$

`RealDiagonalObservation.predict_eq`, `gain_eq`, `update_eq` and `step_eq`
prove equality to the original matrix specification; `step_eq` covers compact,
subtractive and Joseph forms. Nonnegative incoming variance and positive noise
justify every inverse. `run` executes the original matrix Joseph recursion,
rather than assuming the scalar formulas describe it.

[`Definitions/Theorems/RecursionSensitivity.lean`](../Kalman/Definitions/Theorems/RecursionSensitivity.lean)
states a new **Real-only** domain: $|f_i|\le1$, $q_i,r_i\in[1,3/2]$,
$|z_i|\le1$, and initial $p_i\in[1/2,3/2]$, $|x_i|\le1$.
[`RealObservableInvariant.lean`](../Kalman/Proofs/RealObservableInvariant.lean)
proves prediction variance in $[1,3]$, optimal gain in $[2/5,3/4]$, corrected
variance in $[1/2,1]$ and mean magnitude at most one. The exact correction mean
is a convex combination of the predicted mean and measurement. Every finite
prefix stays diagonal, has variance in $[1/2,3/2]$, and has covariance floor
$P\succeq\tfrac12 I\succ0$. The sharper upper cap one holds after each correction.
`identity_domain_nonempty` includes $F=I$; the supporting Real proofs are
dimension-generic, with an analytic two-state exact regression.

These project domain bounds are consequences of the source equations, not new
paper constants. The completed native full-horizon domain is still the earlier
small-F/H family. Supporting native prediction and innovation for $H=I$ and
$|f|\le1$, complete correction, initialized accumulated accuracy and rounded
dense positivity are proved below. The supporting joint sensitivity proof follows.


### Fully observed diagonal Real sensitivity

[`RealObservableSensitivity.lean`](../Kalman/Proofs/RealObservableSensitivity.lean)
proves the full-step sensitivity of the same matrix specification, for every
covariance form and any finite dimension. The model obeys the Real domain above;
the reference obeys its invariant. The other incoming covariance may be any
nonnegative diagonal matrix, with no upper variance or mean cap required for
that state. The two steps use the same model and measurement. Write $e_P$ for
the maximum incoming covariance-entry discrepancy and $e_x$ for the maximum
mean-component discrepancy. `step_sensitivity` proves:

$$
e_P^+\le\frac9{25}e_P,\qquad
e_x^+\le\frac35e_x+\frac12e_P.
$$

The covariance-dependent gain is included. For prior variances $a,b\ge1$,
`gain_difference`, `covariance_difference` and `mean_difference` prove exact
rational identities, including:

$$
k(a)-k(b)=\frac{r(a-b)}{(a+r)(b+r)},\qquad
x^+(a,x)-x^+(b,y)
=\frac{r}{a+r}f(x-y)+(k(a)-k(b))(z-fy).
$$

The correction weights are at most $3/5$, gain sensitivity is at most
$1/4$, and the reference innovation magnitude is at most two. Prediction
does not increase variance discrepancy because $|f|\le1$. These give the
stated coefficients without dropping higher-order terms or linearizing the
gain. They are sufficient project-derived constants, not claimed sharp bounds
or constants quoted from a paper.

`Definitions.Theorems.RecursionSensitivity.DiagonalJointWithin E` means covariance discrepancy at most
$E/2$ and mean discrepancy at most $E$; equivalently, the joint radius weights
covariance by two. `joint_step_contraction` proves:

$$
E^+\le\frac{17}{20}E.
$$

`horizon_contraction` lifts this to two exact time-varying matrix trajectories
whose initial states satisfy the Real domain:
$E_t\le(17/20)^tE_0$ at every finite prefix. This strict contraction includes
$F=I$: observations supply the contraction even when prediction alone does
not reduce error.

`joint_step_with_local_error` also proves the **conditional** recurrence
$E^+\le\delta+(17/20)E$ when a supplied output has local joint discrepancy
at most $\delta$ from the exact step of the other incoming state.
`joint_uniform_budget` proves that $E\le(20/3)\delta$ is preserved under that
same local-error premise. Both are completed Real implications. They supply
a conditional interface; they do **not** themselves establish a Float value
for $\delta$, native diagonal preservation or successful execution. The native
proofs below supply these and initialized componentwise horizon bounds. The
earlier small-dynamics native full-horizon domain has F/H entry caps `1/8` and `1/64`.


### Native prediction and innovation at diagonal transition magnitude one

[`Correctness/InputInterpretation.lean`](../Kalman/Implementation/Correctness/InputInterpretation.lean)
defines `DecodedDiagonal`: off-diagonal entries have exact decoded value zero, allowing
either signed-zero word. Shape and finiteness are separate conditions.
[`FloatDiagonalStorage.lean`](../Kalman/Proofs/FloatDiagonalStorage.lean) proves that
successful finite two-state diagonal multiplication preserves this relation. It also
proves that native Cholesky preserves it on diagonal inputs in the existing Cholesky
domain. These follow the actual ascending product/add schedule and quotient, using FLARE's
exact real-zero lemmas. Diagonal products can still overflow outside bounded domains; no
unconditional success is asserted. No mirroring or symmetry repair is performed.

[`DiagonalStages.Prediction.TwoStateDomain`](../Kalman/Proofs/DiagonalStages.lean)
states a **local stored-input** domain for the existing native algorithm:

- State dimension two; shaped finite diagonal transition with $|f_i|\le1$.
- Shaped finite incoming factor, entries bounded by two, exact Gram diagonals
  at most $13/8$; mean components bounded by $9/8$.
- Original diagonal process-noise words with variances in $[1,3/2]$.
- For innovation, measurement dimension two, shaped finite H decoding to I,
  and original diagonal measurement-noise variances in $[1,3/2]$.

The prediction proof permits correlated incoming factors within the diagonal
energy caps; it does not assume their covariance or QR output is diagonal.
The slack around the Real invariant is deliberate, to accommodate later
roundoff accumulation. A native identity-transition/observation witness proves
the local domains are inhabited. Incoming factors from original dense
initialization and preservation of the complete filter invariant are established
by the separate initialization and horizon theorems below.

[`FloatObservablePrediction.lean`](../Kalman/Proofs/FloatObservablePrediction.lean)
derives every prediction profile and `predictUnchecked` success from that
domain. Original diagonal noise has floor one; its native Cholesky Gram has
floor $63/64$. Diagonal F preserves the incoming covariance diagonal energy
cap. The actual $[\widehat{FL},T_Q]$ prearray therefore has floor $63/64$
and row energy at most $51/16$, meeting the proved QR domain with budget
$M=21/8$. `prediction_accuracy` proves:

$$
\max_{i,j}|\widehat P^-_{ij}-P^-_{ij}|\le2^{-24},\qquad
\max_i|\widehat x^-_i-x^-_i|\le2^{-46}.
$$

The reference is exact matrix prediction from the same stored incoming factor,
mean, original F and original Q. Covariance error includes Q factorization,
FL rounding, prearray construction and actual Householder QR. Output factor
storage validates, factor entries are at most two, mean magnitude at most
$19/16$ (tightened from the earlier $5/4$ convenience cap), Gram diagonals at most $13/4$, and exact retained covariance has floor
$15/16$. `prediction_innovation_domain` derives the whole reached local
innovation domain when the original observation/noise conditions hold.

[`FloatObservableInnovation.lean`](../Kalman/Proofs/FloatObservableInnovation.lean)
derives the actual HL product, R Cholesky, $[T_R,\widehat{HL}]$ prearray and
innovation QR. Its prearray has floor $15/8$, row energy at most $77/16$ and
QR budget $M=25/8$. `factor_accuracy` derives success, finite lower-positive
factor, factor entry cap $9/4$, retained covariance diagonal cap $39/8$,
retained covariance floor $29/16$, and:

$$
\max_{i,j}|\widehat S_{ij}-(P_{\mathrm{stored}}+R)_{ij}|\le2^{-23}.
$$

Here $P_{\mathrm{stored}}$ is the exact Gram of the incoming native prior factor;
R is the original decoded measurement noise. This local innovation error
includes HL and R factorization rounding and actual QR. Its reference does not
include the prior's discrepancy from an independently propagated ideal state.

These are local unchecked-stage theorems, with no intermediate profile or
successful native run assumed. Returned QR diagonality for diagonal incoming
factors and enlarged gain-solve operands are now proved below. The following
results also establish checked model validation, posterior correction, dense
initialization and the accumulated Float budget.
In particular, these stage bounds do not supply the full-step joint $\delta$
required by the Real contraction theorem. The existing full-horizon `2⁻²⁵`
result keeps its documented domain.

The native regression suite adds 1,200 prediction/innovation cases: diagonal
F entries in `{-1,-7/8,0,7/8,1}`, endpoint noise variances, diagonal and
correlated incoming factors reaching Gram diagonal $13/8$, endpoint/slack means,
and opposite signed-zero words. Analytic small-dyadic polynomial expectations
are checked at tolerance `10⁻¹²`; this test tolerance is separate from the
proved allowances. The tests also check observed QR zeros for diagonal factors
and diagonal overflow rejection. The separate QR invariant below is now proved.


### Native diagonal QR and observable stage preservation

[`FloatQRDiagonal.lean`](../Kalman/Proofs/FloatQRDiagonal.lean) proves a structural
property of the actual native QR, separately from its numerical error domains.
For two finite diagonal 2×2 blocks A and B, suppose
`gramFactor 2 4 (fromCols 2 2 2 A B) = .ok L`. Then `DecodedDiagonal 2 L` holds.
There is **no magnitude cap** in this conditional theorem; rank or arithmetic
failure may still reject the call. Either signed-zero encoding is allowed.

The transposed 4×2 prearray has column supports `{0,2}` and `{1,3}`.
Maximum-scaled division and reflector normalization preserve decoded zeros.
The first reflector's actual ascending dot product with the second column is
exactly zero: every separately rounded product and addition is zero.
Its checked updates preserve the required zero entries, source finishing
writes positive zeros, and the second iteration copies the first row.
Signed retention then keeps both factor off-diagonals at decoded zero.
The proof follows those loops and checks; it assumes no abstract exact QR law.
The local subtraction-of-zeros lemma is proved through Lean's binary64 logical
model, with finiteness supplied by FLARE's nearest-subtraction theorem.

[`FloatDiagonalStorage.gram_diagonal`](../Kalman/Proofs/FloatDiagonalStorage.lean)
connects a decoded diagonal factor to its exact Real covariance:

$$
P_L=LL^T=\mathrm{diag}(L_{00}^2,L_{11}^2).
$$

This is the mathematical interpretation of the stored words. Forming a rounded
dense covariance remains a separate operation with a separate positivity proof.

[`FloatObservableDiagonal.lean`](../Kalman/Proofs/FloatObservableDiagonal.lean)
adds the following completed corollaries to the preceding local operating domain:

- `prediction_innovation_diagonal`: a diagonal incoming factor gives successful
  prediction, a diagonal returned factor and exact diagonal Real covariance,
  the reached innovation domain, and local prediction errors `2⁻²⁴` / `2⁻⁴⁶`.
- `innovation_accuracy_diagonal`: a diagonal incoming prior gives successful
  R Cholesky, HL and innovation QR, a diagonal innovation factor and exact
  diagonal Real covariance, strict PD, covariance floor `29/16`, and local
  error `2⁻²³` against the same stored prior covariance plus original R.

These corollaries derive stage success from original local conditions; they
assume no successful run or desired error. The additional incoming diagonality
is explicit. They provide the covariance structure needed for the proved Real
sensitivity argument. The following results establish correction, the native
invariant, full-step joint allowance δ, original dense initialization and
independent ideal-trajectory accumulated accuracy.

Twelve native regressions use independent scaled 3-4-5/2 norm expectations at
the smallest positive binary64 subnormal, `10⁻³⁰⁰`, one and `10³⁰⁰`, with signed
zeros, reversed diagonal signs and zero leading blocks. They check successful
finite positive-diagonal factors and decoded zeros. A rank-deficient case checks
rejection. The normalized-diagonal tolerance `10⁻¹²` is a regression choice,
not a newly proved numerical allowance.


### Fully observed diagonal gain from stored inputs

[`Proofs/CholeskyProfiles.lean`](../Kalman/Proofs/CholeskyProfiles.lean)
defines a larger two-state substitution domain entirely from stored inputs:
L and B have four finite entries, L decodes to a diagonal matrix with
$L_{ii}\ge1$ and $|L_{ij}|\le9/4$, and $|B_{ij}|\le4$.
B may be correlated. No successful execution, intermediate profile or numerical
error is assumed.
[`FloatDiagonalSolve.lean`](../Kalman/Proofs/FloatDiagonalSolve.lean) derives
the actual forward and backward substitution runs with residual mass 16,
diagonal floor one and divisor cap $9/4$. Forward entries are bounded by five,
solution entries by six. Its completed `solve_accuracy` theorem gives

$$
\max_{i,j}|\widehat X_{ij}-((LL^T)^{-1}B)_{ij}|\le2^{-39}.
$$

L and B on the right are exact decodings of the supplied words. This is an
absolute error bound, about $1.82\times10^{-12}$; L is already a stored factor,
so original-noise or QR error is not part of this isolated solve comparison.
`solve_diagonal` additionally proves exact decoded diagonality when B is
diagonal. The proof follows each ordered residual product/subtraction and final
division. Zero cross-products permit larger RHSs without larger residual mass;
signed zeros and underflow remain covered by the existing binary64 bridge.
The runtime and its finite/pivot guards are unchanged; there is no symmetry repair.

[`FloatObservableGain.lean`](../Kalman/Proofs/FloatObservableGain.lean) composes
these solves with the actual formed gain products and innovation QR. Its public
`gain_accuracy` theorem assumes state dimension two, the preceding local
`InnovationDomain`, and a decoded diagonal incoming prior factor:

- H is shaped and finite and decodes to I; original R is shaped finite diagonal
  noise with variances in $[1,3/2]$.
- The shaped finite prior factor has entries bounded by two, exact covariance
  $P_L=LL^T$ with floor $15/16$ and diagonal cap $13/4$.
- The prior factor decodes to a diagonal matrix, allowing either zero sign.

These conditions are derived by the preceding prediction theorem from its local
domain and diagonal incoming factor. They are sufficient local conditions,
not an initialization or complete-filter invariant.

| Completed conclusion | Bound / structure |
| --- | --- |
| Actual HL, original-R Cholesky, innovation QR and both gain solves | Succeed with finite shaped storage; all profiles derived |
| Formed PHT $=\mathrm{fl}(L\widehat{HL}^{\thinspace T})$ | Exactly decoded diagonal; entries bounded by $7/2$ |
| Formed PHT discrepancy from $P_L$ | $2^{-43}$, about $1.14\times10^{-13}$ |
| Chosen complete innovation profile radius | $9\cdot2^{-32}$, about $2.10\times10^{-9}$ |
| Actual gain | Exactly decoded diagonal; diagonal entries in $[3/8,13/16]$ |
| Gain discrepancy from the ideal gain of the same stored prior | $2^{-27}$, about $7.45\times10^{-9}$ |

The final comparison is

$$
\max_{i,j}|\widehat K_{ij}-(P_L(P_L+R)^{-1})_{ij}|\le2^{-27}.
$$

It includes HL/PHT rounding, original-R Cholesky error, actual innovation
Householder QR and both substitution passes. The reference uses the same
stored prior covariance and original decoded H/R. It does not include the
prior's discrepancy from an independently propagated ideal trajectory.

For the selected innovation profile, `innovation_radius_cap` retains the
actual four- and three-row QR constants at budget $25/8$, rather than replacing
the whole innovation radius by the earlier $2^{-23}$ convenience cap. The gain
proof first derives an entry cap six and gain error $2^{-24}$. Exact scalar gain
diagonals $p/(p+r)$ lie in $[5/13,13/17]$, so that preliminary error derives
the actual gain range $[3/8,13/16]$. Reusing that derived cap in the same gain
radius gives $2^{-27}$. The tight cap is a conclusion, not a premise of the
final theorem. All constants include the existing higher-order and subnormal
terms and are project sufficient bounds, not constants attributed to a paper.

Native regressions add 54 larger solve cases with factor diagonals in
`{1,5/4,9/4}`, RHS entries at the magnitude-four boundary, correlated RHSs,
signed zeros and the smallest subnormal. They compare with direct scalar
division by the independently computed exact dyadic diagonal square. The
600 diagonal cases in the existing prediction/innovation grid additionally
check formed gain against $p/(p+r)$, its range and exact decoded zeros. The
`10⁻¹²` regression tolerance is separate from the proved gain allowance.

Factored-Joseph posterior profiles, checked full-step success, original dense
initialization, the complete native invariant and accumulated accuracy for this
larger family are established by the following results. This gain bound alone does
not supply the full-step joint allowance δ used by the Real contraction theorem.
The separate rounded dense positivity proof follows below.


### Fully observed diagonal mean correction and headroom

[`DiagonalStages.Mean.TwoStateDomain`](../Kalman/Proofs/DiagonalStages.lean)
states the original local correction conditions: the preceding two-state
innovation domain, a decoded diagonal prior factor, shaped finite prior mean
with magnitude at most $19/16$, and shaped finite measurement with magnitude
at most one. No intermediate profile, successful execution or desired error
is assumed. The same decoded H/R/z and stored prior are used by the native
operations and Real reference.

[`FloatObservablePrediction.mean_stage`](../Kalman/Proofs/FloatObservablePrediction.lean)
now tightens the reached mean cap from $5/4$ to $19/16$. Diagonal $|F_{ii}|\le1$
bounds the exact predicted mean by $9/8$; the already proved product allowance
$2^{-46}$ fits the new cap. Covariance/factor/QR budgets and the runtime are
unchanged. `FloatObservableMean.prediction_correction_domain` combines this
with the proved prediction/innovation diagonal handoff and original bounded
measurement conditions to derive the entire reached mean-correction domain.

[`FloatObservableMean.lean`](../Kalman/Proofs/FloatObservableMean.lean) proves
all four actual mean operations in their existing order: projected Hx,
measurement subtraction, multiplication by the stored gain, and addition to
the prior mean. Both product profiles use mass eight; both sum profiles use
exponent two. Derived projected, residual and increment magnitude caps are
$5/4$, $19/8$ and two. These derive finiteness and success of each operation.

The stored gain is exactly diagonal with diagonals $k_i\in[3/8,13/16]$,
as derived by the preceding gain theorem. The exact evaluation obeys

$$
|x_i+k_i(z_i-x_i)|
=|(1-k_i)x_i+k_i z_i|
\le(1-k_i)\frac{19}{16}+k_i
\le\frac{143}{128}.
$$

Rounding error at that same stored gain is bounded by $2^{-44}$, about
$5.68\times10^{-14}$. The headroom $9/8-143/128=1/128$ therefore derives the
actual returned mean magnitude cap $9/8$. This closes the mean part of the
larger family's preserved repeated-step invariant established by the
posterior-factor and checked-step theorems.

The public `correction_accuracy` theorem derives the gain and all mean
profiles/runs from the original local conditions and gives

$$
\max_i|\widehat x_i^+-x_{\mathrm{ideal},i}^+|\le2^{-25},
$$

where the ideal correction starts from the same stored prior mean and exact
factor Gram and uses the original decoded H/R/z. The bound includes the
imperfect native gain. Exact diagonal support removes the inner-dimension
factor when multiplying gain discrepancy by the exact residual:

$$
e_{\mathrm{mean}}
\le2^{-44}+\frac{35}{16}\cdot 2^{-27}
\le2^{-25}.
$$

The residual cap $35/16$ here is for the exact operands; the larger $19/8$
cap above is for the stored rounded residual. Evaluation error at the stored
gain and error against the ideal gain are separate completed statements.
All imported normal/subnormal terms remain included. This is a local correction
bound, not a bound against an independent full trajectory or a complete-step
joint δ. Posterior QR and complete local correction are proved in the posterior-correction result below.
Full-step accuracy and the native invariant are established by the complete-step results below, followed by original dense initialization, accumulated accuracy and
rounded dense output.

Native regressions add 270 stored-gain mean cases at the gain/mean endpoints,
with same/opposite-sign measurements, signed zeros and subnormal means.
They compare with the independently associated weighted scalar formula and
check every intermediate cap. The existing 600 diagonal prediction/gain cases
now continue through mean correction, checking the returned cap and the scalar
ideal mean formula. Their `10⁻¹²` tolerance is a regression choice, separate
from the proved allowances.


### Fully observed diagonal posterior correction

[`FloatObservablePosterior.correction_accuracy_and_bounds`](../Kalman/Proofs/FloatObservablePosterior.lean)
completes the existing native measurement update for the larger family. Its original local
input domain is
[`DiagonalStages.Mean.TwoStateDomain`](../Kalman/Proofs/DiagonalStages.lean):

- State and measurement dimensions are two; H decodes exactly to identity.
- The stored prior factor is finite, has four entries, is decoded diagonal and
  has entry magnitudes at most two. Its exact Real Gram has floor `15/16` and
  diagonal cap `13/4`.
- Original R is finite, decoded diagonal, and has diagonal entries in `[1,3/2]`.
  The noise covariance meets the existing Cholesky storage domain.
- The prior mean and measurement have two finite entries with magnitude caps
  `19/16` and one, respectively.

From these inputs alone the theorem derives `updateUnchecked` success and
returned factor-state validation, together with

$$
\max_{i,j}|\widehat P^+_{ij}-P^+_{\mathrm{ideal},ij}|\le2^{-29},
\qquad
\max_i|\widehat x^+_i-x^+_{\mathrm{ideal},i}|\le2^{-25}.
$$

Here $\widehat P^+$ is the **exact Real Gram of the returned native factor**,
and the ideal Joseph update uses the same stored prior and original decoded
H/R/z. Covariance allowance `2⁻²⁹` is approximately `1.86×10⁻⁹`; the mean
allowance remains approximately `2.98×10⁻⁸`. All actual stage runs and profiles
are derived, including both solves and every posterior product/subtraction.
No successful intermediate run or desired error is an original-domain premise.
The theorem does not require valid unrelated F/Q words and therefore promises
`updateUnchecked`, not the input validator of the checked `update` entry point.
Its returned state does pass validation.

The exact scalar Joseph equation and completed quadratic identity are
[`DiagonalObservation.josephVariance`](../Kalman/Definitions/DiagonalObservation.lean) and
[`RealObservablePosterior.joseph_gain_difference`](../Kalman/Proofs/RealObservablePosterior.lean):

$$
(1-k)^2p+k^2r
=\frac{pr}{p+r}+(p+r)\left(k-\frac{p}{p+r}\right)^2.
$$

The optimal gain cancels the linear perturbation exactly. For reached
$p\in[15/16,13/4]$, $r\in[1,3/2]$, the ideal corrected variance lies in
`[15/31,39/38]`. The proved gain error `2⁻²⁷` therefore changes exact Joseph
covariance by at most `2⁻⁵⁰`. This includes the whole quadratic remainder.
The identity is a project algebraic specialization of the source Joseph
formula; it is not a new paper error constant.

`arithmetic_stages` derives KH, I−KH, WL and KTR in the existing native order,
with prearray Gram error `2⁻³⁸` against the same stored gain/noise factor.
`prearray_accuracy` includes original-R Cholesky error and the quadratic gain
term, bounding prearray error against the ideal covariance by `2⁻³⁶`.
The exact rounded-prearray Gram has floor `15/32` and diagonal cap `17/16`,
deriving QR's initial domain at budget `15/8`. The public
[`DiagonalStages.Posterior.localCovarianceRadius`](../Kalman/Proofs/DiagonalStages.lean)
is the actual four/three-row QR radius plus `2⁻³⁶`; its completed cap is
`2⁻²⁹`. Normal/subnormal terms and higher-order products remain included.

The returned factor is finite, has positive diagonal, and is decoded diagonal
without symmetry repair. Its exact covariance is strictly PD with floor
`7/16`, diagonal cap `17/16`, and factor-entry cap `9/8`. Returned mean cap
is also `9/8`. These upper bounds fit the next prediction's input caps;
complete full-step composition and the native repeated-step invariant are
proved in the posterior-correction result below. This local correction comparison itself does
not give error against an independently propagated ideal trajectory. Rounded
dense materialization has its separate accuracy/positivity theorem below.

The 600 reached diagonal prediction/gain cases now continue through all
posterior products and QR, checking assembled-versus-complete-update operation
order, validation, decoded zero support, returned bounds, and the independent
scalar covariance formula. An additional 216 local correction cases cover
prior variance and mean headroom, both noise endpoints, opposite-sign
measurements, signed zero and a subnormal mean. Their `10⁻¹²` comparison
tolerance is an executable regression choice, separate from the proved bounds.


### Fully observed diagonal complete steps and native invariant

[`FloatObservableFilter.step_accuracy_and_invariant`](../Kalman/Proofs/FloatObservableFilter.lean)
proves the complete checked native step from the original model and stored-state
conditions in
[`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy`](../Kalman/Implementation/Correctness/FullyObservedDiagonalFilterAccuracy.lean).
State and measurement dimensions are two. F is finite decoded diagonal with entry
magnitudes at most one; H decodes to identity; Q/R are finite decoded diagonal with
diagonals in `[1,3/2]`; measurements have two finite entries of magnitude at most one. The
incoming mean/factor have sizes two/four, finite storage, mean cap `9/8`, factor cap two,
a lower positive-diagonal factor, decoded diagonality, exact covariance floor `7/16` and
diagonal cap `13/8`. These are original input conditions, without a validation run,
reached profile or desired output error premise.

The theorem derives model/input/output validation and every native stage,
including prediction, both noise factorizations, innovation QR, both gain
substitution passes, mean correction, posterior arithmetic and posterior QR.
Its public accuracy bounds are

$$
\max_{i,j}|\widehat P_{ij}^+-P^+_{\mathrm{step},ij}|\le3\cdot 2^{-30},
\qquad
\max_i|\widehat x_i^+-x^+_{\mathrm{step},i}|\le5\cdot 2^{-28}.
$$

These are approximately `2.79×10⁻⁹` and `1.86×10⁻⁸`, respectively. The ideal
comparator is the full Real prediction/correction from the **same incoming
stored factor Gram and mean**, using exactly the original F/H/Q/R/z words.
`exactStep` fixes only dimension metadata; the proved model domain ensures it
agrees with the native metadata. A joint radius weighting covariance by two
is also bounded by

$$
\delta=5\cdot 2^{-28}.
$$

The composition preserves several sharper intermediate statements:

- `FloatObservablePrediction.prediction_accuracy_sharp` gives covariance error
  `7·2⁻³²`, about `1.63×10⁻⁹`, and mean error `2⁻⁴⁶`, with the previous returned
  prediction margins. It retains the actual four/three-row QR constants plus
  original-Q factorization and rounded FL error. The older `2⁻²⁴` API remains
  a valid wider allowance.
- `FloatObservableMean.mean_accuracy_sharp` and
  `FloatObservablePosterior.correction_accuracy_and_bounds_sharp` give local
  correction mean error `9·2⁻²⁹`, about `1.68×10⁻⁸`. Stored-gain evaluation
  and imperfect-gain contributions remain included. Older `2⁻²⁵` APIs remain.
- [`RealObservableCorrection.update_sensitivity`](../Kalman/Proofs/RealObservableCorrection.lean)
  compares the rounded and ideal predicted states. Both prior variances have
  floor `15/16`; original R lies in `[1,3/2]`; the ideal predicted mean has
  magnitude at most `9/8`. Exact covariance/mean propagation coefficients are
  `2/5` and `8/13,17/30`, including covariance-dependent gain change.

Consequently the explicit full-step allowances satisfy

$$
\begin{aligned}
e_P&\le2^{-29}+\frac25(7\cdot 2^{-32})\le3\cdot 2^{-30},\\
e_x&\le9\cdot 2^{-29}+\frac8{13}2^{-46}
       +\frac{17}{30}(7\cdot 2^{-32})\le5\cdot 2^{-28}.
\end{aligned}
$$

`local_radius_caps` checks these complete expressions. Normal/subnormal and
higher-order native terms remain inside the stage allowances; the Real
sensitivity identities are exact rather than first-order truncations.

The returned finite factor remains decoded diagonal with strictly positive
diagonal. Its exact covariance has floor `7/16`, diagonal cap `17/16`, factor
cap `9/8`, and mean cap `9/8`, which derive the incoming invariant for the
next model in the same family. `run_invariant` proves that every finite prefix
of the actual `SquareRootFilter.run` succeeds and preserves that invariant
and strict-PD exact covariance. `identity_domain_nonempty` proves a complete
domain inhabitant with F=H=Q=R=I and nonzero signed mean/measurements.

This completes execution/invariance at identity dynamics and supplies a native
local δ for the existing Real contraction theorem. Original dense initialization
and accumulated error against an independently propagated ideal trajectory
are completed below. The generic `(20/3)δ` theorem remains an interface,
not an instantiated larger-family native horizon error result. Rounded dense
output has its separate positivity/accuracy theorem below.

All 600 reached diagonal grid cases now compare the public checked `step` with
its assembled prediction/correction result. A new 256-step diagonal horizon
uses identity and near-identity dyadic transitions, sign reversals, changing
noise endpoints and alternating measurements. Native validation, decoded zero
support and storage/covariance caps are checked at all 257 prefixes; seven
checkpoints agree at tolerance `10⁻¹²` with the independent ideal scalar oracle
[`ObservableHorizonReference.py`](../Kalman/Tests/ObservableHorizonReference.py).
The oracle's rounded checkpoint values agree at 120 and 160 decimal digits.
The driver returns exactly the same final factor/mean words as the explicit
step loop. This regression tolerance supplements the proved local δ and does
not certify a stronger accumulated-error bound.


### Fully observed diagonal dense initialization

[`FloatObservableInitialization.initialize_invariant`](../Kalman/Proofs/FloatObservableInitialization.lean)
derives checked `fromCovariance` success, the complete native state invariant, and initial
covariance/mean errors `2⁻⁴²` / zero against **the original dense covariance and mean
words**. The conditions in
[`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.InitializationDomain`](../Kalman/Implementation/Correctness/FullyObservedDiagonalFilterAccuracy.lean)
are two finite mean words of magnitude at most one and four finite decoded diagonal
covariance words with variances in `[1,3/2]`. Either signed zero may occupy either
off-diagonal. This is a sufficient native subset of the wider Real initial variance
interval `[1/2,3/2]`; the smaller half-to-one interval is not covered by this
initialization theorem.

All model/state/symmetry checks, Cholesky execution, finite storage, positive
diagonal and returned decoded diagonality are conclusions, rather than run
premises. The existing backward bound `2⁻⁴²` and original variance cap `3/2`
give retained covariance cap `13/8`; Cholesky's half floor supplies the native
invariant floor `7/16`. Mean words are copied exactly. `exact_initial_invariant`
establishes the independent Real initial invariant from the original covariance,
and `identity_domain_nonempty` proves a signed nonzero-mean inhabitant.

This closes initialization and native execution/invariance for the larger
fully observed family. Accumulated error against the independent ideal trajectory
and rounded dense output are completed below. A 162-case native grid
covers initial variance endpoints/interior values, mean endpoints and opposite
signed-zero covariance words, checks initialization and materialization against
the original covariance, and executes the first checked step. Its `10⁻¹⁴`
comparison tolerance supplements the proved initialization bound.


### Fully observed diagonal accumulated accuracy from original inputs

[`FloatObservableHorizon.initialized_horizon_accuracy`](../Kalman/Proofs/FloatObservableHorizon.lean)
closes the complete initialized native trajectory against **one independent Real matrix
recursion**, starting from the original dense covariance and mean words. Its only domain
premise is
[`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.HorizonDomain`](../Kalman/Implementation/Correctness/FullyObservedDiagonalFilterAccuracy.lean):
original dense initialization with diagonal variances `[1,3/2]` and mean cap one, a valid
original initialization model, and time-varying fully observed diagonal models on the
complete-step domain (`|Fᵢᵢ|≤1`, Q/R diagonals `[1,3/2]`, measurement cap one). There is
no successful run, reached arithmetic profile, unknown error or independently assumed
reference-state bound in this domain.

At every prefix `t≤horizon`, initialization and the actual native driver succeed,
the native stored invariant persists, and the entrywise/component bounds are

$$
\max_{i,j}|\widehat P_{t,ij}-P_{t,ij}|\le 5\cdot 2^{-30},\qquad
\max_i|\widehat x_{t,i}-x_{t,i}|\le 2^{-24}.
$$

These are approximately `4.66×10⁻⁹` and `5.96×10⁻⁸`. Native covariance is the
exact Gram of the retained Float factor; the independently propagated covariance
uses the original dense input and original F/H/Q/R/z words. Both are strictly PD.
The native covariance floor is `7/16`; the independent Real floor is `1/2`.
The bounds do not increase with the finite horizon length.

[`RealObservableHorizon`](../Kalman/Proofs/RealObservableHorizon.lean) proves
that the fixed-dimension view of each original model equals the source diagonal
specification and derives the independent Real invariant at every prefix.
`step_accumulated_accuracy` combines the actual local step proof with exact
sensitivity, including covariance-dependent gain changes. With Eₚ=`5·2⁻³⁰`
and Eₓ=`2⁻²⁴`, `uniform_budget_caps` proves the complete inequalities

$$
\begin{aligned}
3\cdot 2^{-30}+\frac9{25}E_P&\le E_P,\\
5\cdot 2^{-28}+\frac35E_x+\frac12E_P&\le E_x,\\
2^{-42}&\le E_P.
\end{aligned}
$$

The zero mean initialization error also fits Eₓ. This uses separate component
budgets rather than the looser joint estimate `(20/3)δ`. It retains all stage
terms through the completed local allowances and exact Real sensitivity;
it is not a first-order truncation or a sharpness claim.
`identity_domain_nonempty` and `near_identity_domain_nonempty` discharge the
original-input domain for every finite horizon, with nonzero signed means and
native transition words for identity or `diag(1023/1024,−1)`.

The independent 256-step regression now starts from original dense variances
`5/4` and `3/2`, so its Cholesky square roots are not both exactly representable.
It uses changing Q/R endpoints, identity/sign reversals and near-identity dynamics.
Seven scalar ideal checkpoints independently evaluated at 120 and 160 digits
round identically; native invariants and materialization are checked at all 257
prefixes. The `10⁻¹²` regression tolerance supplements the proved uniform bound.
The following theorem completes rounded dense positivity and its additional
covariance error; this horizon result itself concerns the retained factor covariance.


### Fully observed diagonal rounded dense horizon output

[`FloatObservableDenseOutput.initialized_dense_horizon_accuracy`](../Kalman/Proofs/FloatObservableDenseOutput.lean)
completes the initialized filter's rounded dense output at every finite prefix. The only
domain premise is the same original-input
`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.HorizonDomain`; no native
run, materialization, symmetry, spectral floor or unknown output error is assumed. Its
public contract is
[`Implementation.Correctness.FullyObservedDiagonalFilterAccuracy.DenseHorizonAccuracy`](../Kalman/Implementation/Correctness/FullyObservedDiagonalFilterAccuracy.lean).

The actual checked native materialization succeeds, returns finite correctly
shaped output, copies the mean words, and has exactly equal off-diagonal Float
words. No averaging or symmetry repair is performed. Decoding those words gives
a Hermitian Real matrix, separately from the retained factor Gram.
Against the independent ideal trajectory from the original dense initial words,

$$
\max_{i,j}|P^{\mathrm{dense}}_{t,ij}-P_{t,ij}|
\le 5\cdot 2^{-30}+2^{-48},\qquad
\max_i|x^{\mathrm{dense}}_{t,i}-x_{t,i}|\le2^{-24}.
$$

The separate multiplication error is `2⁻⁴⁸`. The decoded dense covariance has
completed strict-PD floor

$$
\frac7{16}-2\cdot 2^{-48}=\frac7{16}-2^{-47}\ge\frac38>0.
$$

`materialization_positive` derives this from the native invariant's exact Gram
floor `7/16`, the finite checked multiplication bound and exact native symmetry.
The two-state entrywise perturbation costs twice its radius in the spectral
floor. This supplies the positivity argument that a rounded Gram needs; factor
positivity alone is not substituted for dense positivity.

`FloatMaterialization.two_state_dot_mass_of_diagonal_cap` and
`two_state_accuracy_of_diagonal_cap` expose the reusable proof with only factor
validity and Gram diagonal cap two. No mean magnitude premise is needed for
materialization, so the observable native mean cap `9/8` is covered. The older
small-dynamics invariant APIs remain as compatibility corollaries. The proof
uses `2|ab|≤a²+b²`, the same pinned FLARE arithmetic/native-model bridge and the
unchanged native product schedule; no new arithmetic assumption is introduced.

A 108-case dense grid covers the larger mean cap, signed-zero upper/lower
positions and factor diagonals `3/4,1,5/4`. It checks exact off-diagonal word
agreement, copied mean words, an independent diagonal polynomial reference and
the simpler `3/8` floor. The 256-step near-identity original-input regression
also checks this dense floor at all 257 prefixes. These are executable
regressions alongside the completed proofs.


### Remaining generalizations

The complete square-root accuracy composition and original-input finite-horizon
bound are proved for the documented two-state family. Two-state Cholesky has an
original-input success/error domain, and two-state solves derive all row profiles
from stored input bounds. Broader Cholesky/solve and QR dimensions, wider
dynamics and weaker scale/rank margins remain generalizations. Dense output
now has success, exact symmetry, accumulated accuracy and a PD floor derived
from the same original-input two-state horizon domain. Generic materialization
outside that family retains its separate error and positivity conditions.
Statistical consistency, physical state-estimation accuracy and hardware/compiler
refinement remain outside these numerical implementation theorems.

The native regressions also exercise 400 small-gain correlated covariance/mean
steps with alternating measurements, comparing the factor filter against a
separate native Joseph evaluation, plus the exact retained signed-zero reset
fixture. The trace driver is also checked for propagation of a rejected prefix.
This executable agreement supplements the proofs; it does not itself
discharge the 400-step Real operand domain or certify a sharper tolerance.
