import Kalman.Proofs.ArithmeticProfiles
import Kalman.Proofs.CholeskyProfiles
import Kalman.Proofs.QRProfiles
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FilterComposition
import Kalman.Proofs.FloatFilterHorizon

/-! Closed coefficient checks for a uniform absolute covariance/mean budget.
These do not claim that arbitrary native models meet the operand profiles. -/

namespace Kalman.Proofs.FloatFilterBudget

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.ArithmeticProfiles
open Kalman.Proofs.CholeskyProfiles
open Kalman.Proofs.QRProfiles
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.SquareRootProfiles.Error
open Kalman.Implementation.Correctness.SquareRootFilterProperties
open Kalman.Proofs.SquareRootProfiles.Update
open Kalman.Proofs.FilterComposition
open Kalman.Proofs.FilterComposition.Budget

set_option maxHeartbeats 1600000

theorem uniform_parameters_radii {input : Input.Model} {initial : Input.FactorState}
    {reference : LinearModel.State input.stateDimension} (p : StepProfile input initial)
    (d : StepEnvironment input reference) (h : UniformStepParameters p d) (eP eX : ℝ)
    : stepCovarianceRadius p d eP = uniformCovarianceRadius eP
      ∧ stepMeanRadius p d eP eX = uniformMeanRadius eP eX := by
  rcases h with ⟨hn, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩
  constructor <;> simp only [
    stepCovarianceRadius, stepMeanRadius, predictedCovarianceRadius, predictedMeanRadius, predictionCovarianceRadius, predictionMeanRadius, posteriorRadius, posteriorEvaluationRadius, meanRadius, gainRadius, gainResidualRadius, innovationRadius, uniformCovarianceRadius, uniformMeanRadius, propagatedCovariance, propagatedMean, localPrediction, localGain, localPosterior, gainMagnitude, correctionCovarianceRadius, correctionMeanRadius, correctionGainRadius, hn, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34] <;> norm_num <;> ring

private theorem denormal_unit
    : 0 ≤ (2 : ℝ) ^ (-1022 : Int) ∧ (2 : ℝ) ^ (-1022 : Int) ≤ 1 := by
  constructor
  · positivity
  · simpa using (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (-1022 : Int) ≤ 0))

theorem uniform_covariance_cap (eP : ℝ) (hP : 0 ≤ eP) (hP' : eP ≤ 1 / 128)
    : uniformCovarianceRadius eP ≤ 1 / 128 := by
  have hm : uniformCovarianceRadius eP ≤ uniformCovarianceRadius (1 / 128) := by
    norm_num [uniformCovarianceRadius, correctionCovarianceRadius, correctionGainRadius, gainMagnitude,
      propagatedCovariance, localPosterior, localGain, localPrediction,
      qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
      productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius]
    gcongr <;> first | assumption | positivity | linarith
  apply hm.trans
  let η : ℝ := (2 : ℝ) ^ (-1022 : Int)
  have hη : (2 : ℝ) ^ (-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := denormal_unit.1
  have hη1 : η ≤ 1 := denormal_unit.2
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  have hη3 := pow_le_one₀ hη0 hη1 (n := 3)
  have hη4 := pow_le_one₀ hη0 hη1 (n := 4)
  simp only [uniformCovarianceRadius, correctionCovarianceRadius, correctionGainRadius, gainMagnitude,
    propagatedCovariance, localPosterior, localGain, localPrediction,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
    productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius, hη]
  norm_num
  ring_nf
  linarith

theorem uniform_mean_cap (eP eX : ℝ) (hP : 0 ≤ eP) (hP' : eP ≤ 1 / 128)
    (hX : 0 ≤ eX) (hX' : eX ≤ 1 / 128)
    : uniformMeanRadius eP eX ≤ 1 / 128 := by
  have hm : uniformMeanRadius eP eX ≤ uniformMeanRadius (1 / 128) (1 / 128) := by
    norm_num [uniformMeanRadius, correctionMeanRadius, correctionGainRadius, gainMagnitude,
      propagatedCovariance, propagatedMean, localGain, localPrediction,
      qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
      productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius]
    gcongr <;> first | assumption | positivity | linarith
  apply hm.trans
  let η : ℝ := (2 : ℝ) ^ (-1022 : Int)
  have hη : (2 : ℝ) ^ (-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := denormal_unit.1
  have hη1 : η ≤ 1 := denormal_unit.2
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  simp only [uniformMeanRadius, correctionMeanRadius, correctionGainRadius, gainMagnitude,
    propagatedCovariance, propagatedMean, localGain, localPrediction,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
    productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius, hη]
  norm_num
  ring_nf
  linarith

/-- Sharper QR estimates close an 8192-times smaller uniform budget with
exactly the same numerical stage allowances. -/
theorem tight_uniform_covariance_cap (eP : ℝ) (hP : 0 ≤ eP) (hP' : eP ≤ 1 / 1048576)
    : uniformCovarianceRadius eP ≤ 1 / 1048576 := by
  have hm : uniformCovarianceRadius eP ≤ uniformCovarianceRadius (1 / 1048576) := by
    norm_num [uniformCovarianceRadius, correctionCovarianceRadius, correctionGainRadius, gainMagnitude,
      propagatedCovariance, localPosterior, localGain, localPrediction,
      qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
      productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius]
    gcongr <;> first | assumption | positivity | linarith
  apply hm.trans
  let η : ℝ := (2 : ℝ) ^ (-1022 : Int)
  have hη : (2 : ℝ) ^ (-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := denormal_unit.1
  have hη1 : η ≤ 1 := denormal_unit.2
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  have hη3 := pow_le_one₀ hη0 hη1 (n := 3)
  have hη4 := pow_le_one₀ hη0 hη1 (n := 4)
  simp only [uniformCovarianceRadius, correctionCovarianceRadius, correctionGainRadius, gainMagnitude,
    propagatedCovariance, localPosterior, localGain, localPrediction,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
    productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius, hη]
  norm_num
  ring_nf
  linarith

theorem tight_uniform_mean_cap (eP eX : ℝ) (hP : 0 ≤ eP) (hP' : eP ≤ 1 / 1048576)
    (hX : 0 ≤ eX) (hX' : eX ≤ 1 / 1048576)
    : uniformMeanRadius eP eX ≤ 1 / 1048576 := by
  have hm : uniformMeanRadius eP eX ≤ uniformMeanRadius (1 / 1048576) (1 / 1048576) := by
    norm_num [uniformMeanRadius, correctionMeanRadius, correctionGainRadius, gainMagnitude,
      propagatedCovariance, propagatedMean, localGain, localPrediction,
      qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
      productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius]
    gcongr <;> first | assumption | positivity | linarith
  apply hm.trans
  let η : ℝ := (2 : ℝ) ^ (-1022 : Int)
  have hη : (2 : ℝ) ^ (-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := denormal_unit.1
  have hη1 : η ≤ 1 := denormal_unit.2
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  simp only [uniformMeanRadius, correctionMeanRadius, correctionGainRadius, gainMagnitude,
    propagatedCovariance, propagatedMean, localGain, localPrediction,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
    productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius, hη]
  norm_num
  ring_nf
  linarith

/-- Dimension-sensitive QR estimates close a 262144-times smaller uniform budget with
exactly the same numerical stage allowances. -/
theorem refined_uniform_covariance_cap (eP : ℝ) (hP : 0 ≤ eP) (hP' : eP ≤ 1 / 33554432)
    : uniformCovarianceRadius eP ≤ 1 / 33554432 := by
  have hm : uniformCovarianceRadius eP ≤ uniformCovarianceRadius (1 / 33554432) := by
    norm_num [uniformCovarianceRadius, correctionCovarianceRadius, correctionGainRadius, gainMagnitude,
      propagatedCovariance, localPosterior, localGain, localPrediction,
      qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
      productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius]
    gcongr <;> first | assumption | positivity | linarith
  apply hm.trans
  let η : ℝ := (2 : ℝ) ^ (-1022 : Int)
  have hη : (2 : ℝ) ^ (-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := denormal_unit.1
  have hη1 : η ≤ 1 := denormal_unit.2
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  have hη3 := pow_le_one₀ hη0 hη1 (n := 3)
  have hη4 := pow_le_one₀ hη0 hη1 (n := 4)
  simp only [uniformCovarianceRadius, correctionCovarianceRadius, correctionGainRadius, gainMagnitude,
    propagatedCovariance, localPosterior, localGain, localPrediction,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
    productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius, hη]
  norm_num
  ring_nf
  linarith

theorem refined_uniform_mean_cap (eP eX : ℝ) (hP : 0 ≤ eP) (hP' : eP ≤ 1 / 33554432)
    (hX : 0 ≤ eX) (hX' : eX ≤ 1 / 33554432)
    : uniformMeanRadius eP eX ≤ 1 / 33554432 := by
  have hm : uniformMeanRadius eP eX ≤ uniformMeanRadius (1 / 33554432) (1 / 33554432) := by
    norm_num [uniformMeanRadius, correctionMeanRadius, correctionGainRadius, gainMagnitude,
      propagatedCovariance, propagatedMean, localGain, localPrediction,
      qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
      productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius]
    gcongr <;> first | assumption | positivity | linarith
  apply hm.trans
  let η : ℝ := (2 : ℝ) ^ (-1022 : Int)
  have hη : (2 : ℝ) ^ (-1022 : Int) = η := rfl
  have hη0 : 0 ≤ η := denormal_unit.1
  have hη1 : η ≤ 1 := denormal_unit.2
  have hη2 := pow_le_one₀ hη0 hη1 (n := 2)
  simp only [uniformMeanRadius, correctionMeanRadius, correctionGainRadius, gainMagnitude,
    propagatedCovariance, propagatedMean, localGain, localPrediction,
    qrGramRadius, iterationGramRadius, iterationRadius, sourceWriteRadius, sourceResidualRadius, columnNormRadius, squareSumRadius, reflectorRadius, applicationRadius, Finset.sum_range_succ, Finset.sum_range_zero,
    productRadius, diagonalRadius, divisionRadius, residualRadius, sumRadius, hη]
  norm_num
  ring_nf
  linarith

/-- Close the horizon's algebraic budget conditions using the fixed constants. -/
noncomputable def uniform_horizon_domain (horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State 2)
    (d : UniformHorizonDomain horizon inputs initial reference)
    : Kalman.Proofs.FilterComposition.Horizon.HorizonDomain
        2 2 horizon inputs initial reference (fun _ => 1 / 128) (fun _ => 1 / 128) := by
  refine {
    toHorizonOperands := d.operands
    initial_accuracy := d.initial_accuracy
    covariance_cap := ?_
    mean_cap := ?_
  }
  · intro t ht current hrun
    rw [(uniform_parameters_radii _ _ (d.parameters t ht current hrun) (1 / 128) (1 / 128)).1]
    exact uniform_covariance_cap _ (by norm_num) le_rfl
  · intro t ht current hrun
    rw [(uniform_parameters_radii _ _ (d.parameters t ht current hrun) (1 / 128) (1 / 128)).2]
    exact uniform_mean_cap _ _ (by norm_num) le_rfl (by norm_num) le_rfl

/-- Any finite length is allowed: both absolute errors stay at most 1/128
when the documented two-state reached-prefix domains hold throughout. -/
theorem uniform_horizon_accuracy (horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State 2)
    (d : UniformHorizonDomain horizon inputs initial reference)
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            Kalman.Implementation.Correctness.InputInterpretation.nativeRun inputs initial
                t
              = .ok output
            ∧ FactorAccuracy (1 / 128) (1 / 128) 2 output
                (Kalman.Implementation.Correctness.InputInterpretation.exactRun 2 2 inputs
                  reference t)
            ∧ (factorState 2 output).covariance.PosDef
            ∧ (Kalman.Implementation.Correctness.InputInterpretation.exactRun 2 2 inputs
                reference t).covariance.PosDef :=
  FloatFilterHorizon.finite_horizon_accuracy 2 2 horizon inputs initial reference _ _
    (uniform_horizon_domain horizon inputs initial reference d)

/-- Close the horizon's algebraic budget conditions using the fixed constants. -/
noncomputable def tight_uniform_horizon_domain (horizon : Nat)
    (inputs : Nat → Input.Model) (initial : Input.FactorState)
    (reference : LinearModel.State 2)
    (d : UniformHorizonDomain horizon inputs initial reference (1 / 1048576))
    : Kalman.Proofs.FilterComposition.Horizon.HorizonDomain 2 2 horizon inputs initial
        reference (fun _ => 1 / 1048576) (fun _ => 1 / 1048576) := by
  refine {
    toHorizonOperands := d.operands
    initial_accuracy := d.initial_accuracy
    covariance_cap := ?_
    mean_cap := ?_
  }
  · intro t ht current hrun
    rw [(uniform_parameters_radii _ _ (d.parameters t ht current hrun) (1 / 1048576) (1 / 1048576)).1]
    exact tight_uniform_covariance_cap _ (by norm_num) le_rfl
  · intro t ht current hrun
    rw [(uniform_parameters_radii _ _ (d.parameters t ht current hrun) (1 / 1048576) (1 / 1048576)).2]
    exact tight_uniform_mean_cap _ _ (by norm_num) le_rfl (by norm_num) le_rfl

/-- Any finite length is allowed: both absolute errors stay at most 1/1048576
when the documented two-state reached-prefix domains hold throughout. -/
theorem tight_uniform_horizon_accuracy (horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State 2)
    (d : UniformHorizonDomain horizon inputs initial reference (1 / 1048576))
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            Kalman.Implementation.Correctness.InputInterpretation.nativeRun inputs initial
                t
              = .ok output
            ∧ FactorAccuracy (1 / 1048576) (1 / 1048576) 2 output
                (Kalman.Implementation.Correctness.InputInterpretation.exactRun 2 2 inputs
                  reference t)
            ∧ (factorState 2 output).covariance.PosDef
            ∧ (Kalman.Implementation.Correctness.InputInterpretation.exactRun 2 2 inputs
                reference t).covariance.PosDef :=
  FloatFilterHorizon.finite_horizon_accuracy 2 2 horizon inputs initial reference _ _
    (tight_uniform_horizon_domain horizon inputs initial reference d)

/-- Close the horizon's algebraic budget conditions using the fixed constants. -/
noncomputable def refined_uniform_horizon_domain (horizon : Nat)
    (inputs : Nat → Input.Model) (initial : Input.FactorState)
    (reference : LinearModel.State 2)
    (d : UniformHorizonDomain horizon inputs initial reference (1 / 33554432))
    : Kalman.Proofs.FilterComposition.Horizon.HorizonDomain 2 2 horizon inputs initial
        reference (fun _ => 1 / 33554432) (fun _ => 1 / 33554432) := by
  refine {
    toHorizonOperands := d.operands
    initial_accuracy := d.initial_accuracy
    covariance_cap := ?_
    mean_cap := ?_
  }
  · intro t ht current hrun
    rw [(uniform_parameters_radii _ _ (d.parameters t ht current hrun) (1 / 33554432) (1 / 33554432)).1]
    exact refined_uniform_covariance_cap _ (by norm_num) le_rfl
  · intro t ht current hrun
    rw [(uniform_parameters_radii _ _ (d.parameters t ht current hrun) (1 / 33554432) (1 / 33554432)).2]
    exact refined_uniform_mean_cap _ _ (by norm_num) le_rfl (by norm_num) le_rfl

/-- Any finite length is allowed: both absolute errors stay at most 1/33554432
when the documented two-state reached-prefix domains hold throughout. -/
theorem refined_uniform_horizon_accuracy (horizon : Nat) (inputs : Nat → Input.Model)
    (initial : Input.FactorState) (reference : LinearModel.State 2)
    (d : UniformHorizonDomain horizon inputs initial reference (1 / 33554432))
    : ∀ t,
        t ≤ horizon
        → ∃ output,
            Kalman.Implementation.Correctness.InputInterpretation.nativeRun inputs initial
                t
              = .ok output
            ∧ FactorAccuracy (1 / 33554432) (1 / 33554432) 2 output
                (Kalman.Implementation.Correctness.InputInterpretation.exactRun 2 2 inputs
                  reference t)
            ∧ (factorState 2 output).covariance.PosDef
            ∧ (Kalman.Implementation.Correctness.InputInterpretation.exactRun 2 2 inputs
                reference t).covariance.PosDef :=
  FloatFilterHorizon.finite_horizon_accuracy 2 2 horizon inputs initial reference _ _
    (refined_uniform_horizon_domain horizon inputs initial reference d)

end Kalman.Proofs.FloatFilterBudget
