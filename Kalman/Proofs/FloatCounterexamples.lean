import Kalman.Proofs.RealRecursion
import Kalman.Implementation.Correctness.CovarianceCounterexamples
import Flare.Binary64.Order

/-! Kernel-evaluated binary64 counterexamples for the actual checked filter.
`decide +kernel` uses logical reduction, without the `native_decide` axiom.
The input bit patterns denote exactly the Real inputs used in the PD proof. -/

namespace Kalman.Proofs.FloatCounterexamples

open Kalman.Definitions
open Matrix
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Implementation.Correctness.CovarianceCounterexamples
open Flare.Binary64.Value

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

-- Instances are proof tooling; the runtime modules do not import this module.
deriving instance DecidableEq for Input.State
deriving instance DecidableEq for Except

def negativeInput : Input.Model :=
  ⟨
    1,
    1,
    #[0.0],
    #[Float.ofBits 0x3ffd8a8f075e6e3b],
    #[1.0],
    #[Float.ofBits 0x3c30000000000000],
    #[0.0]
  ⟩

def initial : Input.State := ⟨#[0.0], #[1.0]⟩

def negativeOutput : Input.State := ⟨#[0.0], #[Float.ofBits 0xbcb0000000000000]⟩

def josephOutput : Input.State := ⟨#[0.0], #[Float.ofBits 0x3c12c6348dfc2caf]⟩

theorem scalar_posDef (a : Float) (ha : 0 < value a) : (matrix 1 1 #[a]).PosDef := by
  have heq : matrix 1 1 #[a] = Matrix.diagonal (fun _ : Fin 1 => value a) := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [heq]
  exact Matrix.posDef_diagonal_iff.mpr fun _ => ha

theorem negative_output_value
    : value (Float.ofBits 0xbcb0000000000000) = -(2 : ℝ) ^ (-52 : Int) := by
  change ((-4503599627370496 : Int) : ℝ) * (2 : ℝ)^(-104 : Int) = _
  norm_num

theorem small_noise_value
    : value (Float.ofBits 0x3c30000000000000) = (2 : ℝ) ^ (-60 : Int) := by
  change (4503599627370496 : ℝ) * (2 : ℝ)^(-112 : Int) = _
  norm_num

theorem negative_input_strict
    : Theorems.CovariancePositiveDefiniteness.StrictDomain (model negativeInput)
        (state 1 initial) := by
  refine ⟨
    by decide,
    by decide,
    scalar_posDef 1.0 (by norm_num [Flare.Binary64.Arithmetic.one_value]),
    scalar_posDef 1.0 (by norm_num [Flare.Binary64.Arithmetic.one_value]),
    ?_
  ⟩
  exact scalar_posDef _ (small_noise_value ▸ zpow_pos (by norm_num) _)

theorem compact_negative_execution
    : Kalman.Implementation.CovarianceFilter.step .compact negativeInput initial
      = .ok negativeOutput := by
  decide +kernel

theorem subtractive_negative_execution
    : Kalman.Implementation.CovarianceFilter.step .subtractive negativeInput initial
      = .ok negativeOutput := by
  decide +kernel

theorem joseph_execution
    : Kalman.Implementation.CovarianceFilter.step .joseph negativeInput initial
      = .ok josephOutput := by
  decide +kernel

theorem observation_value
    : value (Float.ofBits 0x3ffd8a8f075e6e3b) = 8315121233194555 / 4503599627370496 := by
  change (8315121233194555 : ℝ) * (2 : ℝ)^(-52 : Int) = _
  norm_num

theorem joseph_output_value
    : value (Float.ofBits 0x3c12c6348dfc2caf)
      = 5284478603504815 / 20769187434139310514121985316880384 := by
  change (5284478603504815 : ℝ) * (2 : ℝ)^(-114 : Int) = _
  norm_num

theorem joseph_fixture_posDef : (state 1 josephOutput).covariance.PosDef := by
  apply scalar_posDef (Float.ofBits 0x3c12c6348dfc2caf)
  rw [joseph_output_value]
  norm_num

/-- The negative compact output has absolute forward error greater than
2⁻⁵² relative to the exact full step, independently of a closed scalar formula. -/
theorem compact_error_lower_bound
    : (2 : ℝ) ^ (-52 : Int)
      < |(state 1 negativeOutput).covariance 0 0
          - (CovarianceRecursion.step .compact (model negativeInput) (state 1 initial)
              0).covariance
              (0 : Fin 1) (0 : Fin 1)| := by
  let p : ℝ := (CovarianceRecursion.step .compact (model negativeInput) (state 1 initial) 0).covariance
    (0 : Fin 1) (0 : Fin 1)
  have hp := Kalman.Proofs.RealRecursion.stepPositiveDefinite 1 1 (model negativeInput)
    (state 1 initial) 0 negative_input_strict .compact
  have hdiag : 0 < p := hp.diag_pos
  change (2 : ℝ)^(-52 : Int) < |value (Float.ofBits 0xbcb0000000000000) - p|
  rw [negative_output_value]
  have hpow := zpow_pos (by norm_num : (0 : ℝ) < 2) (-52 : Int)
  have hn : -(2 : ℝ)^(-52 : Int) - p < 0 := sub_neg.mpr ((neg_neg_of_pos hpow).trans hdiag)
  rw [abs_of_neg hn]
  linarith only [hdiag]

theorem negative_quadratic
    : dotProduct (fun _ : Fin 1 => (1 : ℝ))
        ((state 1 negativeOutput).covariance *ᵥ (fun _ => 1))
      < 0 := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, state, negativeOutput,
    Flare.Matrix.Value.matrix]
  change 1 * (value (Float.ofBits 0xbcb0000000000000) * 1) < 0
  rw [negative_output_value]
  have := zpow_pos (by norm_num : (0 : ℝ) < 2) (-52 : Int)
  linarith

theorem compact_negative_witness
    : NegativeQuadraticWitness .compact negativeInput initial negativeOutput
        (fun _ => 1) := by
  refine ⟨
    by decide +kernel,
    by decide +kernel,
    negative_input_strict,
    compact_negative_execution,
    by decide +kernel,
    ?_,
    negative_quadratic,
    ?_
  ⟩
  · intro h
    have hh := congrFun h (0 : Fin 1)
    change (1 : ℝ) = 0 at hh
    norm_num at hh
  · exact Kalman.Proofs.RealRecursion.stepPositiveDefinite _ _ _ _ _ negative_input_strict .compact

theorem subtractive_negative_witness
    : NegativeQuadraticWitness .subtractive negativeInput initial negativeOutput
        (fun _ => 1) := by
  refine ⟨
    by decide +kernel,
    by decide +kernel,
    negative_input_strict,
    subtractive_negative_execution,
    by decide +kernel,
    ?_,
    negative_quadratic,
    ?_
  ⟩
  · intro h
    have hh := congrFun h (0 : Fin 1)
    change (1 : ℝ) = 0 at hh
    norm_num at hh
  · exact Kalman.Proofs.RealRecursion.stepPositiveDefinite _ _ _ _ _ negative_input_strict .subtractive

/-- Completed existential compact-failure statement. -/
theorem compactCanReturnNegativeCovariance : CompactCanReturnNegativeCovariance :=
  ⟨negativeInput, initial, negativeOutput, (fun _ => 1), compact_negative_witness⟩

/-- Completed existential subtractive-failure statement. -/
theorem subtractiveCanReturnNegativeCovariance : SubtractiveCanReturnNegativeCovariance :=
  ⟨negativeInput, initial, negativeOutput, (fun _ => 1), subtractive_negative_witness⟩

end Kalman.Proofs.FloatCounterexamples
