import Kalman.Proofs.FloatMaterialization
import Kalman.Proofs.FloatCounterexamples

/-! A PD retained factor whose optional rounded dense covariance is zero.
This certifies why factor-denotation positivity and dense-output positivity
cannot be conflated, even in one dimension. -/

namespace Kalman.Proofs.FloatUnderflow

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.FloatFactorValidity
open Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The lower entry is exactly 2⁻⁶⁰⁰; its exact square is 2⁻¹²⁰⁰. -/
def factor : Input.FactorState := ⟨#[0.0], #[Float.ofBits 0x1a70000000000000]⟩

def dense : Input.State := ⟨#[0.0], #[0.0]⟩

theorem retained_posDef : (factorState 1 factor).covariance.PosDef :=
  validFactor_posDef 1 factor (factor_validate_sound 1 factor (by decide +kernel))

theorem materialization_zero
    : Kalman.Implementation.SquareRootFilter.materialize 1 factor = .ok dense := by
  decide +kernel

theorem dense_not_posDef : ¬(state 1 dense).covariance.PosDef := by
  intro hp
  have hx : (fun _ : Fin 1 => (1 : ℝ)) ≠ 0 := by
    intro h
    have hh := congrFun h (0 : Fin 1)
    change (1 : ℝ) = 0 at hh
    norm_num at hh
  have h := hp.dotProduct_mulVec_pos hx
  simp [dotProduct, Matrix.mulVec, state, dense, Flare.Matrix.Value.matrix,
    Flare.Binary64.Arithmetic.zero_value] at h

end Kalman.Proofs.FloatUnderflow
