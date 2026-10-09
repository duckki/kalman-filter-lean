import Kalman.Proofs.FloatCounterexamples

/-! A nine-step native compact-filter failure on one fixed scalar model.
The first eight native covariances are positive; the ninth is negative.
All exact Real covariances are PD. This is delayed loss of positivity, not a
claim that absolute forward error increases monotonically along the trace. -/

namespace Kalman.Proofs.FloatTraceCounterexample

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.FloatCounterexamples
open Flare.Binary64.Value
open Matrix

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def input : Input.Model :=
  ⟨
    1,
    1,
    #[Float.ofBits 0x4160000000000000],
    #[Float.ofBits 0x3ffecc02dca65478],
    #[Float.ofBits 0x3d00000000000000],
    #[Float.ofBits 0x3c00000000000000],
    #[0.0]
  ⟩

/-- Initial covariance followed by the nine posterior bit patterns. -/
def covarianceBits : Array UInt64 :=
  #[
    0x3ff0000000000000,
    0x3f80000000000000,
    0x3f10000000000000,
    0x3ea0000000000000,
    0x3e30000000000000,
    0x3dc0000000000000,
    0x3d50000000000000,
    0x3ce0000000000002,
    0x3c70000000000102,
    0xbc10000000008102
  ]

def expected (t : Nat) : Input.State :=
  ⟨#[0.0], #[Float.ofBits (covarianceBits.getD t 0)]⟩

def run : Nat → Except Input.Error Input.State
  | 0 => .ok (expected 0)
  | t + 1 => do Kalman.Implementation.CovarianceFilter.step .compact input (← run t)

theorem transition_certificates
    : ∀ t : Fin 9,
        Kalman.Implementation.CovarianceFilter.step .compact input (expected t.val)
        = .ok (expected (t.val + 1)) := by
  decide +kernel

theorem run_certificate : ∀ t, t ≤ 9 → run t = .ok (expected t) := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run, ih (by omega)]
      exact transition_certificates ⟨t, by omega⟩

theorem finite_trace : ∀ t : Fin 10, (expected t.val).validate 1 = .ok () := by
  decide +kernel

theorem positive_prefix : ∀ t : Fin 9, 0 < (state 1 (expected t.val)).covariance 0 0 := by
  have hc : ∀ t : Fin 9,
      (Float.ofBits (covarianceBits.getD t.val 0)).isFinite = true ∧
      (0.0 : Float) < Float.ofBits (covarianceBits.getD t.val 0) := by decide +kernel
  intro t
  have h := (Flare.Binary64.Order.lt_iff _ _ (by decide) (hc t).1).mp (hc t).2
  change 0 < value (Float.ofBits (covarianceBits.getD t.val 0))
  simpa only [Flare.Binary64.Arithmetic.zero_value] using h

theorem negative_final
    : dotProduct (fun _ : Fin 1 => (1 : ℝ))
        ((state 1 (expected 9)).covariance *ᵥ (fun _ => 1))
      < 0 := by
  have hn : value (Float.ofBits 0xbc10000000008102) < 0 := by
    have h := (Flare.Binary64.Order.lt_iff (Float.ofBits 0xbc10000000008102) 0.0
      (by decide +kernel) (by decide)).mp (by decide +kernel)
    simpa only [Flare.Binary64.Arithmetic.zero_value] using h
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one]
  change 1 * (value (Float.ofBits 0xbc10000000008102) * 1) < 0
  simpa using hn

theorem input_valid : input.validate = .ok () := by decide +kernel

theorem noise_posDef
    : (model input).processNoise.PosDef ∧ (model input).measurementNoise.PosDef := by
  constructor
  · apply scalar_posDef (Float.ofBits 0x3d00000000000000)
    have h := (Flare.Binary64.Order.lt_iff 0.0 (Float.ofBits 0x3d00000000000000)
      (by decide) (by decide +kernel)).mp (by decide +kernel)
    simpa only [Flare.Binary64.Arithmetic.zero_value] using h
  · apply scalar_posDef (Float.ofBits 0x3c00000000000000)
    have h := (Flare.Binary64.Order.lt_iff 0.0 (Float.ofBits 0x3c00000000000000)
      (by decide) (by decide +kernel)).mp (by decide +kernel)
    simpa only [Flare.Binary64.Arithmetic.zero_value] using h

noncomputable def exactState : Nat → LinearModel.State 1
  | 0 => state 1 (expected 0)
  | t + 1 => CovarianceRecursion.step .compact (model input) (exactState t) 0

theorem exact_trace_posDef (t : Nat) : (exactState t).covariance.PosDef := by
  induction t with
  | zero => exact scalar_posDef 1.0 (by norm_num [Flare.Binary64.Arithmetic.one_value])
  | succ t ih =>
      exact Kalman.Proofs.RealRecursion.step_posDef .compact (model input)
        (exactState t) 0 ih.posSemidef noise_posDef.1 noise_posDef.2

/-- The failure certificate relates the actual iterated native execution to
the iterated exact specification, rather than restarting from rounded P. -/
theorem repeated_failure
    : run 9 = .ok (expected 9)
      ∧ dotProduct (fun _ : Fin 1 => (1 : ℝ))
          ((state 1 (expected 9)).covariance *ᵥ (fun _ => 1))
        < 0
      ∧ (exactState 9).covariance.PosDef :=
  ⟨run_certificate 9 (by omega), negative_final, exact_trace_posDef 9⟩

end Kalman.Proofs.FloatTraceCounterexample
