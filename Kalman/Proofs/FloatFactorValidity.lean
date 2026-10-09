import Kalman.Implementation.Correctness.SquareRootFilterProperties
import Kalman.Proofs.SquareRootProfiles
import Kalman.Proofs.FactorStructure
import Flare.Binary64.Order
import Flare.Matrix.Storage

/-! Successful retained-factor steps have a strictly PD exact Gram denotation.
This follows from the enforced output validation, not from assuming exact QR
or a backward-error estimate. It does not promise success or dense-output PD. -/

namespace Kalman.Proofs.FloatFactorValidity

open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Proofs.SquareRootProfiles
open Kalman.Implementation.Correctness.SquareRootFilterProperties

theorem factor_validate_sound (n : Nat) (output : Input.FactorState)
    (h : output.validate n = .ok ())
    : ValidFactor n output := by
  have hchecks :
      output.lower.all Float.isFinite = true ∧
      (Array.range n).all (fun i => decide (0.0 < output.lower.getD (i * n + i) 0.0)) = true ∧
      (Array.range n).all (fun i => (Array.range n).all
        (fun j => if i < j then output.lower.getD (i * n + j) 0.0 == 0.0 else true)) = true := by
    cases hshape : (output.mean.size == n && output.lower.size == n * n) with
    | false =>
        simp only [Input.FactorState.validate, hshape, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    | true =>
        cases hfinite
              : (output.mean.all Float.isFinite && output.lower.all Float.isFinite) with
        | false =>
            simp only [Input.FactorState.validate, hshape, hfinite, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        | true =>
            cases hdiag
                  : (Array.range n).all
                      (fun i => decide (0.0 < output.lower.getD (i * n + i) 0.0)) with
            | false =>
                simp only [Input.FactorState.validate, hshape, hfinite, hdiag, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
            | true =>
                cases htri
                      : (Array.range n).all
                          (fun i =>
                            (Array.range n).all
                              (fun j =>
                                if i < j then
                                  output.lower.getD (i * n + j) 0.0 == 0.0
                                else
                                  true)) with
                | false =>
                    simp only [Input.FactorState.validate, hshape, hfinite, hdiag, htri, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
                | true => exact ⟨(Bool.and_eq_true_iff.mp hfinite).2, rfl, rfl⟩
  obtain ⟨hf, hd, ht⟩ := hchecks
  refine ⟨h, ?_, ?_⟩
  · intro i j hij
    rw [Array.all_eq_true] at ht
    have hi := ht i.val (by simp)
    rw [Array.all_eq_true] at hi
    have hj := hi j.val (by simp)
    simp only [Array.getElem_range] at hj
    simp only [show i.val < j.val from hij, ↓reduceIte] at hj
    have he := (Flare.Binary64.Order.beq_iff _ _
      (Flare.Matrix.Storage.getD_finite _ _ hf) (by decide)).mp hj
    simpa only [Flare.Binary64.Arithmetic.zero_value, Flare.Matrix.Value.matrix] using he
  · intro i
    rw [Array.all_eq_true] at hd
    have hi := hd i.val (by simp)
    simp only [Array.getElem_range] at hi
    have he := (Flare.Binary64.Order.lt_iff _ _ (by decide)
      (Flare.Matrix.Storage.getD_finite _ _ hf)).mp (of_decide_eq_true hi)
    simpa only [Flare.Binary64.Arithmetic.zero_value, Flare.Matrix.Value.matrix] using he

theorem validFactor_posDef (n : Nat) (output : Input.FactorState)
    (h : ValidFactor n output)
    : (factorState n output).covariance.PosDef :=
  Kalman.Proofs.FactorStructure.lowerPositive_gram_posDef _ h.2

/-- Finite correctly shaped storage and exact lower-positive interpretation
imply all executable factor checks, including the native diagonal comparisons. -/
theorem factor_validate_complete (n : Nat) (output : Input.FactorState)
    (hm : output.mean.size = n) (hl : output.lower.size = n * n)
    (hfm : output.mean.all Float.isFinite = true)
    (hfl : output.lower.all Float.isFinite = true)
    (hp : FactorRecursion.LowerPositive (matrix n n output.lower))
    : ValidFactor n output := by
  have hd : (Array.range n).all (fun i => decide (0.0 < output.lower.getD (i * n + i) 0.0)) = true := by
    rw [Array.all_eq_true]
    intro i hi
    simp only [Array.size_range] at hi
    simp only [Array.getElem_range, decide_eq_true_eq]
    apply (Flare.Binary64.Order.lt_iff _ _ (by decide)
            (Flare.Matrix.Storage.getD_finite _ _ hfl)).mpr
    simpa only [Flare.Binary64.Arithmetic.zero_value, Flare.Matrix.Value.matrix] using hp.2 ⟨i, hi⟩
  have ht : (Array.range n).all (fun i => (Array.range n).all
      (fun j => if i < j then output.lower.getD (i * n + j) 0.0 == 0.0 else true)) = true := by
    rw [Array.all_eq_true]
    intro i hi
    rw [Array.all_eq_true]
    intro j hj
    simp only [Array.size_range] at hi hj
    simp only [Array.getElem_range]
    split_ifs with hij
    · apply (Flare.Binary64.Order.beq_iff _ _
              (Flare.Matrix.Storage.getD_finite _ _ hfl) (by decide)).mpr
      simpa only [Flare.Binary64.Arithmetic.zero_value, Flare.Matrix.Value.matrix]
        using hp.1 ⟨i, hi⟩ ⟨j, hj⟩ hij
    · rfl
  refine ⟨?_, hp⟩
  have hs : (output.mean.size == n && output.lower.size == n * n) = true := by simp [hm, hl]
  simp only [Input.FactorState.validate, hs, hfm, hfl, Bool.true_and, hd, ht,
    ↓reduceIte]

theorem successfulStepPositiveDefinite : SuccessfulStepPositiveDefinite := by
  intro input initial output hi hs he
  unfold Kalman.Implementation.SquareRootFilter.step at he
  rw [hi, hs] at he
  dsimp only [bind, Except.bind] at he
  cases hp : Kalman.Implementation.SquareRootFilter.predictUnchecked input initial with
  | error e => simp [hp] at he
  | ok prior =>
      rw [hp] at he
      dsimp only [bind, Except.bind] at he
      cases hu : Kalman.Implementation.SquareRootFilter.updateUnchecked input prior with
      | error e => simp [hu] at he
      | ok result =>
          rw [hu] at he
          dsimp only [bind, Except.bind] at he
          cases hv : result.validate input.stateDimension with
          | error e => simp [hv] at he
          | ok resultUnit =>
              have hout : result = output := by simpa [hv, pure, Except.pure] using he
              subst output
              have hvalid := factor_validate_sound input.stateDimension result (by simpa using hv)
              exact ⟨hvalid, validFactor_posDef _ _ hvalid⟩

end Kalman.Proofs.FloatFactorValidity
