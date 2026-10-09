import Kalman.Definitions.Theorems.RecursionSensitivity
import Kalman.Proofs.RealErrorBounds

/-! Quantitative sensitivity of the exact prediction/correction maps.
Used to propagate native stage error to a single ideal trajectory. -/

namespace Kalman.Proofs.RecursionSensitivity

open Matrix
open Kalman.Definitions
open Kalman.Implementation.Correctness.InputInterpretation
open Kalman.Definitions.Theorems.RecursionSensitivity
open Kalman.Proofs.ErrorPropagation

theorem congruence_within {n m : Nat} (a : Matrix (Fin m) (Fin n) ℝ)
    {p q : LinearModel.Square n} {ε A : ℝ} (he : EntrywiseWithin ε p q)
    (hA : 0 ≤ A) (ha : ∀ i j, |a i j| ≤ A)
    : EntrywiseWithin (n ^ 2 * A ^ 2 * ε) (a * p * a.transpose)
        (a * q * a.transpose) := by
  have h := within_mul_right (within_mul_left a he hA ha) a.transpose hA (fun i j => ha j i)
  convert h using 1
  ring

theorem innovation_lower {n m : Nat} (input : LinearModel.Model n m)
    (prior : LinearModel.State n) (α : ℝ) (hp : prior.covariance.PosSemidef)
    (hr : (input.measurementNoise - α • 1).PosSemidef)
    : (CovarianceRecursion.innovationCovariance input prior - α • 1).PosSemidef := by
  have h := hp.mul_mul_conjTranspose_same input.observation
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  convert h.add hr using 1
  dsimp only [CovarianceRecursion.innovationCovariance]
  abel

theorem gain_magnitude {n m : Nat} (input : LinearModel.Model n m)
    (prior : LinearModel.State n) (α P H : ℝ) (hα : 0 < α) (_hP : 0 ≤ P) (_hH : 0 ≤ H)
    (hp : prior.covariance.PosSemidef) (hr : (input.measurementNoise - α • 1).PosSemidef)
    (hb : ∀ i j, |prior.covariance i j| ≤ P) (hh : ∀ i j, |input.observation i j| ≤ H)
    : ∀ i j, |CovarianceRecursion.gain input prior i j| ≤ gainMagnitude n m α P H := by
  have hinv := Flare.Analysis.NumericalBounds.inverse_entry_bound
    (CovarianceRecursion.innovationCovariance input prior) α hα (innovation_lower input prior α hp hr)
  have hc := product_magnitude prior.covariance input.observation.transpose P H hb (fun i j => hh j i)
  have hg := product_magnitude (prior.covariance * input.observation.transpose)
    (CovarianceRecursion.innovationCovariance input prior)⁻¹ (n * P * H) (1 / α) hc hinv
  simpa only [CovarianceRecursion.gain, gainMagnitude, mul_one_div] using hg

theorem gain_sensitivity {n m : Nat} (input : LinearModel.Model n m)
    (actual reference : LinearModel.State n) (α P H eP : ℝ)
    (hα : 0 < α) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hp : actual.covariance.PosSemidef) (hq : reference.covariance.PosSemidef)
    (hr : (input.measurementNoise - α • 1).PosSemidef)
    (hb : ∀ i j, |reference.covariance i j| ≤ P) (hh : ∀ i j, |input.observation i j| ≤ H)
    (he : EntrywiseWithin eP actual.covariance reference.covariance)
    : EntrywiseWithin (correctionGainRadius n m α P H eP)
        (CovarianceRecursion.gain input actual)
        (CovarianceRecursion.gain input reference) := by
  have hep := he.1
  have hb' : ∀ i j, |actual.covariance i j| ≤ P + eP := by
    intro i j
    calc
      _ = |(actual.covariance i j - reference.covariance i j)
            + reference.covariance i j| := by
        congr 1; ring
      _ ≤ |actual.covariance i j - reference.covariance i j|
          + |reference.covariance i j| :=
        abs_add_le _ _
      _ ≤ eP + P := add_le_add (he.2 i j) (hb i j)
      _ = _ := add_comm _ _
  have hka := gain_magnitude input actual α (P + eP) H hα (by positivity) hH hp hr hb' hh
  have es := within_add (congruence_within input.observation he hH hh)
    (within_refl input.measurementNoise)
  simp only [add_zero] at es
  have ec := within_mul_right he input.observation.transpose hH (fun i j => hh j i)
  have esright := within_mul_left (CovarianceRecursion.gain input actual) es (by
      unfold gainMagnitude; positivity) hka
  change EntrywiseWithin _
    (CovarianceRecursion.gain input actual * CovarianceRecursion.innovationCovariance input actual)
    (CovarianceRecursion.gain input actual * CovarianceRecursion.innovationCovariance input reference)
    at esright
  have hn := Flare.Analysis.NumericalBounds.posDef_of_lower_bound input.measurementNoise α hα hr
  rw [RealRecursion.gain_innovation input actual hp hn] at esright
  have eres := within_trans (within_sym esright) ec
  have eg := RealErrorBounds.gain_residual_accuracy
    (CovarianceRecursion.innovationCovariance input reference)
    (reference.covariance * input.observation.transpose) (CovarianceRecursion.gain input actual)
    α _ hα (innovation_lower input reference α hq hr) eres
  convert eg using 1
  · unfold correctionGainRadius
    ring
  · rfl

theorem predict_sensitivity {n m : Nat} (input : LinearModel.Model n m)
    (actual reference : LinearModel.State n) (F eP eX : ℝ) (hF : 0 ≤ F)
    (hf : ∀ i j, |input.transition i j| ≤ F)
    (he : StateWithin eP eX actual reference)
    : StateWithin (n ^ 2 * F ^ 2 * eP) (n * F * eX)
        (CovarianceRecursion.predict input actual)
        (CovarianceRecursion.predict input reference) := by
  have ec := within_add (congruence_within input.transition he.1 hF hf)
    (within_refl input.processNoise)
  have em := within_mul_left input.transition
    (show EntrywiseWithin eX (fun i (_ : Fin 1) => actual.mean i)
      (fun i (_ : Fin 1) => reference.mean i) from ⟨he.2.1, fun i _ => he.2.2 i⟩) hF hf
  refine ⟨?_, em.1, ?_⟩
  · simpa only [add_zero, CovarianceRecursion.predict] using ec
  · intro i
    exact em.2 i 0

/-- Changes in the prior affect both the optimal gain and the residual.
The bound includes their product, with no first-order remainder dropped. -/
theorem update_sensitivity {n m : Nat} (input : LinearModel.Model n m)
    (actual reference : LinearModel.State n) (measurement : LinearModel.Vector m)
    (α P R H Z eP eX : ℝ) (hα : 0 < α) (hP : 0 ≤ P) (hR : 0 ≤ R)
    (hH : 0 ≤ H) (hZ : 0 ≤ Z)
    (hp : actual.covariance.PosSemidef) (hq : reference.covariance.PosSemidef)
    (hr : (input.measurementNoise - α • 1).PosSemidef)
    (hb : ∀ i j, |reference.covariance i j| ≤ P)
    (hnoise : ∀ i j, |input.measurementNoise i j| ≤ R)
    (hh : ∀ i j, |input.observation i j| ≤ H)
    (hz : ∀ i, |CovarianceRecursion.innovation input reference measurement i| ≤ Z)
    (he : StateWithin eP eX actual reference)
    : StateWithin (correctionCovarianceRadius n m α P R H eP)
        (correctionMeanRadius n m α P H Z eP eX)
        (CovarianceRecursion.update .joseph input actual measurement)
        (CovarianceRecursion.update .joseph input reference measurement) := by
  have hep := he.1.1
  have hex := he.2.1
  have hb' : ∀ i j, |actual.covariance i j| ≤ P + eP := by
    intro i j
    calc
      _ = |(actual.covariance i j - reference.covariance i j)
            + reference.covariance i j| := by
        congr 1; ring
      _ ≤ |actual.covariance i j - reference.covariance i j|
          + |reference.covariance i j| :=
        abs_add_le _ _
      _ ≤ eP + P := add_le_add (he.1.2 i j) (hb i j)
      _ = _ := add_comm _ _
  let Ka := gainMagnitude n m α (P + eP) H
  let K := gainMagnitude n m α P H
  have hKa : 0 ≤ Ka := by dsimp [Ka, gainMagnitude]; positivity
  have hK : 0 ≤ K := by dsimp [K, gainMagnitude]; positivity
  have hka := gain_magnitude input actual α (P + eP) H hα (by positivity) hH hp hr hb' hh
  have hk := gain_magnitude input reference α P H hα hP hH hq hr hb hh
  have eg := gain_sensitivity input actual reference α P H eP hα hP hH hp hq hr hb hh he.1
  let w := (1 : LinearModel.Square n) - CovarianceRecursion.gain input actual * input.observation
  have hw : ∀ i j, |w i j| ≤ 1 + m * Ka * H := by
    intro i j
    have hmul := product_magnitude _ _ Ka H hka hh i j
    have hi : |(1 : LinearModel.Square n) i j| ≤ 1 := by
      simp [Matrix.one_apply]; split_ifs <;> norm_num
    exact (abs_sub _ _).trans (add_le_add hi hmul)
  have ec := within_add (congruence_within w he.1 (by positivity) hw)
    (within_refl (CovarianceRecursion.gain input actual * input.measurementNoise
      * (CovarianceRecursion.gain input actual).transpose))
  have ej := RealErrorBounds.joseph_gain_accuracy input reference
    (CovarianceRecursion.gain input actual) (CovarianceRecursion.gain input reference)
    _ P R H K eg hP hR hH hK hb hnoise hh hk
  have ec' := within_trans ec ej
  have ez := within_sub (within_refl (fun i (_ : Fin 1) => measurement i))
    (within_mul_left input.observation
      (show EntrywiseWithin eX (fun i (_ : Fin 1) => actual.mean i)
        (fun i (_ : Fin 1) => reference.mean i) from ⟨hex, fun i _ => he.2.2 i⟩) hH hh)
  simp only [zero_add] at ez
  have ez' : EntrywiseWithin (n * H * eX)
      (fun i (_ : Fin 1) => CovarianceRecursion.innovation input actual measurement i)
      (fun i (_ : Fin 1) => CovarianceRecursion.innovation input reference measurement i) := by
    exact ez
  have einc := within_mul eg ez' hK hZ hk (fun i _ => hz i)
  have em := within_add
    (show EntrywiseWithin eX (fun i (_ : Fin 1) => actual.mean i)
      (fun i (_ : Fin 1) => reference.mean i) from ⟨hex, fun i _ => he.2.2 i⟩) einc
  refine ⟨?_, em.1, ?_⟩
  · convert ec' using 1
    · unfold correctionCovarianceRadius
      dsimp only [Ka, K]
      ring
    · rfl
    · rfl
  · intro i
    convert em.2 i 0 using 1
    · rfl
    · rfl

/-- Proof witness for the exact Real result statement. -/
theorem predictionSensitivity
    : Kalman.Definitions.Theorems.RecursionSensitivity.PredictionSensitivity :=
  predict_sensitivity

/-- Proof witness for the exact Real result statement. -/
theorem correctionSensitivity
    : Kalman.Definitions.Theorems.RecursionSensitivity.CorrectionSensitivity :=
  update_sensitivity

end Kalman.Proofs.RecursionSensitivity
