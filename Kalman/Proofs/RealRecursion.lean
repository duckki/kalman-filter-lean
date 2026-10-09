import Kalman.Proofs.CovarianceStructure
import Kalman.Definitions.Theorems.CovariancePositiveDefiniteness
import Kalman.Definitions.Theorems.FormulationEquivalence
import Mathlib.Tactic

/-! Exact optimal-gain identities, strict positivity, and information equivalence.
The inverses below are justified by positive definiteness, including the
innovation inverse. No floating-point operation occurs in these proofs. -/

namespace Kalman.Proofs.RealRecursion

open Matrix
open Kalman.Definitions.LinearModel
open Kalman.Definitions.CovarianceRecursion
open Kalman.Proofs.CovarianceStructure

theorem compact_eq_subtractive {n m : Nat} (model : Model n m) (prior : State n)
    (k : Matrix (Fin n) (Fin m) ℝ)
    : compact model prior k = subtractive model prior k := by
  simp [compact, subtractive, Matrix.sub_mul, Matrix.mul_assoc]

theorem gain_innovation {n m : Nat} (model : Model n m) (prior : State n)
    (hp : prior.covariance.PosSemidef) (hr : model.measurementNoise.PosDef)
    : gain model prior * innovationCovariance model prior
      = prior.covariance * model.observation.transpose := by
  let := (innovation_posDef model prior hp hr).isUnit.invertible
  simp [gain, Matrix.mul_assoc]

theorem gain_noise {n m : Nat} (model : Model n m) (prior : State n)
    (hp : prior.covariance.PosSemidef) (hr : model.measurementNoise.PosDef)
    : gain model prior * model.measurementNoise
      = (1 - gain model prior * model.observation) * prior.covariance
        * model.observation.transpose := by
  have h := gain_innovation model prior hp hr
  simp only [innovationCovariance, Matrix.mul_add, Matrix.mul_assoc] at h
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  exact eq_sub_of_add_eq' h

theorem joseph_eq_compact {n m : Nat} (model : Model n m) (prior : State n)
    (hp : prior.covariance.PosSemidef) (hr : model.measurementNoise.PosDef)
    : joseph model prior (gain model prior) = compact model prior (gain model prior) := by
  simp only [joseph, compact]
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    ← gain_noise model prior hp hr]
  abel

theorem quadratic_congruence {n m : Nat} (a : Matrix (Fin n) (Fin m) ℝ)
    (p : Square m) (x : Vector n)
    : x ⬝ᵥ ((a * p * a.transpose) *ᵥ x)
      = (a.transpose *ᵥ x) ⬝ᵥ (p *ᵥ (a.transpose *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]

theorem joseph_posDef {n m : Nat} (model : Model n m) (prior : State n)
    (k : Matrix (Fin n) (Fin m) ℝ)
    (hp : prior.covariance.PosDef) (hr : model.measurementNoise.PosDef)
    : (joseph model prior k).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (joseph_posSemidef model prior k hp.posSemidef hr.posSemidef).isHermitian
  intro x hx
  simp only [star_trivial, joseph, Matrix.add_mulVec, dotProduct_add,
    quadratic_congruence]
  have ha := hp.posSemidef.dotProduct_mulVec_nonneg ((1 - k * model.observation).transpose *ᵥ x)
  have hb := hr.posSemidef.dotProduct_mulVec_nonneg (k.transpose *ᵥ x)
  simp only [star_trivial] at ha hb
  by_cases hk : k.transpose *ᵥ x = 0
  · have hw : (1 - k * model.observation).transpose *ᵥ x = x := by
      simp [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.sub_mulVec,
        ← Matrix.mulVec_mulVec, hk]
    rw [hw]
    have hpos := hp.dotProduct_mulVec_pos hx
    simp only [star_trivial] at hpos
    exact add_pos_of_pos_of_nonneg hpos hb
  · have hpos := hr.dotProduct_mulVec_pos hk
    simp only [star_trivial] at hpos
    exact add_pos_of_nonneg_of_pos ha hpos

theorem posteriorPrecision_posDef {n m : Nat} (model : Model n m) (prior : State n)
    (hp : prior.covariance.PosDef) (hr : model.measurementNoise.PosDef)
    : (posteriorPrecision model prior).PosDef := by
  have hh := hr.inv.posSemidef.mul_mul_conjTranspose_same model.observation.transpose
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at hh
  exact hp.inv.add_posSemidef hh

theorem precision_inv_eq_subtractive {n m : Nat} (model : Model n m) (prior : State n)
    (hp : prior.covariance.PosDef) (hr : model.measurementNoise.PosDef)
    : (posteriorPrecision model prior)⁻¹
      = subtractive model prior (gain model prior) := by
  let := hp.isUnit.invertible
  let := hr.isUnit.invertible
  have hs : IsUnit (model.measurementNoise⁻¹⁻¹ +
      model.observation * prior.covariance⁻¹⁻¹ * model.observation.transpose) := by
    simpa [innovationCovariance, add_comm]
      using (innovation_posDef model prior hp.posSemidef hr).isUnit
  simpa [posteriorPrecision, subtractive, gain, innovationCovariance, Matrix.mul_assoc,
    add_comm]
    using Matrix.add_mul_mul_inv_eq_sub prior.covariance⁻¹ model.observation.transpose
      model.measurementNoise⁻¹ model.observation hp.inv.isUnit hr.inv.isUnit hs

theorem informationUpdate_eq_update {n m : Nat} (model : Model n m) (prior : State n)
    (measurement : Vector m) (hp : prior.covariance.PosDef)
    (hr : model.measurementNoise.PosDef)
    : informationUpdate model prior measurement
      = update .joseph model prior measurement := by
  let := hp.isUnit.invertible
  let := hr.isUnit.invertible
  have hc : (posteriorPrecision model prior)⁻¹ = compact model prior (gain model prior) :=
    (precision_inv_eq_subtractive model prior hp hr).trans (compact_eq_subtractive model prior _).symm
  have hcp : (posteriorPrecision model prior)⁻¹ * prior.covariance⁻¹ =
      1 - gain model prior * model.observation := by
    rw [hc]
    simp [compact, Matrix.mul_assoc]
  have hcr : (posteriorPrecision model prior)⁻¹ * model.observation.transpose *
      model.measurementNoise⁻¹ = gain model prior := by
    rw [hc]
    unfold compact
    rw [← gain_noise model prior hp.posSemidef hr]
    simp [Matrix.mul_assoc]
  dsimp only [informationUpdate, update, correctedCovariance, innovation]
  congr 1
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hcp, hcr, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel
  · exact hc.trans (joseph_eq_compact model prior hp.posSemidef hr).symm

theorem update_posDef {n m : Nat} (form : Form) (model : Model n m) (prior : State n)
    (measurement : Vector m) (hp : prior.covariance.PosDef)
    (hr : model.measurementNoise.PosDef)
    : (update form model prior measurement).covariance.PosDef := by
  change (correctedCovariance form model prior (gain model prior)).PosDef
  have hj := joseph_posDef model prior (gain model prior) hp hr
  cases form with
  | joseph => exact hj
  | compact =>
      simpa only [correctedCovariance, joseph_eq_compact model prior hp.posSemidef hr] using hj
  | subtractive =>
      simpa only [correctedCovariance, joseph_eq_compact model prior hp.posSemidef hr,
        compact_eq_subtractive] using hj

theorem step_posDef {n m : Nat} (form : Form) (model : Model n m) (state : State n)
    (measurement : Vector m) (hp : state.covariance.PosSemidef)
    (hq : model.processNoise.PosDef) (hr : model.measurementNoise.PosDef)
    : (step form model state measurement).covariance.PosDef :=
  update_posDef form model (predict model state) measurement
    (prediction_posDef model state hp hq) hr

/-- Every state in a finite trace is PD, including its initial state. The model
may change at each step; both noise covariances must remain strictly PD. -/
theorem trajectory_posDef {n m : Nat} (form : Form) (initial : State n)
    (observations : List (Model n m × Vector m)) (hp : initial.covariance.PosDef)
    (hnoise
      : ∀ observation ∈ observations,
          observation.1.processNoise.PosDef ∧ observation.1.measurementNoise.PosDef)
    : ∀ state ∈ trajectory form initial observations, state.covariance.PosDef := by
  induction observations generalizing initial with
  | nil => simpa [trajectory] using hp
  | cons observation observations ih =>
      have hn := hnoise observation (by simp)
      have hnext := step_posDef form observation.1 initial observation.2 hp.posSemidef hn.1 hn.2
      have htail := ih (step form observation.1 initial observation.2) hnext
        (fun o ho => hnoise o (by simp [ho]))
      simpa only [trajectory, List.scanl_cons, List.mem_cons, forall_eq_or_imp]
        using And.intro hp htail

theorem stepPositiveDefinite
    : Kalman.Definitions.Theorems.CovariancePositiveDefiniteness.StepPositiveDefinite := by
  intro n m model state measurement h form
  exact step_posDef form model state measurement h.2.2.1.posSemidef h.2.2.2.1 h.2.2.2.2

theorem covarianceFormulationsAgree
    : Kalman.Definitions.Theorems.FormulationEquivalence.CovarianceFormulationsAgree := by
  intro n m model prior hp hr
  exact ⟨compact_eq_subtractive model prior _,
    (compact_eq_subtractive model prior _).symm.trans (joseph_eq_compact model prior hp.posSemidef hr).symm⟩

theorem josephPositiveDefinite
    : Kalman.Definitions.Theorems.CovariancePositiveDefiniteness.JosephPositiveDefinite := by
  intro n m model prior k hp hr
  exact joseph_posDef model prior k hp hr

theorem informationFormAgrees
    : Kalman.Definitions.Theorems.FormulationEquivalence.InformationFormAgrees := by
  intro n m model prior measurement hp hr
  exact informationUpdate_eq_update model prior measurement hp hr

end Kalman.Proofs.RealRecursion
