import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRNorm

/-! Native Householder construction and normalization. Bounds are local to at
most 32 active components. The normalization reference decodes the stored vector
after its first subtraction exactly. Application and whole-QR bounds are supplied
by FloatQRApplication and FloatQRComposition; FloatQRInitialDomain derives the
supported initial-input success domain. -/

namespace Kalman.Proofs.FloatQRReflector

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.FloatDenseError
open Flare.Binary64.Value

theorem householderReflector_schedule (first : Nat) (indices : List Nat)
    (v : Array Float) (norm : Float)
    : householderReflector first indices v norm
      = (do
          let alpha := if v.getD first 0.0 < 0.0 then norm else -norm
          let head ← finite (v.getD first 0.0 - alpha)
          let mut v := v.set! first head
          let mut squared := 0.0
          for i in indices do
            let term ← finite (v.getD i 0.0 * v.getD i 0.0)
            squared ← finite (squared + term)
          let vnorm ← finite squared.sqrt
          unless 0.0 < vnorm do
            throw Kalman.Definitions.Input.Error.nonpositivePivot
          for i in indices do
            v := v.set! i (← finite (v.getD i 0.0 / vnorm))
          return (alpha, v)) := by
  simp [householderReflector, reflectorAlpha, sumSquares, normalizeVector]

theorem householderReflector_range_schedule (size first : Nat) (v : Array Float)
    (norm : Float)
    : householderReflector first (List.range' first (size - first)) v norm
      = (do
          let alpha := if v.getD first 0.0 < 0.0 then norm else -norm
          let head ← finite (v.getD first 0.0 - alpha)
          let mut v := v.set! first head
          let mut squared := 0.0
          for i in [first:size] do
            let term ← finite (v.getD i 0.0 * v.getD i 0.0)
            squared ← finite (squared + term)
          let vnorm ← finite squared.sqrt
          unless 0.0 < vnorm do
            throw Kalman.Definitions.Input.Error.nonpositivePivot
          for i in [first:size] do
            v := v.set! i (← finite (v.getD i 0.0 / vnorm))
          return (alpha, v)) := by
  simpa only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]
    using householderReflector_schedule first (List.range' first (size - first)) v norm

/-- Opposite-sign choice is exact and supplies a cancellation-free subtraction,
including both signed-zero first components. -/
theorem reflectorAlpha_correct (first norm : Float)
    (hf : first.isFinite = true) (hn : norm.isFinite = true) (hp : 0 ≤ value norm)
    : (reflectorAlpha first norm).isFinite = true
      ∧ |value (reflectorAlpha first norm)| = value norm
      ∧ |value first - value (reflectorAlpha first norm)|
        = |value first| + value norm := by
  have hlt := Flare.Binary64.Order.lt_iff first 0.0 hf (by decide)
  simp only [Flare.Binary64.Arithmetic.zero_value] at hlt
  by_cases h : first < 0.0
  · have hv := hlt.mp h
    simp only [reflectorAlpha, ite_eq_left h]
    refine ⟨hn, abs_of_nonneg hp, ?_⟩
    rw [abs_of_nonpos (by linarith : value first - value norm ≤ 0), abs_of_neg hv]
    ring
  · have hv : 0 ≤ value first := le_of_not_gt (fun hh => h (hlt.mpr hh))
    have hneg := Flare.Binary64.Order.neg_value norm hn
    simp only [reflectorAlpha, ite_eq_right h]
    refine ⟨hneg.1, ?_, ?_⟩
    · rw [hneg.2, abs_neg, abs_of_nonneg hp]
    · rw [hneg.2, abs_of_nonneg (by linarith : 0 ≤ value first - -value norm),
        abs_of_nonneg hv]
      ring

private theorem set_read (v : Array Float) (k i : Nat) (x : Float) (hk : k < v.size)
    : (v.set! k x).getD i 0.0 = if i = k then x else v.getD i 0.0 := by
  by_cases hi : i = k
  · subst i
    simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hk]
  · simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hi,
      Array.getElem?_setIfInBounds_ne (Ne.symm hi)]

private theorem construction_bounds (first : Nat) (indices : List Nat)
    (v : Array Float) (norm : Float) (p : ReflectorProfile first indices v norm)
    : let alpha := reflectorAlpha (v.getD first 0.0) norm
      let head := v.getD first 0.0 - alpha
      alpha.isFinite = true
      ∧ |value alpha| = value norm
      ∧ head.isFinite = true
      ∧ |value head - (value (v.getD first 0.0) - value alpha)| ≤ (2 : ℝ) ^ (-49 : Int)
      ∧ (1 : ℝ) / 4 ≤ |value head|
      ∧ (constructedVector first v norm).all Float.isFinite = true
      ∧ (∀ i ∈ indices, |value ((constructedVector first v norm).getD i 0.0)| ≤ 9)
      ∧ (1 : ℝ) / 16 ≤ vectorSquares indices (constructedVector first v norm) := by
  let alpha := reflectorAlpha (v.getD first 0.0) norm
  let head := v.getD first 0.0 - alpha
  have hf := Flare.Matrix.Storage.getD_finite v first p.finite
  obtain ⟨haf, hab, hsign⟩ := reflectorAlpha_correct (v.getD first 0.0) norm hf
    p.norm_finite (by linarith [p.norm_lower])
  have hdiff : |value (v.getD first 0.0) - value alpha| ≤ (2 : ℝ) ^ (3 : Int) := by
    dsimp only [alpha]
    rw [hsign]
    have hb := p.magnitude first p.first_mem
    have hu := p.norm_upper
    norm_num at hb hu ⊢
    linarith
  have hs := Flare.Binary64.Arithmetic.sub_error (v.getD first 0.0) alpha 3 hf haf
    (by norm_num) (by norm_num) hdiff
  have he : |value head - (value (v.getD first 0.0) - value alpha)|
      ≤ (2 : ℝ) ^ (-49 : Int) := by simpa [head] using hs.2
  have hmag : |value head| ≤ 9 := by
    have ht := abs_sub_le (value head) (value (v.getD first 0.0) - value alpha) 0
    simp only [sub_zero] at ht
    norm_num at he hdiff ht
    linarith
  have hmargin : (1 : ℝ) / 4 ≤ |value head| := by
    have ht := abs_sub_le (value (v.getD first 0.0) - value alpha) (value head) 0
    simp only [sub_zero, abs_sub_comm (value (v.getD first 0.0) - value alpha)] at ht
    have hl : (1 : ℝ) / 2 ≤ |value (v.getD first 0.0) - value alpha| := by
      dsimp only [alpha]
      rw [hsign]
      linarith [abs_nonneg (value (v.getD first 0.0)), p.norm_lower]
    norm_num at he
    linarith
  have hread : ∀ i, (constructedVector first v norm).getD i 0.0 =
      if i = first then head else v.getD i 0.0 := by
    intro i
    exact set_read v first i head (p.in_bounds first p.first_mem)
  refine ⟨haf, hab, hs.1, he, hmargin,
    Flare.Matrix.Storage.all_set v first head p.finite hs.1, ?_, ?_⟩
  · intro i hi
    rw [hread]
    by_cases h : i = first
    · simpa only [ite_eq_left h] using hmag
    · simp only [ite_eq_right h]
      linarith [p.magnitude i hi]
  · have hterm : (1 : ℝ) / 16 ≤ (value head) ^ 2 := by
      nlinarith [sq_abs (value head), sq_nonneg (|value head| - 1 / 4)]
    have hs0 : (value head) ^ 2 ≤ vectorSquares indices (constructedVector first v norm) := by
      unfold vectorSquares
      apply List.single_le_sum
      · intro z hz
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
        exact sq_nonneg _
      · apply List.mem_map.mpr
        refine ⟨first, p.first_mem, ?_⟩
        simp [hread]
    exact hterm.trans hs0

private theorem sumSquares_cons (i : Nat) (indices : List Nat) (v : Array Float)
    (s : Float)
    : sumSquares (i :: indices) v s
      = (do
          let term ← finite (v.getD i 0.0 * v.getD i 0.0)
          let next ← finite (s + term)
          sumSquares indices v next) := by
  simp [sumSquares, List.forIn_cons, bind_assoc]

private theorem squares_loop (indices : List Nat) (v : Array Float)
    (hv : v.all Float.isFinite = true)
    (hb : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 9)
    (s : Float) (target : ℝ) (p : Nat)
    (hlen : p + indices.length ≤ 32) (hf : s.isFinite = true)
    (htarget : |target| ≤ 81 * p)
    (he : |value s - target| ≤ reflectorSumRadius p)
    : ∃ r,
        sumSquares indices v s = .ok r
        ∧ r.isFinite = true
        ∧ |value r - (target + vectorSquares indices v)|
          ≤ reflectorSumRadius (p + indices.length) := by
  induction indices generalizing s target p with
  | nil => exact ⟨s, rfl, hf, by simpa [vectorSquares] using he⟩
  | cons i indices ih =>
      let x := v.getD i 0.0
      let term := x * x
      have hxf := Flare.Matrix.Storage.getD_finite v i hv
      have hxb := hb i (by simp)
      have hx2 : (value x) ^ 2 ≤ 81 := by
        dsimp only [x]
        nlinarith [(abs_le.mp hxb).1, (abs_le.mp hxb).2]
      have hm := Flare.Binary64.Arithmetic.mul_error x x 7 hxf hxf
        (by norm_num) (by norm_num) (by
          rw [show value x * value x = (value x) ^ 2 by ring,
            abs_of_nonneg (sq_nonneg (value x))]
          norm_num
          linarith)
      have hme : |value term - (value x) ^ 2| ≤ (2 : ℝ) ^ (-45 : Int) := by
        simpa [term, pow_two] using hm.2
      have htm : |value term| ≤ 82 := by
        have ht := abs_sub_le (value term) ((value x) ^ 2) 0
        simp only [sub_zero, abs_of_nonneg (sq_nonneg (value x))] at ht
        norm_num at hme
        linarith
      have hp32 : (p : ℝ) ≤ 32 := by exact_mod_cast (show p ≤ 32 by omega)
      have hsm : |value s| ≤ 2593 := by
        have ht := abs_sub_le (value s) target 0
        simp only [sub_zero] at ht
        norm_num [reflectorSumRadius] at he
        nlinarith
      have ham : |value s + value term| ≤ (2 : ℝ) ^ (12 : Int) := by
        have ht := abs_add_le (value s) (value term)
        norm_num
        linarith
      have ha := Flare.Binary64.Arithmetic.add_error s term 12 hf hm.1
        (by norm_num) (by norm_num) ham
      have htgt : |target + (value x) ^ 2| ≤ 81 * (p + 1 : Nat) := by
        have ht := abs_add_le target ((value x) ^ 2)
        rw [abs_of_nonneg (sq_nonneg (value x))] at ht
        push_cast
        linarith
      have he' : |value (s + term) - (target + (value x) ^ 2)| ≤ reflectorSumRadius (p + 1) := by
        have hsum : |(value s + value term) - (target + (value x) ^ 2)|
            ≤ |value s - target| + |value term - (value x) ^ 2| := by
          rw [show (value s + value term) - (target + (value x) ^ 2) =
            (value s - target) + (value term - (value x) ^ 2) by ring]
          exact abs_add_le _ _
        have ht := abs_sub_le (value (s + term)) (value s + value term) (target + (value x) ^ 2)
        norm_num [reflectorSumRadius] at he hme ha ⊢
        linarith [ha.2]
      obtain ⟨r, hr, hrf, hre⟩ := ih (fun j hj => hb j (by simp [hj]))
        (s + term) (target + (value x) ^ 2) (p + 1) (by simp only [List.length_cons] at hlen; omega)
        ha.1 htgt he'
      refine ⟨r, ?_, hrf, ?_⟩
      · rw [sumSquares_cons, finite_ok _ hm.1]
        change (do
          let next ← finite (s + term)
          sumSquares indices v next) = .ok r
        rw [finite_ok _ ha.1]
        exact hr
      · simpa [vectorSquares, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc, x] using hre

/-- Actual sum-of-squares success and error; no computed-sum premise. -/
theorem sumSquares_accuracy (indices : List Nat) (v : Array Float)
    (hlen : indices.length ≤ 32) (hv : v.all Float.isFinite = true)
    (hb : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 9)
    : ∃ s,
        sumSquares indices v 0.0 = .ok s
        ∧ s.isFinite = true
        ∧ |value s - vectorSquares indices v| ≤ reflectorSumRadius indices.length := by
  simpa [Flare.Binary64.Arithmetic.zero_value, reflectorSumRadius]
    using squares_loop indices v hv hb 0.0 0 0 (by simpa using hlen) (by decide)
      (by simp) (by simp [Flare.Binary64.Arithmetic.zero_value, reflectorSumRadius])

private theorem normalizeVector_cons (i : Nat) (indices : List Nat) (v : Array Float)
    (norm : Float)
    : normalizeVector (i :: indices) v norm
      = (do
          let q ← finite (v.getD i 0.0 / norm)
          normalizeVector indices (v.set! i q) norm) := by
  simp [normalizeVector]

private theorem normalizeVector_storage (indices : List Nat) (v : Array Float)
    (norm : Float) (hn : indices.Nodup) (hv : v.all Float.isFinite = true)
    (hi : ∀ i ∈ indices, i < v.size) (hf : norm.isFinite = true) (hp : 0 < value norm)
    (hb : ∀ i ∈ indices, |value (v.getD i 0.0) / value norm| ≤ 128)
    : ∃ w,
        normalizeVector indices v norm = .ok w
        ∧ w.size = v.size
        ∧ w.all Float.isFinite = true
        ∧ ∀ i,
            w.getD i 0.0 = if i ∈ indices then v.getD i 0.0 / norm else v.getD i 0.0 := by
  induction indices generalizing v with
  | nil => exact ⟨v, rfl, rfl, hv, by simp⟩
  | cons i indices ih =>
      have hni := List.nodup_cons.mp hn
      have hd := Flare.Binary64.Division.div_error (v.getD i 0.0) norm 7
        (Flare.Matrix.Storage.getD_finite v i hv) hf hp.ne'
        (by norm_num) (by norm_num) (by have hh := hb i (by simp); norm_num at hh ⊢; exact hh)
      let next := v.set! i (v.getD i 0.0 / norm)
      have hread : ∀ j ∈ indices, next.getD j 0.0 = v.getD j 0.0 := by
        intro j hj
        have hne : j ≠ i := fun h => hni.1 (h ▸ hj)
        simp only [next, set_read v i j _ (hi i (by simp)), ite_eq_right hne]
      obtain ⟨w, hw, hws, hwf, hwr⟩ := ih next hni.2
        (Flare.Matrix.Storage.all_set v i _ hv hd.1)
        (fun j hj => by simpa [next] using hi j (by simp [hj]))
        (fun j hj => by rw [hread j hj]; exact hb j (by simp [hj]))
      refine ⟨w, ?_, by simpa [next] using hws, hwf, ?_⟩
      · rw [normalizeVector_cons, finite_ok _ hd.1]
        exact hw
      · intro j
        rw [hwr]
        by_cases hj : j ∈ indices
        · simp only [hread j hj, List.mem_cons, hj, or_true, ↓reduceIte]
        · simp only [ite_eq_right hj, next, set_read v i j _ (hi i (by simp))]
          by_cases hji : j = i
          · subst j
            simp [hj]
          · simp [hj, hji]

private theorem vectorSquares_term_le (indices : List Nat) (v : Array Float)
    (i : Nat) (hi : i ∈ indices)
    : (value (v.getD i 0.0)) ^ 2 ≤ vectorSquares indices v := by
  unfold vectorSquares
  apply List.single_le_sum
  · intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    exact sq_nonneg _
  · exact List.mem_map.mpr ⟨i, hi, rfl⟩

private theorem vectorSquares_upper (indices : List Nat) (v : Array Float)
    (hlen : indices.length ≤ 32) (hb : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 9)
    : vectorSquares indices v ≤ 2592 := by
  have hn : (indices.length : ℝ) ≤ 32 := by exact_mod_cast hlen
  have hsum : vectorSquares indices v ≤ 81 * indices.length := by
    unfold vectorSquares
    calc
      _ ≤ (indices.map (fun _ => (81 : ℝ))).sum := by
        apply List.sum_le_sum
        intro i hi
        have h := abs_le.mp (hb i hi)
        nlinarith
      _ = _ := by simp [mul_comm]
  linarith

private theorem squares_loop_relative (indices : List Nat) (v : Array Float) (Q : ℝ)
    (hv : v.all Float.isFinite = true) (hQ : (1 : ℝ) / 16 ≤ Q) (hQu : Q ≤ 2592)
    (s : Float) (target : ℝ) (p : Nat)
    (hlen : p + indices.length ≤ 32) (hf : s.isFinite = true)
    (ht : 0 ≤ target) (hremaining : target + vectorSquares indices v ≤ Q)
    (he : |value s - target| ≤ p * (2 : ℝ) ^ (-49 : Int) * Q)
    : ∃ r,
        sumSquares indices v s = .ok r
        ∧ r.isFinite = true
        ∧ |value r - (target + vectorSquares indices v)|
          ≤ (p + indices.length) * (2 : ℝ) ^ (-49 : Int) * Q := by
  have hQ0 : 0 ≤ Q := by linarith
  have hη : (2 : ℝ) ^ (-1022 : Int) ≤ Q := by
    calc
      _ ≤ (2 : ℝ) ^ (-4 : Int) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      _ = 1 / 16 := by norm_num
      _ ≤ Q := hQ
  have hηsmall : (2 : ℝ) ^ (-1022 : Int) ≤ Q / 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (-6 : Int) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      _ = 1 / 64 := by norm_num
      _ ≤ Q / 4 := by linarith
  induction indices generalizing s target p with
  | nil => exact ⟨s, rfl, hf, by simpa [vectorSquares] using he⟩
  | cons i indices ih =>
      let x := v.getD i 0.0
      let term := x * x
      have htail : 0 ≤ vectorSquares indices v := by
        unfold vectorSquares
        exact List.sum_nonneg (by intro z hz; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz; positivity)
      have htotal : target + (value x) ^ 2 + vectorSquares indices v ≤ Q := by
        simpa [vectorSquares, x, add_assoc] using hremaining
      have hx2 : (value x) ^ 2 ≤ Q := by linarith [sq_nonneg (value x)]
      have hxf := Flare.Matrix.Storage.getD_finite v i hv
      have hmul : |value x * value x| ≤ (2 : ℝ) ^ (1000 : Int) := by
        rw [← pow_two, abs_of_nonneg (sq_nonneg _)]
        exact hx2.trans (hQu.trans ((by norm_num : (2592 : ℝ) ≤ 2 ^ (12 : Int)).trans
          (zpow_le_zpow_right₀ (by norm_num) (by norm_num))))
      obtain ⟨hmf, hme⟩ := Flare.Binary64.Arithmetic.mul_error_relative x x hxf hxf hmul
      have hme' : |value term - (value x) ^ 2| ≤ 2 * (2 : ℝ) ^ (-51 : Int) * Q := by
        calc
          _ ≤ (2 : ℝ) ^ (-51 : Int) * ((value x) ^ 2 + (2 : ℝ) ^ (-1022 : Int)) := by
            simpa only [term, ← pow_two, abs_of_nonneg (sq_nonneg (value x))] using hme
          _ ≤ (2 : ℝ) ^ (-51 : Int) * (2 * Q) := by gcongr; linarith
          _ = _ := by ring
      have hp32 : (p : ℝ) ≤ 32 := by exact_mod_cast (show p ≤ 32 by omega)
      have hterr : p * (2 : ℝ) ^ (-49 : Int) * Q ≤ Q / 8 := by
        have hh := mul_le_mul_of_nonneg_right hp32 hQ0
        norm_num
        nlinarith
      have heabs := he.trans hterr
      have ha : |value s + value term| ≤ 5 * Q / 4 := by
        have hdiff : |(value s + value term) - (target + (value x) ^ 2)|
            ≤ |value s - target| + |value term - (value x) ^ 2| := by
          rw [show (value s + value term) - (target + (value x) ^ 2) =
            (value s - target) + (value term - (value x) ^ 2) by ring]
          exact abs_add_le _ _
        have hh := abs_sub_le (value s + value term) (target + (value x) ^ 2) 0
        simp only [sub_zero, abs_of_nonneg (by positivity : 0 ≤ target + (value x) ^ 2)] at hh
        norm_num at hme'
        linarith
      obtain ⟨haf, hae⟩ := Flare.Binary64.Arithmetic.add_error_relative s term hf hmf
        (ha.trans ((by linarith : 5 * Q / 4 ≤ 4 * Q).trans
          ((mul_le_mul_of_nonneg_left hQu (by norm_num : (0 : ℝ) ≤ 4)).trans
            ((by norm_num : 4 * (2592 : ℝ) ≤ 2 ^ (14 : Int)).trans
              (zpow_le_zpow_right₀ (by norm_num) (by norm_num))))))
      have hae' : |value (s + term) - (value s + value term)|
          ≤ 2 * (2 : ℝ) ^ (-51 : Int) * Q := by
        apply hae.trans
        calc
          _ ≤ (2 : ℝ) ^ (-51 : Int) * (2 * Q) := by gcongr; linarith
          _ = _ := by ring
      have he' : |value (s + term) - (target + (value x) ^ 2)|
          ≤ (p + 1 : Nat) * (2 : ℝ) ^ (-49 : Int) * Q := by
        have hh := abs_sub_le (value (s + term)) (value s + value term) (target + (value x) ^ 2)
        have hdiff : |(value s + value term) - (target + (value x) ^ 2)|
            ≤ |value s - target| + |value term - (value x) ^ 2| := by
          rw [show (value s + value term) - (target + (value x) ^ 2) =
            (value s - target) + (value term - (value x) ^ 2) by ring]
          exact abs_add_le _ _
        push_cast
        norm_num at he hae' hme' ⊢
        linarith
      obtain ⟨r, hr, hrf, hre⟩ := ih (s + term) (target + (value x) ^ 2) (p + 1)
        (by simp only [List.length_cons] at hlen; omega) haf (by positivity) htotal he'
      refine ⟨r, ?_, hrf, ?_⟩
      · rw [sumSquares_cons, finite_ok _ hmf]
        change (do
          let next ← finite (s + term)
          sumSquares indices v next) = .ok r
        rw [finite_ok _ haf]
        exact hr
      · simpa [vectorSquares, x, add_assoc, add_comm, add_left_comm] using hre

/-- Magnitude-scaled accumulation for the actual nonnegative squared sum.
The positive total norm absorbs the explicit native underflow allowance. -/
theorem sumSquares_relative_accuracy (indices : List Nat) (v : Array Float)
    (hlen : indices.length ≤ 32) (hv : v.all Float.isFinite = true)
    (hb : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 9)
    (hlo : (1 : ℝ) / 16 ≤ vectorSquares indices v)
    : ∃ s,
        sumSquares indices v 0.0 = .ok s
        ∧ s.isFinite = true
        ∧ |value s - vectorSquares indices v|
          ≤ indices.length * (2 : ℝ) ^ (-49 : Int) * vectorSquares indices v := by
  simpa [Flare.Binary64.Arithmetic.zero_value]
    using squares_loop_relative indices v
      (vectorSquares indices v) hv hlo (vectorSquares_upper indices v hlen hb) 0.0 0 0
      (by simpa using hlen) (by decide) (by norm_num) (by simp)
      (by simp [Flare.Binary64.Arithmetic.zero_value])

private theorem reflectorNorm_accuracy (indices : List Nat) (v : Array Float)
    (hlen : indices.length ≤ 32) (hv : v.all Float.isFinite = true)
    (hb : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 9)
    (hlo : (1 : ℝ) / 16 ≤ vectorSquares indices v)
    : ∃ s,
        sumSquares indices v 0.0 = .ok s
        ∧ s.sqrt.isFinite = true
        ∧ (1 : ℝ) / 8 ≤ value s.sqrt
        ∧ |(value s.sqrt) ^ 2 - vectorSquares indices v|
          ≤ (indices.length + 1) * (2 : ℝ) ^ (-49 : Int) * vectorSquares indices v := by
  obtain ⟨s, hs, hsf, he⟩ := sumSquares_relative_accuracy indices v hlen hv hb hlo
  have hn : (indices.length : ℝ) ≤ 32 := by exact_mod_cast hlen
  have hQ0 : 0 ≤ vectorSquares indices v := by linarith
  have he' : |value s - vectorSquares indices v|
      ≤ (2 : ℝ) ^ (-43 : Int) * vectorSquares indices v := by
    apply he.trans
    norm_num
    nlinarith
  have hpos : 0 < value s := by
    have h := (abs_le.mp he').1
    norm_num at h
    nlinarith
  obtain ⟨_, hnf, hnp, hne⟩ := FloatResidualError.positiveSqrt_accuracy s hsf hpos
  have hsu : value s ≤ 2 * vectorSquares indices v := by
    have h := (abs_le.mp he').2
    norm_num at h
    linarith
  have herr : |(value s.sqrt) ^ 2 - vectorSquares indices v|
      ≤ (indices.length + 1) * (2 : ℝ) ^ (-49 : Int) * vectorSquares indices v := by
    have ht := abs_sub_le ((value s.sqrt) ^ 2) (value s) (vectorSquares indices v)
    have hm := mul_le_mul_of_nonneg_left hsu
      (by positivity : 0 ≤ 2 * (2 : ℝ) ^ (-53 : Int) + ((2 : ℝ) ^ (-53 : Int)) ^ 2)
    norm_num at he hne hm ⊢
    linarith
  refine ⟨s, hs, hnf, ?_, herr⟩
  have h := (abs_le.mp herr).1
  have hc : (indices.length + 1 : ℝ) * (2 : ℝ) ^ (-49 : Int) ≤ (2 : ℝ) ^ (-43 : Int) := by
    norm_num
    linarith
  have hm := mul_le_mul_of_nonneg_right hc hQ0
  norm_num at h hm
  nlinarith

private theorem map_sum_sub (indices : List Nat) (f g : Nat → ℝ)
    : (indices.map f).sum - (indices.map g).sum
      = (indices.map (fun i => f i - g i)).sum := by
  induction indices with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

private theorem abs_map_sum (indices : List Nat) (f : Nat → ℝ)
    : |(indices.map f).sum| ≤ (indices.map (fun i => |f i|)).sum := by
  induction indices with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)

private theorem normalization_accuracy (indices : List Nat) (v : Array Float) (r : Float)
    (hlen : indices.length ≤ 32) (hn : indices.Nodup) (hv : v.all Float.isFinite = true)
    (hi : ∀ i ∈ indices, i < v.size)
    (hf : r.isFinite = true) (hr : (1 : ℝ) / 8 ≤ value r)
    (hlo : (1 : ℝ) / 16 ≤ vectorSquares indices v)
    (he
      : |(value r) ^ 2 - vectorSquares indices v|
        ≤ (indices.length + 1) * (2 : ℝ) ^ (-49 : Int) * vectorSquares indices v)
    : ∃ w,
        normalizeVector indices v r = .ok w
        ∧ w.size = v.size
        ∧ w.all Float.isFinite = true
        ∧ (∀ i, i ∉ indices → w.getD i 0.0 = v.getD i 0.0)
        ∧ (∀ i ∈ indices,
            |value (w.getD i 0.0)
              - value (v.getD i 0.0) / Real.sqrt (vectorSquares indices v)|
            ≤ reflectorRadius indices.length)
        ∧ |vectorSquares indices w - 1| ≤ reflectorRadius indices.length := by
  let root := Real.sqrt (vectorSquares indices v)
  have hrp : 0 < value r := by linarith
  have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
  have hrootsq : root ^ 2 = vectorSquares indices v := Real.sq_sqrt (by linarith)
  have hroot : (1 : ℝ) / 4 ≤ root := by nlinarith
  have hrootp : 0 < root := by linarith
  have hlenR : (indices.length : ℝ) ≤ 32 := by exact_mod_cast hlen
  have hc : (indices.length + 1 : ℝ) * (2 : ℝ) ^ (-49 : Int) ≤ (1 : ℝ) / 2 := by
    norm_num
    linarith
  have hehalf : |(value r) ^ 2 - vectorSquares indices v| ≤ (1 : ℝ) / 2 * vectorSquares indices v :=
    he.trans (mul_le_mul_of_nonneg_right hc (by linarith))
  have hQ : vectorSquares indices v ≤ 2 * (value r) ^ 2 := by
    have hh := (abs_le.mp hehalf).1
    norm_num at hh
    nlinarith
  have hqbound : ∀ i ∈ indices, |value (v.getD i 0.0) / value r| ≤ 2 := by
    intro i hii
    have ht := vectorSquares_term_le indices v i hii
    rw [abs_div, abs_of_pos hrp]
    apply (div_le_iff₀ hrp).mpr
    nlinarith [sq_abs (value (v.getD i 0.0)), abs_nonneg (value (v.getD i 0.0))]
  obtain ⟨w, hw, hws, hwf, hwr⟩ := normalizeVector_storage indices v r hn hv hi hf hrp
    (fun i hii => (hqbound i hii).trans (by norm_num))
  have hdiv : ∀ i ∈ indices,
      |value (w.getD i 0.0) - value (v.getD i 0.0) / value r| ≤ (2 : ℝ) ^ (-50 : Int) := by
    intro i hii
    have hd := Flare.Binary64.Division.div_error (v.getD i 0.0) r 1
      (Flare.Matrix.Storage.getD_finite v i hv) hf hrp.ne'
      (by norm_num) (by norm_num) (by simpa using hqbound i hii)
    simpa only [hwr i, ite_eq_left hii, show (1 : Int) - 51 = -50 by omega] using hd.2
  have hrelative : |value r - root| / value r ≤ 2 * (indices.length + 1) * (2 : ℝ) ^ (-49 : Int) := by
    have hid : |(value r) ^ 2 - vectorSquares indices v| =
        |value r - root| * (value r + root) := by
      calc
        _ = |(value r) ^ 2 - root ^ 2| := by rw [hrootsq]
        _ = _ := by
          rw [show (value r) ^ 2 - root ^ 2 = (value r - root) * (value r + root) by ring,
            abs_mul, abs_of_pos (by linarith : 0 < value r + root)]
    rw [hid] at he
    apply (div_le_iff₀ hrp).mpr
    have hscaled := mul_le_mul_of_nonneg_left hQ
      (by positivity : 0 ≤ (indices.length + 1 : ℝ) * (2 : ℝ) ^ (-49 : Int))
    norm_num at he hscaled ⊢
    nlinarith [mul_nonneg (abs_nonneg (value r - root)) hroot0]
  have hunit : ∀ i ∈ indices, |value (v.getD i 0.0) / root| ≤ 1 := by
    intro i hii
    have ht := vectorSquares_term_le indices v i hii
    have hbroot : |value (v.getD i 0.0)| ≤ root := by
      nlinarith [sq_abs (value (v.getD i 0.0)), abs_nonneg (value (v.getD i 0.0))]
    rw [abs_div, abs_of_pos hrootp]
    exact (div_le_one hrootp).mpr hbroot
  have href : ∀ i ∈ indices,
      |value (v.getD i 0.0) / value r - value (v.getD i 0.0) / root| ≤ 2 * (indices.length + 1) * (2 : ℝ) ^ (-49 : Int) := by
    intro i hii
    rw [show value (v.getD i 0.0) / value r - value (v.getD i 0.0) / root =
      (value (v.getD i 0.0) / root) * ((root - value r) / value r) by
        field_simp [hrp.ne', hrootp.ne'],
      abs_mul, abs_div (root - value r), abs_sub_comm root, abs_of_pos hrp]
    exact (mul_le_mul (hunit i hii) hrelative (by positivity) (by norm_num)).trans (by simp)
  have hterm : ∀ i ∈ indices,
      |(value (w.getD i 0.0)) ^ 2 - (value (v.getD i 0.0) / value r) ^ 2|
        ≤ 5 * (2 : ℝ) ^ (-50 : Int) := by
    intro i hii
    have hd := hdiv i hii
    have hq := hqbound i hii
    have hwm : |value (w.getD i 0.0)| ≤ 3 := by
      have ht := abs_sub_le (value (w.getD i 0.0)) (value (v.getD i 0.0) / value r) 0
      simp only [sub_zero] at ht
      norm_num at hd hq ht ⊢
      linarith
    have hsum : |value (w.getD i 0.0) + value (v.getD i 0.0) / value r| ≤ 5 := by
      have ht := abs_add_le (value (w.getD i 0.0)) (value (v.getD i 0.0) / value r)
      linarith
    rw [show (value (w.getD i 0.0)) ^ 2 - (value (v.getD i 0.0) / value r) ^ 2 =
      (value (w.getD i 0.0) - value (v.getD i 0.0) / value r) *
        (value (w.getD i 0.0) + value (v.getD i 0.0) / value r) by ring, abs_mul]
    nlinarith [mul_le_mul hd hsum (abs_nonneg _) (by positivity)]
  let Q := (indices.map (fun i => (value (v.getD i 0.0) / value r) ^ 2)).sum
  have hQeq : Q = vectorSquares indices v / (value r) ^ 2 := by
    dsimp only [Q, vectorSquares]
    simp only [div_pow]
    simp only [div_eq_mul_inv, List.sum_map_mul_right]
  have hsumerr : |vectorSquares indices w - Q| ≤
      indices.length * (5 * (2 : ℝ) ^ (-50 : Int)) := by
    dsimp only [Q, vectorSquares]
    rw [map_sum_sub]
    calc
      _ ≤ (indices.map
            (fun i =>
              |(value (w.getD i 0.0)) ^ 2 - (value (v.getD i 0.0) / value r) ^ 2|)).sum :=
        abs_map_sum indices _
      _ ≤ (indices.map (fun _ => 5 * (2 : ℝ) ^ (-50 : Int))).sum := List.sum_le_sum hterm
      _ = _ := by simp
  have hQerr : |Q - 1| ≤ 2 * (indices.length + 1) * (2 : ℝ) ^ (-49 : Int) := by
    rw [hQeq, show vectorSquares indices v / (value r) ^ 2 - 1 =
      (vectorSquares indices v - (value r) ^ 2) / (value r) ^ 2 by field_simp,
      abs_div, abs_sub_comm, abs_of_pos (sq_pos_of_pos hrp)]
    apply (div_le_iff₀ (sq_pos_of_pos hrp)).mpr
    have hscaled := mul_le_mul_of_nonneg_left hQ
      (by positivity : 0 ≤ (indices.length + 1 : ℝ) * (2 : ℝ) ^ (-49 : Int))
    have hh := he
    norm_num at hh hscaled ⊢
    nlinarith
  refine ⟨w, hw, hws, hwf, ?_, ?_, ?_⟩
  · intro i hii
    simp only [hwr, ite_eq_right hii]
  · intro i hii
    have ht := abs_sub_le (value (w.getD i 0.0)) (value (v.getD i 0.0) / value r)
      (value (v.getD i 0.0) / root)
    have hd := hdiv i hii
    have href' := href i hii
    change _ ≤ reflectorRadius indices.length
    norm_num [reflectorRadius] at ht hd href' ⊢
    linarith
  · have ht := abs_sub_le (vectorSquares indices w) Q 1
    have hn32 : (indices.length : ℝ) ≤ 32 := by exact_mod_cast hlen
    norm_num [reflectorRadius] at hsumerr hQerr ⊢
    nlinarith

/-- Compatibility cap for the dimension-sensitive reflector allowance. -/
theorem reflectorRadius_le {k : Nat} (hk : k ≤ 32)
    : reflectorRadius k ≤ (2 : ℝ) ^ (-40 : Int) := by
  have hn : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  norm_num [reflectorRadius]
  linarith

/-- Local reflector guarantee: success, cancellation-free head construction,
finite storage, and component/near-unit bounds follow from operand conditions. -/
theorem householderReflector_accuracy (first : Nat) (indices : List Nat)
    (v : Array Float) (norm : Float) (p : ReflectorProfile first indices v norm)
    : ReflectorAccuracy first indices v norm := by
  let alpha := reflectorAlpha (v.getD first 0.0) norm
  let b := constructedVector first v norm
  obtain ⟨haf, hab, hhf, hhe, hmargin, hbf, hbb, hlo⟩ := construction_bounds first indices v norm p
  obtain ⟨s, hs, hnf, hr, herr⟩ := reflectorNorm_accuracy indices b p.length_le hbf hbb hlo
  obtain ⟨w, hw, hws, hwf, houtside, hentry, hunit⟩ := normalization_accuracy indices b s.sqrt
    p.length_le p.nodup hbf (fun i hi => by simpa [b, constructedVector] using p.in_bounds i hi)
    hnf hr hlo herr
  refine ⟨
    alpha,
    w,
    ?_,
    rfl,
    haf,
    hab,
    hhf,
    hhe,
    hmargin,
    by simpa [b, constructedVector] using hws,
    hwf,
    ?_,
    hentry,
    hunit
  ⟩
  · have hg : 0.0 < s.sqrt := (Flare.Binary64.Order.lt_iff _ _ (by decide) hnf).mpr
      (by simp only [Flare.Binary64.Arithmetic.zero_value]; linarith)
    unfold householderReflector
    dsimp only
    rw [finite_ok _ hhf]
    change (do
      let squared ← sumSquares indices b 0.0
      let vnorm ← finite squared.sqrt
      unless 0.0 < vnorm do
        throw Kalman.Definitions.Input.Error.nonpositivePivot
      let v ← normalizeVector indices b vnorm
      return (alpha, v)) = .ok (alpha, w)
    rw [hs]
    change (do
      let vnorm ← finite s.sqrt
      unless 0.0 < vnorm do
        throw Kalman.Definitions.Input.Error.nonpositivePivot
      let v ← normalizeVector indices b vnorm
      return (alpha, v)) = .ok (alpha, w)
    rw [finite_ok _ hnf]
    change (if 0.0 < s.sqrt then (do
      let v ← normalizeVector indices b s.sqrt
      return (alpha, v)) else _) = .ok (alpha, w)
    simp only [hg, ↓reduceIte]
    rw [hw]
    rfl
  · intro i hi
    rw [houtside i hi]
    have hne : i ≠ first := fun h => hi (h ▸ p.first_mem)
    exact (set_read v first i _ (p.in_bounds first p.first_mem)).trans (ite_eq_right hne)

/-- The preceding column-norm slice supplies every local reflector condition.
No native success or intermediate-error premise is required from the caller. -/
theorem scaledColumn_reflector_accuracy (size first : Nat) (indices : List Nat)
    (x : Nat → Float) (p : ColumnProfile size indices x)
    (hn : indices.Nodup) (hfirst : first ∈ indices)
    : ColumnReflectorAccuracy size first indices x := by
  obtain ⟨scale, v, norm, hrun, hscale, hsf, hsp, hvs, hvf, hread, hve, hnf, hnp, hsq, _⟩ :=
    FloatQRNorm.scaledColumnNorm_accuracy size indices x p
  have hb : ∀ i ∈ indices, |value (x i)| ≤ value scale := by
    rw [hscale]
    exact (FloatQRNorm.columnScale_correct indices x p.finite p.nonzero).2.2.1
  have hc : ∃ i ∈ indices, value scale = |value (x i)| := by
    rw [hscale]
    exact (FloatQRNorm.columnScale_correct indices x p.finite p.nonzero).2.2.2
  obtain ⟨hlo, hhi⟩ := FloatQRNorm.normalizedSquares_bounds indices x scale hsp hb hc
  have hrad := FloatQRNorm.columnNormRadius_le p.length_le
  have herr := hsq.trans hrad
  have hn32 : (indices.length : ℝ) ≤ 32 := by exact_mod_cast p.length_le
  have hnormlo : (1 : ℝ) / 2 ≤ value norm := by
    have h := (abs_le.mp herr).1
    norm_num at h
    nlinarith
  have hnormhi : value norm ≤ 6 := by
    have h := (abs_le.mp herr).2
    norm_num at h
    nlinarith
  have hvb : ∀ i ∈ indices, |value (v.getD i 0.0)| ≤ 2 := by
    intro i hi
    have hq : |value (x i) / value scale| ≤ 1 := by
      rw [abs_div, abs_of_pos hsp]
      exact (div_le_one hsp).mpr (hb i hi)
    have he := hve i hi
    have ht := abs_sub_le (value (v.getD i 0.0)) (value (x i) / value scale) 0
    simp only [sub_zero] at ht
    norm_num at he hq ht ⊢
    linarith
  exact ⟨
    scale,
    v,
    norm,
    hrun,
    hvs,
    householderReflector_accuracy first indices v norm
      ⟨
        p.length_le,
        hn,
        hfirst,
        by simpa [hvs] using p.in_bounds,
        hvf,
        hvb,
        hnf,
        hnormlo,
        hnormhi
      ⟩
  ⟩

end Kalman.Proofs.FloatQRReflector
