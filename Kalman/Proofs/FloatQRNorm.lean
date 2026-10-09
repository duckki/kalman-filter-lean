import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatResidualError

/-! First QR slice: the actual maximum-scaled column norm, with success derived
from finite nonzero column inputs. Native normalization can underflow; the bound
uses absolute binary64 division errors and does not assume normal quotients. -/

namespace Kalman.Proofs.FloatQRNorm

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Kalman.Proofs.FloatDenseError
open Flare.Binary64.Value

/-- Extraction preserves the original column-loop schedule for all operands,
including zero scales and exceptional values that cause rejection. -/
theorem scaledColumnNorm_schedule (size : Nat) (indices : List Nat) (x : Nat → Float)
    : scaledColumnNorm size indices x
      = (do
          let mut scale := 0.0
          for i in indices do
            scale := max scale (x i).abs
          unless 0.0 < scale do
            throw Kalman.Definitions.Input.Error.nonpositivePivot
          let mut v := Array.replicate size 0.0
          let mut sum := 0.0
          for i in indices do
            let value ← finite (x i / scale)
            v := v.set! i value
            let term ← finite (value * value)
            sum ← finite (sum + term)
          let norm ← finite sum.sqrt
          return (scale, v, norm)) := by
  simp [scaledColumnNorm, columnScale, scaledSquares]

/-- The range used by gramFactor visits exactly the same indices as the
extracted List loop, including an empty range. No finiteness premise is needed. -/
theorem scaledColumnNorm_range_schedule (size start : Nat) (x : Nat → Float)
    : scaledColumnNorm size (List.range' start (size - start)) x
      = (do
          let mut scale := 0.0
          for i in [start:size] do
            scale := max scale (x i).abs
          unless 0.0 < scale do
            throw Kalman.Definitions.Input.Error.nonpositivePivot
          let mut v := Array.replicate size 0.0
          let mut sum := 0.0
          for i in [start:size] do
            let value ← finite (x i / scale)
            v := v.set! i value
            let term ← finite (value * value)
            sum ← finite (sum + term)
          let norm ← finite sum.sqrt
          return (scale, v, norm)) := by
  simpa only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]
    using scaledColumnNorm_schedule size (List.range' start (size - start)) x

private theorem scale_fold (indices : List Nat) (x : Nat → Float) (s : Float)
    (hf : s.isFinite = true) (hs : 0 ≤ value s)
    (hx : ∀ i ∈ indices, (x i).isFinite = true)
    : let r := indices.foldl (fun scale i => max scale (x i).abs) s
      r.isFinite = true
      ∧ 0 ≤ value r
      ∧ value s ≤ value r
      ∧ (∀ i ∈ indices, |value (x i)| ≤ value r)
      ∧ (value r = value s ∨ ∃ i ∈ indices, value r = |value (x i)|) := by
  induction indices generalizing s with
  | nil => simp [hf, hs]
  | cons i indices ih =>
      have ha := Flare.Binary64.Order.abs_value (x i) (hx i (by simp))
      have hm := Flare.Binary64.Order.max_value s (x i).abs hf ha.1
      have hmax : value (max s (x i).abs) = max (value s) |value (x i)| := by
        rw [hm.2, ha.2]
      obtain ⟨hrf, hr0, hsr, hbound, hchoice⟩ := ih (max s (x i).abs) hm.1
        (by rw [hmax]; exact hs.trans (le_max_left _ _))
        (fun j hj => hx j (by simp [hj]))
      dsimp only [List.foldl_cons]
      refine ⟨hrf, hr0, ?_, ?_, ?_⟩
      · calc
          value s ≤ value (max s (x i).abs) := by rw [hmax]; exact le_max_left _ _
          _ ≤ _ := hsr
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · calc
            |value (x j)| ≤ value (max s (x j).abs) := by rw [hmax]; exact le_max_right _ _
            _ ≤ _ := hsr
        · exact hbound j hj
      · rcases hchoice with hchoice | ⟨j, hj, he⟩
        · rw [hmax] at hchoice
          by_cases h : |value (x i)| ≤ value s
          · exact Or.inl (by simpa [max_eq_left h] using hchoice)
          · exact Or.inr ⟨i, by simp, by simpa [max_eq_right (le_of_not_ge h)] using hchoice⟩
        · exact Or.inr ⟨j, by simp [hj], he⟩

/-- Maximum selection and absolute value are exact, even for subnormal inputs.
A finite nonzero column therefore supplies a positive scale attained by an entry. -/
theorem columnScale_correct (indices : List Nat) (x : Nat → Float)
    (hx : ∀ i ∈ indices, (x i).isFinite = true)
    (hn : ∃ i ∈ indices, value (x i) ≠ 0)
    : (columnScale indices x).isFinite = true
      ∧ 0 < value (columnScale indices x)
      ∧ (∀ i ∈ indices, |value (x i)| ≤ value (columnScale indices x))
      ∧ ∃ i ∈ indices, value (columnScale indices x) = |value (x i)| := by
  obtain ⟨hf, _, _, hb, hc⟩ := scale_fold indices x 0.0 (by decide)
    (by simp [Flare.Binary64.Arithmetic.zero_value]) hx
  obtain ⟨i, hi, hn⟩ := hn
  have hp : 0 < value (columnScale indices x) :=
    (abs_pos.mpr hn).trans_le (hb i hi)
  refine ⟨hf, hp, hb, ?_⟩
  rcases hc with hc | hc
  · have hz : value (columnScale indices x) = 0 := by
      simpa [columnScale, Flare.Binary64.Arithmetic.zero_value] using hc
    exact (by linarith : False).elim
  · exact hc

private theorem divided_square (x scale : Float)
    (hx : x.isFinite = true) (hs : scale.isFinite = true) (hp : 0 < value scale)
    (hb : |value x| ≤ value scale)
    : (x / scale).isFinite = true
      ∧ ((x / scale) * (x / scale)).isFinite = true
      ∧ |value ((x / scale) * (x / scale))| ≤ 5
      ∧ |value ((x / scale) * (x / scale)) - (value x / value scale) ^ 2|
        ≤ (2 : ℝ) ^ (-48 : Int) := by
  have hq : |value x / value scale| ≤ 1 := by
    rw [abs_div, abs_of_pos hp]
    exact (div_le_one hp).mpr hb
  have hd := Flare.Binary64.Division.div_error x scale 0 hx hs hp.ne'
    (by norm_num) (by norm_num) (by simpa using hq)
  have hd' : |value (x / scale) - value x / value scale| ≤ (2 : ℝ) ^ (-51 : Int) := by
    simpa using hd.2
  have hz : |value (x / scale)| ≤ 2 := by
    have ht := abs_sub_le (value (x / scale)) (value x / value scale) 0
    simp only [sub_zero] at ht
    have hc : (2 : ℝ) ^ (-51 : Int) ≤ 1 := by norm_num
    linarith
  have hsq : |value (x / scale) * value (x / scale)| ≤ (2 : ℝ) ^ (2 : Int) := by
    rw [abs_mul]
    norm_num
    nlinarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
  have hm := Flare.Binary64.Arithmetic.mul_error (x / scale) (x / scale) 2
    hd.1 hd.1 (by norm_num) (by norm_num) hsq
  have hm' : |value ((x / scale) * (x / scale)) - (value (x / scale)) ^ 2|
      ≤ (2 : ℝ) ^ (-50 : Int) := by simpa [pow_two] using hm.2
  have hzq : |value (x / scale) + value x / value scale| ≤ 3 :=
    (abs_add_le _ _).trans (by linarith)
  have hdiff : |(value (x / scale)) ^ 2 - (value x / value scale) ^ 2|
      ≤ 3 * (2 : ℝ) ^ (-51 : Int) := by
    rw [show (value (x / scale)) ^ 2 - (value x / value scale) ^ 2 =
      (value (x / scale) - value x / value scale) *
        (value (x / scale) + value x / value scale) by ring, abs_mul]
    nlinarith [mul_le_mul hd' hzq (abs_nonneg _) (by positivity)]
  refine ⟨hd.1, hm.1, ?_, ?_⟩
  · have ht := abs_sub_le (value ((x / scale) * (x / scale)))
      ((value (x / scale)) ^ 2) 0
    simp only [sub_zero, abs_of_nonneg (sq_nonneg (value (x / scale)))] at ht
    have hzz : (value (x / scale)) ^ 2 ≤ 4 := by
      have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hz
      norm_num [sq_abs] at h
      exact h
    norm_num at hm'
    nlinarith
  · have ht := abs_sub_le (value ((x / scale) * (x / scale)))
      ((value (x / scale)) ^ 2) ((value x / value scale) ^ 2)
    norm_num at hm' hdiff ⊢
    linarith

private theorem scaledSquares_cons (i : Nat) (indices : List Nat) (x : Nat → Float)
    (scale : Float) (v : Array Float) (s : Float)
    : scaledSquares (i :: indices) x scale v s
      = (do
          let q ← finite (x i / scale)
          let term ← finite (q * q)
          let sum ← finite (s + term)
          scaledSquares indices x scale (v.set! i q) sum) := by
  simp [scaledSquares, List.forIn_cons, bind_assoc]

private theorem squares_loop (indices : List Nat) (x : Nat → Float) (scale : Float)
    (hs : scale.isFinite = true) (hp : 0 < value scale)
    (hx : ∀ i ∈ indices, (x i).isFinite = true)
    (hb : ∀ i ∈ indices, |value (x i)| ≤ value scale)
    (v : Array Float) (s : Float) (target : ℝ) (p : Nat)
    (hlen : p + indices.length ≤ 32) (hf : s.isFinite = true)
    (htarget : |target| ≤ p)
    (he : |value s - target| ≤ squareSumRadius p)
    : ∃ w r,
        scaledSquares indices x scale v s = .ok (w, r)
        ∧ w.size = v.size
        ∧ r.isFinite = true
        ∧ |value r - (target + normalizedSquares indices x scale)|
          ≤ squareSumRadius (p + indices.length) := by
  induction indices generalizing v s target p with
  | nil =>
      exact ⟨v, s, rfl, rfl, hf, by simpa [normalizedSquares] using he⟩
  | cons i indices ih =>
      have hi : (x i).isFinite = true := hx i (by simp)
      have hib : |value (x i)| ≤ value scale := hb i (by simp)
      obtain ⟨hqf, htf, htm, hte⟩ := divided_square (x i) scale hi hs hp hib
      let q := x i / scale
      let term := q * q
      let t := value (x i) / value scale
      have hq : |t| ≤ 1 := by
        dsimp [t]
        rw [abs_div, abs_of_pos hp]
        exact (div_le_one hp).mpr hib
      have hq2 : t ^ 2 ≤ 1 := by
        have := (abs_le.mp hq)
        nlinarith [sq_nonneg t]
      have hp32 : (p : ℝ) ≤ 32 := by exact_mod_cast (show p ≤ 32 by omega)
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have hrad : squareSumRadius p ≤ (1 : ℝ) / 4 := by
        unfold squareSumRadius
        have hprod := mul_le_mul hp32 (by linarith : (p : ℝ) + 20 ≤ 52)
          (by positivity : (0 : ℝ) ≤ p + 20) (by norm_num : (0 : ℝ) ≤ 32)
        norm_num at hprod ⊢
        nlinarith
      have hsm : |value s| ≤ p + (1 : ℝ) / 4 := by
        have htri := abs_sub_le (value s) target 0
        simp only [sub_zero] at htri
        linarith
      have htm' : |value term| ≤ (5 : ℝ) / 4 := by
        have ht := abs_sub_le (value term) (t ^ 2) 0
        simp only [sub_zero, abs_of_nonneg (sq_nonneg t)] at ht
        change |value term - t ^ 2| ≤ _ at hte
        norm_num at hte
        linarith
      have ham : |value s + value term| ≤ p + (3 : ℝ) / 2 :=
        (abs_add_le _ _).trans (by linarith)
      obtain ⟨haf, hae⟩ := Flare.Binary64.Arithmetic.add_error_relative s term hf htf
        (ham.trans ((by linarith : (p : ℝ) + 3 / 2 ≤ 64).trans
          ((by norm_num : (64 : ℝ) = 2 ^ (6 : Int)).le.trans
            (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))))
      have hη : (2 : ℝ) ^ (-1022 : Int) ≤ (1 : ℝ) / 2 := by
        simpa using (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (-1022 : Int) ≤ -1))
      have hae' : |value (s + term) - (value s + value term)|
          ≤ (p + 2) * (2 : ℝ) ^ (-51 : Int) := by
        apply hae.trans
        calc
          _ ≤ (2 : ℝ) ^ (-51 : Int) * (p + 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
          _ = _ := by ring
      have htarget' : |target + t ^ 2| ≤ (p + 1 : Nat) := by
        have ht := abs_add_le target (t ^ 2)
        rw [abs_of_nonneg (sq_nonneg t)] at ht
        push_cast
        linarith
      have he' : |value (s + term) - (target + t ^ 2)| ≤ squareSumRadius (p + 1) := by
        have hsum : |(value s + value term) - (target + t ^ 2)|
            ≤ |value s - target| + |value term - t ^ 2| := by
          rw [show (value s + value term) - (target + t ^ 2) =
            (value s - target) + (value term - t ^ 2) by ring]
          exact abs_add_le _ _
        have ht := abs_sub_le (value (s + term)) (value s + value term) (target + t ^ 2)
        have he0 : |value s - target| ≤ squareSumRadius p := by
          exact he
        dsimp [term, q, t] at ht hsum ⊢
        norm_num [squareSumRadius] at he0 hte hae' ⊢
        nlinarith
      obtain ⟨w, r, hr, hw, hrf, hre⟩ := ih
        (fun j hj => hx j (by simp [hj])) (fun j hj => hb j (by simp [hj]))
        (v.set! i q) (s + term) (target + t ^ 2) (p + 1)
        (by simp only [List.length_cons] at hlen; omega) haf htarget' he'
      refine ⟨w, r, ?_, ?_, hrf, ?_⟩
      · rw [scaledSquares_cons, finite_ok _ hqf]
        change (do
          let term ← finite (q * q)
          let sum ← finite (s + term)
          scaledSquares indices x scale (v.set! i q) sum) = .ok (w, r)
        rw [finite_ok _ htf]
        change (do
          let sum ← finite (s + term)
          scaledSquares indices x scale (v.set! i q) sum) = .ok (w, r)
        rw [finite_ok _ haf]
        exact hr
      · simpa using hw
      · simpa [normalizedSquares, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          add_assoc, t] using hre

/-- The normalized sum-of-squares loop succeeds from finite bounded operands.
The output bound includes division rounding as well as square/add rounding. -/
theorem scaledSquares_accuracy (indices : List Nat) (x : Nat → Float) (scale : Float)
    (hlen : indices.length ≤ 32) (hs : scale.isFinite = true) (hp : 0 < value scale)
    (hx : ∀ i ∈ indices, (x i).isFinite = true)
    (hb : ∀ i ∈ indices, |value (x i)| ≤ value scale) (v : Array Float)
    : ∃ w r,
        scaledSquares indices x scale v 0.0 = .ok (w, r)
        ∧ w.size = v.size
        ∧ r.isFinite = true
        ∧ |value r - normalizedSquares indices x scale|
          ≤ squareSumRadius indices.length := by
  simpa [Flare.Binary64.Arithmetic.zero_value, squareSumRadius]
    using squares_loop indices x scale hs hp hx hb v 0.0 0 0 (by simpa using hlen)
      (by decide) (by simp)
      (by simp [Flare.Binary64.Arithmetic.zero_value, squareSumRadius])

theorem normalizedSquares_bounds (indices : List Nat) (x : Nat → Float) (scale : Float)
    (hp : 0 < value scale)
    (hb : ∀ i ∈ indices, |value (x i)| ≤ value scale)
    (hc : ∃ i ∈ indices, value scale = |value (x i)|)
    : 1 ≤ normalizedSquares indices x scale
      ∧ normalizedSquares indices x scale ≤ indices.length := by
  have hterm (i : Nat) (hi : i ∈ indices) : (value (x i) / value scale) ^ 2 ≤ 1 := by
    have hq : |value (x i) / value scale| ≤ 1 := by
      rw [abs_div, abs_of_pos hp]
      exact (div_le_one hp).mpr (hb i hi)
    nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  constructor
  · obtain ⟨i, hi, he⟩ := hc
    have hiq : (value (x i) / value scale) ^ 2 = 1 := by
      rw [← sq_abs, abs_div, abs_of_pos hp, ← he, div_self hp.ne']
      norm_num
    unfold normalizedSquares
    rw [← hiq]
    apply List.single_le_sum
    · intro z hz
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
      exact sq_nonneg _
    · exact List.mem_map.mpr ⟨i, hi, rfl⟩
  · unfold normalizedSquares
    calc
      _ ≤ (indices.map (fun _ => (1 : ℝ))).sum := List.sum_le_sum hterm
      _ = indices.length := by simp

private theorem scaledSquares_storage (indices : List Nat) (x : Nat → Float)
    (scale : Float) (hs : scale.isFinite = true) (hp : 0 < value scale)
    (hx : ∀ i ∈ indices, (x i).isFinite = true)
    (hb : ∀ i ∈ indices, |value (x i)| ≤ value scale) (v : Array Float) (s : Float)
    (w : Array Float) (r : Float) (hv : v.all Float.isFinite = true)
    (hi : ∀ i ∈ indices, i < v.size) (hr : scaledSquares indices x scale v s = .ok (w, r))
    : w.all Float.isFinite = true
      ∧ ∀ j, w.getD j 0.0 = if j ∈ indices then x j / scale else v.getD j 0.0 := by
  induction indices generalizing v s with
  | nil =>
      have he : v = w := by
        change Except.ok (v, s) = Except.ok (w, r) at hr
        have hpair : (v, s) = (w, r) := Except.ok.inj hr
        exact congrArg Prod.fst hpair
      subst w
      exact ⟨hv, by simp⟩
  | cons i indices ih =>
      obtain ⟨hqf, htf, _, _⟩ := divided_square (x i) scale (hx i (by simp))
        hs hp (hb i (by simp))
      rw [scaledSquares_cons, finite_ok _ hqf] at hr
      change (do
        let term ← finite ((x i / scale) * (x i / scale))
        let sum ← finite (s + term)
        scaledSquares indices x scale (v.set! i (x i / scale)) sum) = .ok (w, r) at hr
      rw [finite_ok _ htf] at hr
      change (do
        let sum ← finite (s + (x i / scale) * (x i / scale))
        scaledSquares indices x scale (v.set! i (x i / scale)) sum) = .ok (w, r) at hr
      cases hadd : finite (s + (x i / scale) * (x i / scale)) with
      | error e =>
          rw [hadd] at hr
          change Except.error e = Except.ok (w, r) at hr
          cases hr
      | ok next =>
          rw [hadd] at hr
          change scaledSquares indices x scale (v.set! i (x i / scale)) next = .ok (w, r) at hr
          obtain ⟨hw, hread⟩ := ih (fun j hj => hx j (by simp [hj]))
            (fun j hj => hb j (by simp [hj])) (v.set! i (x i / scale)) next
            (Flare.Matrix.Storage.all_set v i _ hv hqf)
            (fun j hj => by simpa using hi j (by simp [hj])) hr
          refine ⟨hw, ?_⟩
          intro j
          rw [hread]
          by_cases hj : j ∈ indices
          · simp [hj]
          · by_cases hji : j = i
            · subst j
              simp [hj, Array.set!_eq_setIfInBounds, hi i (by simp),
                Array.getD_eq_getD_getElem?]
            · simp [hj, hji, Array.set!_eq_setIfInBounds,
                Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm hji)]

theorem columnNormRadius_le {n : Nat} (hn : n ≤ 32)
    : columnNormRadius n ≤ (2 : ℝ) ^ (-38 : Int) := by
  have h : (n : ℝ) ≤ 32 := by exact_mod_cast hn
  have hprod : (n : ℝ) * (n + 20) ≤ 32 * 52 :=
    mul_le_mul h (by linarith) (by positivity) (by norm_num)
  norm_num [columnNormRadius, squareSumRadius]
  nlinarith

/-- Input-only norm guarantee: at most 32 finite entries with one nonzero entry
ensure successful finite execution and a positive normalized norm. Neither native
success nor intermediate magnitude/positivity is assumed. -/
theorem scaledColumnNorm_accuracy (size : Nat) (indices : List Nat) (x : Nat → Float)
    (p : ColumnProfile size indices x)
    : ColumnNormAccuracy size indices x := by
  let scale := columnScale indices x
  obtain ⟨hsf, hsp, hb, hc⟩ := columnScale_correct indices x p.finite p.nonzero
  obtain ⟨v, s, hs, hv, hsf', he⟩ := scaledSquares_accuracy indices x scale p.length_le
    hsf hsp p.finite hb (Array.replicate size 0.0)
  obtain ⟨hlo, hhi⟩ := normalizedSquares_bounds indices x scale hsp hb hc
  obtain ⟨hvf, hvread⟩ := scaledSquares_storage indices x scale hsf hsp p.finite hb
    (Array.replicate size 0.0) 0.0 v s
    (Flare.Matrix.Storage.replicate_storage size).2 (by simpa using p.in_bounds) hs
  have hrad : squareSumRadius indices.length < 1 := by
    have hn : (indices.length : ℝ) ≤ 32 := by exact_mod_cast p.length_le
    have hprod : (indices.length : ℝ) * (indices.length + 20) ≤ 32 * 52 :=
      mul_le_mul hn (by linarith) (by positivity) (by norm_num)
    norm_num [squareSumRadius]
    nlinarith
  have hpos : 0 < value s := by
    have := (abs_le.mp he).1
    linarith
  obtain ⟨_, hnf, hnp, hne⟩ := FloatResidualError.positiveSqrt_accuracy s hsf' hpos
  have hsbound : value s ≤ indices.length + squareSumRadius indices.length := by
    have := (abs_le.mp he).2
    linarith
  have hnorm : |(value s.sqrt) ^ 2 - normalizedSquares indices x scale|
      ≤ columnNormRadius indices.length := by
    have htri := abs_sub_le ((value s.sqrt) ^ 2) (value s)
      (normalizedSquares indices x scale)
    have hmul := mul_le_mul_of_nonneg_left hsbound
      (by positivity : 0 ≤ 2 * (2 : ℝ) ^ (-53 : Int) + ((2 : ℝ) ^ (-53 : Int)) ^ 2)
    unfold columnNormRadius
    linarith
  have hroot : 1 ≤ Real.sqrt (normalizedSquares indices x scale) := by
    have := Real.sqrt_le_sqrt hlo
    simpa using this
  have hsq : (Real.sqrt (normalizedSquares indices x scale)) ^ 2 =
      normalizedSquares indices x scale := Real.sq_sqrt (by linarith)
  have hnerr : |value s.sqrt - Real.sqrt (normalizedSquares indices x scale)|
      ≤ columnNormRadius indices.length := by
    have hid : |(value s.sqrt) ^ 2 - normalizedSquares indices x scale| =
        |value s.sqrt - Real.sqrt (normalizedSquares indices x scale)| *
          (value s.sqrt + Real.sqrt (normalizedSquares indices x scale)) := by
      calc
        _ = |(value s.sqrt) ^ 2
              - (Real.sqrt (normalizedSquares indices x scale)) ^ 2| := by
          rw [hsq]
        _ = _ := by
          rw [show (value s.sqrt) ^ 2 -
            (Real.sqrt (normalizedSquares indices x scale)) ^ 2 =
            (value s.sqrt - Real.sqrt (normalizedSquares indices x scale)) *
              (value s.sqrt + Real.sqrt (normalizedSquares indices x scale)) by ring,
            abs_mul, abs_of_pos (show 0 < value s.sqrt +
              Real.sqrt (normalizedSquares indices x scale) by linarith)]
    rw [hid] at hnorm
    nlinarith [abs_nonneg (value s.sqrt - Real.sqrt (normalizedSquares indices x scale))]
  have hvread' : ∀ i, v.getD i 0.0 = if i ∈ indices then x i / scale else 0.0 := by
    intro i
    have hz : (Array.replicate size (0.0 : Float)).getD i 0.0 = 0.0 := by
      by_cases hi : i < size <;> simp [Array.getD_eq_getD_getElem?, hi]
    rw [hvread, hz]
  have hve : ∀ i ∈ indices,
      |value (v.getD i 0.0) - value (x i) / value scale| ≤ (2 : ℝ) ^ (-51 : Int) := by
    intro i hi
    have hq : |value (x i) / value scale| ≤ 1 := by
      rw [abs_div, abs_of_pos hsp]
      exact (div_le_one hsp).mpr (hb i hi)
    have hd := Flare.Binary64.Division.div_error (x i) scale 0 (p.finite i hi) hsf hsp.ne'
      (by norm_num) (by norm_num) (by simpa using hq)
    simpa only [hvread', ite_eq_left hi, show (0 : Int) - 51 = -51 by omega] using hd.2
  refine ⟨
    scale,
    v,
    s.sqrt,
    ?_,
    rfl,
    hsf,
    hsp,
    by simpa using hv,
    hvf,
    hvread',
    hve,
    hnf,
    hnp,
    hnorm,
    hnerr
  ⟩
  have hg : 0.0 < scale := (Flare.Binary64.Order.lt_iff _ _ (by decide) hsf).mpr
    (by simpa [Flare.Binary64.Arithmetic.zero_value] using hsp)
  dsimp only [scale] at hg ⊢
  simp only [scaledColumnNorm, hg, ↓reduceIte]
  rw [hs]
  change (do
    let norm ← finite s.sqrt
    return (scale, v, norm)) = .ok (scale, v, s.sqrt)
  rw [finite_ok _ hnf]
  rfl

end Kalman.Proofs.FloatQRNorm
