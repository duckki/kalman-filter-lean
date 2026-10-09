import Kalman.Proofs.QRProfiles
import Kalman.Proofs.FloatQRFinish

/-! One full native QR iteration. Column independence keeps the application
reference at the original stored matrix; finishing then preserves all trailing
results. These bounds do not establish a domain for later QR iterations. -/

namespace Kalman.Proofs.FloatQRIteration

open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation.OrthogonalFactorization
open Kalman.Proofs.QRProfiles
open Flare.Binary64.Value

theorem applyReflectorColumns_range_schedule (height width pivot : Nat)
    (w a : Array Float)
    : applyReflectorColumns width (List.range' (pivot + 1) (width - (pivot + 1)))
        (List.range' pivot (height - pivot)) w a
      = (do
          let mut a := a
          for j in [pivot + 1:width] do
            a ← applyReflector width j (List.range' pivot (height - pivot)) w a
          return a) := by
  simp only [applyReflectorColumns, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]

/-- Exact extraction of the old QR iteration, on all operands and failures. -/
theorem qrIteration_schedule (height width pivot : Nat) (a : Array Float)
    : qrIteration height width pivot a
      = (do
          let (scale, v, norm) ←
            scaledColumnNorm height (List.range' pivot (height - pivot))
              (fun i => entry width a i pivot)
          let (alpha, w) ←
            householderReflector pivot (List.range' pivot (height - pivot)) v norm
          let mut a := a
          for j in [pivot + 1:width] do
            a ← applyReflector width j (List.range' pivot (height - pivot)) w a
          finishColumn width pivot pivot (List.range' (pivot + 1) (height - (pivot + 1)))
            a alpha scale) := by
  unfold qrIteration
  simp [applyReflectorColumns_range_schedule]

private theorem applyReflectorColumns_cons (width column : Nat)
    (columns indices : List Nat) (w a : Array Float)
    : applyReflectorColumns width (column :: columns) indices w a
      = (do
          let next ← applyReflector width column indices w a
          applyReflectorColumns width columns indices w next) := by
  simp [applyReflectorColumns]

private theorem slot_column_ne {width c j i r : Nat} (hc : c < width) (hj : j < width)
    (hn : c ≠ j)
    : i * width + c ≠ r * width + j := by
  intro he
  have hm := congrArg (fun t => t % width) he
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hj] at hm
  exact hn hm

/-- Unselected valid columns are unchanged at every row, not just active rows. -/
theorem outsidePanel_sameColumn (width : Nat) (indices columns : List Nat)
    (a b : Array Float) (hp : OutsidePanel width indices columns a b)
    (hb : ∀ j ∈ columns, j < width) (column : Nat) (hc : column < width)
    (hn : column ∉ columns)
    : SameColumn width column a b := by
  intro i
  exact (hp (i * width + column) (fun r _ j hj =>
    slot_column_ne hc (hb j hj) (fun he => hn (he.symm ▸ hj)))).symm

theorem reflectorAppliedValue_sameColumn (width column : Nat) (indices : List Nat)
    (w a b : Array Float) (h : SameColumn width column a b) (i : Nat)
    : reflectorAppliedValue width column indices w b i
      = reflectorAppliedValue width column indices w a i := by
  unfold reflectorAppliedValue reflectorDotValue
  have hs : ∀ r, entry width a r column = entry width b r column := h
  simp_rw [← hs]

/-- Every selected column is visited once. Its input and exact reference are
those of the original matrix, so the error does not grow with the column count. -/
theorem applyReflectorColumns_accuracy (height width : Nat) (indices columns : List Nat)
    (w a : Array Float) (M : ℝ)
    (p : ColumnPanelProfile height width indices columns w a M)
    : ColumnPanelAccuracy width indices columns w a M := by
  induction columns generalizing a with
  | nil => exact ⟨a, rfl, rfl, p.matrix_finite, by simp [OutsidePanel], by simp⟩
  | cons column columns ih =>
      have hn := List.nodup_cons.mp p.columns_nodup
      have hc := p.columns_bound column (by simp)
      have app : ApplicationProfile height width column indices w a M :=
        ⟨p.length_le, p.rows_nodup, hc, p.rows_bound, p.vector_size, p.matrix_size,
          p.vector_finite, p.matrix_finite, p.vector_magnitude, p.budget_lower, p.budget_upper,
          p.panel_magnitude column (by simp)⟩
      obtain ⟨next, hrun, hsize, hfinite, hcopy, herr⟩ :=
        FloatQRApplication.applyReflector_accuracy height width column indices w a M app
      have hsame : ∀ j ∈ columns, SameColumn width j a next := by
        intro j hj
        apply outsidePanel_sameColumn width indices [column] a next
          (by simpa [OutsidePanel] using hcopy) (by simpa using hc) j
          (p.columns_bound j (by simp [hj]))
        simpa only [List.mem_singleton] using (show j ≠ column from fun he => hn.1 (he ▸ hj))
      have tailProfile : ColumnPanelProfile height width indices columns w next M :=
        ⟨p.length_le, p.rows_nodup, hn.2, fun j hj => p.columns_bound j (by simp [hj]),
          p.rows_bound, p.vector_size, hsize.trans p.matrix_size, p.vector_finite, hfinite,
          p.vector_magnitude, p.budget_lower, p.budget_upper, by
            intro j hj i hi
            rw [← hsame j hj i]
            exact p.panel_magnitude j (by simp [hj]) i hi⟩
      obtain ⟨output, hout, hos, hof, hocopy, hoe⟩ := ih next tailProfile
      have hhead : SameColumn width column next output := outsidePanel_sameColumn width indices
        columns next output hocopy tailProfile.columns_bound column hc hn.1
      refine ⟨output, ?_, hos.trans hsize, hof, ?_, ?_⟩
      · rw [applyReflectorColumns_cons, hrun]
        exact hout
      · intro t ht
        rw [hocopy t (fun i hi j hj => ht i hi j (by simp [hj]))]
        exact hcopy t (fun i hi => ht i hi column (by simp))
      · intro j hj i hi
        rcases List.mem_cons.mp hj with rfl | hj
        · rw [← hhead i]
          exact herr i hi
        · have he := hoe j hj i hi
          rw [reflectorAppliedValue_sameColumn width j indices w a next (hsame j hj) i] at he
          exact he

/-- Both source finishing and trailing application determine the iteration allowance. -/
theorem iterationRadius_mono {k l : Nat} (hkl : k ≤ l) (M : ℝ) (hM : 0 ≤ M)
    : iterationRadius k M ≤ iterationRadius l M := by
  unfold iterationRadius applicationRadius reflectorRadius
  apply add_le_add
  · exact max_le_max (FloatQRFinish.sourceWriteRadius_mono hkl M hM) (by gcongr)
  · gcongr

private theorem iterationRadius_cap {k : Nat} (M : ℝ) (hk : k ≤ 32) (hM : 0 ≤ M)
    : iterationRadius k M ≤ (2 : ℝ) ^ (-31 : Int) * M := by
  apply (iterationRadius_mono hk M hM).trans
  unfold iterationRadius
  apply (add_le_add
          (max_le (FloatQRFinish.sourceWriteRadius_le_tight M le_rfl hM)
            (by norm_num [applicationRadius]; nlinarith))
          le_rfl).trans
  norm_num [reflectorRadius]
  nlinarith

theorem iterationRadius_le {k : Nat} (M : ℝ) (hk : k ≤ 32) (hM : 0 ≤ M)
    : iterationRadius k M ≤ (2 : ℝ) ^ (-17 : Int) * M := by
  exact (iterationRadius_cap M hk hM).trans (mul_le_mul_of_nonneg_right (by norm_num) hM)

/-- Sharper cap from the tightened reflector and source estimates. -/
theorem iterationRadius_le_tight {k : Nat} (M : ℝ) (hk : k ≤ 32) (hM : 0 ≤ M)
    : iterationRadius k M ≤ (2 : ℝ) ^ (-31 : Int) * M :=
  iterationRadius_cap M hk hM

/-- The Real normalization reference has exactly unit squared norm, even though
the returned native reflector has only the preceding near-unit guarantee. -/
theorem constructedUnitComponent_unit (first : Nat) (indices : List Nat)
    (v : Array Float) (norm : Float)
    (hS : 0 < vectorSquares indices (constructedVector first v norm))
    : (indices.map (fun i => (constructedUnitComponent first indices v norm i) ^ 2)).sum
      = 1 := by
  let b := constructedVector first v norm
  let S := vectorSquares indices b
  change (indices.map (fun i => (value (b.getD i 0.0)/Real.sqrt S)^2)).sum = 1
  have hr : (Real.sqrt S)^2 = S := Real.sq_sqrt hS.le
  simp_rw [div_pow, hr, div_eq_mul_inv]
  rw [List.sum_map_mul_right]
  exact mul_inv_cancel₀ (ne_of_gt hS)

private theorem mem_unit_range (start stop i : Nat)
    : i ∈ List.range' start (stop - start) ↔ start ≤ i ∧ i < stop := by
  rw [List.mem_range']
  constructor
  · rintro ⟨t, ht, he⟩
    simp only [Nat.one_mul] at he
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨i - start, by omega, ?_⟩
    simp only [Nat.one_mul]
    omega

private theorem norm_run_unique (height : Nat) (indices : List Nat) (x : Nat → Float)
    (s vNorm : Float) (v : Array Float) (s' vNorm' : Float) (v' : Array Float)
    (h : scaledColumnNorm height indices x = .ok (s, v, vNorm))
    (h' : scaledColumnNorm height indices x = .ok (s', v', vNorm'))
    : s' = s ∧ v' = v ∧ vNorm' = vNorm := by
  have hp := Except.ok.inj (h'.symm.trans h)
  exact ⟨congrArg Prod.fst hp, congrArg (fun t => t.2.1) hp, congrArg (fun t => t.2.2) hp⟩

set_option maxHeartbeats 800000 in
/-- Input-only success and error for one entire QR iteration. All active
references use the matrix before any trailing-column writes. Later profiles
are derived separately in FloatQRInitialDomain on the eight-row input domain. -/
theorem qrIteration_accuracy (height width pivot : Nat) (a : Array Float) (M : ℝ)
    (p : IterationProfile height width pivot a M)
    : IterationAccuracy height width pivot a M := by
  let I := List.range' pivot (height - pivot)
  let J := List.range' (pivot + 1) (width - (pivot + 1))
  let tail := List.range' (pivot + 1) (height - (pivot + 1))
  let x := fun i => entry width a i pivot
  have hI : I = pivot :: tail := FloatQRFinish.active_range_cons height pivot p.pivot_height
  have hrows : ∀ i, i ∈ I ↔ pivot ≤ i ∧ i < height := mem_unit_range pivot height
  have hcols : ∀ j, j ∈ J ↔ pivot + 1 ≤ j ∧ j < width := mem_unit_range (pivot + 1) width
  have hn : I.Nodup := List.nodup_range'
  have hfirst : pivot ∈ I := (hrows pivot).mpr ⟨le_rfl, p.pivot_height⟩
  have hlen : I.length ≤ 32 := by simpa [I] using p.length_le
  have input : ColumnProfile height I x := by
    refine ⟨hlen, fun i hi => ((hrows i).mp hi).2, ?_, ?_⟩
    · intro i _
      exact Flare.Matrix.Storage.getD_finite a _ p.matrix_finite
    · obtain ⟨i, hi, hib, he⟩ := p.source_witness
      exact ⟨i, (hrows i).mpr ⟨hi, hib⟩,
        abs_pos.mp ((zpow_pos (by norm_num : (0 : ℝ)<2) (-900 : Int)).trans_le he)⟩
  have source : SourceColumnProfile height width pivot pivot tail a := by
    have hn' := List.nodup_cons.mp (hI ▸ hn)
    refine ⟨by simpa only [← hI] using hlen, hn'.2, hn'.1, p.pivot_width,
      by simpa only [← hI] using input.in_bounds, p.matrix_size, p.matrix_finite, ?_, ?_⟩
    · intro i hi
      have hr := (hrows i).mp (hI.symm ▸ hi)
      exact (p.panel_magnitude i hr.1 hr.2 pivot le_rfl p.pivot_width).trans p.budget_upper
    · obtain ⟨i, hi, hib, he⟩ := p.source_witness
      exact ⟨i, hI ▸ (hrows i).mpr ⟨hi, hib⟩, he⟩
  obtain ⟨scale, v, norm, alpha, w, sourceOutput, hnorm, hreflect, _, hsf, hsp, _, hsourcef,
      hsourcediag, hsourcelo, hsourceguard, hsourcezero, _, hsourceSquare, hsourceError⟩ :=
    FloatQRFinish.scaledColumn_finish_accuracy height width pivot pivot tail a source
  rw [← hI] at hnorm hreflect hsourceSquare hsourceError
  obtain ⟨scale', v', norm', hnorm', hvs, hreflector⟩ :=
    FloatQRReflector.scaledColumn_reflector_accuracy height pivot I x input hn hfirst
  obtain ⟨hs, hv, hr⟩ := norm_run_unique height I x scale norm v scale' norm' v' hnorm hnorm'
  subst scale' v' norm'
  obtain ⟨alpha', w', hreflect', halpha, _, _, _, _, hmargin, hws, hwf, _, hwe, hunit⟩ := hreflector
  have hpair := Except.ok.inj (hreflect'.symm.trans hreflect)
  have heAlpha := congrArg Prod.fst hpair
  have heVector := congrArg Prod.snd hpair
  change alpha' = alpha at heAlpha
  change w' = w at heVector
  subst heAlpha heVector
  obtain ⟨scale', v', norm', hnorm', hscale, _⟩ := FloatQRNorm.scaledColumnNorm_accuracy height I x input
  obtain ⟨hs, _, _⟩ := norm_run_unique height I x scale norm v scale' norm' v' hnorm hnorm'
  have hScale : scale = columnScale I x := hs.symm.trans hscale
  have hsM : value scale ≤ M := by
    obtain ⟨i, hi, he⟩ := (FloatQRNorm.columnScale_correct I x input.finite input.nonzero).2.2.2
    rw [← hScale] at he
    rw [he]
    obtain ⟨hil, hib⟩ := (hrows i).mp hi
    exact p.panel_magnitude i hil hib pivot le_rfl p.pivot_width
  have hsLower : (2 : ℝ)^(-900 : Int) ≤ value scale := by
    obtain ⟨i, hil, hib, he⟩ := p.source_witness
    have hbound := (FloatQRNorm.columnScale_correct I x input.finite input.nonzero).2.2.1
    rw [← hScale] at hbound
    exact he.trans (hbound i ((hrows i).mpr ⟨hil, hib⟩))
  have hM : 0 < M := (zpow_pos (by norm_num) _).trans_le p.budget_lower
  have hwm := FloatQRApplication.nearUnit_magnitude I w' (hunit.trans (FloatQRReflector.reflectorRadius_le hlen))
  have panelProfile : ColumnPanelProfile height width I J w' a M :=
    ⟨hlen, hn, List.nodup_range', fun j hj => ((hcols j).mp hj).2,
      input.in_bounds, hws.trans hvs, p.matrix_size, hwf, p.matrix_finite, hwm,
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-1022 : Int) ≤ -900)).trans p.budget_lower,
      p.budget_upper, by
        intro j hj i hi
        obtain ⟨hjl, hjb⟩ := (hcols j).mp hj
        obtain ⟨hil, hib⟩ := (hrows i).mp hi
        exact p.panel_magnitude i hil hib j (by omega) hjb⟩
  obtain ⟨panel, hpanel, hpanels, hpanelf, hpanelcopy, hpanelError⟩ :=
    applyReflectorColumns_accuracy height width I J w' a M panelProfile
  have hdf : (alpha' * scale).isFinite = true := by
    rw [← hsourcediag]
    exact Flare.Matrix.Storage.getD_finite sourceOutput _ hsourcef
  obtain ⟨output, hout, hos, hof, hdiag, hzero, hcopy⟩ := FloatQRFinish.finishColumn_storage
    height width pivot pivot tail panel alpha' scale hpanelf (hpanels.trans p.matrix_size)
    p.pivot_width source.in_bounds source.first_not_tail hdf
  have hsourceRead : ∀ i ∈ I, entry width output i pivot = entry width sourceOutput i pivot := by
    intro i hi
    rw [hI] at hi
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hdiag, hsourcediag]
    · rw [hzero i hi, hsourcezero i hi]
  have htrailRead : ∀ j ∈ J, SameColumn width j panel output := by
    intro j hj i
    obtain ⟨hjl, hjb⟩ := (hcols j).mp hj
    have hne : j ≠ pivot := by omega
    exact (hcopy (i * width + j) (slot_column_ne hjb p.pivot_width hne)
      (fun r _ => slot_column_ne hjb p.pivot_width hne)).symm
  have hframe : OutsidePanel width I (pivot :: J) a output := by
    intro t ht
    rw [hcopy t (ht pivot hfirst pivot (by simp)) (fun i hi =>
      ht i (hI.symm ▸ (List.mem_cons_of_mem pivot hi)) pivot (by simp))]
    exact hpanelcopy t (fun i hi j hj => ht i hi j (by simp [hj]))
  have htrailing : ∀ j ∈ J, ∀ i ∈ I,
      |value (entry width output i j)-reflectorAppliedValue width j I w' a i|
        ≤ applicationRadius I.length M := by
    intro j hj i hi
    rw [← htrailRead j hj i]
    exact hpanelError j hj i hi
  have hall : ∀ j ∈ pivot :: J, ∀ i ∈ I,
      |value (entry width output i j)-reflectorAppliedValue width j I w' a i|
        ≤ max (sourceWriteRadius I.length M) (applicationRadius I.length M) := by
    intro j hj i hi
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [hsourceRead i hi]
      exact (hsourceError i hi).trans (by
        apply le_trans _ (le_max_left _ _)
        unfold sourceWriteRadius sourceResidualRadius columnNormRadius squareSumRadius reflectorRadius
        exact mul_le_mul_of_nonneg_left hsM (by positivity))
    · exact (htrailing j hj i hi).trans (le_max_right _ _)
  let b := constructedVector pivot v norm
  have hhead : b.getD pivot 0.0 = v.getD pivot 0.0-alpha' := by
    dsimp only [b, constructedVector]
    rw [← halpha]
    have hpv : pivot < v.size := by rw [hvs]; exact p.pivot_height
    simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hpv]
  have hS : 0 < vectorSquares I b := by
    have hterm : (value (b.getD pivot 0.0))^2 ≤ vectorSquares I b := by
      apply List.single_le_sum
      · intro z hz
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
        exact sq_nonneg _
      · exact List.mem_map.mpr ⟨pivot, hfirst, rfl⟩
    rw [hhead] at hterm
    nlinarith [sq_abs (value (v.getD pivot 0.0-alpha'))]
  refine ⟨
    scale,
    v,
    norm,
    alpha',
    w',
    panel,
    output,
    hnorm,
    hreflect,
    hpanel,
    hout,
    ?_,
    hos.trans hpanels,
    hof,
    hframe,
    hsf,
    hsp,
    hsLower,
    hsM,
    hws.trans hvs,
    hwf,
    hS,
    constructedUnitComponent_unit pivot I v norm hS,
    hdiag,
    by simpa only [hdiag, hsourcediag] using hsourcelo,
    by simpa only [hdiag, hsourcediag] using hsourceguard,
    hzero,
    ?_,
    htrailing,
    hall,
    ?_
  ⟩
  · unfold qrIteration
    dsimp only
    rw [hnorm]
    change (do
      let (alpha', w') ← householderReflector pivot I v norm
      let panel ← applyReflectorColumns width J I w' a
      finishColumn width pivot pivot tail panel alpha' scale) = .ok output
    rw [hreflect]
    change (do
      let panel ← applyReflectorColumns width J I w' a
      finishColumn width pivot pivot tail panel alpha' scale) = .ok output
    rw [hpanel]
    exact hout
  · rw [hdiag, ← hsourcediag]
    exact hsourceSquare
  · intro j hj i hi
    have hjb : j < width := by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact p.pivot_width
      · exact ((hcols j).mp hj).2
    have hjl : pivot ≤ j := by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact le_rfl
      · have := ((hcols j).mp hj).1; omega
    have hperturb := FloatQRApplication.constructed_perturbation width j pivot I w' v a norm M hwm
      (fun r hr => p.panel_magnitude r ((hrows r).mp hr).1 ((hrows r).mp hr).2 j hjl hjb) hwe
    exact (abs_sub_le (value (entry width output i j)) (reflectorAppliedValue width j I w' a i)
      (constructedAppliedValue width j pivot I v norm a i)).trans
      (add_le_add (hall j hj i hi) (hperturb i hi))

end Kalman.Proofs.FloatQRIteration
