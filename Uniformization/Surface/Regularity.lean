/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Rado.Surface.Barriers

/-!
# Dirichlet problem on exterior-disk-regular domains

`ExteriorDiskAt W ξ` says a chart around the frontier point `ξ` contains a
closed disk touching `e ξ` whose interior misses `W` — the classical exterior
disk condition. It yields a strong log-barrier at `ξ` (use a smaller disk
internally tangent at `e ξ` to get quantitative separation away from `ξ`, then
extend by `max` with a negative constant outside the chart annulus, as in
`Rado/Surface/Barriers.lean`).

`exists_dirichlet_solution` solves the Dirichlet problem by Perron's method on
a relatively compact open set all of whose frontier points satisfy the
exterior disk condition: normalize the boundary data into `[0,1]`, run
`Rado.IsPerronFamily`/`Rado.perronSup`, and prove boundary attainment with the
barrier.
-/

open Set Metric Topology MeasureTheory InnerProductSpace Complex Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The exterior disk condition at a point `ξ` (relative to a set `W ⊆ X`):
some chart around `ξ` contains a closed disk whose interior misses `W` and
whose boundary circle passes through `e ξ`. This is the regularity condition
our exhaustion pieces satisfy at every frontier point. -/
def ExteriorDiskAt (W : Set X) (ξ : X) : Prop :=
  ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧ ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
    closedBall c r ⊆ e.target ∧ dist (e ξ) c = r ∧
    ∀ x ∈ W ∩ e.source, e x ∉ ball c r

/-! ## Geometry: the internally tangent disk -/

/-- Median (parallelogram) identity in `ℂ`. -/
private theorem norm_sub_midpoint_sq (z a c : ℂ) :
    ‖z - (a + c) / 2‖ ^ 2 =
      (1 / 2) * ‖z - a‖ ^ 2 + (1 / 2) * ‖z - c‖ ^ 2 - (1 / 4) * ‖a - c‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im]
  norm_num
  ring

/-- Quantitative separation from the internally tangent half-disk: if `a` lies
on the circle of radius `r` about `c` and `z` lies outside the open disk
`ball c r`, then `z` keeps distance at least `r/2` from the tangent center
`(a+c)/2`, with a quadratic gap in `‖z - a‖`. -/
private theorem tangent_gap {z a c : ℂ} {r : ℝ} (hr : 0 ≤ r) (ha : ‖a - c‖ = r)
    (hz : r ≤ ‖z - c‖) :
    (r / 2) ^ 2 + (1 / 2) * ‖z - a‖ ^ 2 ≤ ‖z - (a + c) / 2‖ ^ 2 := by
  have hid := norm_sub_midpoint_sq z a c
  have h1 : r ^ 2 ≤ ‖z - c‖ ^ 2 := by nlinarith [norm_nonneg (z - c)]
  have h2 : ‖a - c‖ ^ 2 = r ^ 2 := by rw [ha]
  nlinarith [norm_nonneg (z - a)]

/-! ## Affine images of harmonic functions -/

private theorem surfaceHarmonicOn_affine {u : X → ℝ} {s : Set X}
    (hu : SurfaceHarmonicOn u s) (a b : ℝ) :
    SurfaceHarmonicOn (fun x ↦ a + b * u x) s := by
  intro e he z hz
  have hb : HarmonicAt (b • (u ∘ e.symm)) z := (hu e he z hz).const_smul
  have hsum : HarmonicAt ((fun _ ↦ a) + b • (u ∘ e.symm)) z := (harmonicAt_const a).add hb
  refine (harmonicAt_congr_nhds ?_).mpr hsum
  filter_upwards with w
  simp [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]

/-! ## The Dirichlet Perron family -/

/-- Perron family for boundary data `φ` on the open set `W`: subharmonic
functions on `W`, continuous and `[0,1]`-valued on `closure W`, dominated by
`φ` on the frontier. -/
def dirichletFamily (W : Set X) (φ : X → ℝ) : Set (X → ℝ) :=
  {g | SurfaceSubharmonicOn g W ∧ (∀ x ∈ closure W, g x ∈ Icc (0 : ℝ) 1)
      ∧ ContinuousOn g (closure W) ∧ ∀ ξ ∈ frontier W, g ξ ≤ φ ξ}

private theorem zero_mem_dirichletFamily {W : Set X} {φ : X → ℝ}
    (hφ : ∀ ξ ∈ frontier W, 0 ≤ φ ξ) : (fun _ ↦ (0 : ℝ)) ∈ dirichletFamily W φ :=
  ⟨⟨continuousOn_const, fun _ _ ↦ SubMeanOn.const⟩, fun _ _ ↦ ⟨le_rfl, zero_le_one⟩,
    continuousOn_const, fun ξ hξ ↦ hφ ξ hξ⟩

/-- The Dirichlet family is a Perron family. -/
theorem isPerronFamily_dirichletFamily [T2Space X] {W : Set X} (hWo : IsOpen W)
    {φ : X → ℝ} (hφ : ∀ ξ ∈ frontier W, 0 ≤ φ ξ) :
    IsPerronFamily (dirichletFamily W φ) W := by
  refine ⟨⟨_, zero_mem_dirichletFamily hφ⟩, ?_, ?_, ?_, ?_⟩
  · exact fun g hg ↦ hg.1
  · exact fun g hg x hx ↦ hg.2.1 x (subset_closure hx)
  · -- closed under pairwise max
    rintro g₁ ⟨h₁sub, h₁icc, h₁cont, h₁bd⟩ g₂ ⟨h₂sub, h₂icc, h₂cont, h₂bd⟩
    refine ⟨h₁sub.max h₂sub, ?_, ContinuousOn.sup h₁cont h₂cont, ?_⟩
    · intro x hx
      exact ⟨le_trans (h₁icc x hx).1 (le_max_left _ _),
        max_le (h₁icc x hx).2 (h₂icc x hx).2⟩
    · intro ξ hξ
      exact max_le (h₁bd ξ hξ) (h₂bd ξ hξ)
  · -- closed under harmonic replacement
    rintro g ⟨hgsub, hgicc, hgcont, hgbd⟩ e' c' r' hd
    have hDW : e'.symm '' closedBall c' r' ⊆ W := hd.preimage_subset
    have hDclosed : IsClosed (e'.symm '' closedBall c' r') := hd.compact_preimage.isClosed
    have hgsub' : SurfaceSubharmonicOn (surfaceReplace g e' c' r') W :=
      surfaceReplace_surfaceSubharmonicOn hWo hgsub hd
    have hicc' : ∀ x ∈ W, surfaceReplace g e' c' r' x ∈ Icc (0 : ℝ) 1 :=
      surfaceReplace_mem_Icc hgsub hd fun x hx ↦ hgicc x (subset_closure hx)
    refine ⟨hgsub', ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxD : x ∈ e'.symm '' closedBall c' r'
      · exact hicc' x (hDW hxD)
      · rw [surfaceReplace_eqOn_compl hxD]; exact hgicc x hx
    · intro x hx
      by_cases hxW : x ∈ W
      · exact (hgsub'.continuousOn.continuousAt (hWo.mem_nhds hxW)).continuousWithinAt
      · have hxD : x ∉ e'.symm '' closedBall c' r' := fun hcon ↦ hxW (hDW hcon)
        have hev : surfaceReplace g e' c' r' =ᶠ[𝓝 x] g := by
          filter_upwards [hDclosed.isOpen_compl.mem_nhds hxD] with y hy
          exact surfaceReplace_eqOn_compl hy
        exact (hgcont x hx).congr_of_eventuallyEq
          (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
    · intro ξ hξ
      have hξW : ξ ∉ W := by
        rw [frontier, hWo.interior_eq] at hξ; exact hξ.2
      have hξD : ξ ∉ e'.symm '' closedBall c' r' := fun hcon ↦ hξW (hDW hcon)
      rw [surfaceReplace_eqOn_compl hξD]
      exact hgbd ξ hξ

/-! ## Boundary attainment via the barrier (upper and lower estimates) -/

/-- Upper barrier estimate: near a regular frontier point the Perron envelope
does not exceed the boundary value. -/
private theorem dirichlet_upper [T2Space X] {W : Set X} (hWo : IsOpen W)
    (hWc : IsCompact (closure W)) {φ : X → ℝ} (hφc : ContinuousOn φ (frontier W))
    (hφ01 : ∀ ξ ∈ frontier W, φ ξ ∈ Icc (0 : ℝ) 1) {ξ : X} (hξ : ξ ∈ frontier W)
    (hExt : ExteriorDiskAt W ξ) :
    ∀ ε > 0, ∀ᶠ x in 𝓝[W] ξ, perronSup (dirichletFamily W φ) x ≤ φ ξ + ε := by
  intro ε hε
  obtain ⟨e, he, hξe, c, r, hr, hcballr, hdist, hext⟩ := hExt
  set a := e ξ with ha_def
  have ha : ‖a - c‖ = r := by rw [← dist_eq_norm]; exact hdist
  have hφξ0 : 0 ≤ φ ξ := (hφ01 ξ hξ).1
  -- enlarge the chart disk
  obtain ⟨η, hη, hthick⟩ :=
    (isCompact_closedBall c r).exists_thickening_subset_open e.open_target hcballr
  rw [thickening_closedBall hη hr.le] at hthick
  set R := r + η / 2 with hR_def
  have hRr : r < R := by rw [hR_def]; linarith
  have hRt : closedBall c R ⊆ e.target :=
    (closedBall_subset_ball (by rw [hR_def]; linarith)).trans hthick
  -- the internally tangent half disk
  set r' := r / 2 with hr'_def
  have hr'pos : 0 < r' := by positivity
  set c' := (a + c) / 2 with hc'_def
  have hac' : ‖a - c'‖ = r' := by
    have h : a - c' = (a - c) / 2 := by rw [hc'_def]; ring
    rw [h, norm_div, ha]; simp [hr'_def]
  have hcc' : ‖c' - c‖ = r' := by
    have h : c' - c = (a - c) / 2 := by rw [hc'_def]; ring
    rw [h, norm_div, ha]; simp [hr'_def]
  -- W-image stays outside `ball c r`
  have hcball_out : ∀ w ∈ closure (chartImage e W), r ≤ ‖w - c‖ := by
    have hsub : chartImage e W ⊆ {w : ℂ | r ≤ ‖w - c‖} := by
      rintro _ ⟨x, ⟨hxW, hxe⟩, rfl⟩
      have h := hext x ⟨hxW, hxe⟩
      rw [mem_ball, dist_eq_norm, not_lt] at h
      exact h
    have hclosed : IsClosed {w : ℂ | r ≤ ‖w - c‖} :=
      isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
    exact fun w hw ↦ closure_minimal hsub hclosed hw
  -- geometric gap and the resulting lower bound on `‖w - c'‖`
  have hgap : ∀ w : ℂ, r ≤ ‖w - c‖ → r' ^ 2 + (1 / 2) * ‖w - a‖ ^ 2 ≤ ‖w - c'‖ ^ 2 := by
    intro w hw
    have := tangent_gap hr.le ha hw
    rwa [← hr'_def, ← hc'_def] at this
  have hnorm_ge : ∀ w : ℂ, r ≤ ‖w - c‖ → r' ≤ ‖w - c'‖ := by
    intro w hw
    have h1 : r' ^ 2 ≤ ‖w - c'‖ ^ 2 := by nlinarith [norm_nonneg (w - a), hgap w hw]
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hr'pos.le, Real.sqrt_sq (norm_nonneg _)] at this
  have hpos_c' : ∀ w : ℂ, r ≤ ‖w - c‖ → 0 < ‖w - c'‖ :=
    fun w hw ↦ lt_of_lt_of_le hr'pos (hnorm_ge w hw)
  -- the barrier's harmonic core
  set δbar : ℂ → ℝ := (fun w ↦ Real.log ‖w - c'‖ - Real.log r') with hδbar_def
  have hδa : δbar a = 0 := by rw [hδbar_def]; simp [hac']
  have hδnn : ∀ w : ℂ, r ≤ ‖w - c‖ → 0 ≤ δbar w := by
    intro w hw
    rw [hδbar_def]
    have := Real.log_le_log hr'pos (hnorm_ge w hw)
    simpa using this
  -- constant for the artificial (sphere) part of the frontier
  set L₁ := Real.log (r' + η / 2) - Real.log r' with hL1_def
  have hL1pos : 0 < L₁ := by
    rw [hL1_def]
    have : Real.log r' < Real.log (r' + η / 2) := Real.log_lt_log hr'pos (by linarith)
    linarith
  -- continuity of `φ` gives a neighbourhood where `φ < φ ξ + ε/2`
  have hφcont : Tendsto φ (𝓝[frontier W] ξ) (𝓝 (φ ξ)) := hφc ξ hξ
  have hφev : {y | φ y < φ ξ + ε / 2} ∈ 𝓝[frontier W] ξ :=
    hφcont (Iio_mem_nhds (by linarith))
  obtain ⟨N, hNo, hξN, hNsub⟩ := mem_nhdsWithin.mp hφev
  -- pull back the neighbourhood through the chart to get a chart-metric radius `δ`
  have hae_target : a ∈ e.target := e.map_source hξe
  have hea_symm : e.symm a = ξ := by rw [ha_def]; exact e.left_inv hξe
  have hsc : ContinuousAt e.symm a :=
    e.continuousAt_symm hae_target
  have hN_nhds : ∀ᶠ w in 𝓝 a, e.symm w ∈ N :=
    hsc.preimage_mem_nhds (hea_symm ▸ hNo.mem_nhds hξN)
  obtain ⟨δ, hδpos, hδball⟩ := Metric.eventually_nhds_iff.mp hN_nhds
  -- constant for the interior (chart-boundary) part of the frontier
  set S := Real.sqrt (r' ^ 2 + (1 / 2) * δ ^ 2) with hS_def
  have hSpos : r' < S := by
    rw [hS_def]
    have h1 : r' ^ 2 < r' ^ 2 + (1 / 2) * δ ^ 2 := by nlinarith [hδpos]
    calc r' = Real.sqrt (r' ^ 2) := (Real.sqrt_sq hr'pos.le).symm
      _ < Real.sqrt (r' ^ 2 + (1 / 2) * δ ^ 2) := Real.sqrt_lt_sqrt (by positivity) h1
  set L₂ := Real.log S - Real.log r' with hL2_def
  have hL2pos : 0 < L₂ := by
    rw [hL2_def]
    have : Real.log r' < Real.log S := Real.log_lt_log hr'pos hSpos
    linarith
  -- the multiplier making the barrier dominate on both parts
  set C := 1 / L₁ + 1 / L₂ with hC_def
  have hCnn : 0 ≤ C := by positivity
  have hCL1 : (1 : ℝ) ≤ C * L₁ := by
    have h : C * L₁ = 1 + L₁ / L₂ := by rw [hC_def]; field_simp
    rw [h]; linarith [div_nonneg hL1pos.le hL2pos.le]
  have hCL2 : (1 : ℝ) ≤ C * L₂ := by
    have h : C * L₂ = L₂ / L₁ + 1 := by rw [hC_def]; field_simp
    rw [h]; linarith [div_nonneg hL2pos.le hL1pos.le]
  -- the scaled global barrier `Cbar w = C * δbar w`
  set Cbar : ℂ → ℝ := fun w ↦ C * δbar w with hCbar_def
  have hCbar_a : Cbar a = 0 := by simp only [hCbar_def, hδa, mul_zero]
  -- the truncated open annular domain in the chart
  set Ũ : Set ℂ := ball c R ∩ chartImage e W with hŨ_def
  have hŨopen : IsOpen Ũ := isOpen_ball.inter (isOpen_chartImage e hWo)
  have hŨbd : Bornology.IsBounded Ũ := (isBounded_ball).subset inter_subset_left
  have hŨchart : Ũ ⊆ chartImage e W := inter_subset_right
  have hRpos : 0 < R := by linarith
  have hclŨ_ball : closure Ũ ⊆ closedBall c R :=
    (closure_mono inter_subset_left).trans (closure_ball c hRpos.ne').subset
  have hclŨ_chart : closure Ũ ⊆ closure (chartImage e W) := closure_mono inter_subset_right
  have hclŨ_target : closure Ũ ⊆ e.target := hclŨ_ball.trans hRt
  have hclŨ_out : ∀ w ∈ closure Ũ, r ≤ ‖w - c‖ := fun w hw ↦ hcball_out w (hclŨ_chart hw)
  have hclŨ_le : ∀ w ∈ closure Ũ, ‖w - c‖ ≤ R := by
    intro w hw; rw [← dist_eq_norm]; exact mem_closedBall.mp (hclŨ_ball hw)
  -- `e.symm` sends the closure of `Ũ` into `closure W`
  have hmapcl : ∀ w ∈ closure Ũ, e.symm w ∈ closure W := by
    intro w hw
    have hwt : w ∈ e.target := hclŨ_target hw
    have hsc' : ContinuousWithinAt e.symm (chartImage e W) w :=
      (e.continuousAt_symm hwt).continuousWithinAt
    have h1 : e.symm w ∈ closure (e.symm '' chartImage e W) :=
      hsc'.mem_closure_image (hclŨ_chart hw)
    exact closure_mono (mapsTo_symm_chartImage.image_subset) h1
  -- the barrier is harmonic on `Ũ`, hence mean-preserving
  have hδmean : MeanEqOn Cbar Ũ := by
    have h1 : HarmonicOnNhd (fun w ↦ Real.log ‖w - c'‖) Ũ := by
      intro w hw
      have hp := hpos_c' w (hcball_out w (subset_closure (hŨchart hw)))
      have hne : (fun z : ℂ ↦ z - c') w ≠ 0 := by
        show w - c' ≠ 0; exact norm_pos_iff.mp hp
      exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ z - c') w).harmonicAt_log_norm hne
    have h2 : HarmonicOnNhd δbar Ũ := h1.sub (fun w _ ↦ harmonicAt_const _)
    have h3 : HarmonicOnNhd Cbar Ũ := by
      intro w hw
      have hb := (h2 w hw).const_smul (c := C)
      refine (harmonicAt_congr_nhds ?_).mpr hb
      filter_upwards with z
      simp [hCbar_def, smul_eq_mul]
    exact HarmonicOnNhd.meanEqOn h3
  -- barrier continuity on `closure Ũ`
  have hCbarcont : ContinuousOn Cbar (closure Ũ) := by
    have hlogcont : ContinuousOn (fun w ↦ Real.log ‖w - c'‖) (closure Ũ) :=
      ((continuous_id.sub continuous_const).norm.continuousOn).log
        (fun w hw ↦ (hpos_c' w (hclŨ_out w hw)).ne')
    have : ContinuousOn δbar (closure Ũ) := hlogcont.sub continuousOn_const
    exact this.const_smul C
  -- the per-member comparison on `closure Ũ`
  have hcomp : ∀ g ∈ dirichletFamily W φ, ∀ w ∈ closure Ũ,
      (g ∘ e.symm) w ≤ φ ξ + ε / 2 + Cbar w := by
    rintro g ⟨hgsub, hgicc, hgcont, hgbd⟩ w hw
    -- the subharmonic difference on `Ũ`
    have hsm : SubMeanOn ((g ∘ e.symm) + (-Cbar)) Ũ :=
      ((hgsub.subMeanOn e he).mono hŨchart).add_meanEq hδmean.neg
    have hcont2 : ContinuousOn ((g ∘ e.symm) + (-Cbar)) (closure Ũ) := by
      refine ContinuousOn.add ?_ hCbarcont.neg
      exact hgcont.comp (e.symm.continuousOn.mono (by simpa using hclŨ_target)) hmapcl
    have hfrle : ∀ w ∈ frontier Ũ, ((g ∘ e.symm) + (-Cbar)) w ≤ φ ξ + ε / 2 := by
      intro w hwf
      have hwcl : w ∈ closure Ũ := frontier_subset_closure hwf
      have hwr : r ≤ ‖w - c‖ := hclŨ_out w hwcl
      have hwR : ‖w - c‖ ≤ R := hclŨ_le w hwcl
      have hwt : w ∈ e.target := hclŨ_target hwcl
      have hCbarnn : 0 ≤ Cbar w :=
        mul_nonneg hCnn (hδnn w hwr)
      simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply]
      by_cases hcase : ‖w - c‖ = R
      · -- artificial sphere: `g ≤ 1`, barrier `≥ 1`
        have hg1 : g (e.symm w) ≤ 1 := (hgicc (e.symm w) (hmapcl w hwcl)).2
        have hnc' : r' + η / 2 ≤ ‖w - c'‖ := by
          have h := norm_sub_norm_le (w - c) (c' - c)
          rw [show (w - c) - (c' - c) = w - c' by ring, hcc'] at h
          rw [hcase] at h; rw [hR_def] at h; linarith [h]
        have hbar1 : (1 : ℝ) ≤ Cbar w := by
          have hle : L₁ ≤ δbar w := by
            rw [hδbar_def, hL1_def]
            have := Real.log_le_log (by linarith) hnc'
            linarith
          have : C * L₁ ≤ Cbar w := by
            rw [hCbar_def]; exact mul_le_mul_of_nonneg_left hle hCnn
          linarith [hCL1]
        linarith [hφξ0, hε]
      · -- chart-boundary point: `e.symm w ∈ frontier W`, `g ≤ φ`
        have hwlt : ‖w - c‖ < R := lt_of_le_of_ne hwR hcase
        have hwball : w ∈ ball c R := by rw [mem_ball, dist_eq_norm]; exact hwlt
        have hnotU : w ∉ Ũ := by
          have := hwf.2; rwa [hŨopen.interior_eq] at this
        have hnotchart : w ∉ chartImage e W := fun hc ↦ hnotU ⟨hwball, hc⟩
        have hsymmW : e.symm w ∈ closure W := hmapcl w hwcl
        have hsymmnotW : e.symm w ∉ W := fun hc ↦
          hnotchart ⟨e.symm w, ⟨hc, e.map_target hwt⟩, e.right_inv hwt⟩
        have hsymmFr : e.symm w ∈ frontier W := by
          rw [frontier, hWo.interior_eq]; exact ⟨hsymmW, hsymmnotW⟩
        have hg_le : g (e.symm w) ≤ φ (e.symm w) := hgbd (e.symm w) hsymmFr
        by_cases hnear : ‖w - a‖ < δ
        · have hdw : dist w a < δ := by rw [dist_eq_norm]; exact hnear
          have hwN : e.symm w ∈ N := hδball hdw
          have hφlt : φ (e.symm w) < φ ξ + ε / 2 := hNsub ⟨hwN, hsymmFr⟩
          linarith
        · push_neg at hnear
          have hφ1 : φ (e.symm w) ≤ 1 := (hφ01 (e.symm w) hsymmFr).2
          have hbar1 : (1 : ℝ) ≤ Cbar w := by
            have hSle : S ≤ ‖w - c'‖ := by
              have h1 : S ^ 2 ≤ ‖w - c'‖ ^ 2 := by
                rw [hS_def, Real.sq_sqrt (by positivity)]
                nlinarith [hgap w hwr,
                  mul_nonneg (sub_nonneg.mpr hnear)
                    (by linarith [norm_nonneg (w - a), hδpos] : (0 : ℝ) ≤ ‖w - a‖ + δ)]
              have := Real.sqrt_le_sqrt h1
              rwa [Real.sqrt_sq (by linarith [hSpos, hr'pos] : (0 : ℝ) ≤ S),
                Real.sqrt_sq (norm_nonneg _)] at this
            have hle : L₂ ≤ δbar w := by
              rw [hδbar_def, hL2_def]
              have := Real.log_le_log (by linarith [hSpos, hr'pos]) hSle
              linarith
            have : C * L₂ ≤ Cbar w := by
              rw [hCbar_def]; exact mul_le_mul_of_nonneg_left hle hCnn
            linarith [hCL2]
          linarith [hφξ0, hε]
    have := hsm.le_of_frontier_le hŨopen hŨbd hcont2 hfrle w hw
    simpa [Pi.add_apply, Pi.neg_apply] using this
  -- pointwise bound for the Perron envelope at chart points near `ξ`
  have hne𝓕 : (dirichletFamily W φ).Nonempty :=
    ⟨_, zero_mem_dirichletFamily (fun ζ hζ ↦ (hφ01 ζ hζ).1)⟩
  have hpt : ∀ x, x ∈ W → x ∈ e.source → e x ∈ ball c R →
      perronSup (dirichletFamily W φ) x ≤ φ ξ + ε / 2 + Cbar (e x) := by
    intro x hxW hxe hxb
    have hwcl : e x ∈ closure Ũ := subset_closure ⟨hxb, mem_chartImage_of_mem hxW hxe⟩
    refine csSup_le (hne𝓕.image _) ?_
    rintro _ ⟨g, hg, rfl⟩
    have h := hcomp g hg (e x) hwcl
    rwa [Function.comp_apply, e.left_inv hxe] at h
  -- barrier vanishes at `ξ`, so eventually its contribution is `< ε/2`
  have hCbar_tend : Tendsto (fun x ↦ Cbar (e x)) (𝓝 ξ) (𝓝 (Cbar a)) := by
    have hce : ContinuousAt (fun x ↦ e x) ξ := e.continuousAt hξe
    have hbar_at : ContinuousAt Cbar a := by
      have hlog : ContinuousAt (fun w ↦ Real.log ‖w - c'‖) a :=
        (((continuous_id.sub continuous_const).norm).continuousAt).log
          (by simp only [id_eq]; rw [hac']; exact hr'pos.ne')
      have hδcont : ContinuousAt δbar a := hlog.sub continuousAt_const
      have hb := hδcont.const_smul (c := C)
      exact hb.congr (by filter_upwards with z; simp [hCbar_def, smul_eq_mul])
    exact hbar_at.comp hce
  rw [hCbar_a] at hCbar_tend
  have hev3 : ∀ᶠ x in 𝓝 ξ, Cbar (e x) < ε / 2 :=
    hCbar_tend.eventually (Iio_mem_nhds (by linarith))
  have ha_ball : a ∈ ball c R := by rw [mem_ball, dist_eq_norm, ha]; exact hRr
  have hev2 : ∀ᶠ x in 𝓝 ξ, e x ∈ ball c R :=
    (e.continuousAt hξe).preimage_mem_nhds (isOpen_ball.mem_nhds ha_ball)
  have hev1 : ∀ᶠ x in 𝓝 ξ, x ∈ e.source := e.open_source.mem_nhds hξe
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev1,
    nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3] with x hxW hxe hxb hxbar
  have := hpt x hxW hxe hxb
  linarith

set_option maxHeartbeats 1000000 in
/-- Lower barrier estimate: near a regular frontier point the Perron envelope
is at least the boundary value. -/
private theorem dirichlet_lower [T2Space X] {W : Set X} (hWo : IsOpen W)
    (hWc : IsCompact (closure W)) {φ : X → ℝ} (hφc : ContinuousOn φ (frontier W))
    (hφ01 : ∀ ξ ∈ frontier W, φ ξ ∈ Icc (0 : ℝ) 1) {ξ : X} (hξ : ξ ∈ frontier W)
    (hExt : ExteriorDiskAt W ξ) :
    ∀ ε > 0, ∀ᶠ x in 𝓝[W] ξ, φ ξ - ε ≤ perronSup (dirichletFamily W φ) x := by
  classical
  intro ε hε
  obtain ⟨e, he, hξe, c, r, hr, hcballr, hdist, hext⟩ := hExt
  set a := e ξ with ha_def
  have ha : ‖a - c‖ = r := by rw [← dist_eq_norm]; exact hdist
  have hφξ0 : 0 ≤ φ ξ := (hφ01 ξ hξ).1
  have hφξ1 : φ ξ ≤ 1 := (hφ01 ξ hξ).2
  obtain ⟨η, hη, hthick⟩ :=
    (isCompact_closedBall c r).exists_thickening_subset_open e.open_target hcballr
  rw [thickening_closedBall hη hr.le] at hthick
  set R := r + η / 2 with hR_def
  have hRr : r < R := by rw [hR_def]; linarith
  have hRpos : 0 < R := by linarith
  have hRt : closedBall c R ⊆ e.target :=
    (closedBall_subset_ball (by rw [hR_def]; linarith)).trans hthick
  set r' := r / 2 with hr'_def
  have hr'pos : 0 < r' := by positivity
  set c' := (a + c) / 2 with hc'_def
  have hac' : ‖a - c'‖ = r' := by
    have h : a - c' = (a - c) / 2 := by rw [hc'_def]; ring
    rw [h, norm_div, ha]; simp [hr'_def]
  have hcc' : ‖c' - c‖ = r' := by
    have h : c' - c = (a - c) / 2 := by rw [hc'_def]; ring
    rw [h, norm_div, ha]; simp [hr'_def]
  -- `W ∩ e.source` and its image stay outside `ball c r`
  have hKr : ∀ y, y ∈ e.source → y ∈ W → r ≤ ‖e y - c‖ := by
    intro y hye hyW
    have h := hext y ⟨hyW, hye⟩
    rw [mem_ball, dist_eq_norm, not_lt] at h; exact h
  have hgap : ∀ w : ℂ, r ≤ ‖w - c‖ → r' ^ 2 + (1 / 2) * ‖w - a‖ ^ 2 ≤ ‖w - c'‖ ^ 2 := by
    intro w hw
    have := tangent_gap hr.le ha hw
    rwa [← hr'_def, ← hc'_def] at this
  have hnorm_ge : ∀ w : ℂ, r ≤ ‖w - c‖ → r' ≤ ‖w - c'‖ := by
    intro w hw
    have h1 : r' ^ 2 ≤ ‖w - c'‖ ^ 2 := by nlinarith [norm_nonneg (w - a), hgap w hw]
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hr'pos.le, Real.sqrt_sq (norm_nonneg _)] at this
  have hpos_c' : ∀ w : ℂ, r ≤ ‖w - c‖ → 0 < ‖w - c'‖ :=
    fun w hw ↦ lt_of_lt_of_le hr'pos (hnorm_ge w hw)
  -- `e.symm`-image of the closure of `W` in the source keeps distance `≥ r`
  have hnorm_cl : ∀ x ∈ closure W, x ∈ e.source → r ≤ ‖e x - c‖ := by
    intro x hx hxe
    have hcl : x ∈ closure (e.source ∩ W) := e.open_source.inter_closure ⟨hxe, hx⟩
    haveI : (𝓝[e.source ∩ W] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hcont : ContinuousWithinAt (fun y ↦ ‖e y - c‖) (e.source ∩ W) x :=
      (((e.continuousAt hxe).sub continuousAt_const).norm).continuousWithinAt
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hKr y hy.1 hy.2
  set δbar : ℂ → ℝ := (fun w ↦ Real.log ‖w - c'‖ - Real.log r') with hδbar_def
  have hδa : δbar a = 0 := by rw [hδbar_def]; simp [hac']
  have hδnn : ∀ w : ℂ, r ≤ ‖w - c‖ → 0 ≤ δbar w := by
    intro w hw
    rw [hδbar_def]
    have := Real.log_le_log hr'pos (hnorm_ge w hw)
    simpa using this
  -- constants
  set L₁ := Real.log (r' + η / 2) - Real.log r' with hL1_def
  have hL1pos : 0 < L₁ := by
    rw [hL1_def]
    have : Real.log r' < Real.log (r' + η / 2) := Real.log_lt_log hr'pos (by linarith)
    linarith
  -- lower neighbourhood from continuity of `φ`
  have hφcont : Tendsto φ (𝓝[frontier W] ξ) (𝓝 (φ ξ)) := hφc ξ hξ
  have hφev : {y | φ ξ - ε / 2 < φ y} ∈ 𝓝[frontier W] ξ :=
    hφcont (Ioi_mem_nhds (by linarith))
  obtain ⟨N, hNo, hξN, hNsub⟩ := mem_nhdsWithin.mp hφev
  have hae_target : a ∈ e.target := e.map_source hξe
  have hea_symm : e.symm a = ξ := by rw [ha_def]; exact e.left_inv hξe
  have hsc : ContinuousAt e.symm a := e.continuousAt_symm hae_target
  have hN_nhds : ∀ᶠ w in 𝓝 a, e.symm w ∈ N :=
    hsc.preimage_mem_nhds (hea_symm ▸ hNo.mem_nhds hξN)
  obtain ⟨δ, hδpos, hδball⟩ := Metric.eventually_nhds_iff.mp hN_nhds
  set S := Real.sqrt (r' ^ 2 + (1 / 2) * δ ^ 2) with hS_def
  have hSpos : r' < S := by
    rw [hS_def]
    have h1 : r' ^ 2 < r' ^ 2 + (1 / 2) * δ ^ 2 := by nlinarith [hδpos]
    calc r' = Real.sqrt (r' ^ 2) := (Real.sqrt_sq hr'pos.le).symm
      _ < Real.sqrt (r' ^ 2 + (1 / 2) * δ ^ 2) := Real.sqrt_lt_sqrt (by positivity) h1
  set L₂ := Real.log S - Real.log r' with hL2_def
  have hL2pos : 0 < L₂ := by
    rw [hL2_def]
    have : Real.log r' < Real.log S := Real.log_lt_log hr'pos hSpos
    linarith
  set C' := 1 / L₁ + 1 / L₂ + 1 with hC'_def
  have hC'pos : 0 < C' := by positivity
  have hC'L1 : φ ξ - ε / 2 ≤ C' * L₁ := by
    have h : C' * L₁ = 1 / L₁ * L₁ + 1 / L₂ * L₁ + L₁ := by rw [hC'_def]; ring
    rw [h, one_div_mul_cancel hL1pos.ne']
    have h2 : 0 ≤ 1 / L₂ * L₁ := mul_nonneg (by positivity) hL1pos.le
    linarith [hφξ1, hε, hL1pos]
  have hC'L2 : φ ξ - ε / 2 ≤ C' * L₂ := by
    have h : C' * L₂ = 1 / L₁ * L₂ + 1 / L₂ * L₂ + L₂ := by rw [hC'_def]; ring
    rw [h, one_div_mul_cancel hL2pos.ne']
    have h2 : 0 ≤ 1 / L₁ * L₂ := mul_nonneg (by positivity) hL2pos.le
    linarith [hφξ1, hε, hL2pos]
  -- the barrier subfunction and the `[0,1]`-cap radius
  set Hfun : ℂ → ℝ := fun w ↦ (φ ξ - ε / 2) - C' * (Real.log ‖w - c'‖ - Real.log r') with hHfun_def
  set ρ₁ := r' * Real.exp ((φ ξ - ε / 2) / C') with hρ₁_def
  have hρ₁pos : 0 < ρ₁ := by positivity
  have hlogρ₁ : Real.log (ρ₁ / r') = (φ ξ - ε / 2) / C' := by
    have h : ρ₁ / r' = Real.exp ((φ ξ - ε / 2) / C') := by rw [hρ₁_def]; field_simp
    rw [h, Real.log_exp]
  have hρ₁_le : ρ₁ ≤ r' + η / 2 := by
    have hexpL1 : Real.exp L₁ = (r' + η / 2) / r' := by
      rw [hL1_def, Real.exp_sub, Real.exp_log (by linarith), Real.exp_log hr'pos]
    have h1 : (φ ξ - ε / 2) / C' ≤ L₁ := by
      rw [div_le_iff₀ hC'pos]; linarith [hC'L1]
    have h2 : Real.exp ((φ ξ - ε / 2) / C') ≤ Real.exp L₁ := Real.exp_le_exp.mpr h1
    rw [hρ₁_def]
    calc r' * Real.exp ((φ ξ - ε / 2) / C') ≤ r' * Real.exp L₁ :=
          mul_le_mul_of_nonneg_left h2 hr'pos.le
      _ = r' + η / 2 := by rw [hexpL1]; field_simp
  have hK₀t : closedBall c' ρ₁ ⊆ e.target := by
    refine subset_trans ?_ hRt
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_closedBall]
    calc dist z c ≤ dist z c' + dist c' c := dist_triangle z c' c
      _ ≤ ρ₁ + r' := add_le_add hz (by rw [dist_eq_norm]; exact le_of_eq hcc')
      _ ≤ R := by rw [hR_def]; linarith [hρ₁_le]
  have hK₀_sub_source : e.symm '' closedBall c' ρ₁ ⊆ e.source := by
    rintro _ ⟨w, hw, rfl⟩; exact e.map_target (hK₀t hw)
  have hK₀closed : IsClosed (e.symm '' closedBall c' ρ₁) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using hK₀t))).isClosed
  -- the member function
  set gstar : X → ℝ := fun x ↦ if x ∈ e.source then max 0 (Hfun (e x)) else 0 with hgstar_def
  have hg0 : ∀ x, x ∉ e.source → gstar x = 0 := fun x hx ↦ if_neg hx
  have hgin : ∀ x, x ∈ e.source → gstar x = max 0 (Hfun (e x)) := fun x hx ↦ if_pos hx
  have hgnn : ∀ x, 0 ≤ gstar x := by
    intro x; by_cases hx : x ∈ e.source
    · rw [hgin x hx]; exact le_max_left _ _
    · rw [hg0 x hx]
  have hHeq : ∀ w : ℂ, Hfun w = (φ ξ - ε / 2) - C' * δbar w := fun w ↦ by
    simp only [hHfun_def, hδbar_def]
  have hHle : ∀ x ∈ closure W, x ∈ e.source → Hfun (e x) ≤ φ ξ - ε / 2 := by
    intro x hx hxe
    have hδb : 0 ≤ δbar (e x) := hδnn (e x) (hnorm_cl x hx hxe)
    rw [hHeq]; nlinarith [mul_nonneg hC'pos.le hδb]
  have hgle1 : ∀ x ∈ closure W, gstar x ≤ 1 := by
    intro x hx
    by_cases hxe : x ∈ e.source
    · rw [hgin x hxe]
      exact max_le zero_le_one (le_trans (hHle x hx hxe) (by linarith))
    · rw [hg0 x hxe]; exact zero_le_one
  -- barrier is `≤ 0`, hence `gstar = 0`, off the compact cap
  have hg_zero_off : ∀ y, y ∉ e.symm '' closedBall c' ρ₁ → gstar y = 0 := by
    intro y hy
    by_cases hye : y ∈ e.source
    · rw [hgin y hye]
      have hnotball : ρ₁ < ‖e y - c'‖ := by
        have h : e y ∉ closedBall c' ρ₁ := fun hc ↦ hy ⟨e y, hc, e.left_inv hye⟩
        rwa [mem_closedBall, dist_eq_norm, not_le] at h
      have hloglt : Real.log ρ₁ < Real.log ‖e y - c'‖ := Real.log_lt_log hρ₁pos hnotball
      have hlρ : Real.log ρ₁ - Real.log r' = (φ ξ - ε / 2) / C' := by
        rw [← Real.log_div hρ₁pos.ne' hr'pos.ne', hlogρ₁]
      have hδgt : (φ ξ - ε / 2) / C' < δbar (e y) := by
        rw [hδbar_def]; simp only; linarith [hloglt, hlρ]
      have hmul : φ ξ - ε / 2 < C' * δbar (e y) := by
        rw [mul_comm]; exact (div_lt_iff₀ hC'pos).mp hδgt
      have hHneg : Hfun (e y) ≤ 0 := by rw [hHeq]; linarith [hmul]
      exact max_eq_left hHneg
    · rw [hg0 y hye]
  -- continuity on the closure
  have hgcont : ContinuousOn gstar (closure W) := by
    intro x hx
    by_cases hxe : x ∈ e.source
    · have h1 : r ≤ ‖e x - c‖ := hnorm_cl x hx hxe
      have hne : ‖e x - c'‖ ≠ 0 := (hpos_c' _ h1).ne'
      have hcont1 : ContinuousAt (fun y ↦ max 0 (Hfun (e y))) x := by
        refine Filter.Tendsto.max continuousAt_const ?_
        have hlog : ContinuousAt (fun y ↦ Real.log ‖e y - c'‖) x :=
          (((e.continuousAt hxe).sub continuousAt_const).norm).log hne
        have : ContinuousAt
            (fun y ↦ (φ ξ - ε / 2) - C' * (Real.log ‖e y - c'‖ - Real.log r')) x :=
          continuousAt_const.sub (continuousAt_const.mul (hlog.sub continuousAt_const))
        exact this
      refine (hcont1.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hxe] with y hy
      exact (hgin y hy).symm
    · have hxK : x ∉ e.symm '' closedBall c' ρ₁ := fun hc ↦ hxe (hK₀_sub_source hc)
      have hev : gstar =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [hK₀closed.isOpen_compl.mem_nhds hxK] with y hy
        exact hg_zero_off y hy
      exact continuousWithinAt_const.congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
  -- subharmonicity on `W`
  have hgsub : SurfaceSubharmonicOn gstar W := by
    refine SurfaceSubharmonicOn.of_locally ?_
    intro x hxW
    by_cases hxe : x ∈ e.source
    · refine ⟨e.source ∩ W, e.open_source.inter hWo, ⟨hxe, hxW⟩, inter_subset_right, ?_⟩
      have hharm : SurfaceHarmonicOn (fun y ↦ Hfun (e y)) (e.source ∩ W) := by
        refine SurfaceHarmonicOn.of_chartwise ?_
        rintro y ⟨hys, hyW⟩
        refine ⟨e, he, hys, ?_⟩
        have hy_ne : e y - c' ≠ 0 :=
          norm_pos_iff.mp (hpos_c' (e y) (hKr y hys hyW))
        have hexp : HarmonicAt (fun w : ℂ ↦ Hfun w) (e y) := by
          have h1 : AnalyticAt ℂ (fun w : ℂ ↦ w - c') (e y) := by fun_prop
          have hlog := h1.harmonicAt_log_norm hy_ne
          have hbase : HarmonicAt
              ((fun _ : ℂ ↦ ((φ ξ - ε / 2) + C' * Real.log r'))
                - C' • fun w : ℂ ↦ Real.log ‖w - c'‖) (e y) :=
            (harmonicAt_const _).sub hlog.const_smul
          refine (harmonicAt_congr_nhds ?_).mpr hbase
          filter_upwards with w
          simp only [hHfun_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        refine (harmonicAt_congr_nhds ?_).mpr hexp
        filter_upwards [e.open_target.mem_nhds (e.map_source hys)] with w hw
        simp only [Function.comp_apply]
        rw [e.right_inv hw]
      have hmax := SurfaceSubharmonicOn.max
        (⟨continuousOn_const, fun e' _ ↦ SubMeanOn.const⟩ :
          SurfaceSubharmonicOn (fun _ ↦ (0 : ℝ)) (e.source ∩ W))
        hharm.surfaceSubharmonicOn
      refine surfaceSubharmonicOn_congr hmax ?_
      intro y hy
      exact hgin y hy.1
    · have hxK : x ∉ e.symm '' closedBall c' ρ₁ := fun hc ↦ hxe (hK₀_sub_source hc)
      refine ⟨(e.symm '' closedBall c' ρ₁)ᶜ ∩ W, hK₀closed.isOpen_compl.inter hWo,
        ⟨hxK, hxW⟩, inter_subset_right, ?_⟩
      refine surfaceSubharmonicOn_congr
        (⟨continuousOn_const, fun e' _ ↦ SubMeanOn.const⟩ :
          SurfaceSubharmonicOn (fun _ ↦ (0 : ℝ)) _) ?_
      intro y hy
      exact hg_zero_off y hy.1
  -- frontier domination
  have hgbd : ∀ ζ ∈ frontier W, gstar ζ ≤ φ ζ := by
    intro ζ hζ
    have hζcl : ζ ∈ closure W := frontier_subset_closure hζ
    have hφζ0 : 0 ≤ φ ζ := (hφ01 ζ hζ).1
    by_cases hζe : ζ ∈ e.source
    · rw [hgin ζ hζe]
      refine max_le hφζ0 ?_
      have hr_fr : r ≤ ‖e ζ - c‖ := hnorm_cl ζ hζcl hζe
      by_cases hnear : ‖e ζ - a‖ < δ
      · have hdw : dist (e ζ) a < δ := by rw [dist_eq_norm]; exact hnear
        have hζN : e.symm (e ζ) ∈ N := hδball hdw
        rw [e.left_inv hζe] at hζN
        have : φ ξ - ε / 2 < φ ζ := hNsub ⟨hζN, hζ⟩
        exact le_trans (hHle ζ hζcl hζe) (by linarith)
      · push_neg at hnear
        have hSle : S ≤ ‖e ζ - c'‖ := by
          have h1 : S ^ 2 ≤ ‖e ζ - c'‖ ^ 2 := by
            rw [hS_def, Real.sq_sqrt (by positivity)]
            nlinarith [hgap (e ζ) hr_fr,
              mul_nonneg (sub_nonneg.mpr hnear)
                (by linarith [norm_nonneg (e ζ - a), hδpos] : (0 : ℝ) ≤ ‖e ζ - a‖ + δ)]
          have := Real.sqrt_le_sqrt h1
          rwa [Real.sqrt_sq (by linarith [hSpos, hr'pos] : (0 : ℝ) ≤ S),
            Real.sqrt_sq (norm_nonneg _)] at this
        have hδbarL2 : L₂ ≤ δbar (e ζ) := by
          rw [hδbar_def]; simp only; rw [hL2_def]
          have := Real.log_le_log (by linarith [hSpos, hr'pos]) hSle
          linarith
        have hHneg : Hfun (e ζ) ≤ 0 := by
          rw [hHeq]
          nlinarith [hC'L2, mul_le_mul_of_nonneg_left hδbarL2 hC'pos.le]
        exact le_trans hHneg hφζ0
    · rw [hg0 ζ hζe]; exact hφζ0
  -- `gstar` belongs to the family; conclude via `le_perronSup`
  have hmem : gstar ∈ dirichletFamily W φ :=
    ⟨hgsub, fun x hx ↦ ⟨hgnn x, hgle1 x hx⟩, hgcont, hgbd⟩
  have hle : ∀ x ∈ W, gstar x ≤ perronSup (dirichletFamily W φ) x :=
    (isPerronFamily_dirichletFamily hWo (fun ζ hζ ↦ (hφ01 ζ hζ).1)).le_perronSup hmem
  -- the barrier vanishes at `ξ`, so `gstar ≥ φ ξ - ε` near `ξ`
  have hδcont_a : ContinuousAt δbar a := by
    have hlog : ContinuousAt (fun w ↦ Real.log ‖w - c'‖) a :=
      (((continuous_id.sub continuous_const).norm).continuousAt).log
        (by simp only [id_eq]; rw [hac']; exact hr'pos.ne')
    exact hlog.sub continuousAt_const
  have htend : Tendsto (fun x ↦ C' * δbar (e x)) (𝓝 ξ) (𝓝 (C' * δbar a)) :=
    continuousAt_const.mul (hδcont_a.comp (e.continuousAt hξe))
  rw [hδa, mul_zero] at htend
  have hev3 : ∀ᶠ x in 𝓝 ξ, C' * δbar (e x) < ε / 2 :=
    htend.eventually (Iio_mem_nhds (by linarith))
  have hev1 : ∀ᶠ x in 𝓝 ξ, x ∈ e.source := e.open_source.mem_nhds hξe
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev1,
    nhdsWithin_le_nhds hev3] with x hxW hxe hxbar
  have h1 : Hfun (e x) ≤ gstar x := by rw [hgin x hxe]; exact le_max_right _ _
  have h2 : φ ξ - ε ≤ Hfun (e x) := by rw [hHeq]; linarith [hxbar]
  exact le_trans h2 (le_trans h1 (hle x hxW))

private theorem dirichlet_tendsto [T2Space X] {W : Set X} (hWo : IsOpen W)
    (hWc : IsCompact (closure W)) {φ : X → ℝ} (hφc : ContinuousOn φ (frontier W))
    (hφ01 : ∀ ξ ∈ frontier W, φ ξ ∈ Icc (0 : ℝ) 1) {ξ : X} (hξ : ξ ∈ frontier W)
    (hExt : ExteriorDiskAt W ξ) :
    Tendsto (perronSup (dirichletFamily W φ)) (𝓝[W] ξ) (𝓝 (φ ξ)) := by
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  have hup := dirichlet_upper hWo hWc hφc hφ01 hξ hExt (ε' / 2) (by linarith)
  have hlo := dirichlet_lower hWo hWc hφc hφ01 hξ hExt (ε' / 2) (by linarith)
  filter_upwards [hup, hlo] with x hxu hxl
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## Main theorem -/

/-- **Perron solution of the Dirichlet problem** on a relatively compact open
set with exterior-disk-regular frontier. -/
theorem exists_dirichlet_solution [T2Space X]
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact (closure W))
    (hfr : (frontier W).Nonempty)
    (hreg : ∀ ξ ∈ frontier W, ExteriorDiskAt W ξ)
    {f : X → ℝ} (hfc : ContinuousOn f (frontier W)) :
    ∃ u : X → ℝ, SurfaceHarmonicOn u W ∧ ContinuousOn u (closure W) ∧
      EqOn u f (frontier W) ∧
      ∀ x ∈ closure W, u x ∈ Icc (sInf (f '' frontier W)) (sSup (f '' frontier W)) := by
  classical
  have hFrc : IsCompact (frontier W) :=
    hWc.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨xm, hxm, hminm⟩ := hFrc.exists_isMinOn hfr hfc
  obtain ⟨xM, hxM, hmaxM⟩ := hFrc.exists_isMaxOn hfr hfc
  set m := f xm with hm
  set M := f xM with hMdef
  have hmin : ∀ y ∈ frontier W, m ≤ f y := fun y hy ↦ isMinOn_iff.1 hminm y hy
  have hmax : ∀ y ∈ frontier W, f y ≤ M := fun y hy ↦ isMaxOn_iff.1 hmaxM y hy
  have hmM : m ≤ M := hmin xM hxM
  have hInf : sInf (f '' frontier W) = m :=
    IsLeast.csInf_eq ⟨⟨xm, hxm, rfl⟩, fun v ⟨y, hy, hv⟩ ↦ hv ▸ hmin y hy⟩
  have hSup : sSup (f '' frontier W) = M :=
    IsGreatest.csSup_eq ⟨⟨xM, hxM, rfl⟩, fun v ⟨y, hy, hv⟩ ↦ hv ▸ hmax y hy⟩
  have hξnotW : ∀ ξ ∈ frontier W, ξ ∉ W := by
    intro ξ hξ; rw [frontier, hWo.interior_eq] at hξ; exact hξ.2
  rcases eq_or_lt_of_le hmM with heq | hlt
  · -- degenerate case: boundary data is constant
    refine ⟨fun _ ↦ m, fun e he z hz ↦ harmonicAt_const m, continuousOn_const, ?_, ?_⟩
    · intro ξ hξ
      exact le_antisymm (hmin ξ hξ) (le_trans (hmax ξ hξ) heq.symm.le)
    · intro x hx
      rw [hInf, hSup]
      exact ⟨le_rfl, heq.le⟩
  · -- main case
    set φ : X → ℝ := fun x ↦ (f x - m) / (M - m) with hφdef
    have hMm : 0 < M - m := by linarith
    have hφ01 : ∀ ξ ∈ frontier W, φ ξ ∈ Icc (0 : ℝ) 1 := by
      intro ξ hξ
      refine ⟨div_nonneg (by linarith [hmin ξ hξ]) hMm.le, ?_⟩
      rw [div_le_one hMm]; linarith [hmax ξ hξ]
    have hφc : ContinuousOn φ (frontier W) :=
      (hfc.sub continuousOn_const).div_const _
    have hφnn : ∀ ξ ∈ frontier W, 0 ≤ φ ξ := fun ξ hξ ↦ (hφ01 ξ hξ).1
    set 𝓕 := dirichletFamily W φ with h𝓕
    have hPF : IsPerronFamily 𝓕 W := isPerronFamily_dirichletFamily hWo hφnn
    set u₀ := perronSup 𝓕 with hu₀
    have hu₀harm : SurfaceHarmonicOn u₀ W := hPF.surfaceHarmonicOn_perronSup hWo
    have h0mem : (fun _ ↦ (0 : ℝ)) ∈ 𝓕 := zero_mem_dirichletFamily hφnn
    have hu₀nn : ∀ x ∈ W, 0 ≤ u₀ x := fun x hx ↦ hPF.le_perronSup h0mem x hx
    have hu₀le1 : ∀ x ∈ W, u₀ x ≤ 1 := fun x hx ↦
      hPF.perronSup_le (fun g hg ↦ (hPF.bounds g hg x hx).2)
    -- the rescaled solution
    set u : X → ℝ := fun x ↦ if x ∈ W then m + (M - m) * u₀ x else f x with hudef
    have huW : ∀ x ∈ W, u x = m + (M - m) * u₀ x := fun x hx ↦ if_pos hx
    have huFr : ∀ x ∈ frontier W, u x = f x := fun x hx ↦ if_neg (hξnotW x hx)
    have hφeq : ∀ ξ ∈ frontier W, m + (M - m) * φ ξ = f ξ := by
      intro ξ hξ
      rw [hφdef]
      field_simp
      ring
    refine ⟨u, ?_, ?_, ?_, ?_⟩
    · -- harmonic on W
      have haff : SurfaceHarmonicOn (fun x ↦ m + (M - m) * u₀ x) W :=
        surfaceHarmonicOn_affine hu₀harm m (M - m)
      intro e he z hz
      refine (harmonicAt_congr_nhds ?_).mpr (haff e he z hz)
      filter_upwards [(isOpen_chartImage e hWo).mem_nhds hz] with w hw
      obtain ⟨x, ⟨hxW, hxe⟩, rfl⟩ := hw
      simp only [Function.comp_apply, e.left_inv hxe]
      exact huW x hxW
    · -- continuous on closure W
      intro x hx
      by_cases hxW : x ∈ W
      · have hu₀at : ContinuousAt u₀ x :=
          hu₀harm.continuousOn.continuousAt (hWo.mem_nhds hxW)
        have haffat : ContinuousAt (fun y ↦ m + (M - m) * u₀ y) x :=
          continuousAt_const.add (continuousAt_const.mul hu₀at)
        have huat : ContinuousAt u x := by
          refine haffat.congr ?_
          filter_upwards [hWo.mem_nhds hxW] with y hy using (huW y hy).symm
        exact huat.continuousWithinAt
      · -- frontier point: barrier gives the limit
        have hxFr : x ∈ frontier W := by
          rw [frontier, hWo.interior_eq]; exact ⟨hx, hxW⟩
        have hclW : closure W = W ∪ frontier W := by
          rw [frontier, hWo.interior_eq]
          exact (union_sdiff_cancel subset_closure).symm
        rw [ContinuousWithinAt, huFr x hxFr, hclW, nhdsWithin_union]
        rw [tendsto_sup]
        constructor
        · -- W-side: barrier tendsto plus rescaling
          have htend : Tendsto u₀ (𝓝[W] x) (𝓝 (φ x)) :=
            dirichlet_tendsto hWo hWc hφc hφ01 hxFr (hreg x hxFr)
          have h2 : Tendsto (fun y ↦ m + (M - m) * u₀ y) (𝓝[W] x) (𝓝 (f x)) := by
            have := (tendsto_const_nhds (x := m)).add
              ((tendsto_const_nhds (x := M - m)).mul htend)
            rwa [hφeq x hxFr] at this
          refine h2.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with y hy using (huW y hy).symm
        · -- frontier-side: `u = f`
          have hf : Tendsto f (𝓝[frontier W] x) (𝓝 (f x)) := hfc x hxFr
          refine hf.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with y hy using (huFr y hy).symm
    · -- boundary values
      intro ξ hξ; rw [huFr ξ hξ]
    · -- range
      intro x hx
      rw [hInf, hSup]
      by_cases hxW : x ∈ W
      · rw [huW x hxW]
        refine ⟨by nlinarith [hu₀nn x hxW], by nlinarith [hu₀le1 x hxW]⟩
      · have hxFr : x ∈ frontier W := by rw [frontier, hWo.interior_eq]; exact ⟨hx, hxW⟩
        rw [huFr x hxFr]
        exact ⟨hmin x hxFr, hmax x hxFr⟩

end Uniformization
