import Rado.Complex.Dirichlet
import Rado.Complex.PlanarConnected
import Rado.Surface.Charts
import Rado.Topology.PoincareVolterra

/-!
# Surface-level theory: harmonic functions, Perron's method, conjugate germs

Steps 3–6 of `Rado/PLAN.md`, on the Riemann surface `X` itself. Kept in a
single file during development (to be split later): sub/harmonicity of
functions `X → ℝ` via chart representatives, Perron families and their
suprema, the explicit log-barriers for the two-disk configuration, and the
étale space of harmonic-conjugate germs with its evaluation map.

Conventions. For a chart `e` and a set `s ⊆ X`, the chart representative of
`g : X → ℝ` lives on `chartImage e s := e '' (s ∩ e.source) ⊆ ℂ`. All
definitions quantify over the maximal atlas (`Rado.riemannAtlas`), so no
`subharmonic ∘ holomorphic` invariance is ever needed; harmonic-side
invariance is `HarmonicOnNhd.comp_analytic`.
-/

open Set Topology Metric MeasureTheory InnerProductSpace Complex Filter

set_option linter.unusedSectionVars false

set_option autoImplicit false

namespace Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The image of `s` in the chart `e`. -/
def chartImage (e : OpenPartialHomeomorph X ℂ) (s : Set X) : Set ℂ :=
  e '' (s ∩ e.source)

theorem isOpen_chartImage (e : OpenPartialHomeomorph X ℂ) {s : Set X} (hs : IsOpen s) :
    IsOpen (chartImage e s) :=
  e.isOpen_image_of_subset_source (hs.inter e.open_source) inter_subset_right

theorem chartImage_subset_target (e : OpenPartialHomeomorph X ℂ) (s : Set X) :
    chartImage e s ⊆ e.target := fun _ ⟨_, hx, hex⟩ => hex ▸ e.map_source hx.2

theorem mem_chartImage_of_mem {e : OpenPartialHomeomorph X ℂ} {s : Set X} {x : X}
    (hx : x ∈ s) (hxe : x ∈ e.source) : e x ∈ chartImage e s :=
  ⟨x, ⟨hx, hxe⟩, rfl⟩

theorem mapsTo_symm_chartImage {e : OpenPartialHomeomorph X ℂ} {s : Set X} :
    MapsTo e.symm (chartImage e s) s := by
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  rw [e.left_inv hxe]
  exact hxs

/-- A continuous function on `s` reads as continuous through any chart. -/
theorem continuousOn_comp_chart_symm {g : X → ℝ} (e : OpenPartialHomeomorph X ℂ) {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (g ∘ e.symm) (chartImage e s) :=
  hg.comp (e.symm.continuousOn.mono (chartImage_subset_target e s)) mapsTo_symm_chartImage

/-! ## Harmonic and subharmonic functions on a Riemann surface -/

/-- `u : X → ℝ` is harmonic on `s`: every chart representative is harmonic. -/
def SurfaceHarmonicOn (u : X → ℝ) (s : Set X) : Prop :=
  ∀ e ∈ riemannAtlas X, HarmonicOnNhd (u ∘ e.symm) (chartImage e s)

/-- `g : X → ℝ` is subharmonic on `s`: continuous, and every chart
representative satisfies the sub-mean-value inequality. -/
structure SurfaceSubharmonicOn (g : X → ℝ) (s : Set X) : Prop where
  continuousOn : ContinuousOn g s
  subMeanOn : ∀ e ∈ riemannAtlas X, SubMeanOn (g ∘ e.symm) (chartImage e s)

namespace SurfaceHarmonicOn

variable {u v : X → ℝ} {s : Set X}

theorem continuousOn (hu : SurfaceHarmonicOn u s) (_hs : IsOpen s) : ContinuousOn u s := by
  intro x hx
  have h1 : ContinuousAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (hu _ (chartAt_mem_riemannAtlas x) _
      (mem_chartImage_of_mem hx (mem_chart_source ℂ x))).1.continuousAt
  have h2 : ContinuousAt ((u ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) x :=
    h1.comp ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))
  refine (h2.congr ?_).continuousWithinAt
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with z hz
  simp [(chartAt ℂ x).left_inv hz]

theorem mono (hu : SurfaceHarmonicOn u s) {t : Set X} (hts : t ⊆ s) :
    SurfaceHarmonicOn u t := fun e he z hz =>
  hu e he z (image_mono (inter_subset_inter_left _ hts) hz)

/-- To be harmonic it suffices to be harmonic in one maximal-atlas chart around
each point (chart invariance, via `HarmonicOnNhd.comp_analytic`). -/
theorem of_chartwise (_hs : IsOpen s)
    (h : ∀ x ∈ s, ∃ e ∈ riemannAtlas X, x ∈ e.source ∧ HarmonicAt (u ∘ e.symm) (e x)) :
    SurfaceHarmonicOn u s := by
  rintro e' he' z ⟨x, ⟨hxs, hxe'⟩, rfl⟩
  obtain ⟨e, he, hxe, hharm⟩ := h x hxs
  -- a ball around `e x` on which `u ∘ e.symm` is harmonic
  obtain ⟨ρ, hρpos, hball⟩ := Metric.eventually_nhds_iff_ball.mp hharm.eventually
  -- the transition `φ = e ∘ e'.symm` is analytic near `e' x`
  have htrans : AnalyticAt ℂ (e ∘ e'.symm) (e' x) := transition_analyticAt he' he ⟨hxe', hxe⟩
  -- the open set where the congruence `u ∘ e'.symm = (u ∘ e.symm) ∘ (e ∘ e'.symm)` holds
  have hWopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source) :=
    e'.symm.continuousOn.isOpen_inter_preimage e'.open_target e.open_source
  have hxW : e' x ∈ e'.target ∩ e'.symm ⁻¹' e.source :=
    ⟨e'.map_source hxe', by rw [mem_preimage, e'.left_inv hxe']; exact hxe⟩
  -- a small ball around `e' x` inside all the relevant sets
  have hnhds : (e'.target ∩ e'.symm ⁻¹' e.source) ∩
      ((e ∘ e'.symm) ⁻¹' ball (e x) ρ ∩ {w | AnalyticAt ℂ (e ∘ e'.symm) w}) ∈ 𝓝 (e' x) := by
    refine Filter.inter_mem (hWopen.mem_nhds hxW) (Filter.inter_mem ?_ ?_)
    · refine ContinuousAt.preimage_mem_nhds htrans.continuousAt ?_
      have hφx : (e ∘ e'.symm) (e' x) = e x := by simp [Function.comp, e'.left_inv hxe']
      rw [hφx]
      exact ball_mem_nhds _ hρpos
    · exact htrans.eventually_analyticAt
  obtain ⟨δ, hδpos, hδball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnhds
  -- harmonicity of the composition on that ball
  have hcomp : HarmonicOnNhd ((u ∘ e.symm) ∘ (e ∘ e'.symm)) (ball (e' x) δ) := by
    refine HarmonicOnNhd.comp_analytic (fun y hy => hball y hy) isOpen_ball
      isOpen_ball (fun w hw => (hδball hw).2.2) fun w hw => (hδball hw).2.1
  -- transfer along the congruence
  have hcongr : u ∘ e'.symm =ᶠ[𝓝 (e' x)] (u ∘ e.symm) ∘ (e ∘ e'.symm) := by
    filter_upwards [hWopen.mem_nhds hxW] with w hw
    simp [Function.comp, e.left_inv hw.2]
  exact (harmonicAt_congr_nhds hcongr).mpr (hcomp _ (mem_ball_self hδpos))

theorem surfaceSubharmonicOn (hu : SurfaceHarmonicOn u s) (hs : IsOpen s) :
    SurfaceSubharmonicOn u s where
  continuousOn := hu.continuousOn hs
  subMeanOn e he :=
    (HarmonicOnNhd.meanEqOn (isOpen_chartImage e hs) (hu e he)).subMeanOn

theorem neg (hu : SurfaceHarmonicOn u s) : SurfaceHarmonicOn (-u) s :=
  fun e he z hz => (hu e he z hz).neg

end SurfaceHarmonicOn

namespace SurfaceSubharmonicOn

variable {g g₁ g₂ : X → ℝ} {s : Set X}

theorem mono (hg : SurfaceSubharmonicOn g s) {t : Set X} (hts : t ⊆ s) :
    SurfaceSubharmonicOn g t where
  continuousOn := hg.continuousOn.mono hts
  subMeanOn e he := (hg.subMeanOn e he).mono (image_mono (inter_subset_inter_left _ hts))

theorem max (h₁ : SurfaceSubharmonicOn g₁ s) (h₂ : SurfaceSubharmonicOn g₂ s) :
    SurfaceSubharmonicOn (fun x => Max.max (g₁ x) (g₂ x)) s where
  continuousOn := ContinuousOn.sup h₁.continuousOn h₂.continuousOn
  subMeanOn e he := (h₁.subMeanOn e he).max (h₂.subMeanOn e he)

end SurfaceSubharmonicOn

/-! ## Local-to-global bridge for the sub-mean-value property

`SubMeanOn` (in `Rado/Complex/SubMean.lean`) demands the sub-mean inequality on
*every* circle whose closed disk lies in the domain. Verifications (gluing in
the harmonic replacement) naturally produce only *small* circles. The bridge is
classical: small circles give the maximum principle, the maximum principle
gives comparison with the Poisson extension on any closed disk, and comparison
gives the inequality on the full circle
(`HarmonicContOnCl.circleAverage_eq` closes the loop at the boundary radius).
-/

/-- Continuity plus the sub-mean-value inequality on all sufficiently small
circles around each point. -/
structure SubMeanLocalOn (g : ℂ → ℝ) (s : Set ℂ) : Prop where
  continuousOn : ContinuousOn g s
  submean_small : ∀ z ∈ s, ∀ᶠ r in 𝓝[>] (0 : ℝ), g z ≤ Real.circleAverage g z r

theorem SubMeanLocalOn.mono {g : ℂ → ℝ} {s t : Set ℂ} (hg : SubMeanLocalOn g s) (hts : t ⊆ s) :
    SubMeanLocalOn g t :=
  ⟨hg.continuousOn.mono hts, fun z hz => hg.submean_small z (hts hz)⟩

/-- If a continuous function is at most `M` on a sphere of positive radius while its
circle average is at least `M`, then it equals `M` everywhere on the sphere. -/
private lemma eqOn_sphere_of_le_of_circleAverage_ge {g : ℂ → ℝ} {a : ℂ} {r M : ℝ}
    (hr : 0 < r) (hc : ContinuousOn g (sphere a r)) (hle : ∀ z ∈ sphere a r, g z ≤ M)
    (havg : M ≤ Real.circleAverage g a r) : ∀ z ∈ sphere a r, g z = M := by
  intro z hz
  by_contra hne
  have hzlt : g z < M := lt_of_le_of_ne (hle z hz) hne
  -- find a parameter `θ₀ ∈ Icc 0 (2π)` hitting `z`
  have hz' : z ∈ Set.range (circleMap a r) := by
    rw [range_circleMap, abs_of_pos hr]; exact hz
  obtain ⟨θ, hθ⟩ := hz'
  have hmem : toIocMod Real.two_pi_pos 0 θ ∈ Set.Ioc 0 (2 * Real.pi) := by
    simpa using toIocMod_mem_Ioc Real.two_pi_pos 0 θ
  have hθ₀ : circleMap a r (toIocMod Real.two_pi_pos 0 θ) = z := by
    rw [← self_sub_toIocDiv_zsmul Real.two_pi_pos 0 θ, (periodic_circleMap a r).sub_zsmul_eq]
    exact hθ
  -- strict inequality of interval integrals
  have hcont : Continuous fun θ => g (circleMap a r θ) :=
    hc.comp_continuous (continuous_circleMap a r) fun θ => circleMap_mem_sphere a hr.le θ
  have hint : (∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap a r θ))
      < ∫ _ in (0:ℝ)..2 * Real.pi, M := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      Real.two_pi_pos hcont.continuousOn continuousOn_const
      (fun x _ => hle _ (circleMap_mem_sphere a hr.le x)) ?_
    exact ⟨toIocMod Real.two_pi_pos 0 θ, Set.Ioc_subset_Icc_self hmem, by rw [hθ₀]; exact hzlt⟩
  have hlt : Real.circleAverage g a r < M := by
    rw [Real.circleAverage_def, smul_eq_mul]
    calc (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap a r θ)
        < (2 * Real.pi)⁻¹ * ∫ _ in (0:ℝ)..2 * Real.pi, M := by
          exact mul_lt_mul_of_pos_left hint (by positivity)
      _ = M := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc,
            inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]
  exact absurd havg (not_le.mpr hlt)

/-- Small circles suffice for the strong maximum principle. -/
theorem SubMeanLocalOn.eqOn_const_of_isMaxOn {g : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hsc : IsPreconnected s) (hg : SubMeanLocalOn g s) {x₀ : ℂ} (hx₀ : x₀ ∈ s)
    (hmax : IsMaxOn g s x₀) : EqOn g (fun _ => g x₀) s := by
  set M := g x₀ with hM
  set A : Set ℂ := {x ∈ s | g x = M} with hA
  set B : Set ℂ := {x ∈ s | g x ≠ M} with hB
  -- `A` is open: around each of its points, `g = M` on all small spheres
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro a ⟨has, hga⟩
    obtain ⟨ε, hε, hballs⟩ := Metric.isOpen_iff.mp hs a has
    obtain ⟨ρ, hρ, hsmall⟩ : ∃ ρ > (0:ℝ), ∀ r ∈ Ioo (0:ℝ) ρ, g a ≤ Real.circleAverage g a r := by
      obtain ⟨u, hu, huss⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hg.submean_small a has)
      exact ⟨u, hu, fun r hr => huss hr⟩
    refine ⟨min ε ρ, lt_min hε hρ, fun y hy => ?_⟩
    have hylt : dist y a < min ε ρ := mem_ball.mp hy
    rcases eq_or_ne y a with rfl | hne
    · exact ⟨has, hga⟩
    · have hrpos : 0 < dist y a := dist_pos.mpr hne
      have hcb : closedBall a (dist y a) ⊆ s :=
        (closedBall_subset_ball (hylt.trans_le (min_le_left _ _))).trans hballs
      have hsph : sphere a (dist y a) ⊆ s := sphere_subset_closedBall.trans hcb
      have h1 : ∀ z ∈ sphere a (dist y a), g z ≤ M := fun z hz => hmax (hsph hz)
      have h2 : M ≤ Real.circleAverage g a (dist y a) := by
        rw [← hga]
        exact hsmall _ ⟨hrpos, hylt.trans_le (min_le_right _ _)⟩
      have heq := eqOn_sphere_of_le_of_circleAverage_ge hrpos
        (hg.continuousOn.mono hsph) h1 h2
      exact ⟨hballs (mem_ball.mpr (hylt.trans_le (min_le_left _ _))),
        heq y (mem_sphere.mpr rfl)⟩
  -- `B` is open by continuity
  have hBopen : IsOpen B := by
    have hBeq : B = s ∩ g ⁻¹' {M}ᶜ := by
      ext x
      simp [hB]
    rw [hBeq]
    exact hg.continuousOn.isOpen_inter_preimage hs isOpen_compl_singleton
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hxM⟩ ⟨_, hxM'⟩
    exact hxM' hxM
  have hcover : s ⊆ A ∪ B := fun x hx => by
    by_cases h : g x = M
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  rcases hsc.subset_or_subset hAopen hBopen hdisj hcover with hsA | hsB
  · intro x hx
    exact (hsA hx).2
  · exact absurd hM.symm (hsB hx₀).2

/-- Small circles suffice for the boundary comparison principle. -/
theorem SubMeanLocalOn.le_of_frontier_le {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hg : SubMeanLocalOn g U)
    (hgc : ContinuousOn g (closure U)) {M : ℝ} (hbd : ∀ x ∈ frontier U, g x ≤ M) :
    ∀ x ∈ closure U, g x ≤ M := by
  intro x hx
  have hKc : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨z, hzK, hzmax⟩ := hKc.exists_isMaxOn ⟨x, hx⟩ hgc
  suffices h : g z ≤ M from le_trans (hzmax hx) h
  by_cases hzU : z ∈ U
  · -- interior maximum: `g` is constant on the connected component of `z` in `U`
    have hCopen : IsOpen (connectedComponentIn U z) := hU.connectedComponentIn
    have hCU : connectedComponentIn U z ⊆ U := connectedComponentIn_subset U z
    have hzC : z ∈ connectedComponentIn U z := mem_connectedComponentIn hzU
    have hmaxC : IsMaxOn g (connectedComponentIn U z) z := fun y hy =>
      hzmax (subset_closure (hCU hy))
    have heq : EqOn g (fun _ => g z) (connectedComponentIn U z) :=
      (hg.mono hCU).eqOn_const_of_isMaxOn hCopen isPreconnected_connectedComponentIn hzC hmaxC
    -- the component has nonempty frontier since it is bounded and nonempty
    have hfr : (frontier (connectedComponentIn U z)).Nonempty := by
      rw [nonempty_frontier_iff]
      refine ⟨⟨z, hzC⟩, fun huniv => ?_⟩
      have hCb : Bornology.IsBounded (connectedComponentIn U z) := hUb.subset hCU
      rw [huniv] at hCb
      exact NormedSpace.unbounded_univ ℝ ℂ hCb
    obtain ⟨b, hb⟩ := hfr
    have hbC : b ∈ closure (connectedComponentIn U z) := frontier_subset_closure hb
    have hbU : b ∈ closure U := closure_mono hCU hbC
    -- `g b = g z` by continuity up to the closure
    have hgb : g b = g z := by
      have h1 : ContinuousWithinAt g (connectedComponentIn U z) b :=
        (hgc.continuousWithinAt hbU).mono (hCU.trans subset_closure)
      haveI hne : (𝓝[connectedComponentIn U z] b).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp hbC
      have h2 : Filter.Tendsto g (𝓝[connectedComponentIn U z] b) (𝓝 (g z)) :=
        Filter.Tendsto.congr'
          (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun y hy => (heq hy).symm)
          tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    -- `b` lies on the frontier of `U`
    have hbfr : b ∈ frontier U := by
      rw [hU.frontier_eq]
      refine ⟨hbU, fun hbU' => ?_⟩
      have hCb' : connectedComponentIn U b ∈ 𝓝 b :=
        (hU.connectedComponentIn).mem_nhds (mem_connectedComponentIn hbU')
      obtain ⟨y, hyt, hyC⟩ := mem_closure_iff_nhds.mp hbC _ hCb'
      have hcomp : connectedComponentIn U b = connectedComponentIn U z := by
        rw [connectedComponentIn_eq hyt, connectedComponentIn_eq hyC]
      have hbmem : b ∈ connectedComponentIn U z := hcomp ▸ mem_connectedComponentIn hbU'
      have hbnot : b ∉ connectedComponentIn U z := by
        rw [hCopen.frontier_eq] at hb
        exact hb.2
      exact hbnot hbmem
    calc g z = g b := hgb.symm
      _ ≤ M := hbd b hbfr
  · exact hbd z (by rw [hU.frontier_eq]; exact ⟨hzK, hzU⟩)

/-- The bridge: on an open set, the sub-mean-value inequality on small circles
implies it on all circles (compare with the Poisson extension on any legal
closed disk). -/
theorem SubMeanLocalOn.subMeanOn {g : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hg : SubMeanLocalOn g s) : SubMeanOn g s := by
  refine ⟨hg.continuousOn, fun c R hR hsub => ?_⟩
  have hgs : ContinuousOn g (sphere c R) :=
    hg.continuousOn.mono (sphere_subset_closedBall.trans hsub)
  have hPc : ContinuousOn (poissonExtension g c R) (closedBall c R) :=
    poissonExtension_continuousOn hR hgs
  have hPh : HarmonicOnNhd (poissonExtension g c R) (ball c R) :=
    poissonExtension_harmonicOnNhd hR hgs
  have hPm : MeanEqOn (poissonExtension g c R) (ball c R) :=
    HarmonicOnNhd.meanEqOn isOpen_ball hPh
  -- `g - P` satisfies the small-circle sub-mean inequality on the open ball
  have hloc : SubMeanLocalOn (fun z => g z - poissonExtension g c R z) (ball c R) := by
    constructor
    · exact (hg.continuousOn.mono (ball_subset_closedBall.trans hsub)).sub
        (hPc.mono ball_subset_closedBall)
    · intro z hz
      have hzs : z ∈ s := hsub (ball_subset_closedBall hz)
      have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall z r ⊆ ball c R := by
        have hpos : 0 < R - dist z c := by
          rw [mem_ball] at hz; linarith
        filter_upwards [Ioo_mem_nhdsGT hpos] with r hr
        exact closedBall_subset_ball' (by have := hr.2; linarith)
      filter_upwards [hg.submean_small z hzs, h2, self_mem_nhdsWithin] with r hr1 hr2 hr3
      have hrpos : (0:ℝ) < r := hr3
      have hsph_s : sphere z r ⊆ s :=
        sphere_subset_closedBall.trans (hr2.trans (ball_subset_closedBall.trans hsub))
      have hsph_cb : sphere z r ⊆ closedBall c R :=
        sphere_subset_closedBall.trans (hr2.trans ball_subset_closedBall)
      have hig : CircleIntegrable g z r :=
        (hg.continuousOn.mono hsph_s).circleIntegrable hrpos.le
      have hiP : CircleIntegrable (poissonExtension g c R) z r :=
        (hPc.mono hsph_cb).circleIntegrable hrpos.le
      have havg : Real.circleAverage (fun w => g w - poissonExtension g c R w) z r
          = Real.circleAverage g z r - Real.circleAverage (poissonExtension g c R) z r :=
        Real.circleAverage_fun_sub hig hiP
      show g z - poissonExtension g c R z
          ≤ Real.circleAverage (fun w => g w - poissonExtension g c R w) z r
      rw [havg, hPm.mean_eq z r hrpos hr2]
      exact sub_le_sub_right hr1 _
  -- comparison on the closed ball
  have hcl : closure (ball c R) = closedBall c R := closure_ball c hR.ne'
  have hfr : ∀ x ∈ frontier (ball c R), g x - poissonExtension g c R x ≤ 0 := by
    intro x hx
    rw [frontier_ball c hR.ne'] at hx
    rw [poissonExtension_eqOn_sphere hR hgs hx]
    simp
  have hcomp := hloc.le_of_frontier_le isOpen_ball isBounded_ball
    (by rw [hcl]; exact (hg.continuousOn.mono hsub).sub hPc) hfr
  have h0 := hcomp c (by rw [hcl]; exact mem_closedBall_self hR.le)
  simp only [sub_nonpos] at h0
  -- mean value at the boundary radius
  have hPcirc : Real.circleAverage (poissonExtension g c R) c R = poissonExtension g c R c := by
    apply HarmonicContOnCl.circleAverage_eq
    rw [abs_of_pos hR]
    exact HarmonicContOnCl.mk_ball hPh hPc
  have hcongr : Real.circleAverage (poissonExtension g c R) c R = Real.circleAverage g c R := by
    apply Real.circleAverage_congr_sphere
    rw [abs_of_pos hR]
    exact poissonExtension_eqOn_sphere hR hgs
  calc g c ≤ poissonExtension g c R c := h0
    _ = Real.circleAverage (poissonExtension g c R) c R := hPcirc.symm
    _ = Real.circleAverage g c R := hcongr

/-- Subharmonicity is local. -/
theorem SurfaceSubharmonicOn.of_locally {g : X → ℝ} {s : Set X} (hs : IsOpen s)
    (h : ∀ x ∈ s, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ s ∧ SurfaceSubharmonicOn g V) :
    SurfaceSubharmonicOn g s := by
  have hcont : ContinuousOn g s := by
    intro x hx
    obtain ⟨V, hVo, hxV, hVs, hgV⟩ := h x hx
    exact (hgV.continuousOn.continuousAt (hVo.mem_nhds hxV)).continuousWithinAt
  refine ⟨hcont, fun e he => ?_⟩
  refine SubMeanLocalOn.subMeanOn (isOpen_chartImage e hs) ?_
  refine ⟨continuousOn_comp_chart_symm e hcont, ?_⟩
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  obtain ⟨V, hVo, hxV, hVs, hgV⟩ := h x hxs
  have hsm : SubMeanOn (g ∘ e.symm) (chartImage e V) := hgV.subMeanOn e he
  have hmem : e x ∈ chartImage e V := mem_chartImage_of_mem hxV hxe
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (isOpen_chartImage e hVo) _ hmem
  filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
  exact hsm.submean (e x) r hr.1 ((closedBall_subset_ball hr.2).trans hball)

/-! ## Harmonic replacement and Perron families -/

open Classical in
/-- Replace `g` inside the closed disk `e.symm '' closedBall c r` by the
Dirichlet solution with `g`'s boundary values, read through the chart. -/
noncomputable def surfaceReplace (g : X → ℝ) (e : OpenPartialHomeomorph X ℂ)
    (c : ℂ) (r : ℝ) : X → ℝ := fun x =>
  if _h : x ∈ e.source ∧ e x ∈ closedBall c r then
    poissonExtension (g ∘ e.symm) c r (e x)
  else g x

section Replace

variable {g : X → ℝ} {s : Set X} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {r : ℝ}

/-- Data for a legal replacement disk: a maximal-atlas chart and a closed disk
in its target whose preimage lies in `s`. -/
structure IsReplaceDisk (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ) (s : Set X) :
    Prop where
  mem_atlas : e ∈ riemannAtlas X
  r_pos : 0 < r
  closedBall_subset : closedBall c r ⊆ e.target
  preimage_subset : e.symm '' closedBall c r ⊆ s

theorem IsReplaceDisk.compact_preimage (hd : IsReplaceDisk e c r s) :
    IsCompact (e.symm '' closedBall c r) :=
  (isCompact_closedBall c r).image_of_continuousOn
    (e.symm.continuousOn.mono (by simpa using hd.closedBall_subset))

/-- The replacement agrees with `g` off the closed replacement disk. -/
theorem surfaceReplace_eqOn_compl (_hd : IsReplaceDisk e c r s) :
    EqOn (surfaceReplace g e c r) g (e.symm '' closedBall c r)ᶜ := by
  intro x hx
  rw [surfaceReplace, dif_neg]
  rintro ⟨hxs, hxb⟩
  exact hx ⟨e x, hxb, e.left_inv hxs⟩

private theorem IsReplaceDisk.closedBall_subset_chartImage (hd : IsReplaceDisk e c r s) :
    closedBall c r ⊆ chartImage e s := fun w hw =>
  ⟨e.symm w, ⟨hd.preimage_subset ⟨w, hw, rfl⟩, e.map_target (hd.closedBall_subset hw)⟩,
    e.right_inv (hd.closedBall_subset hw)⟩

private theorem IsReplaceDisk.isOpen_ball_image (hd : IsReplaceDisk e c r s) :
    IsOpen (e.symm '' ball c r) :=
  e.symm.isOpen_image_of_subset_source isOpen_ball
    (by simpa using ball_subset_closedBall.trans hd.closedBall_subset)

private theorem IsReplaceDisk.continuousOn_sphere (hd : IsReplaceDisk e c r s)
    (hg : SurfaceSubharmonicOn g s) : ContinuousOn (g ∘ e.symm) (sphere c r) :=
  (continuousOn_comp_chart_symm e hg.continuousOn).mono
    (sphere_subset_closedBall.trans hd.closedBall_subset_chartImage)

/-- `g` is dominated by its replacement (comparison principle); helper form. -/
private theorem le_surfaceReplace_aux (hs : IsOpen s) (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) : ∀ x ∈ s, g x ≤ surfaceReplace g e c r x := by
  intro x hx
  by_cases hxD : x ∈ e.symm '' closedBall c r
  · obtain ⟨w, hwb, rfl⟩ := hxD
    have hwt : w ∈ e.target := hd.closedBall_subset hwb
    have hxsrc : e.symm w ∈ e.source := e.map_target hwt
    have hew : e (e.symm w) = w := e.right_inv hwt
    have hle := (hg.subMeanOn e hd.mem_atlas).le_poissonExtension_on
      (isOpen_chartImage e hs) hd.r_pos hd.closedBall_subset_chartImage w hwb
    rw [surfaceReplace, dif_pos ⟨hxsrc, by rw [hew]; exact hwb⟩, hew]
    exact hle
  · exact (surfaceReplace_eqOn_compl hd hxD).ge

/-- The replacement is harmonic inside the disk; helper form. -/
private theorem surfaceReplace_surfaceHarmonicOn_aux (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) :
    SurfaceHarmonicOn (surfaceReplace g e c r) (e.symm '' ball c r) := by
  have hbt : ball c r ⊆ e.target := ball_subset_closedBall.trans hd.closedBall_subset
  have hgs : ContinuousOn (g ∘ e.symm) (sphere c r) := hd.continuousOn_sphere hg
  refine SurfaceHarmonicOn.of_chartwise hd.isOpen_ball_image ?_
  rintro x ⟨w, hwb, rfl⟩
  have hwt : w ∈ e.target := hbt hwb
  have hxsrc : e.symm w ∈ e.source := e.map_target hwt
  have hew : e (e.symm w) = w := e.right_inv hwt
  refine ⟨e, hd.mem_atlas, hxsrc, ?_⟩
  rw [hew]
  have hharm := poissonExtension_harmonicOnNhd hd.r_pos hgs w hwb
  refine (harmonicAt_congr_nhds ?_).mpr hharm
  filter_upwards [isOpen_ball.mem_nhds hwb] with w' hw'
  have hwt' : w' ∈ e.target := hbt hw'
  simp only [Function.comp_apply]
  rw [surfaceReplace, dif_pos ⟨e.map_target hwt',
    by rw [e.right_inv hwt']; exact ball_subset_closedBall hw'⟩, e.right_inv hwt']

/-- The replacement is subharmonic (Anghel–Stan Remark 4): with `[T2Space X]`
the compact replacement disk is closed, and the replacement is subharmonic on
`s` — harmonic inside the disk, equal to `g` outside, and the sub-mean
inequality glues across the circle because `g ≤ surfaceReplace g` there.

The Hausdorff hypothesis is genuinely needed: on the plane with doubled
origin, with `g = ‖chart value‖²`, the replacement on the copy-1 unit disk is
`≡ 1` on the shared punctured disk but `0` at the doubled origin, which lies
in the closure of the replacement disk but outside `e.source` — so the
replacement fails to be continuous, let alone subharmonic. -/
theorem surfaceReplace_surfaceSubharmonicOn [T2Space X] (hs : IsOpen s)
    (hg : SurfaceSubharmonicOn g s) (hd : IsReplaceDisk e c r s) :
    SurfaceSubharmonicOn (surfaceReplace g e c r) s := by
  classical
  have hgs : ContinuousOn (g ∘ e.symm) (sphere c r) := hd.continuousOn_sphere hg
  have hrepg : ContinuousOn (g ∘ e.symm) (chartImage e s) :=
    continuousOn_comp_chart_symm e hg.continuousOn
  -- the chart-side glued function is continuous on `chartImage e s`
  have hh : ContinuousOn (fun w => if w ∈ closedBall c r
      then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) (chartImage e s) := by
    refine ContinuousOn.if ?_ ?_ ?_
    · intro a ha
      have h2 := ha.2
      simp only [Set.setOf_mem_eq] at h2
      rw [frontier_closedBall c hd.r_pos.ne'] at h2
      exact poissonExtension_eqOn_sphere hd.r_pos hgs h2
    · refine (poissonExtension_continuousOn hd.r_pos hgs).mono ?_
      refine inter_subset_right.trans ?_
      simp only [Set.setOf_mem_eq]
      rw [isClosed_closedBall.closure_eq]
    · exact hrepg.mono inter_subset_left
  -- continuity of the replacement on `s`
  have hcont : ContinuousOn (surfaceReplace g e c r) s := by
    intro x hx
    by_cases hxsrc : x ∈ e.source
    · have hex : e x ∈ chartImage e s := mem_chartImage_of_mem hx hxsrc
      have h1 : ContinuousAt (fun w => if w ∈ closedBall c r
          then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) (e x) :=
        hh.continuousAt ((isOpen_chartImage e hs).mem_nhds hex)
      have h2 : ContinuousAt ((fun w => if w ∈ closedBall c r
          then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) ∘ e) x :=
        h1.comp (e.continuousAt hxsrc)
      refine (h2.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hxsrc] with y hy
      by_cases hyb : e y ∈ closedBall c r
      · simp only [Function.comp_apply, if_pos hyb]
        rw [surfaceReplace, dif_pos ⟨hy, hyb⟩]
      · simp only [Function.comp_apply, if_neg hyb]
        rw [surfaceReplace, dif_neg fun hcon => hyb hcon.2]
        simp only [Function.comp_apply, e.left_inv hy]
    · -- off the chart source: the disk is closed (T2), so the replacement
      -- agrees with `g` on a neighbourhood
      have hxD : x ∉ e.symm '' closedBall c r := by
        rintro ⟨w, hw, rfl⟩
        exact hxsrc (e.map_target (hd.closedBall_subset hw))
      have hDc : IsClosed (e.symm '' closedBall c r) := hd.compact_preimage.isClosed
      have hev : surfaceReplace g e c r =ᶠ[𝓝 x] g := by
        filter_upwards [hDc.isOpen_compl.mem_nhds hxD] with y hy
        exact surfaceReplace_eqOn_compl hd hy
      exact (hg.continuousOn x hx).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
  -- the sub-mean inequality in every chart, on small circles
  refine ⟨hcont, fun e' he' => ?_⟩
  refine SubMeanLocalOn.subMeanOn (isOpen_chartImage e' hs) ?_
  refine ⟨continuousOn_comp_chart_symm e' hcont, ?_⟩
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  by_cases hxB : x ∈ e.symm '' ball c r
  · -- interior of the disk: harmonic, hence the mean-value equality
    have hharm : HarmonicOnNhd (surfaceReplace g e c r ∘ e'.symm)
        (chartImage e' (e.symm '' ball c r)) :=
      surfaceReplace_surfaceHarmonicOn_aux hg hd e' he'
    have hMeq : MeanEqOn (surfaceReplace g e c r ∘ e'.symm)
        (chartImage e' (e.symm '' ball c r)) :=
      HarmonicOnNhd.meanEqOn (isOpen_chartImage e' hd.isOpen_ball_image) hharm
    have hmem : e' x ∈ chartImage e' (e.symm '' ball c r) := mem_chartImage_of_mem hxB hxe
    obtain ⟨ρ, hρ, hball⟩ :=
      Metric.isOpen_iff.mp (isOpen_chartImage e' hd.isOpen_ball_image) _ hmem
    filter_upwards [Ioo_mem_nhdsGT hρ] with r' hr'
    exact (hMeq.mean_eq (e' x) r' hr'.1 ((closedBall_subset_ball hr'.2).trans hball)).ge
  · -- on the circle or outside: the replacement equals `g` at the point and
    -- dominates `g` on the circles
    have hux : surfaceReplace g e c r x = g x := by
      by_cases hxD : x ∈ e.symm '' closedBall c r
      · obtain ⟨w', hw', rfl⟩ := hxD
        have hwt : w' ∈ e.target := hd.closedBall_subset hw'
        have hxsrc : e.symm w' ∈ e.source := e.map_target hwt
        have hew : e (e.symm w') = w' := e.right_inv hwt
        have hsph : w' ∈ sphere c r := by
          rw [mem_sphere]
          rcases lt_or_eq_of_le (mem_closedBall.mp hw') with hlt | heq'
          · exact absurd ⟨w', mem_ball.mpr hlt, rfl⟩ hxB
          · exact heq'
        rw [surfaceReplace, dif_pos ⟨hxsrc, by rw [hew]; exact hw'⟩, hew,
          poissonExtension_eqOn_sphere hd.r_pos hgs hsph]
        simp
      · exact surfaceReplace_eqOn_compl hd hxD
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (isOpen_chartImage e' hs) _
      (mem_chartImage_of_mem hxs hxe)
    filter_upwards [Ioo_mem_nhdsGT hρ] with r' hr'
    have hcb : closedBall (e' x) r' ⊆ chartImage e' s :=
      (closedBall_subset_ball hr'.2).trans hball
    have hsph_sub : sphere (e' x) r' ⊆ chartImage e' s := sphere_subset_closedBall.trans hcb
    have hig : CircleIntegrable (g ∘ e'.symm) (e' x) r' :=
      ((hg.subMeanOn e' he').continuousOn.mono hsph_sub).circleIntegrable hr'.1.le
    have hiu : CircleIntegrable (surfaceReplace g e c r ∘ e'.symm) (e' x) r' :=
      ((continuousOn_comp_chart_symm e' hcont).mono hsph_sub).circleIntegrable hr'.1.le
    have hle1 : (g ∘ e'.symm) (e' x) ≤ Real.circleAverage (g ∘ e'.symm) (e' x) r' :=
      (hg.subMeanOn e' he').submean (e' x) r' hr'.1 hcb
    have hle2 : Real.circleAverage (g ∘ e'.symm) (e' x) r'
        ≤ Real.circleAverage (surfaceReplace g e c r ∘ e'.symm) (e' x) r' := by
      refine Real.circleAverage_mono hig hiu ?_
      intro z hz
      rw [abs_of_pos hr'.1] at hz
      obtain ⟨y, ⟨hys, hye⟩, rfl⟩ := hsph_sub hz
      simp only [Function.comp_apply]
      rw [e'.left_inv hye]
      exact le_surfaceReplace_aux hs hg hd y hys
    have hval : (surfaceReplace g e c r ∘ e'.symm) (e' x) = (g ∘ e'.symm) (e' x) := by
      simp only [Function.comp_apply, e'.left_inv hxe, hux]
    rw [hval]
    exact hle1.trans hle2

/-- `g` is dominated by its replacement (comparison principle). -/
theorem le_surfaceReplace (hs : IsOpen s) (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) : ∀ x ∈ s, g x ≤ surfaceReplace g e c r x :=
  le_surfaceReplace_aux hs hg hd

/-- The replacement is harmonic in the open replacement disk. -/
theorem surfaceReplace_surfaceHarmonicOn (hs : IsOpen s) (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) :
    SurfaceHarmonicOn (surfaceReplace g e c r) (e.symm '' ball c r) :=
  surfaceReplace_surfaceHarmonicOn_aux hg hd

/-- The replacement stays in `[0,1]` if `g` does (on `s`). -/
theorem surfaceReplace_mem_Icc (hs : IsOpen s) (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ x ∈ s, g x ∈ Icc (0 : ℝ) 1) :
    ∀ x ∈ s, surfaceReplace g e c r x ∈ Icc (0 : ℝ) 1 := by
  intro x hx
  by_cases hxD : x ∈ e.symm '' closedBall c r
  · obtain ⟨w, hwb, rfl⟩ := hxD
    have hwt : w ∈ e.target := hd.closedBall_subset hwb
    have hxsrc : e.symm w ∈ e.source := e.map_target hwt
    have hew : e (e.symm w) = w := e.right_inv hwt
    have hbd : ∀ z ∈ sphere c r, (g ∘ e.symm) z ∈ Icc (0:ℝ) 1 := fun z hz =>
      hb _ (hd.preimage_subset ⟨z, sphere_subset_closedBall hz, rfl⟩)
    have hval := poissonExtension_mem_Icc hd.r_pos (hd.continuousOn_sphere hg) hbd w hwb
    rw [surfaceReplace, dif_pos ⟨hxsrc, by rw [hew]; exact hwb⟩, hew]
    exact hval
  · rw [surfaceReplace_eqOn_compl hd hxD]
    exact hb x hx

end Replace

/-- A Perron family on `s`: a nonempty set of `[0,1]`-valued subharmonic
functions, closed under pairwise `max` and under harmonic replacement on disks
inside `s` (Anghel–Stan Definition 5, with the `[0,1]` normalization that
suffices for Radó). -/
structure IsPerronFamily (𝓕 : Set (X → ℝ)) (s : Set X) : Prop where
  nonempty : 𝓕.Nonempty
  subharmonic : ∀ g ∈ 𝓕, SurfaceSubharmonicOn g s
  bounds : ∀ g ∈ 𝓕, ∀ x ∈ s, g x ∈ Icc (0 : ℝ) 1
  max_mem : ∀ g₁ ∈ 𝓕, ∀ g₂ ∈ 𝓕, (fun x => Max.max (g₁ x) (g₂ x)) ∈ 𝓕
  replace_mem : ∀ g ∈ 𝓕, ∀ e c r, IsReplaceDisk e c r s → surfaceReplace g e c r ∈ 𝓕

/-- The upper envelope of a family of functions. -/
noncomputable def perronSup (𝓕 : Set (X → ℝ)) : X → ℝ := fun x =>
  sSup ((fun g => g x) '' 𝓕)

/-! ### Harnack's principle for monotone sequences of harmonic functions -/

/-- The Poisson kernel is continuous on the boundary circle, for a fixed
interior point. -/
private theorem continuousOn_poissonKernel_sphere {z₀ w : ℂ} {R : ℝ}
    (hw : w ∈ ball z₀ R) : ContinuousOn (poissonKernel z₀ w) (sphere z₀ R) := by
  have hdR : ‖w - z₀‖ < R := mem_ball_iff_norm.mp hw
  have hfun : poissonKernel z₀ w
      = fun z => (‖z - z₀‖ ^ 2 - ‖w - z₀‖ ^ 2) / ‖(z - z₀) - (w - z₀)‖ ^ 2 :=
    funext fun z => poissonKernel_def z₀ w z
  intro z hz
  have hzR : ‖z - z₀‖ = R := mem_sphere_iff_norm.mp hz
  have hne : (z - z₀) - (w - z₀) ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    rw [hcon] at hzR
    exact hdR.ne hzR
  apply ContinuousAt.continuousWithinAt
  rw [hfun]
  exact ContinuousAt.div (by fun_prop) (by fun_prop)
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

/-- **Harnack's inequality**, upper bound: a nonnegative harmonic function on a
closed disk is controlled at interior points by its value at the center. -/
private theorem harnack_le {h : ℂ → ℝ} {z₀ w : ℂ} {R : ℝ} (hR : 0 < R)
    (hh : HarmonicOnNhd h (closedBall z₀ R))
    (hpos : ∀ z ∈ closedBall z₀ R, 0 ≤ h z) (hw : w ∈ ball z₀ R) :
    h w ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := by
  have hcont : ContinuousOn h (sphere z₀ R) := fun z hz =>
    ((hh z (sphere_subset_closedBall hz)).1.continuousAt).continuousWithinAt
  have hker : ContinuousOn (poissonKernel z₀ w) (sphere z₀ R) :=
    continuousOn_poissonKernel_sphere hw
  have hrep : Real.circleAverage (poissonKernel z₀ w • h) z₀ R = h w :=
    hh.circleAverage_poissonKernel_smul hw
  have hmv : Real.circleAverage h z₀ R = h z₀ := by
    apply HarmonicOnNhd.circleAverage_eq
    rwa [abs_of_pos hR]
  have hint1 : CircleIntegrable (poissonKernel z₀ w • h) z₀ R :=
    (hker.smul hcont).circleIntegrable hR.le
  have hint2 : CircleIntegrable
      (fun z => (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R :=
    (continuousOn_const.mul hcont).circleIntegrable hR.le
  have hmono : Real.circleAverage (poissonKernel z₀ w • h) z₀ R
      ≤ Real.circleAverage (fun z => (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R := by
    refine Real.circleAverage_mono hint1 hint2 ?_
    intro z hz
    rw [abs_of_pos hR] at hz
    have hkb : poissonKernel z₀ w z ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) := by
      have h1 := re_herglotzRieszKernel_le hz hw
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      simpa [herglotzRieszKernel_def] using h1
    have h0 : 0 ≤ h z := hpos z (sphere_subset_closedBall hz)
    calc (poissonKernel z₀ w • h) z = poissonKernel z₀ w z * h z := rfl
      _ ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z := mul_le_mul_of_nonneg_right hkb h0
  have havg : Real.circleAverage (fun z => (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R
      = (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := by
    have h1 : Real.circleAverage (fun z => ((R + ‖w - z₀‖) / (R - ‖w - z₀‖)) • h z) z₀ R
        = ((R + ‖w - z₀‖) / (R - ‖w - z₀‖)) • Real.circleAverage h z₀ R :=
      Real.circleAverage_fun_smul
    simpa [smul_eq_mul, hmv] using h1
  calc h w = Real.circleAverage (poissonKernel z₀ w • h) z₀ R := hrep.symm
    _ ≤ Real.circleAverage (fun z => (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R := hmono
    _ = (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := havg

/-- **Harnack's principle** (bounded case): the pointwise supremum of a
monotone sequence of `[0,1]`-valued harmonic functions on an open set is
harmonic. Continuity comes from Harnack's inequality applied to the
differences, the mean value property passes to the limit by dominated
convergence. -/
private theorem harmonicOnNhd_ciSup_of_monotone {h : ℕ → ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hharm : ∀ n, HarmonicOnNhd (h n) U)
    (hmono : ∀ z ∈ U, ∀ m n : ℕ, m ≤ n → h m z ≤ h n z)
    (hbd : ∀ n, ∀ z ∈ U, h n z ∈ Icc (0 : ℝ) 1) :
    HarmonicOnNhd (fun z => ⨆ n, h n z) U := by
  set W : ℂ → ℝ := fun z => ⨆ n, h n z with hWdef
  have hWapp : ∀ z, W z = ⨆ n, h n z := fun z => rfl
  have hbdd : ∀ z ∈ U, BddAbove (range fun n => h n z) := fun z hz =>
    ⟨1, by rintro v ⟨n, rfl⟩; exact (hbd n z hz).2⟩
  have hle : ∀ n, ∀ z ∈ U, h n z ≤ W z := fun n z hz => le_ciSup (hbdd z hz) n
  have htend : ∀ z ∈ U, Tendsto (fun n => h n z) atTop (𝓝 (W z)) := fun z hz =>
    tendsto_atTop_ciSup (fun m n hmn => hmono z hz m n hmn) (hbdd z hz)
  -- continuity of the supremum, via Harnack's inequality
  have hWc : ContinuousOn W U := by
    intro z₀ hz₀
    apply ContinuousAt.continuousWithinAt
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
    obtain ⟨m, hm⟩ : ∃ m, W z₀ - ε / 8 < h m z₀ := by
      have h1 : W z₀ - ε / 8 < ⨆ n, h n z₀ := by
        rw [← hWapp]; exact sub_lt_self _ (by linarith)
      exact exists_lt_of_lt_ciSup h1
    have hcm : ContinuousAt (h m) z₀ := (hharm m z₀ hz₀).1.continuousAt
    rw [Metric.continuousAt_iff] at hcm
    obtain ⟨δ₁, hδ₁, hδ₁p⟩ := hcm (ε / 8) (by linarith)
    -- Harnack control of the tail on the half ball
    have hkey : ∀ x ∈ ball z₀ (R / 2), W x - h m x ≤ 3 * (W z₀ - h m z₀) := by
      intro x hx
      have hxR : x ∈ ball z₀ R := ball_subset_ball (by linarith) hx
      have hxU : x ∈ U := hRU (ball_subset_closedBall hxR)
      have htends : Tendsto (fun n => h n x - h m x) atTop (𝓝 (W x - h m x)) :=
        (htend x hxU).sub tendsto_const_nhds
      refine le_of_tendsto htends ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      have hdiff : HarmonicOnNhd (fun z => h n z - h m z) (closedBall z₀ R) := fun z hz =>
        (hharm n z (hRU hz)).sub (hharm m z (hRU hz))
      have hnonneg : ∀ z ∈ closedBall z₀ R, 0 ≤ h n z - h m z := fun z hz =>
        sub_nonneg.mpr (hmono z (hRU hz) m n hn)
      have hHar := harnack_le hR hdiff hnonneg hxR
      have hd2 : ‖x - z₀‖ < R / 2 := mem_ball_iff_norm.mp hx
      have hd0 : (0 : ℝ) ≤ ‖x - z₀‖ := norm_nonneg _
      have hfrac : (R + ‖x - z₀‖) / (R - ‖x - z₀‖) ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      have h0 : 0 ≤ h n z₀ - h m z₀ := sub_nonneg.mpr (hmono z₀ hz₀ m n hn)
      have hWn : h n z₀ ≤ W z₀ := hle n z₀ hz₀
      calc h n x - h m x ≤ (R + ‖x - z₀‖) / (R - ‖x - z₀‖) * (h n z₀ - h m z₀) := hHar
        _ ≤ 3 * (h n z₀ - h m z₀) := mul_le_mul_of_nonneg_right hfrac h0
        _ ≤ 3 * (W z₀ - h m z₀) := by linarith
    refine ⟨min δ₁ (R / 2), lt_min hδ₁ (by linarith), ?_⟩
    intro x hx
    have hx1 : dist x z₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 : x ∈ ball z₀ (R / 2) := mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _))
    have hxU : x ∈ U := hRU (ball_subset_closedBall (ball_subset_ball (by linarith) hx2))
    have k1 := hkey x hx2
    have k2 : 0 ≤ W x - h m x := sub_nonneg.mpr (hle m x hxU)
    have k3 : |h m x - h m z₀| < ε / 8 := by
      have := hδ₁p hx1
      rwa [Real.dist_eq] at this
    have k4 : 0 ≤ W z₀ - h m z₀ := sub_nonneg.mpr (hle m z₀ hz₀)
    rw [Real.dist_eq, abs_lt]
    rw [abs_lt] at k3
    constructor
    · linarith [k3.1]
    · linarith [k3.2]
  -- the mean value property passes to the limit
  have hmean : MeanEqOn W U := by
    refine ⟨hWc, fun a ρ hρ hsub => ?_⟩
    have haU : a ∈ U := hsub (mem_closedBall_self hρ.le)
    have hsph : sphere a ρ ⊆ U := sphere_subset_closedBall.trans hsub
    have hcm : ∀ n, Continuous fun θ : ℝ => h n (circleMap a ρ θ) := by
      intro n
      refine continuous_iff_continuousAt.mpr fun θ => ?_
      exact ((hharm n _ (hsph (circleMap_mem_sphere a hρ.le θ))).1.continuousAt).comp
        (continuous_circleMap a ρ).continuousAt
    have hci : Tendsto (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi, h n (circleMap a ρ θ)) atTop
        (𝓝 (∫ θ in (0 : ℝ)..2 * Real.pi, W (circleMap a ρ θ))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => (1 : ℝ)) (Filter.Eventually.of_forall fun n => (hcm n).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun n => ae_of_all _ fun θ _ => ?_)
        intervalIntegrable_const (ae_of_all _ fun θ _ => ?_)
      · have hmem := hbd n _ (hsph (circleMap_mem_sphere a hρ.le θ))
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hmem.1], hmem.2⟩
      · exact htend _ (hsph (circleMap_mem_sphere a hρ.le θ))
    have h2 : Tendsto (fun n => Real.circleAverage (h n) a ρ) atTop
        (𝓝 (Real.circleAverage W a ρ)) := by
      simp only [Real.circleAverage_def]
      exact hci.const_smul _
    have h3 : Tendsto (fun n => Real.circleAverage (h n) a ρ) atTop (𝓝 (W a)) :=
      Filter.Tendsto.congr
        (fun n => ((HarmonicOnNhd.meanEqOn hU (hharm n)).mean_eq a ρ hρ hsub).symm)
        (htend a haU)
    exact tendsto_nhds_unique h2 h3
  exact hmean.harmonicOnNhd hU

/-! ### The Perron approximation sequence -/

/-- Pointwise maximum of the first `j + 1` members of a sequence of
functions. -/
private def maxUpTo (f : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => f 0
  | j + 1 => fun y => Max.max (maxUpTo f j y) (f (j + 1) y)

private theorem maxUpTo_mem {𝓕 : Set (X → ℝ)} {s : Set X} (h𝓕 : IsPerronFamily 𝓕 s)
    {f : ℕ → X → ℝ} (hf : ∀ j, f j ∈ 𝓕) : ∀ j, maxUpTo f j ∈ 𝓕 := by
  intro j
  induction j with
  | zero => rw [maxUpTo]; exact hf 0
  | succ j ih => rw [maxUpTo]; exact h𝓕.max_mem _ ih _ (hf (j + 1))

private theorem le_maxUpTo {f : ℕ → X → ℝ} {i j : ℕ} (hij : i ≤ j) (y : X) :
    f i y ≤ maxUpTo f j y := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.mp hij
    rw [maxUpTo]
  | succ j ih =>
    rw [maxUpTo]
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_max_right _ _
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (le_max_left _ _)

/-- The recursive Perron approximation sequence: harmonic replacements of the
running maxima of a given sequence of family members. -/
private noncomputable def perronSeq (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ)
    (b : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => surfaceReplace (b 0) e c r
  | n + 1 => surfaceReplace
      (fun y => Max.max (perronSeq e c r b n y) (b (n + 1) y)) e c r

section PerronSeq

variable {𝓕 : Set (X → ℝ)} {s : Set X} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {r : ℝ}
  {b : ℕ → X → ℝ}

private theorem perronSeq_mem (h𝓕 : IsPerronFamily 𝓕 s) (hd : IsReplaceDisk e c r s)
    (hb : ∀ n, b n ∈ 𝓕) : ∀ n, perronSeq e c r b n ∈ 𝓕 := by
  intro n
  induction n with
  | zero =>
    rw [perronSeq]
    exact h𝓕.replace_mem _ (hb 0) e c r hd
  | succ n ih =>
    rw [perronSeq]
    exact h𝓕.replace_mem _ (h𝓕.max_mem _ ih _ (hb (n + 1))) e c r hd

private theorem le_perronSeq (hs : IsOpen s) (h𝓕 : IsPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    ∀ y ∈ s, b n y ≤ perronSeq e c r b n y := by
  intro y hy
  cases n with
  | zero =>
    rw [perronSeq]
    exact le_surfaceReplace hs (h𝓕.subharmonic _ (hb 0)) hd y hy
  | succ n =>
    rw [perronSeq]
    refine le_trans (le_max_right (perronSeq e c r b n y) (b (n + 1) y)) ?_
    exact le_surfaceReplace hs (h𝓕.subharmonic _
      (h𝓕.max_mem _ (perronSeq_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd y hy

private theorem perronSeq_le_succ (hs : IsOpen s) (h𝓕 : IsPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    ∀ y ∈ s, perronSeq e c r b n y ≤ perronSeq e c r b (n + 1) y := by
  intro y hy
  rw [perronSeq]
  refine le_trans (le_max_left (perronSeq e c r b n y) (b (n + 1) y)) ?_
  exact le_surfaceReplace hs (h𝓕.subharmonic _
    (h𝓕.max_mem _ (perronSeq_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd y hy

private theorem perronSeq_mono (hs : IsOpen s) (h𝓕 : IsPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) {m n : ℕ} (hmn : m ≤ n) :
    ∀ y ∈ s, perronSeq e c r b m y ≤ perronSeq e c r b n y := by
  intro y hy
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact ih.trans (perronSeq_le_succ hs h𝓕 hd hb n y hy)

private theorem perronSeq_surfaceHarmonicOn (hs : IsOpen s) (h𝓕 : IsPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    SurfaceHarmonicOn (perronSeq e c r b n) (e.symm '' ball c r) := by
  cases n with
  | zero =>
    rw [perronSeq]
    exact surfaceReplace_surfaceHarmonicOn hs (h𝓕.subharmonic _ (hb 0)) hd
  | succ n =>
    rw [perronSeq]
    exact surfaceReplace_surfaceHarmonicOn hs (h𝓕.subharmonic _
      (h𝓕.max_mem _ (perronSeq_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd

end PerronSeq

/-- **Perron's principle** (Anghel–Stan Theorem 6, Hubbard Prop. 1.2.3): the
upper envelope of a Perron family is harmonic. -/
theorem IsPerronFamily.surfaceHarmonicOn_perronSup {𝓕 : Set (X → ℝ)} {s : Set X}
    (hs : IsOpen s) (h𝓕 : IsPerronFamily 𝓕 s) :
    SurfaceHarmonicOn (perronSup 𝓕) s := by
  refine SurfaceHarmonicOn.of_chartwise hs fun x hx => ?_
  set e := chartAt ℂ x with he_def
  have he : e ∈ riemannAtlas X := chartAt_mem_riemannAtlas x
  have hxe : x ∈ e.source := mem_chart_source ℂ x
  refine ⟨e, he, hxe, ?_⟩
  -- choose a legal replacement disk around `e x`
  have hmem : e x ∈ chartImage e s := mem_chartImage_of_mem hx hxe
  obtain ⟨r, hr, hcb⟩ := nhds_basis_closedBall.mem_iff.mp
    ((isOpen_chartImage e hs).mem_nhds hmem)
  set c : ℂ := e x with hc_def
  have hd : IsReplaceDisk e c r s :=
    ⟨he, hr, hcb.trans (chartImage_subset_target e s), by
      rintro y ⟨w, hw, rfl⟩
      exact mapsTo_symm_chartImage (hcb hw)⟩
  have hBmem : ∀ w ∈ ball c r, e.symm w ∈ s := fun w hw =>
    hd.preimage_subset ⟨w, ball_subset_closedBall hw, rfl⟩
  have hball_sub : ball c r ⊆ chartImage e (e.symm '' ball c r) := by
    intro w hw
    have hwt : w ∈ e.target := hd.closedBall_subset (ball_subset_closedBall hw)
    exact ⟨e.symm w, ⟨⟨w, hw, rfl⟩, e.map_target hwt⟩, e.right_inv hwt⟩
  -- unfolded form of the envelope
  have hPS : ∀ y : X, perronSup 𝓕 y = sSup ((fun g => g y) '' 𝓕) := fun y => rfl
  have hPSbdd : ∀ y ∈ s, BddAbove ((fun g => g y) '' 𝓕) := fun y hy =>
    ⟨1, by rintro v ⟨g', hg', rfl⟩; exact (h𝓕.bounds g' hg' y hy).2⟩
  -- a dense sequence in the disk
  haveI hnB : Nonempty (ball c r) := ⟨⟨c, mem_ball_self hr⟩⟩
  set zs : ℕ → ℂ := fun j => (TopologicalSpace.denseSeq (ball c r) j : ℂ) with hzs_def
  have hzs_mem : ∀ j, zs j ∈ ball c r := fun j => (TopologicalSpace.denseSeq (ball c r) j).2
  have hzs_dense : ∀ w ∈ ball c r, w ∈ closure (range zs) := by
    intro w hw
    have h1 : (⟨w, hw⟩ : ball c r) ∈ closure (range (TopologicalSpace.denseSeq (ball c r))) :=
      TopologicalSpace.denseRange_denseSeq (ball c r) _
    have h2 : MapsTo (Subtype.val : ball c r → ℂ)
        (range (TopologicalSpace.denseSeq (ball c r))) (range zs) := by
      rintro q ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    exact map_mem_closure continuous_subtype_val h1 h2
  -- near-optimal family members at the dense points
  have hopt : ∀ j n : ℕ, ∃ g ∈ 𝓕,
      perronSup 𝓕 (e.symm (zs j)) - 1 / ((n : ℝ) + 1) < g (e.symm (zs j)) := by
    intro j n
    have h1 : perronSup 𝓕 (e.symm (zs j)) - 1 / ((n : ℝ) + 1)
        < sSup ((fun g => g (e.symm (zs j))) '' 𝓕) := by
      rw [← hPS]
      exact sub_lt_self _ (by positivity)
    obtain ⟨v, ⟨g, hg, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (h𝓕.nonempty.image _) h1
    exact ⟨g, hg, hv⟩
  choose fj hfj𝓕 hfjval using hopt
  -- running maxima of the near-optimal members
  set cseq : ℕ → X → ℝ := fun n => maxUpTo (fun i => fj i n) n with hcseq_def
  have hcseq_mem : ∀ n, cseq n ∈ 𝓕 := fun n => maxUpTo_mem h𝓕 (fun i => hfj𝓕 i n) n
  have hcseq_dom : ∀ j n : ℕ, j ≤ n → ∀ y, fj j n y ≤ cseq n y := by
    intro j n hjn y
    rw [hcseq_def]
    exact le_maxUpTo (f := fun i => fj i n) hjn y
  -- boundedness of the approximating suprema
  have hbddW : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) → ∀ w ∈ ball c r,
      BddAbove (range fun n => perronSeq e c r b n (e.symm w)) := fun b hb w hw =>
    ⟨1, by
      rintro v ⟨n, rfl⟩
      exact (h𝓕.bounds _ (perronSeq_mem h𝓕 hd hb n) _ (hBmem w hw)).2⟩
  -- harmonicity of the suprema (Harnack's principle)
  have hWharm : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) →
      HarmonicOnNhd (fun w => ⨆ n, perronSeq e c r b n (e.symm w)) (ball c r) := by
    intro b hb
    refine harmonicOnNhd_ciSup_of_monotone isOpen_ball (fun n => ?_) ?_ ?_
    · intro w hw
      exact perronSeq_surfaceHarmonicOn hs h𝓕 hd hb n e he w (hball_sub hw)
    · intro w hw m n hmn
      exact perronSeq_mono hs h𝓕 hd hb hmn (e.symm w) (hBmem w hw)
    · intro n w hw
      exact h𝓕.bounds _ (perronSeq_mem h𝓕 hd hb n) _ (hBmem w hw)
  -- the suprema are dominated by the Perron envelope
  have hWle : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) → ∀ w ∈ ball c r,
      (⨆ n, perronSeq e c r b n (e.symm w)) ≤ perronSup 𝓕 (e.symm w) := by
    intro b hb w hw
    refine ciSup_le fun n => ?_
    rw [hPS]
    exact le_csSup (hPSbdd _ (hBmem w hw)) ⟨_, perronSeq_mem h𝓕 hd hb n, rfl⟩
  -- at the dense points, any supremum built from a dominating sequence attains
  -- the envelope
  have hWge : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) →
      (∀ j n : ℕ, j ≤ n → ∀ y, fj j n y ≤ b n y) → ∀ j : ℕ,
      (⨆ n, perronSeq e c r b n (e.symm (zs j))) = perronSup 𝓕 (e.symm (zs j)) := by
    intro b hb hdom j
    refine le_antisymm (hWle b hb (zs j) (hzs_mem j)) ?_
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    set m := Max.max j n with hm_def
    have h1 := hfjval j m
    have h2 : fj j m (e.symm (zs j)) ≤ b m (e.symm (zs j)) :=
      hdom j m (le_max_left j n) _
    have h3 : b m (e.symm (zs j)) ≤ perronSeq e c r b m (e.symm (zs j)) :=
      le_perronSeq hs h𝓕 hd hb m _ (hBmem (zs j) (hzs_mem j))
    have h4 : perronSeq e c r b m (e.symm (zs j))
        ≤ ⨆ k, perronSeq e c r b k (e.symm (zs j)) :=
      le_ciSup (hbddW b hb (zs j) (hzs_mem j)) m
    have h5 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (le_max_right j n)
      linarith
    linarith
  -- the supremum for the running-maxima sequence
  have hW₁harm : HarmonicOnNhd (fun w => ⨆ n, perronSeq e c r cseq n (e.symm w))
      (ball c r) := hWharm cseq hcseq_mem
  -- the Perron envelope agrees with this harmonic function on the disk
  have hfinal : ∀ w ∈ ball c r,
      perronSup 𝓕 (e.symm w) = ⨆ n, perronSeq e c r cseq n (e.symm w) := by
    intro w hw
    refine le_antisymm ?_ (hWle cseq hcseq_mem w hw)
    rw [hPS]
    refine csSup_le (h𝓕.nonempty.image _) ?_
    rintro v ⟨g, hg, rfl⟩
    -- the second sequence, dominating both `g` and the first sequence
    have hb₂mem : ∀ n, (fun n' y => Max.max (g y) (cseq n' y)) n ∈ 𝓕 := fun n =>
      h𝓕.max_mem _ hg _ (hcseq_mem n)
    have hb₂dom : ∀ j n : ℕ, j ≤ n → ∀ y,
        fj j n y ≤ (fun n' y => Max.max (g y) (cseq n' y)) n y := fun j n hjn y =>
      (hcseq_dom j n hjn y).trans (le_max_right _ _)
    have hW₂harm := hWharm _ hb₂mem
    -- the two suprema agree on the dense sequence, hence at `w`
    have heq : (⨆ n, perronSeq e c r (fun n' y => Max.max (g y) (cseq n' y)) n (e.symm w))
        = ⨆ n, perronSeq e c r cseq n (e.symm w) := by
      have h1 : Tendsto (fun w' => ⨆ n, perronSeq e c r cseq n (e.symm w'))
          (𝓝[range zs] w) (𝓝 (⨆ n, perronSeq e c r cseq n (e.symm w))) :=
        ((hW₁harm w hw).1.continuousAt).continuousWithinAt
      have h2 : Tendsto
          (fun w' => ⨆ n, perronSeq e c r (fun n' y => Max.max (g y) (cseq n' y)) n (e.symm w'))
          (𝓝[range zs] w)
          (𝓝 (⨆ n, perronSeq e c r (fun n' y => Max.max (g y) (cseq n' y)) n (e.symm w))) :=
        ((hW₂harm w hw).1.continuousAt).continuousWithinAt
      haveI : (𝓝[range zs] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hzs_dense w hw)
      have hcongr :
          (fun w' => ⨆ n, perronSeq e c r (fun n' y => Max.max (g y) (cseq n' y)) n (e.symm w'))
          =ᶠ[𝓝[range zs] w] fun w' => ⨆ n, perronSeq e c r cseq n (e.symm w') := by
        filter_upwards [self_mem_nhdsWithin] with w' hw'
        obtain ⟨j, rfl⟩ := hw'
        exact (hWge _ hb₂mem hb₂dom j).trans (hWge cseq hcseq_mem hcseq_dom j).symm
      exact tendsto_nhds_unique (h2.congr' hcongr) h1
    -- `g` is dominated by the second supremum
    have hgle : g (e.symm w)
        ≤ ⨆ n, perronSeq e c r (fun n' y => Max.max (g y) (cseq n' y)) n (e.symm w) := by
      refine le_trans (le_max_left (g (e.symm w)) (cseq 0 (e.symm w))) ?_
      refine le_trans (le_perronSeq hs h𝓕 hd hb₂mem 0 _ (hBmem w hw)) ?_
      exact le_ciSup (hbddW _ hb₂mem w hw) 0
    exact le_of_le_of_eq hgle heq
  -- conclude via congruence on the open disk
  have hcongr : (perronSup 𝓕 ∘ e.symm) =ᶠ[𝓝 c]
      fun w => ⨆ n, perronSeq e c r cseq n (e.symm w) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    exact hfinal w hw
  exact (harmonicAt_congr_nhds hcongr).mpr (hW₁harm c (mem_ball_self hr))

theorem IsPerronFamily.le_perronSup {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : IsPerronFamily 𝓕 s) {g : X → ℝ} (hg : g ∈ 𝓕) :
    ∀ x ∈ s, g x ≤ perronSup 𝓕 x := fun x hx =>
  le_csSup ⟨1, fun _ ⟨g', hg', hgx⟩ => hgx ▸ (h𝓕.bounds g' hg' x hx).2⟩ ⟨g, hg, rfl⟩

theorem IsPerronFamily.perronSup_le {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : IsPerronFamily 𝓕 s) {M : ℝ} {x : X} (_hx : x ∈ s)
    (hM : ∀ g ∈ 𝓕, g x ≤ M) : perronSup 𝓕 x ≤ M :=
  csSup_le (h𝓕.nonempty.image _) fun _ ⟨g, hg, hgx⟩ => hgx ▸ hM g hg

/-- `SubMeanOn` transfers along equality on the domain. -/
private theorem subMeanOn_congr {g₁ g₂ : ℂ → ℝ} {s : Set ℂ} (hg : SubMeanOn g₁ s)
    (h : EqOn g₂ g₁ s) : SubMeanOn g₂ s := by
  refine ⟨hg.continuousOn.congr h, fun c r hr hsub => ?_⟩
  have havg : Real.circleAverage g₂ c r = Real.circleAverage g₁ c r := by
    refine Real.circleAverage_congr_sphere fun z hz => ?_
    rw [abs_of_pos hr] at hz
    exact h (hsub (sphere_subset_closedBall hz))
  rw [h (hsub (mem_closedBall_self hr.le)), havg]
  exact hg.submean c r hr hsub

/-- `SurfaceSubharmonicOn` transfers along equality on the domain. -/
private theorem surfaceSubharmonicOn_congr {g₁ g₂ : X → ℝ} {s : Set X}
    (hg : SurfaceSubharmonicOn g₁ s) (h : EqOn g₂ g₁ s) : SurfaceSubharmonicOn g₂ s := by
  refine ⟨hg.continuousOn.congr h, fun e' he' => ?_⟩
  refine subMeanOn_congr (hg.subMeanOn e' he') ?_
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  simp only [Function.comp_apply]
  rw [e'.left_inv hxe]
  exact h hxs

/-! ## The two-disk configuration and its barriers

Fixed configuration in a chart `e` whose target contains `ball 0 8`: the
removed disks are the preimages of the closed unit disks at `±4`, the barriers
live on the annuli `1 ≤ |ζ ∓ 4| ≤ 2` (`Rado/Complex/PlanarConnected.lean`).
-/

section Config

variable (e : OpenPartialHomeomorph X ℂ)

/-- The surface `X` minus the two closed configuration disks. -/
def configY : Set X :=
  univ \ (e.symm '' closedBall (-4) 1 ∪ e.symm '' closedBall 4 1)

/-- The Perron family for the configuration: subharmonic on `configY`,
`[0,1]`-valued there, continuous up to the closure, and `≤ 0` on the boundary
circle of the disk at `-4`. -/
def configFamily : Set (X → ℝ) :=
  {g | SurfaceSubharmonicOn g (configY e) ∧ (∀ x ∈ closure (configY e), g x ∈ Icc (0 : ℝ) 1)
      ∧ ContinuousOn g (closure (configY e))
      ∧ ∀ x ∈ closure (configY e) ∩ e.symm '' closedBall (-4) 1, g x ≤ 0}

/-- Both configuration disks (in fact, both surrounding annuli) lie inside the
standard ball. -/
private theorem closedBall_config_subset {c : ℂ} (hc : ‖c‖ = 4) {r : ℝ} (hr : r ≤ 2) :
    closedBall c r ⊆ ball (0 : ℂ) 8 := by
  intro z hz
  rw [mem_closedBall] at hz
  rw [mem_ball]
  calc dist z 0 ≤ dist z c + dist c 0 := dist_triangle z c 0
    _ ≤ r + 4 := add_le_add hz (le_of_eq (by rw [dist_zero_right, hc]))
    _ < 8 := by linarith

private theorem norm_two_cpow_quarter :
    ‖(2 : ℂ) ^ ((1 : ℂ) / 4)‖ = (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  have h1 : ((1 : ℂ) / 4) = (((1 : ℝ) / 4 : ℝ) : ℂ) := by norm_num
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h1, h2, norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2), Complex.ofReal_re]

private theorem one_lt_two_rpow_quarter : 1 < (2 : ℝ) ^ ((1 : ℝ) / 4) :=
  (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, by norm_num⟩)

private theorem two_rpow_quarter_lt_two : (2 : ℝ) ^ ((1 : ℝ) / 4) < 2 := by
  nth_rewrite 2 [← Real.rpow_one 2]
  exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by norm_num)

variable {e} (he : e ∈ riemannAtlas X) (hb : ball (0 : ℂ) 8 ⊆ e.target)

/-- A point of the big ball whose distance to a disk center exceeds the radius
does not land in the disk preimage. -/
private theorem notMem_image_of_dist_gt (hb : ball (0 : ℂ) 8 ⊆ e.target) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 8) {c : ℂ} (hc : closedBall c 1 ⊆ ball (0 : ℂ) 8)
    (hdist : 1 < dist w c) : e.symm w ∉ e.symm '' closedBall c 1 := by
  rintro ⟨w', hw', heq⟩
  have h1 : w' ∈ e.target := hb (hc hw')
  have h2 : w ∈ e.target := hb hw
  have hww : w' = w := by
    have h3 := congrArg e heq
    rwa [e.right_inv h1, e.right_inv h2] at h3
  rw [hww] at hw'
  exact absurd (mem_closedBall.mp hw') (not_le.mpr hdist)

include he hb

/-- `configY` is open. -/
theorem isOpen_configY [T2Space X] : IsOpen (configY e) := by
  have hb₁ : closedBall (-4 : ℂ) 1 ⊆ e.target :=
    (closedBall_config_subset (by simp) (by norm_num)).trans hb
  have hb₂ : closedBall (4 : ℂ) 1 ⊆ e.target :=
    (closedBall_config_subset (by simp) (by norm_num)).trans hb
  have hc₁ : IsCompact (e.symm '' closedBall (-4 : ℂ) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using hb₁))
  have hc₂ : IsCompact (e.symm '' closedBall (4 : ℂ) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using hb₂))
  have hcl : IsClosed (e.symm '' closedBall (-4 : ℂ) 1 ∪ e.symm '' closedBall (4 : ℂ) 1) :=
    hc₁.isClosed.union hc₂.isClosed
  rw [configY, ← Set.compl_eq_univ_diff]
  exact hcl.isOpen_compl

/-- Both witness points lie in `configY`. -/
theorem witness_mem_configY :
    e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4)) ∈ configY e ∧
      e.symm (-4 + (2 : ℂ) ^ ((1 : ℂ) / 4)) ∈ configY e := by
  set t := (2 : ℂ) ^ ((1 : ℂ) / 4) with ht
  have hnorm : ‖t‖ = (2:ℝ) ^ ((1:ℝ)/4) := norm_two_cpow_quarter
  have h1 : 1 < ‖t‖ := by rw [hnorm]; exact one_lt_two_rpow_quarter
  have h2 : ‖t‖ < 2 := by rw [hnorm]; exact two_rpow_quarter_lt_two
  have h8 : ‖(8:ℂ)‖ = 8 := by simp
  have hb₁ : closedBall (-4 : ℂ) 1 ⊆ ball (0:ℂ) 8 :=
    closedBall_config_subset (by simp) (by norm_num)
  have hb₂ : closedBall (4 : ℂ) 1 ⊆ ball (0:ℂ) 8 :=
    closedBall_config_subset (by simp) (by norm_num)
  have hw₁ : (4 + t) ∈ ball (0:ℂ) 8 := by
    rw [mem_ball, dist_zero_right]
    have h4 : ‖(4:ℂ)‖ = 4 := by simp
    calc ‖4 + t‖ ≤ ‖(4:ℂ)‖ + ‖t‖ := norm_add_le _ _
      _ < 8 := by rw [h4]; linarith
  have hw₂ : (-4 + t) ∈ ball (0:ℂ) 8 := by
    rw [mem_ball, dist_zero_right]
    have h4 : ‖(-4:ℂ)‖ = 4 := by simp
    calc ‖-4 + t‖ ≤ ‖(-4:ℂ)‖ + ‖t‖ := norm_add_le _ _
      _ < 8 := by rw [h4]; linarith
  have hd₁ : 1 < dist (4 + t) 4 := by
    rw [dist_eq_norm, add_sub_cancel_left]; exact h1
  have hd₂ : 1 < dist (4 + t) (-4) := by
    rw [dist_eq_norm]
    have hrw : (4 + t) - (-4) = 8 + t := by ring
    rw [hrw]
    have hlow := norm_sub_norm_le (8:ℂ) (-t)
    rw [sub_neg_eq_add, norm_neg] at hlow
    linarith
  have hd₃ : 1 < dist (-4 + t) (-4) := by
    rw [dist_eq_norm]
    have hrw : (-4 + t) - (-4) = t := by ring
    rw [hrw]; exact h1
  have hd₄ : 1 < dist (-4 + t) 4 := by
    rw [dist_eq_norm]
    have hrw : (-4 + t) - 4 = t - 8 := by ring
    rw [hrw, norm_sub_rev]
    have hlow := norm_sub_norm_le (8:ℂ) t
    linarith
  constructor
  · refine ⟨mem_univ _, ?_⟩
    rintro (hmem | hmem)
    · exact notMem_image_of_dist_gt hb hw₁ hb₁ hd₂ hmem
    · exact notMem_image_of_dist_gt hb hw₁ hb₂ hd₁ hmem
  · refine ⟨mem_univ _, ?_⟩
    rintro (hmem | hmem)
    · exact notMem_image_of_dist_gt hb hw₂ hb₁ hd₃ hmem
    · exact notMem_image_of_dist_gt hb hw₂ hb₂ hd₄ hmem

/-- `configY` is connected when `X` is (clopen argument through the chart,
using `isPathConnected_ball_diff_two_disks`). -/
theorem isConnected_configY [ConnectedSpace X] [T2Space X] : IsConnected (configY e) := by
  have hYo : IsOpen (configY e) := isOpen_configY he hb
  -- the connected chart core `P`
  set P : Set X := e.symm '' (ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1))
    with hP_def
  have hsub8 : ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) ⊆ e.target :=
    fun w hw => hb hw.1
  have hPY : P ⊆ configY e := by
    rintro x ⟨w, hw, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    rintro (hmem | hmem)
    · have hd : 1 < dist w (-4 : ℂ) := by
        by_contra hle
        push_neg at hle
        exact hw.2 (Or.inl (mem_closedBall.mpr hle))
      exact notMem_image_of_dist_gt hb hw.1
        (closedBall_config_subset (by simp) (by norm_num)) hd hmem
    · have hd : 1 < dist w (4 : ℂ) := by
        by_contra hle
        push_neg at hle
        exact hw.2 (Or.inr (mem_closedBall.mpr hle))
      exact notMem_image_of_dist_gt hb hw.1
        (closedBall_config_subset (by simp) (by norm_num)) hd hmem
  have hPconn : IsPreconnected P :=
    ((isPathConnected_ball_diff_two_disks.isConnected).image _
      (e.symm.continuousOn.mono (by simpa using hsub8))).isPreconnected
  have hPne : P.Nonempty := by
    refine ⟨e.symm 0, 0, ⟨mem_ball_self (by norm_num), ?_⟩, rfl⟩
    rintro (hmem | hmem)
    · rw [mem_closedBall] at hmem
      have h4 : dist (0 : ℂ) (-4) = 4 := by
        rw [dist_eq_norm, zero_sub, norm_neg]
        simp
      rw [h4] at hmem
      norm_num at hmem
    · rw [mem_closedBall] at hmem
      have h4 : dist (0 : ℂ) 4 = 4 := by
        rw [dist_eq_norm, zero_sub, norm_neg]
        simp
      rw [h4] at hmem
      norm_num at hmem
  refine ⟨⟨_, (witness_mem_configY he hb).1⟩, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  -- the key step, symmetric in `u` and `v`
  have key : ∀ u' v' : Set X, IsOpen u' → IsOpen v' → configY e ⊆ u' ∪ v' →
      configY e ∩ (u' ∩ v') = ∅ → P ⊆ u' → configY e ⊆ u' := by
    intro u' v' hu' hv' hcov' hdisj' hPu
    have hdisj'' : ∀ z, z ∈ configY e → z ∈ u' → z ∈ v' → False := fun z h1 h2 h3 =>
      eq_empty_iff_forall_notMem.mp hdisj' z ⟨h1, h2, h3⟩
    -- `Y ∩ v'` is clopen in `X`
    have hTopen : IsOpen (configY e ∩ v') := hYo.inter hv'
    have hTclosed : IsClosed (configY e ∩ v') := by
      refine isClosed_of_closure_subset ?_
      intro z hz
      by_cases hzY : z ∈ configY e
      · rcases hcov' hzY with hzu | hzv
        · exfalso
          obtain ⟨y, hyu, hyT⟩ := mem_closure_iff.mp hz u' hu' hzu
          exact hdisj'' y hyT.1 hyu hyT.2
        · exact ⟨hzY, hzv⟩
      · -- limit points inside the removed disks are impossible: near them,
        -- `Y` is contained in `P ⊆ u'`
        exfalso
        have hzK : z ∈ e.symm '' closedBall (-4 : ℂ) 1 ∪ e.symm '' closedBall (4 : ℂ) 1 := by
          by_contra hcon
          exact hzY ⟨mem_univ _, hcon⟩
        have hzN : z ∈ e.symm '' ball (0 : ℂ) 8 := by
          rcases hzK with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
          · exact ⟨w, closedBall_config_subset (by simp) (by norm_num) hw, rfl⟩
          · exact ⟨w, closedBall_config_subset (by simp) (by norm_num) hw, rfl⟩
        have hNopen : IsOpen (e.symm '' ball (0 : ℂ) 8) :=
          e.symm.isOpen_image_of_subset_source isOpen_ball (by simpa using hb)
        have hNY : ∀ y ∈ e.symm '' ball (0 : ℂ) 8, y ∈ configY e → y ∈ P := by
          rintro y ⟨w, hw, rfl⟩ hyY
          refine ⟨w, ⟨hw, ?_⟩, rfl⟩
          rintro (hmem | hmem)
          · exact hyY.2 (Or.inl ⟨w, hmem, rfl⟩)
          · exact hyY.2 (Or.inr ⟨w, hmem, rfl⟩)
        obtain ⟨y, hyN, hyT⟩ := mem_closure_iff.mp hz _ hNopen hzN
        exact hdisj'' y hyT.1 (hPu (hNY y hyN hyT.1)) hyT.2
    rcases isClopen_iff.mp ⟨hTclosed, hTopen⟩ with hT0 | hT1
    · intro z hz
      rcases hcov' hz with hzu | hzv
      · exact hzu
      · exact absurd (show z ∈ configY e ∩ v' from ⟨hz, hzv⟩)
          (by rw [hT0]; exact notMem_empty z)
    · exfalso
      obtain ⟨p, hp⟩ := hPne
      have hpT : p ∈ configY e ∩ v' := by rw [hT1]; exact mem_univ p
      exact hdisj'' p (hPY hp) (hPu hp) hpT.2
  have hPuv : P ⊆ u ∪ v := hPY.trans hcov
  have hPdisj : P ∩ (u ∩ v) = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun z hz =>
      eq_empty_iff_forall_notMem.mp hdisj z ⟨hPY hz.1, hz.2⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp hPconn u v hu hv hPuv hPdisj with hPu | hPv
  · exact Or.inl (key u v hu hv hcov hdisj hPu)
  · refine Or.inr (key v u hv hu ?_ ?_ hPv)
    · rwa [union_comm]
    · rwa [inter_comm v u]

/-- The configuration family is a Perron family. -/
theorem isPerronFamily_configFamily [T2Space X] :
    IsPerronFamily (configFamily e) (configY e) := by
  have hYo : IsOpen (configY e) := isOpen_configY he hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- nonempty: the zero function belongs to the family
    refine ⟨fun _ => 0, ⟨continuousOn_const, fun e' _ => SubMeanOn.const⟩, ?_, ?_, ?_⟩
    · exact fun x _ => ⟨le_rfl, zero_le_one⟩
    · exact continuousOn_const
    · exact fun x _ => le_rfl
  · exact fun g hg => hg.1
  · exact fun g hg x hx => hg.2.1 x (subset_closure hx)
  · -- closed under pairwise max
    rintro g₁ ⟨h₁sub, h₁icc, h₁cont, h₁bd⟩ g₂ ⟨h₂sub, h₂icc, h₂cont, h₂bd⟩
    refine ⟨h₁sub.max h₂sub, ?_, ContinuousOn.sup h₁cont h₂cont, ?_⟩
    · intro x hx
      exact ⟨le_trans (h₁icc x hx).1 (le_max_left _ _),
        max_le (h₁icc x hx).2 (h₂icc x hx).2⟩
    · intro x hx
      exact max_le (h₁bd x hx) (h₂bd x hx)
  · -- closed under harmonic replacement
    rintro g ⟨hgsub, hgicc, hgcont, hgbd⟩ e' c' r' hd
    have hDY : e'.symm '' closedBall c' r' ⊆ configY e := hd.preimage_subset
    have hDclosed : IsClosed (e'.symm '' closedBall c' r') := hd.compact_preimage.isClosed
    have hgsub' : SurfaceSubharmonicOn (surfaceReplace g e' c' r') (configY e) :=
      surfaceReplace_surfaceSubharmonicOn hYo hgsub hd
    have hicc' : ∀ x ∈ configY e, surfaceReplace g e' c' r' x ∈ Icc (0 : ℝ) 1 :=
      surfaceReplace_mem_Icc hYo hgsub hd fun x hx => hgicc x (subset_closure hx)
    refine ⟨hgsub', ?_, ?_, ?_⟩
    · -- values in `[0, 1]` on the closure
      intro x hx
      by_cases hxD : x ∈ e'.symm '' closedBall c' r'
      · exact hicc' x (hDY hxD)
      · rw [surfaceReplace_eqOn_compl hd hxD]
        exact hgicc x hx
    · -- continuity on the closure
      intro x hx
      by_cases hxY : x ∈ configY e
      · exact (hgsub'.continuousOn.continuousAt (hYo.mem_nhds hxY)).continuousWithinAt
      · have hxD : x ∉ e'.symm '' closedBall c' r' := fun hcon => hxY (hDY hcon)
        have hev : surfaceReplace g e' c' r' =ᶠ[𝓝 x] g := by
          filter_upwards [hDclosed.isOpen_compl.mem_nhds hxD] with y hy
          exact surfaceReplace_eqOn_compl hd hy
        exact (hgcont x hx).congr_of_eventuallyEq
          (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
    · -- boundary condition at the disk `K₀`
      intro x hx
      have hxY : x ∉ configY e := fun hcon => hcon.2 (Or.inl hx.2)
      have hxD : x ∉ e'.symm '' closedBall c' r' := fun hcon => hxY (hDY hcon)
      rw [surfaceReplace_eqOn_compl hd hxD]
      exact hgbd x hx

/-- The lower barrier: forced value `≥ 3/4` at the witness point near the disk
at `+4` (the function `max 0 (log(2/|ζ-4|)/log 2)` belongs to the family). -/
theorem perronSup_ge_witness [T2Space X] :
    3 / 4 ≤ perronSup (configFamily e) (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) := by
  classical
  have hYo : IsOpen (configY e) := isOpen_configY he hb
  -- the lower barrier
  set β : X → ℝ := fun x =>
    if x ∈ e.source then Max.max 0 ((Real.log 2 - Real.log ‖e x - 4‖) / Real.log 2) else 0
    with hβ_def
  have hβ0 : ∀ x, x ∉ e.source → β x = 0 := fun x hx => if_neg hx
  have hβin : ∀ x ∈ e.source,
      β x = Max.max 0 ((Real.log 2 - Real.log ‖e x - 4‖) / Real.log 2) := fun x hx => if_pos hx
  have hβnn : ∀ x, 0 ≤ β x := by
    intro x
    by_cases hx : x ∈ e.source
    · rw [hβin x hx]; exact le_max_left _ _
    · rw [hβ0 x hx]
  -- points of `Y` in the chart keep distance `> 1` from the disk center `4`
  have hK₁ : ∀ y ∈ e.source, y ∈ configY e → 1 < ‖e y - 4‖ := by
    intro y hys hyY
    by_contra hle
    push_neg at hle
    have h1 : e y ∈ closedBall (4 : ℂ) 1 := by rwa [mem_closedBall, dist_eq_norm]
    exact hyY.2 (Or.inr ⟨e y, h1, e.left_inv hys⟩)
  -- ... and distance `≥ 1` on the closure of `Y`
  have hnorm1 : ∀ x ∈ closure (configY e), x ∈ e.source → 1 ≤ ‖e x - 4‖ := by
    intro x hx hxe
    have hcl : x ∈ closure (e.source ∩ configY e) :=
      e.open_source.inter_closure ⟨hxe, hx⟩
    haveI : (𝓝[e.source ∩ configY e] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hcont : ContinuousWithinAt (fun y => ‖e y - 4‖) (e.source ∩ configY e) x :=
      (((e.continuousAt hxe).sub continuousAt_const).norm).continuousWithinAt
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hK₁ y hy.1 hy.2).le
  have hβle1 : ∀ x ∈ closure (configY e), β x ≤ 1 := by
    intro x hx
    by_cases hxe : x ∈ e.source
    · rw [hβin x hxe]
      have h1 : 1 ≤ ‖e x - 4‖ := hnorm1 x hx hxe
      have h2 : 0 ≤ Real.log ‖e x - 4‖ := Real.log_nonneg h1
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      refine max_le zero_le_one ?_
      rw [div_le_one hlog2]
      linarith
    · rw [hβ0 x hxe]; exact zero_le_one
  -- `β` vanishes off the compact preimage of `closedBall 4 2`
  have hC_sub : closedBall (4 : ℂ) 2 ⊆ ball (0 : ℂ) 8 :=
    closedBall_config_subset (by simp) le_rfl
  have hCclosed : IsClosed (e.symm '' closedBall (4 : ℂ) 2) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using hC_sub.trans hb))).isClosed
  have hβ_zero_off : ∀ y, y ∉ e.symm '' closedBall (4 : ℂ) 2 → β y = 0 := by
    intro y hyC
    by_cases hys : y ∈ e.source
    · rw [hβin y hys]
      have h1 : e y ∉ closedBall (4 : ℂ) 2 := fun hcon => hyC ⟨e y, hcon, e.left_inv hys⟩
      have h2 : 2 < ‖e y - 4‖ := by
        rw [mem_closedBall, dist_eq_norm, not_le] at h1
        exact h1
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have h3 : Real.log 2 < Real.log ‖e y - 4‖ := Real.log_lt_log two_pos h2
      exact max_eq_left (div_nonpos_iff.mpr (Or.inr ⟨by linarith, hlog2.le⟩))
    · exact hβ0 y hys
  -- continuity of `β` on the closure of `Y`
  have hβcont : ContinuousOn β (closure (configY e)) := by
    intro x hx
    by_cases hxe : x ∈ e.source
    · have h1 : 1 ≤ ‖e x - 4‖ := hnorm1 x hx hxe
      have hne : ‖e x - 4‖ ≠ 0 := by positivity
      have hcont1 : ContinuousAt
          (fun y => Max.max 0 ((Real.log 2 - Real.log ‖e y - 4‖) / Real.log 2)) x := by
        refine Filter.Tendsto.max continuousAt_const ?_
        refine ContinuousAt.div ?_ continuousAt_const (Real.log_pos one_lt_two).ne'
        refine ContinuousAt.sub continuousAt_const ?_
        exact (((e.continuousAt hxe).sub continuousAt_const).norm).log hne
      refine (hcont1.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hxe] with y hy
      exact (hβin y hy).symm
    · have hxC : x ∉ e.symm '' closedBall (4 : ℂ) 2 := by
        rintro ⟨w, hw, rfl⟩
        exact hxe (e.map_target (hb (hC_sub hw)))
      have hev : β =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hCclosed.isOpen_compl.mem_nhds hxC] with y hy
        exact hβ_zero_off y hy
      exact continuousWithinAt_const.congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
  -- subharmonicity of `β` on `Y`, by locality
  have hβsub : SurfaceSubharmonicOn β (configY e) := by
    refine SurfaceSubharmonicOn.of_locally hYo ?_
    intro x hxY
    by_cases hxe : x ∈ e.source
    · -- on `e.source ∩ Y`, `β = max 0 (harmonic)`
      refine ⟨e.source ∩ configY e, e.open_source.inter hYo, ⟨hxe, hxY⟩,
        inter_subset_right, ?_⟩
      have hharm : SurfaceHarmonicOn
          (fun y => (Real.log 2 - Real.log ‖e y - 4‖) / Real.log 2)
          (e.source ∩ configY e) := by
        refine SurfaceHarmonicOn.of_chartwise (e.open_source.inter hYo) ?_
        rintro y ⟨hys, hyY⟩
        refine ⟨e, he, hys, ?_⟩
        have hy4 : e y ≠ 4 := by
          intro hcon
          have h1 := hK₁ y hys hyY
          rw [hcon] at h1
          simp at h1
          norm_num at h1
        have hexp : HarmonicAt
            (fun w : ℂ => (Real.log 2 - Real.log ‖w - 4‖) / Real.log 2) (e y) := by
          have h1 : AnalyticAt ℂ (fun w : ℂ => w - 4) (e y) := by fun_prop
          have h2 : (fun w : ℂ => w - 4) (e y) ≠ 0 := sub_ne_zero.mpr hy4
          have hlog := h1.harmonicAt_log_norm h2
          have hsub : HarmonicAt (fun w : ℂ => Real.log 2 - Real.log ‖w - 4‖) (e y) :=
            (harmonicAt_const _).sub hlog
          have heq : (fun w : ℂ => (Real.log 2 - Real.log ‖w - 4‖) / Real.log 2)
              = (Real.log 2)⁻¹ • fun w : ℂ => Real.log 2 - Real.log ‖w - 4‖ := by
            funext w
            simp [div_eq_inv_mul]
          rw [heq]
          exact hsub.const_smul
        refine (harmonicAt_congr_nhds ?_).mpr hexp
        filter_upwards [e.open_target.mem_nhds (e.map_source hys)] with w hw
        simp only [Function.comp_apply]
        rw [e.right_inv hw]
      have hmax := SurfaceSubharmonicOn.max
        (⟨continuousOn_const, fun e' _ => SubMeanOn.const⟩ :
          SurfaceSubharmonicOn (fun _ => (0 : ℝ)) (e.source ∩ configY e))
        (hharm.surfaceSubharmonicOn (e.open_source.inter hYo))
      refine surfaceSubharmonicOn_congr hmax ?_
      intro y hy
      exact hβin y hy.1
    · -- off the source, `β` vanishes on a neighbourhood
      have hxC : x ∉ e.symm '' closedBall (4 : ℂ) 2 := by
        rintro ⟨w, hw, rfl⟩
        exact hxe (e.map_target (hb (hC_sub hw)))
      refine ⟨(e.symm '' closedBall (4 : ℂ) 2)ᶜ ∩ configY e,
        hCclosed.isOpen_compl.inter hYo, ⟨hxC, hxY⟩, inter_subset_right, ?_⟩
      refine surfaceSubharmonicOn_congr
        (⟨continuousOn_const, fun e' _ => SubMeanOn.const⟩ :
          SurfaceSubharmonicOn (fun _ => (0 : ℝ)) _) ?_
      intro y hy
      exact hβ_zero_off y hy.1
  -- boundary condition at the disk `K₀`
  have hβbd : ∀ x ∈ closure (configY e) ∩ e.symm '' closedBall (-4 : ℂ) 1, β x ≤ 0 := by
    rintro x ⟨-, w, hw, rfl⟩
    have hwt : w ∈ e.target := hb (closedBall_config_subset (by simp) (by norm_num) hw)
    refine le_of_eq (hβ_zero_off _ ?_)
    rintro ⟨w', hw', heq⟩
    have h1 : w' ∈ e.target := hb (hC_sub hw')
    have hww : w' = w := by
      have h3 := congrArg e heq
      rwa [e.right_inv h1, e.right_inv hwt] at h3
    rw [hww] at hw'
    have d1 : dist w (4 : ℂ) ≤ 2 := mem_closedBall.mp hw'
    have d2 : dist w (-4 : ℂ) ≤ 1 := mem_closedBall.mp hw
    have d3 : dist (-4 : ℂ) (4 : ℂ) = 8 := by
      rw [dist_eq_norm, show ((-4 : ℂ) - 4) = -8 by ring, norm_neg]
      simp
    have htri := dist_triangle (-4 : ℂ) w 4
    rw [dist_comm (-4 : ℂ) w] at htri
    linarith
  -- `β` belongs to the family
  have hβmem : β ∈ configFamily e :=
    ⟨hβsub, fun x hx => ⟨hβnn x, hβle1 x hx⟩, hβcont, hβbd⟩
  -- value at the witness point
  have hval : β (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) = 3 / 4 := by
    set t := (2 : ℂ) ^ ((1 : ℂ) / 4) with ht
    have hnt : ‖t‖ = (2 : ℝ) ^ ((1 : ℝ) / 4) := norm_two_cpow_quarter
    have h2t : ‖t‖ < 2 := by rw [hnt]; exact two_rpow_quarter_lt_two
    have hw₁ : (4 + t) ∈ ball (0 : ℂ) 8 := by
      rw [mem_ball, dist_zero_right]
      have h4 : ‖(4 : ℂ)‖ = 4 := by simp
      calc ‖4 + t‖ ≤ ‖(4 : ℂ)‖ + ‖t‖ := norm_add_le _ _
        _ < 8 := by rw [h4]; linarith
    have hwt : (4 + t) ∈ e.target := hb hw₁
    have hxs : e.symm (4 + t) ∈ e.source := e.map_target hwt
    rw [hβin _ hxs, e.right_inv hwt, show (4 + t) - 4 = t by ring, hnt,
      Real.log_rpow two_pos]
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have hcalc : (Real.log 2 - 1 / 4 * Real.log 2) / Real.log 2 = 3 / 4 := by
      field_simp
      ring
    rw [hcalc]
    exact max_eq_right (by norm_num)
  calc (3 : ℝ) / 4 = β (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) := hval.symm
    _ ≤ perronSup (configFamily e) (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) :=
        (isPerronFamily_configFamily he hb).le_perronSup hβmem _
          (witness_mem_configY he hb).1

/-- The upper barrier: forced value `≤ 1/4` at the witness point near the disk
at `-4` (every family member is dominated on the annulus by
`1 - log(2/|ζ+4|)/log 2`, by the boundary comparison principle). -/
theorem perronSup_le_witness [T2Space X] :
    perronSup (configFamily e) (e.symm (-4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) ≤ 1 / 4 := by
  have hYo : IsOpen (configY e) := isOpen_configY he hb
  set t := (2 : ℂ) ^ ((1 : ℂ) / 4) with ht
  have hnt : ‖t‖ = (2 : ℝ) ^ ((1 : ℝ) / 4) := norm_two_cpow_quarter
  have h1t : 1 < ‖t‖ := by rw [hnt]; exact one_lt_two_rpow_quarter
  have h2t : ‖t‖ < 2 := by rw [hnt]; exact two_rpow_quarter_lt_two
  -- the annulus and the upper barrier
  set A : Set ℂ := {w | 1 < ‖w + 4‖ ∧ ‖w + 4‖ < 2} with hA_def
  set γ : ℂ → ℝ := fun w => Real.log ‖w + 4‖ / Real.log 2 with hγ_def
  have hcontf : Continuous fun w : ℂ => ‖w + 4‖ := by fun_prop
  have hAopen : IsOpen A := isOpen_Ioo.preimage hcontf
  have hclA : closure A ⊆ {w : ℂ | 1 ≤ ‖w + 4‖ ∧ ‖w + 4‖ ≤ 2} :=
    closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) (isClosed_Icc.preimage hcontf)
  have hAbd : Bornology.IsBounded A := by
    refine (isBounded_ball (x := (-4 : ℂ)) (r := 2)).subset ?_
    intro w hw
    rw [mem_ball, dist_eq_norm, show w - (-4 : ℂ) = w + 4 by ring]
    exact hw.2
  -- annulus points stay in the big ball and in `Y`
  have hAball : ∀ w : ℂ, ‖w + 4‖ ≤ 2 → w ∈ ball (0 : ℂ) 8 := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have h1 : ‖w‖ ≤ ‖w + 4‖ + ‖(-4 : ℂ)‖ := by
      calc ‖w‖ = ‖(w + 4) + (-4)‖ := by ring_nf
        _ ≤ ‖w + 4‖ + ‖(-4 : ℂ)‖ := norm_add_le _ _
    have h4 : ‖(-4 : ℂ)‖ = 4 := by simp
    linarith
  have hAY : ∀ w ∈ A, e.symm w ∈ configY e := by
    intro w hw
    have hwb : w ∈ ball (0 : ℂ) 8 := hAball w hw.2.le
    refine ⟨mem_univ _, ?_⟩
    rintro (hmem | hmem)
    · have hd : 1 < dist w (-4 : ℂ) := by
        rw [dist_eq_norm, show w - (-4 : ℂ) = w + 4 by ring]
        exact hw.1
      exact notMem_image_of_dist_gt hb hwb
        (closedBall_config_subset (by simp) (by norm_num)) hd hmem
    · have hd : 1 < dist w (4 : ℂ) := by
        rw [dist_eq_norm, show w - (4 : ℂ) = (w + 4) - 8 by ring, norm_sub_rev]
        have hlow := norm_sub_norm_le (8 : ℂ) (w + 4)
        have h8 : ‖(8 : ℂ)‖ = 8 := by simp
        linarith [hw.2]
      exact notMem_image_of_dist_gt hb hwb
        (closedBall_config_subset (by simp) (by norm_num)) hd hmem
  have hAchart : A ⊆ chartImage e (configY e) := by
    intro w hw
    have hwt : w ∈ e.target := hb (hAball w hw.2.le)
    exact ⟨e.symm w, ⟨hAY w hw, e.map_target hwt⟩, e.right_inv hwt⟩
  -- closure points map into the closure of `Y`
  have hclAY : ∀ w ∈ closure A, e.symm w ∈ closure (configY e) := by
    intro w hw
    have hwt : w ∈ e.target := hb (hAball w (hclA hw).2)
    have hcont : ContinuousWithinAt e.symm A w :=
      (e.symm.continuousAt (by simpa using hwt)).continuousWithinAt
    refine closure_mono ?_ (hcont.mem_closure_image hw)
    rintro y ⟨w', hw', rfl⟩
    exact hAY w' hw'
  -- the barrier is harmonic on the annulus
  have hγharm : HarmonicOnNhd γ A := by
    intro w hw
    have hne : w + 4 ≠ 0 := by
      intro hcon
      have h1 := hw.1
      rw [hcon] at h1
      simp at h1
      norm_num at h1
    have h1 : AnalyticAt ℂ (fun w : ℂ => w + 4) w := by fun_prop
    have hlog := h1.harmonicAt_log_norm hne
    have heq : γ = (Real.log 2)⁻¹ • fun w : ℂ => Real.log ‖w + 4‖ := by
      funext w
      simp [hγ_def, div_eq_inv_mul]
    rw [heq]
    exact hlog.const_smul
  -- continuity of the barrier up to the closure
  have hγcont : ContinuousOn γ (closure A) := by
    intro w hw
    have h1 : 1 ≤ ‖w + 4‖ := (hclA hw).1
    have hne : ‖w + 4‖ ≠ 0 := by positivity
    exact ((hcontf.continuousAt.log hne).div_const _).continuousWithinAt
  -- every family member is dominated by the barrier on the annulus
  have hkey : ∀ g ∈ configFamily e, g (e.symm (-4 + t)) ≤ 1 / 4 := by
    rintro g ⟨hgsub, hgicc, hgcont, hgbd⟩
    have hgsm : SubMeanOn (g ∘ e.symm) A := (hgsub.subMeanOn e he).mono hAchart
    have hγmeq : MeanEqOn γ A := HarmonicOnNhd.meanEqOn hAopen hγharm
    have hsm : SubMeanOn ((g ∘ e.symm) + -γ) A := hgsm.add_meanEq hγmeq.neg
    have hcont2 : ContinuousOn ((g ∘ e.symm) + -γ) (closure A) := by
      refine ContinuousOn.add ?_ hγcont.neg
      refine hgcont.comp (e.symm.continuousOn.mono ?_) fun w hw => hclAY w hw
      have hsub : closure A ⊆ e.target := fun w hw => hb (hAball w (hclA hw).2)
      simpa using hsub
    have hfr : ∀ w ∈ frontier A, ((g ∘ e.symm) + -γ) w ≤ 0 := by
      intro w hw
      have hwcl : w ∈ closure A := frontier_subset_closure hw
      have hwc := hclA hwcl
      have hnA : w ∉ A := by
        intro hcon
        rw [← hAopen.interior_eq] at hcon
        exact hw.2 hcon
      have hcases : ‖w + 4‖ = 1 ∨ ‖w + 4‖ = 2 := by
        rcases eq_or_lt_of_le hwc.1 with heq | hlt1
        · exact Or.inl heq.symm
        rcases eq_or_lt_of_le hwc.2 with heq | hlt2
        · exact Or.inr heq
        · exact absurd ⟨hlt1, hlt2⟩ hnA
      simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply]
      rcases hcases with h1 | h2
      · -- inner circle: the barrier vanishes and `g ≤ 0`
        have hγ0 : γ w = 0 := by
          show Real.log ‖w + 4‖ / Real.log 2 = 0
          rw [h1]
          simp
        have hK : e.symm w ∈ e.symm '' closedBall (-4 : ℂ) 1 :=
          ⟨w, by rw [mem_closedBall, dist_eq_norm, show w - (-4 : ℂ) = w + 4 by ring, h1], rfl⟩
        have hgw : g (e.symm w) ≤ 0 := hgbd _ ⟨hclAY w hwcl, hK⟩
        rw [hγ0]
        linarith
      · -- outer circle: the barrier is `1` and `g ≤ 1`
        have hγ1 : γ w = 1 := by
          show Real.log ‖w + 4‖ / Real.log 2 = 1
          rw [h2]
          exact div_self (Real.log_pos one_lt_two).ne'
        have hgw : g (e.symm w) ≤ 1 := (hgicc _ (hclAY w hwcl)).2
        rw [hγ1]
        linarith
    have hle := hsm.le_of_frontier_le hAopen hAbd hcont2 hfr
    have hwA : (-4 + t) ∈ A := by
      show 1 < ‖(-4 + t) + 4‖ ∧ ‖(-4 + t) + 4‖ < 2
      rw [show (-4 + t) + 4 = t by ring]
      exact ⟨h1t, h2t⟩
    have hval := hle _ (subset_closure hwA)
    simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply] at hval
    have hγw : γ (-4 + t) = 1 / 4 := by
      show Real.log ‖(-4 + t) + 4‖ / Real.log 2 = 1 / 4
      rw [show (-4 + t) + 4 = t by ring, hnt, Real.log_rpow two_pos]
      have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      field_simp
    rw [hγw] at hval
    linarith
  exact (isPerronFamily_configFamily he hb).perronSup_le
    (witness_mem_configY he hb).2 hkey

end Config

/-! ## Conjugate germs and the étale space -/

/-- `F` is a holomorphic conjugate-package for `u` on `V`: holomorphic with
`Re F = u` there. -/
def IsConjugate (u : X → ℝ) (F : X → ℂ) (V : Set X) : Prop :=
  HolomorphicOn F V ∧ ∀ x ∈ V, (F x).re = u x

/-- Existence of conjugates on small connected neighbourhoods of any point of a
harmonic function's domain (Schwarz integral in a chart;
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`). -/
theorem exists_conjugate {u : X → ℝ} {s : Set X} (hu : SurfaceHarmonicOn u s)
    (hs : IsOpen s) {x : X} (hx : x ∈ s) :
    ∃ V F, IsOpen V ∧ IsPreconnected V ∧ x ∈ V ∧ V ⊆ s ∧ IsConjugate u F V := by
  have he := chartAt_mem_riemannAtlas (X := X) x
  have hmem : chartAt ℂ x x ∈ chartImage (chartAt ℂ x) s :=
    mem_chartImage_of_mem hx (mem_chart_source ℂ x)
  obtain ⟨ρ, hρpos, hball⟩ := Metric.isOpen_iff.mp (isOpen_chartImage _ hs) _ hmem
  have hharm : HarmonicOnNhd (u ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) ρ) :=
    fun y hy => hu _ he y (hball hy)
  obtain ⟨H, hHan, hHre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
  have hsub : ball (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target :=
    fun w hw => chartImage_subset_target _ _ (hball hw)
  refine ⟨(chartAt ℂ x).symm '' ball (chartAt ℂ x x) ρ, H ∘ (chartAt ℂ x), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact (chartAt ℂ x).symm.isOpen_image_of_subset_source isOpen_ball (by simpa using hsub)
  · exact ((convex_ball _ _).isPreconnected).image _
      ((chartAt ℂ x).symm.continuousOn.mono (by simpa using hsub))
  · exact ⟨_, mem_ball_self hρpos, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)⟩
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨y, ⟨hys, hysrc⟩, rfl⟩ := hball hw
    rwa [(chartAt ℂ x).left_inv hysrc]
  · -- holomorphy of `H ∘ chart`
    rintro z ⟨w, hw, rfl⟩
    have hzsrc : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source :=
      (chartAt ℂ x).map_target (hsub hw)
    have htrans : AnalyticAt ℂ
        ((chartAt ℂ x) ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        (chartAt ℂ ((chartAt ℂ x).symm w) ((chartAt ℂ x).symm w)) :=
      transition_analyticAt (chartAt_mem_riemannAtlas _) he ⟨mem_chart_source _ _, hzsrc⟩
    have hfx : ((chartAt ℂ x) ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        (chartAt ℂ ((chartAt ℂ x).symm w) ((chartAt ℂ x).symm w)) = w := by
      simp only [Function.comp_apply,
        (chartAt ℂ ((chartAt ℂ x).symm w)).left_inv (mem_chart_source _ _)]
      exact (chartAt ℂ x).right_inv (hsub hw)
    have hH : AnalyticAt ℂ H (((chartAt ℂ x) ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        (chartAt ℂ ((chartAt ℂ x).symm w) ((chartAt ℂ x).symm w))) := by
      rw [hfx]; exact hHan w hw
    exact hH.comp htrans
  · -- the real part is `u`
    rintro z ⟨w, hw, rfl⟩
    have := hHre hw
    simpa [(chartAt ℂ x).right_inv (hsub hw)] using this

/-- Local rigidity: two conjugates near a point agree near that point up to an
imaginary constant; in particular a conjugate germ over a preconnected open `V`
extends to all of `V` once one conjugate exists on `V`. -/
theorem IsConjugate.eventuallyEq_add_const {u : X → ℝ} {F G : X → ℂ} {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hF : IsConjugate u F V) (hG : IsConjugate u G W)
    {y : X} (hyV : y ∈ V) (hyW : y ∈ W) :
    ∃ t : ℝ, F =ᶠ[𝓝 y] fun z => G z + t * I := by
  -- the difference read through the chart at `y`, on a small ball
  set e := chartAt ℂ y with he_def
  have he := chartAt_mem_riemannAtlas (X := X) y
  have hVWo : IsOpen (V ∩ W ∩ e.source) :=
    (hV.inter hW).inter e.open_source
  have hyVW : y ∈ V ∩ W ∩ e.source := ⟨⟨hyV, hyW⟩, mem_chart_source ℂ y⟩
  have himg : IsOpen (e '' (V ∩ W ∩ e.source)) :=
    e.isOpen_image_of_subset_source hVWo inter_subset_right
  obtain ⟨ρ, hρpos, hball⟩ := Metric.isOpen_iff.mp himg (e y) ⟨y, hyVW, rfl⟩
  have hsymm_mem : ∀ w ∈ ball (e y) ρ, e.symm w ∈ V ∩ W ∩ e.source := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hball hw
    rwa [e.left_inv hz.2]
  -- the difference is analytic with vanishing real part on the ball
  have hd : AnalyticOnNhd ℂ (fun w => F (e.symm w) - G (e.symm w)) (ball (e y) ρ) := by
    intro w hw
    have hzV : e.symm w ∈ V ∩ e.source :=
      ⟨(hsymm_mem w hw).1.1, (hsymm_mem w hw).2⟩
    have hzW : e.symm w ∈ W ∩ e.source :=
      ⟨(hsymm_mem w hw).1.2, (hsymm_mem w hw).2⟩
    have hwt : w ∈ e.target := by
      obtain ⟨z, hz, rfl⟩ := hball hw
      exact e.map_source hz.2
    have h1 : AnalyticAt ℂ (F ∘ e.symm) w := by
      have := hF.1.analyticAt_comp_symm hV he (x := e.symm w) ⟨hzV.1, hzV.2⟩
      rw [← he_def] at this
      rwa [e.right_inv hwt] at this
    have h2 : AnalyticAt ℂ (G ∘ e.symm) w := by
      have := hG.1.analyticAt_comp_symm hW he (x := e.symm w) ⟨hzW.1, hzW.2⟩
      rw [← he_def] at this
      rwa [e.right_inv hwt] at this
    exact h1.sub h2
  have hre : ∀ w ∈ ball (e y) ρ, (F (e.symm w) - G (e.symm w)).re = 0 := by
    intro w hw
    have hm := hsymm_mem w hw
    simp [Complex.sub_re, hF.2 _ hm.1.1, hG.2 _ hm.1.2]
  -- open mapping: the difference is constant on the ball
  obtain ⟨cst, hcst⟩ := hd.eq_const_of_re_eq_const hre isOpen_ball
    ⟨⟨_, mem_ball_self hρpos⟩, (convex_ball _ _).isPreconnected⟩
  refine ⟨cst.im, ?_⟩
  have hcre : cst.re = 0 := by
    have := hre _ (mem_ball_self hρpos)
    rw [hcst _ (mem_ball_self hρpos)] at this
    exact this
  -- transfer back through the chart
  have hmem : e.source ∩ e ⁻¹' ball (e y) ρ ∈ 𝓝 y := by
    refine (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).mem_nhds
      ⟨mem_chart_source ℂ y, mem_ball_self hρpos⟩
  filter_upwards [hmem] with z hz
  have h1 : F z - G z = cst := by
    have := hcst _ hz.2
    rwa [e.left_inv hz.1] at this
  have h2 : cst = cst.im * I := by
    rw [Complex.ext_iff]
    simp [hcre]
  rw [← sub_eq_iff_eq_add', ← h2] at *
  exact h1

/-- Adding an imaginary constant preserves conjugacy. -/
theorem IsConjugate.add_const_mul_I {u : X → ℝ} {F : X → ℂ} {V : Set X}
    (hF : IsConjugate u F V) (t : ℝ) : IsConjugate u (fun z => F z + t * I) V := by
  refine ⟨fun x hx => ?_, fun x hx => by simp [hF.2 x hx]⟩
  exact (hF.1 x hx).add analyticAt_const

/-- Conjugates restrict to subsets. -/
theorem IsConjugate.mono {u : X → ℝ} {F : X → ℂ} {V W : Set X} (hF : IsConjugate u F V)
    (hWV : W ⊆ V) : IsConjugate u F W :=
  ⟨hF.1.mono hWV, fun x hx => hF.2 x (hWV hx)⟩

/-- Rigidity: two conjugates on a preconnected open set differ by an imaginary
constant. -/
theorem IsConjugate.exists_sub_const {u : X → ℝ} {F G : X → ℂ} {V : Set X}
    (hV : IsOpen V) (hVc : IsPreconnected V) (hF : IsConjugate u F V)
    (hG : IsConjugate u G V) : ∃ t : ℝ, EqOn G (fun z => F z + t * I) V := by
  rcases V.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun z hz => absurd hz (notMem_empty z)⟩
  obtain ⟨t₀, ht₀⟩ := IsConjugate.eventuallyEq_add_const hV hV hG hF hx₀ hx₀
  exact ⟨t₀, HolomorphicOn.eqOn_of_eventuallyEq hG.1
    (IsConjugate.add_const_mul_I hF t₀).1 hV hVc hx₀ ht₀⟩

/-- A harmonic function that is locally constant near an accumulation of
constancy cannot avoid being constant: on a preconnected open set, if `u` is
locally constant near one point, it is constant. (Via conjugates and the
identity theorem for the chart derivative.) -/
theorem SurfaceHarmonicOn.eqOn_const_of_locallyConstant {u : X → ℝ} {s : Set X}
    (hu : SurfaceHarmonicOn u s) (hs : IsOpen s)
    (hsc : IsPreconnected s) {y : X} (hy : y ∈ s) (hloc : ∀ᶠ z in 𝓝 y, u z = u y) :
    EqOn u (fun _ => u y) s := by
  classical
  -- the locally-constant locus
  set A : Set X := {z | z ∈ s ∧ ∀ᶠ w in 𝓝 z, u w = u z} with hA
  have hyA : y ∈ A := ⟨hy, hloc⟩
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzs, hzloc⟩
    filter_upwards [hzloc.eventually_nhds, hs.mem_nhds hzs, hzloc] with w hw hws hwz
    exact ⟨hws, by filter_upwards [hw] with v hv; rw [hv, hwz]⟩
  -- closure step: a boundary point of `A` inside `s` lies in `A`, and in fact
  -- `u` is constant on a whole conjugate neighbourhood of it
  have hclosure : ∀ z ∈ s, z ∈ closure A → z ∈ A := by
    intro z hzs hzcl
    obtain ⟨V, F, hVo, hVc, hzV, hVs, hFconj⟩ := exists_conjugate hu hs hzs
    -- pick a point of `A` in `V`
    obtain ⟨a, haV, haA⟩ := mem_closure_iff.mp hzcl V hVo hzV
    -- near `a`, the constant `u a` is a conjugate of `u`
    have hWmem : {w | u w = u a} ∈ 𝓝 a := haA.2
    set W := V ∩ interior {w | u w = u a} with hW
    have hWo : IsOpen W := hVo.inter isOpen_interior
    have haW : a ∈ W := ⟨haV, mem_interior_iff_mem_nhds.mpr hWmem⟩
    have hGconj : IsConjugate u (fun _ => (u a : ℂ)) W := by
      refine ⟨fun x hx => analyticAt_const, fun x hx => ?_⟩
      have := interior_subset hx.2
      simp only [mem_setOf_eq] at this
      simp [this]
    -- rigidity: `F` is eventually constant at `a`, hence constant on `V`
    obtain ⟨t, ht⟩ := IsConjugate.eventuallyEq_add_const hVo hWo hFconj hGconj haV haW
    have hFconst : EqOn F (fun _ => (u a : ℂ) + t * I) V :=
      HolomorphicOn.eqOn_of_eventuallyEq hFconj.1
        (fun x hx => analyticAt_const) hVo hVc haV ht
    -- so `u` is constant on `V`, and `z ∈ A`
    have huV : ∀ w ∈ V, u w = u a := by
      intro w hw
      have h1 := hFconj.2 w hw
      rw [hFconst hw] at h1
      simpa using h1.symm
    refine ⟨hzs, ?_⟩
    filter_upwards [hVo.mem_nhds hzV] with w hw
    rw [huV w hw, huV z hzV]
  -- `A` is relatively clopen in preconnected `s`, hence `s ⊆ A`
  have hsub : s ⊆ A := by
    have hBopen : IsOpen (s \ closure A) := hs.sdiff isClosed_closure
    have hcover : s ⊆ A ∪ (s \ closure A) := by
      intro z hz
      by_cases hzA : z ∈ closure A
      · exact Or.inl (hclosure z hz hzA)
      · exact Or.inr ⟨hz, hzA⟩
    have hdisj : Disjoint A (s \ closure A) :=
      disjoint_sdiff_right.mono_left subset_closure
    rcases hsc.subset_or_subset hAopen hBopen hdisj hcover with h | h
    · exact h
    · exact absurd (h hy) fun hcon => hcon.2 (subset_closure hyA)
  -- a locally constant function on a preconnected set is constant
  have hCopen : IsOpen {z | z ∈ s ∧ u z = u y} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzs, hzu⟩
    filter_upwards [(hsub hzs).2, hs.mem_nhds hzs] with w hw hws
    exact ⟨hws, by rw [hw, hzu]⟩
  have hDopen : IsOpen {z | z ∈ s ∧ u z ≠ u y} := by
    have : {z | z ∈ s ∧ u z ≠ u y} = s ∩ u ⁻¹' {u y}ᶜ := by ext; simp
    rw [this]
    exact (hu.continuousOn hs).isOpen_inter_preimage hs isOpen_compl_singleton
  have hdisj : Disjoint {z | z ∈ s ∧ u z = u y} {z | z ∈ s ∧ u z ≠ u y} := by
    rw [Set.disjoint_left]
    rintro z ⟨_, h1⟩ ⟨_, h2⟩
    exact h2 h1
  have hcover : s ⊆ {z | z ∈ s ∧ u z = u y} ∪ {z | z ∈ s ∧ u z ≠ u y} := by
    intro z hz
    by_cases h : u z = u y
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  rcases hsc.subset_or_subset hCopen hDopen hdisj hcover with h | h
  · exact fun z hz => (h hz).2
  · exact absurd (h hy).2 (by simp)


variable (u : X → ℝ) (Y : Set X)

/-- The value of a germ at the base point of its filter (well defined because
every neighbourhood of `y` contains `y`). -/
noncomputable def germValue {y : X} (γ : Germ (𝓝 y) ℂ) : ℂ :=
  γ.liftOn (fun f => f y) fun _ _ h => h.self_of_nhds

@[simp] theorem germValue_coe {y : X} (F : X → ℂ) :
    germValue (F : Germ (𝓝 y) ℂ) = F y := rfl

/-- The set of points where two functions have the same germ is open. -/
theorem isOpen_eventuallyEq_nhds {F G : X → ℂ} : IsOpen {x : X | F =ᶠ[𝓝 x] G} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact eventually_eventuallyEq_nhds.mpr hx

/-- The étale space of conjugate germs of `u` over `Y`: pairs of a point
`y ∈ Y` and the germ at `y` of a conjugate of `u` defined on some open
neighbourhood inside `Y`. -/
def ConjEtale : Type _ :=
  {p : Σ y : X, Germ (𝓝 y) ℂ // p.1 ∈ Y ∧
    ∃ V F, IsOpen V ∧ p.1 ∈ V ∧ V ⊆ Y ∧ IsConjugate u F V ∧ p.2 = (F : Germ (𝓝 p.1) ℂ)}

namespace ConjEtale

variable {u Y}

/-- The sheet of a conjugate `F` over `V`. -/
def sheet (V : Set X) (F : X → ℂ) : Set (ConjEtale u Y) :=
  {q | q.1.1 ∈ V ∧ q.1.2 = (F : Germ (𝓝 q.1.1) ℂ)}

variable (u Y) in
/-- Basic open sets: sheets of conjugates over preconnected opens inside `Y`. -/
def basicSets : Set (Set (ConjEtale u Y)) :=
  {S | ∃ V F, IsOpen V ∧ IsPreconnected V ∧ V ⊆ Y ∧ IsConjugate u F V ∧ S = sheet V F}

instance : TopologicalSpace (ConjEtale u Y) :=
  TopologicalSpace.generateFrom (basicSets u Y)

/-- The projection to the surface. -/
def proj (q : ConjEtale u Y) : X := q.1.1

/-- The evaluation map. -/
noncomputable def eval (q : ConjEtale u Y) : ℂ := germValue q.1.2

section Etale

variable (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y)

/-- Membership in a sheet, unfolded. -/
theorem mem_sheet_iff {V : Set X} {F : X → ℂ} {q : ConjEtale u Y} :
    q ∈ sheet V F ↔ q.1.1 ∈ V ∧ q.1.2 = (F : Germ (𝓝 q.1.1) ℂ) := Iff.rfl

/-- Basic sets are open. -/
theorem isOpen_of_mem_basicSets {S : Set (ConjEtale u Y)} (hS : S ∈ basicSets u Y) :
    IsOpen S :=
  TopologicalSpace.isOpen_generateFrom_of_mem hS

/-- The sheets form a topological basis. -/
theorem isTopologicalBasis_basicSets :
    TopologicalSpace.IsTopologicalBasis (basicSets u Y) := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  refine ⟨?_, ?_, rfl⟩
  · -- intersections refine
    rintro S₁ ⟨V₁, F₁, hV₁o, _, hV₁Y, hF₁, rfl⟩ S₂ ⟨V₂, F₂, hV₂o, _, hV₂Y, hF₂, rfl⟩
      q ⟨⟨hy₁, hg₁⟩, ⟨hy₂, hg₂⟩⟩
    have hev : F₁ =ᶠ[𝓝 q.1.1] F₂ := Filter.Germ.coe_eq.mp (hg₁.symm.trans hg₂)
    have hOopen : IsOpen {x : X | F₁ =ᶠ[𝓝 x] F₂} := isOpen_eventuallyEq_nhds
    set W := connectedComponentIn (V₁ ∩ V₂ ∩ {x : X | F₁ =ᶠ[𝓝 x] F₂}) q.1.1 with hW
    have hWsub : W ⊆ V₁ ∩ V₂ ∩ {x : X | F₁ =ᶠ[𝓝 x] F₂} := connectedComponentIn_subset _ _
    have hWo : IsOpen W := ((hV₁o.inter hV₂o).inter hOopen).connectedComponentIn
    have hqW : q.1.1 ∈ W := mem_connectedComponentIn ⟨⟨hy₁, hy₂⟩, hev⟩
    refine ⟨sheet W F₁, ⟨W, F₁, hWo, isPreconnected_connectedComponentIn,
      fun z hz => hV₁Y (hWsub hz).1.1, hF₁.mono fun z hz => (hWsub hz).1.1, rfl⟩,
      ⟨hqW, hg₁⟩, ?_⟩
    rintro p ⟨hpW, hpF⟩
    have hp12 := hWsub hpW
    refine ⟨⟨hp12.1.1, hpF⟩, hp12.1.2, ?_⟩
    rw [hpF]
    exact Filter.Germ.coe_eq.mpr hp12.2
  · -- coverage
    rw [sUnion_eq_univ_iff]
    intro q
    obtain ⟨hqY, V, F, hVo, hqV, hVY, hF, hgerm⟩ := q.2
    set W := connectedComponentIn V q.1.1 with hW
    have hWsub : W ⊆ V := connectedComponentIn_subset _ _
    exact ⟨sheet W F, ⟨W, F, hVo.connectedComponentIn, isPreconnected_connectedComponentIn,
      hWsub.trans hVY, hF.mono hWsub, rfl⟩, mem_connectedComponentIn hqV, hgerm⟩

theorem continuous_proj : Continuous (proj (u := u) (Y := Y)) := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  rw [continuous_def]
  intro O hO
  rw [(isTopologicalBasis_basicSets (u := u) (Y := Y)).isOpen_iff]
  intro q hq
  obtain ⟨hqY, V, F, hVo, hqV, hVY, hF, hgerm⟩ := q.2
  have hsub : connectedComponentIn (V ∩ O) q.1.1 ⊆ V ∩ O := connectedComponentIn_subset _ _
  refine ⟨sheet (connectedComponentIn (V ∩ O) q.1.1) F,
    ⟨_, F, (hVo.inter hO).connectedComponentIn, isPreconnected_connectedComponentIn,
      fun z hz => hVY (hsub hz).1, hF.mono fun z hz => (hsub hz).1, rfl⟩,
    ⟨mem_connectedComponentIn ⟨hqV, hq⟩, hgerm⟩, ?_⟩
  rintro p ⟨hpW, _⟩
  exact (hsub hpW).2

theorem isOpenMap_proj : IsOpenMap (proj (u := u) (Y := Y)) := by
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨q, hqO, rfl⟩
  obtain ⟨S, hSb, hqS, hSO⟩ :=
    (isTopologicalBasis_basicSets (u := u) (Y := Y)).isOpen_iff.mp hO q hqO
  obtain ⟨V, F, hVo, hVc, hVY, hF, rfl⟩ := hSb
  have himg : V ⊆ proj (u := u) (Y := Y) '' O := fun z hz =>
    ⟨⟨⟨z, (F : Germ (𝓝 z) ℂ)⟩, hVY hz, V, F, hVo, hz, hVY, hF, rfl⟩, hSO ⟨hz, rfl⟩, rfl⟩
  exact Filter.mem_of_superset (hVo.mem_nhds hqS.1) himg

/-- `proj` restricted to a sheet is injective (germs of a single `F`). -/
theorem injOn_proj_sheet {V : Set X} {F : X → ℂ} :
    InjOn (proj (u := u) (Y := Y)) (sheet V F) := by
  rintro ⟨⟨y, γ⟩, hq⟩ hmem ⟨⟨y', γ'⟩, hq'⟩ hmem' h
  have hyy : y = y' := h
  subst hyy
  obtain ⟨-, hγ⟩ := hmem
  obtain ⟨-, hγ'⟩ := hmem'
  simp only at hγ hγ'
  subst hγ
  subst hγ'
  rfl

/-- Hausdorffness of the étale space (identity theorem). -/
theorem t2Space [T2Space X] : T2Space (ConjEtale u Y) := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  constructor
  intro q₁ q₂ hne
  by_cases hbase : proj q₁ = proj q₂
  · -- same base point: separate the germs by sheets over a common
    -- preconnected neighbourhood, disjoint by the identity theorem
    obtain ⟨hY₁, V₁, F₁, hV₁o, hq₁V, hV₁Y, hF₁, hg₁⟩ := q₁.2
    obtain ⟨hY₂, V₂, F₂, hV₂o, hq₂V, hV₂Y, hF₂, hg₂⟩ := q₂.2
    set W := connectedComponentIn (V₁ ∩ V₂) (proj q₁) with hWdef
    have hWo : IsOpen W := (hV₁o.inter hV₂o).connectedComponentIn
    have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
    have hWsub : W ⊆ V₁ ∩ V₂ := connectedComponentIn_subset _ _
    have hq₂V₂ : proj q₁ ∈ V₂ := by rw [hbase]; exact hq₂V
    have hyW : proj q₁ ∈ W := mem_connectedComponentIn ⟨hq₁V, hq₂V₂⟩
    have hyW₂ : q₂.1.1 ∈ W := by
      show proj q₂ ∈ W
      rw [← hbase]
      exact hyW
    have hWY : W ⊆ Y := fun z hz => hV₁Y (hWsub hz).1
    have hb₁ : sheet W F₁ ∈ basicSets u Y :=
      ⟨W, F₁, hWo, hWc, hWY, hF₁.mono fun z hz => (hWsub hz).1, rfl⟩
    have hb₂ : sheet W F₂ ∈ basicSets u Y :=
      ⟨W, F₂, hWo, hWc, hWY, hF₂.mono fun z hz => (hWsub hz).2, rfl⟩
    refine ⟨sheet W F₁, sheet W F₂, isOpen_of_mem_basicSets hb₁, isOpen_of_mem_basicSets hb₂,
      ⟨hyW, hg₁⟩, ⟨hyW₂, hg₂⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro p ⟨hpW, hp₁⟩ ⟨-, hp₂⟩
    -- the two conjugates agree near `p`, hence on `W`, hence at the base point
    have hev : F₁ =ᶠ[𝓝 p.1.1] F₂ := Filter.Germ.coe_eq.mp (hp₁.symm.trans hp₂)
    have heqOn : EqOn F₁ F₂ W :=
      HolomorphicOn.eqOn_of_eventuallyEq (hF₁.1.mono fun z hz => (hWsub hz).1)
        (hF₂.1.mono fun z hz => (hWsub hz).2) hWo hWc hpW hev
    have hyev : F₁ =ᶠ[𝓝 (proj q₁)] F₂ := by
      filter_upwards [hWo.mem_nhds hyW] with z hz
      exact heqOn hz
    have hyev₂ : F₁ =ᶠ[𝓝 (proj q₂)] F₂ := by
      rw [← hbase]
      exact hyev
    have hg₂' : q₂.1.2 = (F₁ : Germ (𝓝 q₂.1.1) ℂ) :=
      hg₂.trans (Filter.Germ.coe_eq.mpr hyev₂).symm
    exact absurd (injOn_proj_sheet ⟨hyW, hg₁⟩ ⟨hyW₂, hg₂'⟩ hbase) hne
  · obtain ⟨O₁, O₂, hO₁, hO₂, h₁, h₂, hdisj⟩ := t2_separation hbase
    exact ⟨proj ⁻¹' O₁, proj ⁻¹' O₂, hO₁.preimage continuous_proj,
      hO₂.preimage continuous_proj, h₁, h₂, hdisj.preimage _⟩

/-- Every point of `Y` has a conjugate germ over it. -/
theorem exists_mk (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y) {y : X} (hy : y ∈ Y) :
    ∃ q : ConjEtale u Y, proj q = y := by
  obtain ⟨V, F, hVo, hVc, hyV, hVY, hF⟩ := exists_conjugate hu hY hy
  exact ⟨⟨⟨y, (F : Germ (𝓝 y) ℂ)⟩, hy, V, F, hVo, hyV, hVY, hF, rfl⟩, rfl⟩

/-- Every étale point lies on a basic sheet. -/
private theorem exists_basic_sheet_mem (q : ConjEtale u Y) :
    ∃ V F, IsOpen V ∧ IsPreconnected V ∧ V ⊆ Y ∧ IsConjugate u F V ∧ q ∈ sheet V F := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  obtain ⟨hqY, V, F, hVo, hqV, hVY, hF, hgerm⟩ := q.2
  exact ⟨connectedComponentIn V q.1.1, F, hVo.connectedComponentIn,
    isPreconnected_connectedComponentIn, (connectedComponentIn_subset _ _).trans hVY,
    hF.mono (connectedComponentIn_subset _ _), mem_connectedComponentIn hqV, hgerm⟩

/-- The tautological section of a basic sheet. -/
private def sheetSec {V : Set X} {F : X → ℂ} (hVo : IsOpen V) (hVY : V ⊆ Y)
    (hF : IsConjugate u F V) : V → ConjEtale u Y := fun z =>
  ⟨⟨z.1, (F : Germ (𝓝 z.1) ℂ)⟩, hVY z.2, V, F, hVo, z.2, hVY, hF, rfl⟩

private theorem sheetSec_image {V : Set X} {F : X → ℂ} (hVo : IsOpen V) (hVY : V ⊆ Y)
    (hF : IsConjugate u F V) (O : Set X) :
    sheetSec hVo hVY hF '' (Subtype.val ⁻¹' O) = proj ⁻¹' O ∩ sheet V F := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z.2, rfl⟩
  · rintro ⟨hqO, hqV, hqF⟩
    refine ⟨⟨q.1.1, hqV⟩, hqO, ?_⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq hqF.symm)

private theorem continuous_sheetSec {V : Set X} {F : X → ℂ} (hVo : IsOpen V) (hVY : V ⊆ Y)
    (hF : IsConjugate u F V) : Continuous (sheetSec hVo hVY hF) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro S ⟨W, G, hWo, hWc, hWY, hG, rfl⟩
  have heq : sheetSec hVo hVY hF ⁻¹' sheet W G
      = Subtype.val ⁻¹' (W ∩ {x : X | F =ᶠ[𝓝 x] G}) := by
    ext z
    simp only [sheetSec, mem_preimage, sheet, mem_setOf_eq, mem_inter_iff]
    exact and_congr Iff.rfl Filter.Germ.coe_eq
  rw [heq]
  exact (hWo.inter isOpen_eventuallyEq_nhds).preimage continuous_subtype_val

private theorem sheetSec_image_mem_nhds {W : Set X} {G : X → ℂ} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hWY : W ⊆ Y) (hG : IsConjugate u G W) {q : ConjEtale u Y}
    (hq : q ∈ sheet W G) {K : Set X} (hK : K ∈ 𝓝 q.1.1) :
    sheetSec hWo hWY hG '' (Subtype.val ⁻¹' K) ∈ 𝓝 q := by
  rw [sheetSec_image]
  refine Filter.mem_of_superset ?_ (inter_subset_inter_left _ (preimage_mono interior_subset))
  have hopen : IsOpen (proj (u := u) (Y := Y) ⁻¹' interior K ∩ sheet W G) :=
    (isOpen_interior.preimage continuous_proj).inter
      (isOpen_of_mem_basicSets ⟨W, G, hWo, hWc, hWY, hG, rfl⟩)
  exact hopen.mem_nhds ⟨mem_interior_iff_mem_nhds.mpr hK, hq⟩

/-- The étale space inherits the local properties needed by Poincaré–Volterra:
local compactness, local connectedness, local second countability. -/
theorem locallyCompactSpace [T2Space X] (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y) :
    LocallyCompactSpace (ConjEtale u Y) := by
  haveI : LocallyCompactSpace X := Rado.locallyCompactSpace
  constructor
  intro q N hN
  obtain ⟨S, hSb, hqS, hSN⟩ :=
    (isTopologicalBasis_basicSets (u := u) (Y := Y)).mem_nhds_iff.mp hN
  obtain ⟨W, G, hWo, hWc, hWY, hG, rfl⟩ := hSb
  obtain ⟨K, hKn, hKW, hKc⟩ := local_compact_nhds (hWo.mem_nhds hqS.1)
  refine ⟨sheetSec hWo hWY hG '' (Subtype.val ⁻¹' K),
    sheetSec_image_mem_nhds hWo hWc hWY hG hqS hKn, ?_, ?_⟩
  · rw [sheetSec_image]
    exact inter_subset_right.trans hSN
  · have hKcomp : IsCompact (Subtype.val ⁻¹' K : Set W) := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Set.image_preimage_eq_inter_range,
        Subtype.range_coe, inter_eq_self_of_subset_left hKW]
      exact hKc
    exact hKcomp.image (continuous_sheetSec hWo hWY hG)

theorem locallyConnectedSpace [T2Space X] (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y) :
    LocallyConnectedSpace (ConjEtale u Y) := by
  haveI hX : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro q U hU
  obtain ⟨S, hSb, hqS, hSN⟩ :=
    (isTopologicalBasis_basicSets (u := u) (Y := Y)).mem_nhds_iff.mp hU
  obtain ⟨W, G, hWo, hWc, hWY, hG, rfl⟩ := hSb
  obtain ⟨V', hV'n, hV'c, hV'W⟩ :=
    locallyConnectedSpace_iff_connected_subsets.mp hX q.1.1 W (hWo.mem_nhds hqS.1)
  refine ⟨sheetSec hWo hWY hG '' (Subtype.val ⁻¹' V'),
    sheetSec_image_mem_nhds hWo hWc hWY hG hqS hV'n, ?_, ?_⟩
  · haveI := Subtype.preconnectedSpace hV'c
    have hcont : Continuous ((sheetSec hWo hWY hG) ∘ Set.inclusion hV'W) :=
      (continuous_sheetSec hWo hWY hG).comp (continuous_inclusion hV'W)
    have hrange : range ((sheetSec hWo hWY hG) ∘ Set.inclusion hV'W)
        = sheetSec hWo hWY hG '' (Subtype.val ⁻¹' V') := by
      rw [range_comp, Set.range_inclusion]
      rfl
    rw [← hrange]
    exact isPreconnected_range hcont
  · rw [sheetSec_image]
    exact inter_subset_right.trans hSN

/-- A sheet over a second-countable base is second countable: the restricted
projection is an open embedding into `↥W`. -/
private theorem secondCountable_sheet {W : Set X} {F : X → ℂ} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hWY : W ⊆ Y) (hF : IsConjugate u F W)
    (hWsc : SecondCountableTopology W) :
    SecondCountableTopology (sheet (u := u) (Y := Y) W F) := by
  haveI := hWsc
  have hSb : sheet W F ∈ basicSets u Y := ⟨W, F, hWo, hWc, hWY, hF, rfl⟩
  let ρ : {p : ConjEtale u Y // p ∈ sheet W F} → {z : X // z ∈ W} :=
    fun p => ⟨proj p.1, p.2.1⟩
  have hρcont : Continuous ρ :=
    Continuous.subtype_mk (continuous_proj.comp continuous_subtype_val) _
  have hρinj : Function.Injective ρ := by
    intro p₁ p₂ h
    exact Subtype.ext (injOn_proj_sheet p₁.2 p₂.2 (congrArg Subtype.val h))
  have hρopen : IsOpenMap ρ := by
    intro T hT
    obtain ⟨T', hT', rfl⟩ := isOpen_induced_iff.mp hT
    have himg : ρ '' (Subtype.val ⁻¹' T')
        = Subtype.val ⁻¹' (proj (u := u) (Y := Y) '' (T' ∩ sheet W F)) := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, ⟨hp, p.2⟩, rfl⟩
      · rintro ⟨p, ⟨hpT, hpS⟩, hpz⟩
        exact ⟨⟨p, hpS⟩, hpT, Subtype.ext hpz⟩
    rw [himg]
    exact (isOpenMap_proj _ (hT'.inter (isOpen_of_mem_basicSets hSb))).preimage
      continuous_subtype_val
  exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hρcont hρinj
    hρopen).isEmbedding.secondCountableTopology

theorem locally_secondCountable [T2Space X] (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y)
    (q : ConjEtale u Y) :
    ∃ U : Set (ConjEtale u Y), q ∈ U ∧ IsOpen U ∧ SecondCountableTopology U := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  -- a basic sheet through `q` refined into a second-countable chart piece
  obtain ⟨V, F, hVo, hVc, hVY, hF, hqV⟩ := exists_basic_sheet_mem q
  obtain ⟨U₀, hqU₀, hU₀o, hU₀sc⟩ := Rado.locally_secondCountable (X := X) q.1.1
  set W := connectedComponentIn (V ∩ U₀) q.1.1 with hWdef
  have hWsub : W ⊆ V ∩ U₀ := connectedComponentIn_subset _ _
  have hWo : IsOpen W := (hVo.inter hU₀o).connectedComponentIn
  have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
  have hWY : W ⊆ Y := fun z hz => hVY (hWsub hz).1
  have hqW : q.1.1 ∈ W := mem_connectedComponentIn ⟨hqV.1, hqU₀⟩
  have hGW : IsConjugate u F W := hF.mono fun z hz => (hWsub hz).1
  have hSb : sheet W F ∈ basicSets u Y := ⟨W, F, hWo, hWc, hWY, hGW, rfl⟩
  -- second countability of `↥W` (hereditary from `↥U₀`)
  have hWsc : SecondCountableTopology W := by
    haveI := hU₀sc
    exact (Topology.IsEmbedding.inclusion fun z hz => (hWsub hz).2).secondCountableTopology
  exact ⟨sheet W F, ⟨hqW, hqV.2⟩, isOpen_of_mem_basicSets hSb,
    secondCountable_sheet hWo hWc hWY hGW hWsc⟩

theorem continuous_eval (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y) :
    Continuous (eval (u := u) (Y := Y)) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨V, F, hVo, hVc, hVY, hF, hqV⟩ := exists_basic_sheet_mem q
  have hopen : IsOpen (sheet V F : Set (ConjEtale u Y)) :=
    isOpen_of_mem_basicSets ⟨V, F, hVo, hVc, hVY, hF, rfl⟩
  have hproj : ContinuousAt (proj (u := u) (Y := Y)) q := continuous_proj.continuousAt
  have hFc : ContinuousAt F (proj (u := u) (Y := Y) q) :=
    hF.1.continuousOn.continuousAt (hVo.mem_nhds hqV.1)
  have h1 : ContinuousAt (F ∘ proj (u := u) (Y := Y)) q := hFc.comp hproj
  refine h1.congr ?_
  filter_upwards [hopen.mem_nhds hqV] with p hp
  simp only [Function.comp_apply, eval, hp.2, germValue_coe]
  rfl

/-- Discreteness of the fibers of `eval`: if evaluation were constant near a
germ, `u` would be locally constant near the base point, hence constant on all
of connected `Y` (`SurfaceHarmonicOn.eqOn_const_of_locallyConstant`) —
contradicting nonconstancy. -/
theorem eval_discrete_fibers [T2Space X] (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y)
    (hYc : IsPreconnected Y) {x₀ x₁ : X} (h₀ : x₀ ∈ Y) (h₁ : x₁ ∈ Y)
    (hne : u x₀ ≠ u x₁) (q : ConjEtale u Y) :
    ∃ U ∈ 𝓝 q, ∀ w ∈ U, eval w = eval q → w = q := by
  obtain ⟨V, F, hVo, hVc, hVY, hF, hqV⟩ := exists_basic_sheet_mem q
  set y := q.1.1 with hy_def
  have hyV : y ∈ V := hqV.1
  have hevalq : eval q = F y := by
    rw [hy_def]
    simp only [eval, hqV.2, germValue_coe]
  -- the chart representative of `F` is analytic at the base point
  have hFan : AnalyticAt ℂ (F ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hF.1 y hyV
  rcases hFan.eventually_eq_or_eventually_ne analyticAt_const (g := fun _ => F y) with hcase | hcase
  · -- `F` locally constant near `y` forces `u` locally constant, contradiction
    exfalso
    have htend : Filter.Tendsto (chartAt ℂ y) (𝓝 y) (𝓝 (chartAt ℂ y y)) :=
      (chartAt ℂ y).continuousAt (mem_chart_source ℂ y)
    have hFev : ∀ᶠ w in 𝓝 y, F w = F y := by
      filter_upwards [htend.eventually hcase,
        (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)] with w hw hwsrc
      rwa [Function.comp_apply, (chartAt ℂ y).left_inv hwsrc] at hw
    have huev : ∀ᶠ w in 𝓝 y, u w = u y := by
      filter_upwards [hFev, hVo.mem_nhds hyV] with w hw hwV
      rw [← hF.2 w hwV, ← hF.2 y hyV, hw]
    have hconst := hu.eqOn_const_of_locallyConstant hY hYc (hVY hyV) huev
    exact hne ((hconst h₀).trans (hconst h₁).symm)
  · -- isolated `F y`-points: the sheet is locally injective for `eval`
    have htend : Filter.Tendsto (chartAt ℂ y) (𝓝 y) (𝓝 (chartAt ℂ y y)) :=
      (chartAt ℂ y).continuousAt (mem_chart_source ℂ y)
    -- transfer the punctured-neighbourhood condition through the chart
    have hFev : ∀ᶠ w in 𝓝 y, w ≠ y → F w ≠ F y := by
      have h1 : ∀ᶠ z in 𝓝 (chartAt ℂ y y), z ≠ chartAt ℂ y y →
          (F ∘ (chartAt ℂ y).symm) z ≠ F y := by
        rw [eventually_nhdsWithin_iff] at hcase
        exact hcase.mono fun z hz hne => hz hne
      filter_upwards [htend.eventually h1,
        (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)] with w hw hwsrc hwne
      have hzne : chartAt ℂ y w ≠ chartAt ℂ y y := fun hcon =>
        hwne ((chartAt ℂ y).injOn hwsrc (mem_chart_source ℂ y) hcon)
      have := hw hzne
      rwa [Function.comp_apply, (chartAt ℂ y).left_inv hwsrc] at this
    obtain ⟨N, hNprop, hNo, hyN⟩ := eventually_nhds_iff.mp hFev
    have hSopen : IsOpen (sheet V F : Set (ConjEtale u Y)) :=
      isOpen_of_mem_basicSets ⟨V, F, hVo, hVc, hVY, hF, rfl⟩
    refine ⟨proj ⁻¹' N ∩ sheet V F,
      ((hNo.preimage continuous_proj).inter hSopen).mem_nhds ⟨hyN, hqV⟩, ?_⟩
    rintro w ⟨hwN, hwS⟩ heval
    have hevalw : eval w = F (proj w) := by
      simp only [eval, proj, hwS.2, germValue_coe]
    have hwy : proj w = y := by
      by_contra hcon
      exact hNprop _ hwN hcon (by rw [← hevalw, heval, hevalq])
    exact injOn_proj_sheet hwS hqV hwy

/-- Over a connected `Y`, every connected component of the étale space projects
onto all of `Y` (openness and closedness of the image of a component, via local
triviality of `proj` over small preconnected chart neighbourhoods). -/
theorem surjOn_proj_connectedComponent [T2Space X] (hu : SurfaceHarmonicOn u Y)
    (hY : IsOpen Y) (hYc : IsPreconnected Y) (q₀ : ConjEtale u Y) :
    SurjOn (proj (u := u) (Y := Y)) (connectedComponent q₀) Y := by
  haveI : LocallyConnectedSpace (ConjEtale u Y) := locallyConnectedSpace hu hY
  set S := proj (u := u) (Y := Y) '' connectedComponent q₀ with hS_def
  have hSopen : IsOpen S := isOpenMap_proj _ isOpen_connectedComponent
  -- the image is relatively closed in `Y`: any closure point in `Y` lies on a
  -- sheet over a preconnected trivializing neighbourhood that meets the
  -- component, hence is contained in it
  have key : ∀ y ∈ Y, y ∈ closure S → y ∈ S := by
    intro y hyY hycl
    obtain ⟨V, F, hVo, hVc, hyV, hVY, hF⟩ := exists_conjugate hu hY hyY
    obtain ⟨y', hy'V, hy'S⟩ := mem_closure_iff.mp hycl V hVo hyV
    obtain ⟨q', hq'C, hq'proj⟩ := hy'S
    have hq'V : proj q' ∈ V := by rw [hq'proj]; exact hy'V
    -- local triviality: `q'` lies on a sheet over `V`
    obtain ⟨hq'Y, W, G, hWo, hq'W, hWY, hG, hgerm⟩ := q'.2
    obtain ⟨s, hs⟩ := IsConjugate.eventuallyEq_add_const hWo hVo hG hF hq'W hq'V
    have hFs : IsConjugate u (fun z => F z + s * I) V := hF.add_const_mul_I s
    have hq'sheet : q' ∈ sheet V (fun z => F z + s * I) := by
      refine ⟨hq'V, ?_⟩
      rw [hgerm]
      exact Filter.Germ.coe_eq.mpr hs
    -- the sheet is preconnected (image of the continuous section)
    have hsheet_conn : IsPreconnected (sheet (u := u) (Y := Y) V (fun z => F z + s * I)) := by
      haveI := Subtype.preconnectedSpace hVc
      have hrange : range (sheetSec hVo hVY hFs) = sheet V (fun z => F z + s * I) := by
        rw [← image_univ]
        have h1 : (univ : Set V) = Subtype.val ⁻¹' V := by
          ext z
          simp [z.2]
        rw [h1, sheetSec_image]
        ext p
        exact ⟨fun hp => hp.2, fun hp => ⟨hp.1, hp⟩⟩
      rw [← hrange]
      exact isPreconnected_range (continuous_sheetSec hVo hVY hFs)
    have hsub : sheet (u := u) (Y := Y) V (fun z => F z + s * I) ⊆ connectedComponent q₀ := by
      have h1 := hsheet_conn.subset_connectedComponent hq'sheet
      rwa [← connectedComponent_eq hq'C] at h1
    exact ⟨sheetSec hVo hVY hFs ⟨y, hyV⟩, hsub ⟨hyV, rfl⟩, rfl⟩
  -- clopen argument on the preconnected `Y`
  have hBopen : IsOpen (Y \ closure S) := hY.sdiff isClosed_closure
  have hcover : Y ⊆ S ∪ (Y \ closure S) := by
    intro y hy
    by_cases h : y ∈ closure S
    · exact Or.inl (key y hy h)
    · exact Or.inr ⟨hy, h⟩
  have hdisj : Disjoint S (Y \ closure S) := disjoint_sdiff_right.mono_left subset_closure
  rcases hYc.subset_or_subset hSopen hBopen hdisj hcover with h | h
  · exact fun y hy => h hy
  · exfalso
    have h1 : proj q₀ ∈ Y := q₀.2.1
    have h2 : proj q₀ ∈ S := ⟨q₀, mem_connectedComponent, rfl⟩
    exact (h h1).2 (subset_closure h2)

end Etale

end ConjEtale

/-! ## Assembly -/

section Assembly

variable [T2Space X] [ConnectedSpace X]

/-- Some maximal-atlas chart has target containing the standard configuration
ball (affine renormalization of any chart,
`Rado.affine_trans_mem_riemannAtlas`). -/
theorem exists_config_chart [Nonempty X] :
    ∃ e ∈ riemannAtlas X, ball (0 : ℂ) 8 ⊆ e.target := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have he₀ := chartAt_mem_riemannAtlas x₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (chartAt ℂ x₀).open_target _
    ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  have hρC : ((ρ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have ha : (8 / (ρ:ℂ)) ≠ 0 := div_ne_zero (by norm_num) hρC
  obtain ⟨e', he', hsrc, hval⟩ := affine_trans_mem_riemannAtlas he₀ (a := 8/(ρ:ℂ))
    (b := -(8/(ρ:ℂ)) * (chartAt ℂ x₀ x₀)) ha
  refine ⟨e', he', ?_⟩
  intro w hw
  set z := chartAt ℂ x₀ x₀ + ((ρ:ℂ)/8) * w with hz
  have hzball : z ∈ ball (chartAt ℂ x₀ x₀) ρ := by
    rw [mem_ball, dist_eq_norm]
    have hzz : z - chartAt ℂ x₀ x₀ = ((ρ:ℂ)/8) * w := by rw [hz]; ring
    rw [hzz, norm_mul]
    have h1 : ‖((ρ:ℂ)/8)‖ = ρ/8 := by
      rw [norm_div]
      simp [abs_of_pos hρ]
    rw [h1]
    have hw8 : ‖w‖ < 8 := by rwa [mem_ball, dist_zero_right] at hw
    calc ρ/8 * ‖w‖ < ρ/8 * 8 := by
          exact mul_lt_mul_of_pos_left hw8 (by positivity)
      _ = ρ := by field_simp
  have hzt : z ∈ (chartAt ℂ x₀).target := hball hzball
  have hxs : (chartAt ℂ x₀).symm z ∈ (chartAt ℂ x₀).source := (chartAt ℂ x₀).map_target hzt
  have hval' := hval _ hxs
  rw [(chartAt ℂ x₀).right_inv hzt] at hval'
  have hwz : e' ((chartAt ℂ x₀).symm z) = w := by
    rw [hval', hz]
    field_simp
    ring
  have hmem : (chartAt ℂ x₀).symm z ∈ e'.source := by rw [hsrc]; exact hxs
  rw [← hwz]
  exact e'.map_source hmem

/-- Transfer of local second countability to an open subspace. -/
theorem locally_secondCountable_subtype {Z : Type*} [TopologicalSpace Z] {C : Set Z}
    (hC : IsOpen C) (h : ∀ z ∈ C, ∃ U : Set Z, z ∈ U ∧ IsOpen U ∧ SecondCountableTopology U)
    (q : C) : ∃ W : Set C, q ∈ W ∧ IsOpen W ∧ SecondCountableTopology W := by
  obtain ⟨U, hqU, hUo, hUsc⟩ := h q.1 q.2
  refine ⟨Subtype.val ⁻¹' U, hqU, hUo.preimage continuous_subtype_val, ?_⟩
  haveI := hUsc
  exact (Topology.IsEmbedding.subtypeVal.restrictPreimage U).secondCountableTopology

/-- The heart of the proof: `Y = configY e` is second countable, via Perron,
the étale space of conjugate germs, and Poincaré–Volterra. -/
theorem secondCountable_configY {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) (hb : ball (0 : ℂ) 8 ⊆ e.target) :
    SecondCountableTopology (configY e) := by
  classical
  set Y : Set X := configY e with hY_def
  have hYo : IsOpen Y := isOpen_configY he hb
  have hYc : IsPreconnected Y := (isConnected_configY he hb).isPreconnected
  set u : X → ℝ := perronSup (configFamily e) with hu_def
  have hu : SurfaceHarmonicOn u Y :=
    (isPerronFamily_configFamily he hb).surfaceHarmonicOn_perronSup hYo
  -- the two witness points and nonconstancy of the Perron envelope
  obtain ⟨hwp, hwm⟩ := witness_mem_configY he hb
  have hne : u (e.symm (-4 + (2 : ℂ) ^ ((1 : ℂ) / 4)))
      ≠ u (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) := by
    have h1 := perronSup_le_witness he hb
    have h2 := perronSup_ge_witness he hb
    rw [← hu_def] at h1 h2
    intro hcon
    rw [hcon] at h1
    linarith
  -- ambient instances
  haveI : LocallyCompactSpace X := Rado.locallyCompactSpace
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  haveI : T2Space (ConjEtale u Y) := ConjEtale.t2Space
  haveI : LocallyCompactSpace (ConjEtale u Y) := ConjEtale.locallyCompactSpace hu hYo
  haveI : LocallyConnectedSpace (ConjEtale u Y) := ConjEtale.locallyConnectedSpace hu hYo
  -- a germ over the witness point and its connected component
  obtain ⟨q₀, hq₀⟩ := ConjEtale.exists_mk hu hYo hwm
  set C : Set (ConjEtale u Y) := connectedComponent q₀ with hC_def
  have hCopen : IsOpen C := isOpen_connectedComponent
  haveI : ConnectedSpace C := Subtype.connectedSpace isConnected_connectedComponent
  haveI : LocallyCompactSpace C := hCopen.locallyCompactSpace
  haveI : LocallyConnectedSpace C := hCopen.locallyConnectedSpace
  -- Poincaré–Volterra for the evaluation on the component
  haveI hCsc : SecondCountableTopology C := by
    refine poincare_volterra
      (locally_secondCountable_subtype hCopen fun z _ =>
        ConjEtale.locally_secondCountable hu hYo z)
      (f := fun q : C => ConjEtale.eval q.1)
      ((ConjEtale.continuous_eval hu hYo).comp continuous_subtype_val) ?_
    intro q
    obtain ⟨U, hU, hUdisc⟩ := ConjEtale.eval_discrete_fibers hu hYo hYc hwm hwp hne q.1
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
    intro w hw heval
    exact Subtype.ext (hUdisc w.1 hw heval)
  -- descend along the restricted projection
  have hCY : ∀ q : C, ConjEtale.proj q.1 ∈ Y := fun q => q.1.2.1
  set g : C → Y := fun q => ⟨ConjEtale.proj q.1, hCY q⟩ with hg_def
  have hgcont : Continuous g :=
    Continuous.subtype_mk
      ((ConjEtale.continuous_proj).comp continuous_subtype_val) hCY
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨q, hqC, hqy⟩ := ConjEtale.surjOn_proj_connectedComponent hu hYo hYc q₀ y.2
    exact ⟨⟨q, hqC⟩, Subtype.ext hqy⟩
  have hgopen : IsOpenMap g := by
    intro T hT
    obtain ⟨T', hT', rfl⟩ := isOpen_induced_iff.mp hT
    have himg : g '' (Subtype.val ⁻¹' T')
        = Subtype.val ⁻¹' (ConjEtale.proj (u := u) (Y := Y) '' (T' ∩ C)) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q.1, ⟨hq, q.2⟩, rfl⟩
      · rintro ⟨q, ⟨hqT, hqC⟩, hqy⟩
        exact ⟨⟨q, hqC⟩, hqT, Subtype.ext hqy⟩
    rw [himg]
    exact (ConjEtale.isOpenMap_proj _ (hT'.inter hCopen)).preimage continuous_subtype_val
  exact (hgopen.isQuotientMap hgcont hgsurj).secondCountableTopology hgopen

/-- **Radó's theorem**, instance form: a connected Hausdorff Riemann surface is
second countable. `X = configY e ∪ (chart ball)`, both open and second
countable. -/
theorem secondCountableTopology_of_riemannSurface : SecondCountableTopology X := by
  rcases isEmpty_or_nonempty X with hX | hX
  · -- the empty surface: empty cover
    refine Rado.secondCountableTopology_of_countable_setCover (𝒰 := ∅) countable_empty
      (fun U hU => absurd hU (notMem_empty U))
      (fun U hU => absurd hU (notMem_empty U)) ?_
    rw [sUnion_empty]
    exact (univ_eq_empty_iff.mpr hX).symm
  · obtain ⟨e, he, hb⟩ := exists_config_chart (X := X)
    have hopen₂ : IsOpen (e.symm '' ball (0 : ℂ) 8 : Set X) :=
      e.symm.isOpen_image_of_subset_source isOpen_ball (by simpa using hb)
    have hsc₂ : SecondCountableTopology (e.symm '' ball (0 : ℂ) 8 : Set X) := by
      haveI := e.secondCountableTopology_source
      have hsub : (e.symm '' ball (0 : ℂ) 8 : Set X) ⊆ e.source := by
        rintro x ⟨w, hw, rfl⟩
        exact e.map_target (hb hw)
      exact (Topology.IsEmbedding.inclusion hsub).secondCountableTopology
    refine Rado.secondCountableTopology_of_countable_setCover
      (𝒰 := {configY e, e.symm '' ball (0 : ℂ) 8}) ((countable_singleton _).insert _)
      ?_ ?_ ?_
    · rintro U (rfl | rfl)
      · exact isOpen_configY he hb
      · exact hopen₂
    · rintro U (rfl | rfl)
      · exact secondCountable_configY he hb
      · exact hsc₂
    · rw [sUnion_insert, sUnion_singleton, eq_univ_iff_forall]
      intro x
      by_cases hx : x ∈ e.symm '' closedBall (-4 : ℂ) 1 ∪ e.symm '' closedBall (4 : ℂ) 1
      · right
        rcases hx with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
        · exact ⟨w, closedBall_config_subset (by simp) (by norm_num) hw, rfl⟩
        · exact ⟨w, closedBall_config_subset (by simp) (by norm_num) hw, rfl⟩
      · exact Or.inl ⟨mem_univ _, hx⟩

end Assembly

end Rado
