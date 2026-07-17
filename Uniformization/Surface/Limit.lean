/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill
import Uniformization.Surface.Biholo
import Uniformization.Surface.Packaging
import Uniformization.Complex.Koebe
import Uniformization.RMT.RiemannMapping

/-!
# The uniformization limit assembly

Given a connected, noncompact, second countable, simply connected Riemann
surface `X`, we build an exhaustion by simply connected regular pieces `Vₙ`,
biholomorphisms `φₙ : Vₙ ≅ 𝔻`, normalize them, and extract a locally uniform
limit `ψ : X → ℂ` that is holomorphic and injective. Packaging then produces the
biholomorphism onto an open subset of `ℂ` (the statement `uniformization_key`).
-/

open Set Metric Topology Filter
open scoped Manifold UniformConvergence Uniformity

namespace Uniformization

open Rado

/-- **Scaled Koebe growth bound.** For `g` injective holomorphic on `ball 0 r`
with `g 0 = 0` and `deriv g 0 = 1`, `‖g w‖ ≤ ‖w‖ / (1 - ‖w‖/r)²` on `ball 0 r`. -/
theorem growth_scaled {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 r)) (hinj : InjOn g (ball 0 r))
    (h0 : g 0 = 0) (hd : deriv g 0 = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    ‖g w‖ ≤ ‖w‖ / (1 - ‖w‖ / r) ^ 2 := by
  set R : ℂ := (r : ℂ) with hR
  have hR0 : R ≠ 0 := by simp [hR, ne_of_gt hr]
  have hRnorm : ‖R‖ = r := by simp [hR, abs_of_pos hr]
  have hmaps : ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → R * z ∈ ball (0 : ℂ) r := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul, hRnorm]
    calc r * ‖z‖ < r * 1 := by exact mul_lt_mul_of_pos_left hz hr
      _ = r := mul_one r
  set f : ℂ → ℂ := fun z => g (R * z) / R with hf
  have hfdiff : DifferentiableOn ℂ f (ball 0 1) := by
    apply DifferentiableOn.div_const
    apply DifferentiableOn.comp (t := ball 0 r) hg
    · exact (differentiable_id.const_mul R).differentiableOn
    · intro z hz; exact hmaps hz
  have hfinj : InjOn f (ball 0 1) := by
    intro z₁ hz₁ z₂ hz₂ h
    simp only [hf] at h
    have : g (R * z₁) = g (R * z₂) := by field_simp at h; exact h
    have := hinj (hmaps hz₁) (hmaps hz₂) this
    exact mul_left_cancel₀ hR0 this
  have hf0 : f 0 = 0 := by simp [hf, h0]
  have hg0 : HasDerivAt g 1 0 := by
    have hda : DifferentiableAt ℂ g 0 :=
      hg.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    rw [← hd]; exact hda.hasDerivAt
  have hfderiv : HasDerivAt f 1 0 := by
    have h1 : HasDerivAt (fun z : ℂ => R * z) R 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul R
    have hg0' : HasDerivAt g 1 (R * 0) := by simpa using hg0
    have h2 : HasDerivAt (fun z : ℂ => g (R * z)) (1 * R) 0 := hg0'.comp 0 h1
    have h3 : HasDerivAt f (1 * R / R) 0 := h2.div_const R
    have : (1 : ℂ) * R / R = 1 := by field_simp
    rw [this] at h3
    exact h3
  have hfd : deriv f 0 = 1 := hfderiv.deriv
  set z : ℂ := w / R with hz
  have hznorm : ‖z‖ = ‖w‖ / r := by rw [hz, norm_div, hRnorm]
  have hwlt : ‖w‖ < r := by rwa [mem_ball_zero_iff] at hw
  have hzlt : ‖z‖ < 1 := by
    rw [hznorm, div_lt_one hr]; exact hwlt
  have hzmem : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; exact hzlt
  have hgrow := koebe_growth hfdiff hfinj hf0 hfd hzmem
  have hRzw : R * z = w := by rw [hz]; field_simp
  have hfz : f z = g w / R := by show g (R * z) / R = g w / R; rw [hRzw]
  rw [hfz, norm_div, hRnorm] at hgrow
  rw [hznorm] at hgrow
  have hpos : (0 : ℝ) < 1 - ‖w‖ / r := by
    have : ‖w‖ / r < 1 := by rw [div_lt_one hr]; exact hwlt
    linarith
  rw [div_le_iff₀ hr] at hgrow
  calc ‖g w‖ ≤ (‖w‖ / r) / (1 - ‖w‖ / r) ^ 2 * r := hgrow
    _ = ‖w‖ / (1 - ‖w‖ / r) ^ 2 := by field_simp

section Planar

open Complex

/-- **Local injectivity forces a nonvanishing derivative** (planar copy of the Packaging lemma). -/
theorem deriv_ne_zero_of_injOn {F : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀)
    {s : Set ℂ} (hs : s ∈ 𝓝 z₀) (hinj : Set.InjOn F s) : deriv F z₀ ≠ 0 := by
  intro hderiv
  have hz₀s : z₀ ∈ s := mem_of_mem_nhds hs
  set G : ℂ → ℂ := fun z => F z - F z₀ with hGdef
  have hGan : AnalyticAt ℂ G z₀ := hF.sub analyticAt_const
  have hGz₀ : G z₀ = 0 := by simp [hGdef]
  have hGderiv : deriv G z₀ = 0 := by
    simp only [hGdef]; rw [deriv_sub_const]; exact hderiv
  have hGne : ¬ (∀ᶠ z in 𝓝 z₀, G z = 0) := by
    intro hev
    have hFev : ∀ᶠ z in 𝓝 z₀, F z = F z₀ := by
      filter_upwards [hev] with z hz; simpa [hGdef, sub_eq_zero] using hz
    have ht : s ∩ {z | F z = F z₀} ∈ 𝓝 z₀ := inter_mem hs hFev
    have hnb : (𝓝[≠] z₀).NeBot := inferInstance
    obtain ⟨z₁, ⟨hz₁s, hz₁F⟩, hz₁ne⟩ :=
      hnb.nonempty_of_mem (inter_mem (mem_nhdsWithin_of_mem_nhds ht) self_mem_nhdsWithin)
    exact hz₁ne (hinj hz₁s hz₀s hz₁F)
  obtain ⟨n, g, hgan, hgne, hfact⟩ :=
    (hGan.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hGne
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hgg : G =ᶠ[𝓝 z₀] g := by filter_upwards [hfact] with z hz; simpa using hz
    have := hgg.eq_of_nhds
    rw [hGz₀] at this; exact hgne this.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hev1 : G =ᶠ[𝓝 z₀] fun z => (z - z₀) * g z := by
      filter_upwards [hfact] with z hz; simpa using hz
    have hd : HasDerivAt (fun z => (z - z₀) * g z) (g z₀) z₀ := by
      have h1 : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
      have h2 : HasDerivAt g (deriv g z₀) z₀ := hgan.differentiableAt.hasDerivAt
      have h3 := h1.mul h2
      rw [show (1:ℂ) * g z₀ + (z₀ - z₀) * deriv g z₀ = g z₀ from by ring] at h3
      exact h3
    have hgz : deriv G z₀ = g z₀ := by rw [hev1.deriv_eq, hd.deriv]
    rw [hGderiv] at hgz; exact hgne hgz.symm
  have hn_ge2 : 1 < n := by omega
  set c : ℂ := g z₀ with hcdef
  have hc0 : c ≠ 0 := hgne
  set root : ℂ → ℂ := fun z => (g z / c) ^ ((n : ℂ)⁻¹) with hrootdef
  have hbase_an : AnalyticAt ℂ (fun z => g z / c) z₀ := by
    apply hgan.div analyticAt_const; exact hc0
  have hroot_an : AnalyticAt ℂ root z₀ := by
    apply hbase_an.cpow analyticAt_const
    show g z₀ / c ∈ slitPlane
    rw [← hcdef, div_self hc0]; exact one_mem_slitPlane
  have hroot_pow : ∀ z, root z ^ n = g z / c := fun z => Complex.cpow_nat_inv_pow _ hn0
  have hroot_z₀ : root z₀ = 1 := by
    simp only [hrootdef]; rw [← hcdef, div_self hc0, one_cpow]
  set w : ℂ := c ^ ((n : ℂ)⁻¹) with hwdef
  have hwn : w ^ n = c := Complex.cpow_nat_inv_pow c hn0
  have hw0 : w ≠ 0 := by intro h; apply hc0; rw [← hwn, h, zero_pow hn0]
  set h : ℂ → ℂ := fun z => w * root z with hhdef
  have hh_an : AnalyticAt ℂ h z₀ := analyticAt_const.mul hroot_an
  have hh_z₀ : h z₀ = w := by simp [hhdef, hroot_z₀]
  have hh_pow : ∀ z, h z ^ n = g z := by
    intro z
    simp only [hhdef, mul_pow, hwn, hroot_pow z]
    rw [mul_comm, div_mul_cancel₀ _ hc0]
  set H : ℂ → ℂ := fun z => (z - z₀) * h z with hHdef
  have hH_an : AnalyticAt ℂ H z₀ := (analyticAt_id.sub analyticAt_const).mul hh_an
  have hH_z₀ : H z₀ = 0 := by simp [hHdef]
  have hHpow : ∀ᶠ z in 𝓝 z₀, F z = F z₀ + H z ^ n := by
    filter_upwards [hfact] with z hz
    have hGH : G z = H z ^ n := by
      simp only [hHdef, mul_pow, hh_pow z]
      rw [hz, smul_eq_mul]
    simpa [hGdef, sub_eq_iff_eq_add'] using hGH
  have hHderiv : HasStrictDerivAt H w z₀ := by
    have hsd := hH_an.hasStrictDerivAt
    have hderivH : deriv H z₀ = w := by
      have hd : HasDerivAt H (h z₀) z₀ := by
        simp only [hHdef]
        have h1 : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
        have h2 : HasDerivAt h (deriv h z₀) z₀ := hh_an.differentiableAt.hasDerivAt
        have h3 := h1.mul h2
        rw [show (1:ℂ) * h z₀ + (z₀ - z₀) * deriv h z₀ = h z₀ from by ring] at h3
        exact h3
      rw [hd.deriv, hh_z₀]
    rwa [hderivH] at hsd
  let i : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 w hw0)
  have hfd : HasStrictFDerivAt H (i : ℂ →L[ℂ] ℂ) z₀ := hHderiv
  set R : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph H with hRdef
  have hRcoe : ∀ z, R z = H z := fun z => rfl
  have hz₀src : z₀ ∈ R.source := hfd.mem_toOpenPartialHomeomorph_source
  have hRz₀ : R z₀ = 0 := by rw [hRcoe, hH_z₀]
  have h0tgt : (0 : ℂ) ∈ R.target := by
    have hh := hfd.image_mem_toOpenPartialHomeomorph_target
    rwa [show H z₀ = (0 : ℂ) from hH_z₀] at hh
  have hRtgt_nhds : R.target ∈ 𝓝 (0 : ℂ) := R.open_target.mem_nhds h0tgt
  have hsymm0 : R.symm 0 = z₀ := by rw [← hRz₀, R.left_inv hz₀src]
  have hsymm_cont : ContinuousAt R.symm 0 := R.continuousAt_symm h0tgt
  set W : Set ℂ := {z | F z = F z₀ + H z ^ n} ∩ s with hWdef
  have hWnhd : W ∈ 𝓝 z₀ := inter_mem hHpow hs
  have hpre : R.symm ⁻¹' W ∈ 𝓝 (0 : ℂ) := by
    apply hsymm_cont.preimage_mem_nhds
    rw [hsymm0]; exact hWnhd
  have hN : R.target ∩ R.symm ⁻¹' W ∈ 𝓝 (0 : ℂ) := inter_mem hRtgt_nhds hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / n) with hζdef
  have hζprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζpow : ζ ^ n = 1 := hζprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζprim.ne_one hn_ge2
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζpow hn0
  set u : ℂ := (↑(ε / 2) : ℂ) with hudef
  have hu0 : u ≠ 0 := by
    simp only [hudef, ne_eq, Complex.ofReal_eq_zero]; positivity
  have hunorm : ‖u‖ < ε := by
    simp only [hudef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < ε/2)]
    linarith
  have huball : u ∈ ball (0 : ℂ) ε := by simpa [Metric.mem_ball, dist_zero_right] using hunorm
  have hζuball : ζ * u ∈ ball (0 : ℂ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul]
    exact hunorm
  have hu_mem : u ∈ R.target ∩ R.symm ⁻¹' W := hball huball
  have hζu_mem : ζ * u ∈ R.target ∩ R.symm ⁻¹' W := hball hζuball
  set z₁ : ℂ := R.symm u with hz₁def
  set z₂ : ℂ := R.symm (ζ * u) with hz₂def
  have hz₁W : z₁ ∈ W := hu_mem.2
  have hz₂W : z₂ ∈ W := hζu_mem.2
  have hHz₁ : H z₁ = u := by rw [← hRcoe, hz₁def, R.right_inv hu_mem.1]
  have hHz₂ : H z₂ = ζ * u := by rw [← hRcoe, hz₂def, R.right_inv hζu_mem.1]
  have hFeq : F z₁ = F z₂ := by
    rw [hz₁W.1, hz₂W.1, hHz₁, hHz₂, mul_pow, hζpow, one_mul]
  have hz_eq : z₁ = z₂ := hinj hz₁W.2 hz₂W.2 hFeq
  have huζu : u ≠ ζ * u := by
    intro he
    have h1 : (1 - ζ) * u = 0 := by rw [sub_mul, one_mul, ← he, sub_self]
    rcases mul_eq_zero.mp h1 with hz | hz
    · exact hζ1 (sub_eq_zero.mp hz).symm
    · exact hu0 hz
  have hz_ne : z₁ ≠ z₂ := by
    intro he
    apply huζu
    calc u = H z₁ := hHz₁.symm
      _ = H z₂ := by rw [he]
      _ = ζ * u := hHz₂
  exact hz_ne hz_eq

end Planar

section Exhaustion

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [SimplyConnectedSpace X]

/-- The invariant carried by each piece in the exhaustion. -/
structure GoodPiece (x₀ : X) (V : Set X) : Prop where
  isOpen : IsOpen V
  isConnected : IsConnected V
  compactClosure : IsCompact (closure V)
  simplyConnected : IsSimplyConnected V
  frontierNonempty : (frontier V).Nonempty
  exteriorDisk : ∀ ξ ∈ frontier V, ExteriorDiskAt V ξ
  mem : x₀ ∈ V

/-- One step: given a compact set `C` containing `x₀`, produce a good piece containing `C`. -/
private noncomputable def stepPiece (hnc : ¬ CompactSpace X) (x₀ : X)
    (C : Set X) (hC : IsCompact C) (hx : x₀ ∈ C) : {V : Set X // GoodPiece x₀ V ∧ C ⊆ V} :=
  ⟨(exists_simply_connected_piece hnc hC hx).choose, by
    obtain ⟨hVo, hVconn, hVcl, hKV, hVsc, hVfr, hext⟩ :=
      (exists_simply_connected_piece hnc hC hx).choose_spec
    exact ⟨⟨hVo, hVconn, hVcl, hVsc, hVfr, hext, hKV hx⟩, hKV⟩⟩

/-- The recursively-built exhausting sequence of good pieces. -/
private noncomputable def gPiece (hnc : ¬ CompactSpace X) (x₀ : X) (K : CompactExhaustion X) :
    ℕ → {V : Set X // GoodPiece x₀ V}
  | 0 =>
      let s := stepPiece hnc x₀ (K 0 ∪ {x₀}) ((K.isCompact 0).union isCompact_singleton)
        (Or.inr rfl)
      ⟨s.1, s.2.1⟩
  | (n + 1) =>
      let prev := gPiece hnc x₀ K n
      let s := stepPiece hnc x₀ (K (n + 1) ∪ closure prev.1)
        ((K.isCompact (n + 1)).union prev.2.compactClosure)
        (Or.inr (subset_closure prev.2.mem))
      ⟨s.1, s.2.1⟩

/-- **Normalized biholomorphism.** A good piece `V` carries a holomorphic bijection `ψ`
onto some `ball 0 R` with `ψ x₀ = 0` and chart-derivative `1` at `x₀`. -/
theorem exists_normalized {V : Set X} (x₀ : X)
    (hVo : IsOpen V) (hVconn : IsConnected V) (hVcl : IsCompact (closure V))
    (hVsc : IsSimplyConnected V) (hfr : (frontier V).Nonempty)
    (hreg : ∀ ξ ∈ frontier V, ExteriorDiskAt V ξ) (hx₀ : x₀ ∈ V) :
    ∃ (ψ : X → ℂ) (R : ℝ), 0 < R ∧ HolomorphicOn ψ V ∧ InjOn ψ V ∧ ψ x₀ = 0 ∧
      BijOn ψ V (ball 0 R) ∧
      deriv (ψ ∘ (chartAt ℂ x₀).symm) (chartAt ℂ x₀ x₀) = 1 := by
  obtain ⟨φ, hφholo, hφbij, hφ0⟩ := exists_biholo_ball hVo hVconn hVcl hVsc hfr hreg hx₀
  have hinj : InjOn φ V := hφbij.injOn
  set e₀ := chartAt ℂ x₀ with he₀
  set p₀ := e₀ x₀ with hp₀
  have hxe : x₀ ∈ e₀.source := mem_chart_source ℂ x₀
  -- neighborhood of `p₀` in the chart on which `φ ∘ e₀.symm` is injective
  set s : Set ℂ := e₀.target ∩ e₀.symm ⁻¹' V with hs
  have hsnhd : s ∈ 𝓝 p₀ := by
    refine (e₀.symm.continuousOn.isOpen_inter_preimage e₀.open_target hVo).mem_nhds ?_
    exact ⟨e₀.map_source hxe, by show e₀.symm (e₀ x₀) ∈ V; rw [e₀.left_inv hxe]; exact hx₀⟩
  have hginj : InjOn (φ ∘ e₀.symm) s := by
    intro a ha b hb hab
    simp only [Function.comp_apply] at hab
    have hsymm : e₀.symm a = e₀.symm b := hinj ha.2 hb.2 hab
    calc a = e₀ (e₀.symm a) := (e₀.right_inv ha.1).symm
      _ = e₀ (e₀.symm b) := by rw [hsymm]
      _ = b := e₀.right_inv hb.1
  set d : ℂ := deriv (φ ∘ e₀.symm) p₀ with hd
  have hd0 : d ≠ 0 := deriv_ne_zero_of_injOn (hφholo x₀ hx₀) hsnhd hginj
  set R : ℝ := 1 / ‖d‖ with hR
  have hnorm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  have hRpos : 0 < R := by rw [hR]; positivity
  set ψ : X → ℂ := fun x => φ x / d with hψ
  -- disk scaling `(· / d)` is a bijection `ball 0 1 → ball 0 R`
  have hscale : BijOn (fun z : ℂ => z / d) (ball 0 1) (ball 0 R) := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_div, hR]
      gcongr
    · intro a _ b _ hab
      exact (div_left_inj' hd0).mp hab
    · intro w hw
      rw [mem_ball_zero_iff] at hw
      refine ⟨w * d, ?_, by show w * d / d = w; rw [mul_div_assoc, div_self hd0, mul_one]⟩
      rw [mem_ball_zero_iff, norm_mul]
      rw [hR] at hw
      rwa [lt_div_iff₀ hnorm_pos] at hw
  refine ⟨ψ, R, hRpos, ?_, ?_, ?_, ?_, ?_⟩
  · -- HolomorphicOn ψ V
    intro x hx
    have hax : AnalyticAt ℂ (φ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hφholo x hx
    have : (ψ ∘ (chartAt ℂ x).symm) = fun z => (φ ∘ (chartAt ℂ x).symm) z / d := rfl
    rw [this]
    exact hax.div analyticAt_const hd0
  · -- InjOn ψ V
    intro a ha b hb hab
    simp only [hψ] at hab
    exact hinj ha hb ((div_left_inj' hd0).mp hab)
  · -- ψ x₀ = 0
    simp [hψ, hφ0]
  · -- BijOn ψ V (ball 0 R)
    have : ψ = (fun z : ℂ => z / d) ∘ φ := rfl
    rw [this]
    exact hscale.comp hφbij
  · -- chart derivative 1
    show deriv (ψ ∘ e₀.symm) p₀ = 1
    have : (ψ ∘ e₀.symm) = fun z => (φ ∘ e₀.symm) z / d := rfl
    rw [this, deriv_div_const]
    rw [← hd]; exact div_self hd0

/-- **Comparison map.** For normalized biholomorphisms `ψn : V ≅ ball 0 Rn` and `ψm` holomorphic
injective on `W ⊇ V`, both with chart-derivative `1` at `x₀` and vanishing there, the map
`h w = ψm (ψn⁻¹ w)` is a schlicht function on `ball 0 Rn` with `h ∘ ψn = ψm` on `V`. -/
theorem exists_comparison {ψn ψm : X → ℂ} {V W : Set X} (x₀ : X) {Rn : ℝ}
    (hVo : IsOpen V) (hVW : V ⊆ W)
    (hψn_holo : HolomorphicOn ψn V) (hψm_holo : HolomorphicOn ψm W)
    (hψn_inj : InjOn ψn V) (hψm_inj : InjOn ψm W)
    (hx₀ : x₀ ∈ V) (hψn0 : ψn x₀ = 0) (hψm0 : ψm x₀ = 0)
    (hbij : BijOn ψn V (ball 0 Rn))
    (hψnd : deriv (ψn ∘ (chartAt ℂ x₀).symm) (chartAt ℂ x₀ x₀) = 1)
    (hψmd : deriv (ψm ∘ (chartAt ℂ x₀).symm) (chartAt ℂ x₀ x₀) = 1) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball 0 Rn) ∧ InjOn h (ball 0 Rn) ∧
      h 0 = 0 ∧ deriv h 0 = 1 ∧ ∀ x ∈ V, h (ψn x) = ψm x := by
  set inv : ℂ → X := Function.invFunOn ψn V with hinvdef
  set h : ℂ → ℂ := fun w => ψm (inv w) with hhdef
  have himg : ψn '' V = ball 0 Rn := hbij.image_eq
  have hinvmem : ∀ w ∈ ball 0 Rn, inv w ∈ V := by
    intro w hw
    rw [← himg] at hw; exact Function.invFunOn_mem hw
  have hinveq : ∀ w ∈ ball 0 Rn, ψn (inv w) = w := by
    intro w hw
    rw [← himg] at hw; exact Function.invFunOn_eq hw
  have hleft : ∀ x ∈ V, inv (ψn x) = x := fun x hx => hψn_inj.leftInvOn_invFunOn hx
  have hinv0 : inv 0 = x₀ := by have := hleft x₀ hx₀; rwa [hψn0] at this
  -- the map property
  have hmap : ∀ x ∈ V, h (ψn x) = ψm x := by
    intro x hx; show ψm (inv (ψn x)) = ψm x; rw [hleft x hx]
  -- key local analysis at each point of V
  have key : ∀ x ∈ V, AnalyticAt ℂ h (ψn x) ∧
      HasDerivAt h (deriv (ψm ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) *
        (deriv (ψn ∘ (chartAt ℂ x).symm) (chartAt ℂ x x))⁻¹) (ψn x) := by
    intro x hx
    set e := chartAt ℂ x with he
    set cx := e x with hcx
    have hxe : x ∈ e.source := mem_chart_source ℂ x
    set G : ℂ → ℂ := ψn ∘ e.symm with hG
    have hG_an : AnalyticAt ℂ G cx := hψn_holo x hx
    have hGcx : G cx = ψn x := by simp only [hG, Function.comp_apply, hcx, e.left_inv hxe]
    -- injectivity of `G` near `cx`
    set s' : Set ℂ := e.target ∩ e.symm ⁻¹' V with hs'
    have hs'nhd : s' ∈ 𝓝 cx := by
      refine (e.symm.continuousOn.isOpen_inter_preimage e.open_target hVo).mem_nhds ?_
      exact ⟨e.map_source hxe, by show e.symm (e x) ∈ V; rw [e.left_inv hxe]; exact hx⟩
    have hGinj : InjOn G s' := by
      intro a ha b hb hab
      simp only [hG, Function.comp_apply] at hab
      have := hψn_inj ha.2 hb.2 hab
      calc a = e (e.symm a) := (e.right_inv ha.1).symm
        _ = e (e.symm b) := by rw [this]
        _ = b := e.right_inv hb.1
    have hGd0 : deriv G cx ≠ 0 := deriv_ne_zero_of_injOn hG_an hs'nhd hGinj
    set Ginv : ℂ → ℂ := hG_an.hasStrictDerivAt.localInverse _ _ _ hGd0 with hGinv
    have hGinv_an : AnalyticAt ℂ Ginv (G cx) := hG_an.analyticAt_localInverse hGd0
    have hGinv_hd : HasDerivAt Ginv (deriv G cx)⁻¹ (G cx) :=
      (hG_an.hasStrictDerivAt.to_localInverse hGd0).hasDerivAt
    have hGinv_img : Ginv (G cx) = cx :=
      (hG_an.hasStrictDerivAt.eventually_left_inverse hGd0).self_of_nhds
    have hrinv : ∀ᶠ v in 𝓝 (G cx), G (Ginv v) = v :=
      hG_an.hasStrictDerivAt.eventually_right_inverse hGd0
    -- `e.symm (Ginv v) ∈ V` eventually
    have hmemV : ∀ᶠ v in 𝓝 (G cx), e.symm (Ginv v) ∈ V := by
      have hcont : ContinuousAt (fun v => e.symm (Ginv v)) (G cx) := by
        apply (e.continuousAt_symm ?_).comp hGinv_hd.continuousAt
        rw [hGinv_img]; exact e.map_source hxe
      have hval : e.symm (Ginv (G cx)) = x := by rw [hGinv_img]; exact e.left_inv hxe
      exact hcont.preimage_mem_nhds (by rw [hval]; exact hVo.mem_nhds hx)
    -- eventual equality `h = (ψm ∘ e.symm) ∘ Ginv`
    have hev : h =ᶠ[𝓝 (G cx)] (ψm ∘ e.symm) ∘ Ginv := by
      filter_upwards [hrinv, hmemV] with v hv1 hv2
      have hvV : ∃ a ∈ V, ψn a = v := ⟨e.symm (Ginv v), hv2, hv1⟩
      have hinvv : inv v = e.symm (Ginv v) :=
        hψn_inj (Function.invFunOn_mem hvV) hv2 (by rw [Function.invFunOn_eq hvV]; exact hv1.symm)
      show ψm (inv v) = (ψm ∘ e.symm) (Ginv v)
      rw [hinvv]; rfl
    -- analyticity and derivative of the composition at `G cx`
    have hψm_an : AnalyticAt ℂ (ψm ∘ e.symm) cx := hψm_holo x (hVW hx)
    have hcomp_an : AnalyticAt ℂ ((ψm ∘ e.symm) ∘ Ginv) (G cx) := by
      refine AnalyticAt.comp ?_ hGinv_an
      rw [hGinv_img]; exact hψm_an
    have hψm_hd : HasDerivAt (ψm ∘ e.symm) (deriv (ψm ∘ e.symm) cx) cx :=
      hψm_an.differentiableAt.hasDerivAt
    have hcomp_hd : HasDerivAt ((ψm ∘ e.symm) ∘ Ginv)
        (deriv (ψm ∘ e.symm) cx * (deriv G cx)⁻¹) (G cx) := by
      have hf : HasDerivAt (ψm ∘ e.symm) (deriv (ψm ∘ e.symm) cx) (Ginv (G cx)) := by
        rw [hGinv_img]; exact hψm_hd
      exact hf.comp (G cx) hGinv_hd
    refine ⟨?_, ?_⟩
    · rw [hGcx] at hev hcomp_an
      exact hcomp_an.congr hev.symm
    · rw [hGcx] at hev hcomp_hd
      exact hcomp_hd.congr_of_eventuallyEq hev
  refine ⟨h, ?_, ?_, ?_, ?_, hmap⟩
  · -- DifferentiableOn on ball 0 Rn
    intro w hw
    have hx := hinvmem w hw
    have heq : ψn (inv w) = w := hinveq w hw
    have := (key (inv w) hx).1
    rw [heq] at this
    exact this.differentiableAt.differentiableWithinAt
  · -- InjOn on ball 0 Rn
    intro w1 hw1 w2 hw2 hww
    have h1 : ψm (inv w1) = ψm (inv w2) := hww
    have := hψm_inj (hVW (hinvmem w1 hw1)) (hVW (hinvmem w2 hw2)) h1
    rw [← hinveq w1 hw1, ← hinveq w2 hw2, this]
  · -- h 0 = 0
    show ψm (inv 0) = 0; rw [hinv0]; exact hψm0
  · -- deriv h 0 = 1
    have hd := (key x₀ hx₀).2
    rw [hψn0, hψnd, hψmd] at hd
    simpa using hd.deriv

/-- Precomposition of an equicontinuous family by a fixed continuous map. -/
theorem equicontinuousAt_comp_right {ι : Type*} {G : ι → ℂ → ℂ} {g : X → ℂ} {x : X}
    (hG : EquicontinuousAt G (g x)) (hg : ContinuousAt g x) :
    EquicontinuousAt (fun i => G i ∘ g) x := fun U hU => hg.eventually (hG U hU)

/-- Splitting an ℕ-indexed family into a finite head and a tail preserves equicontinuity. -/
theorem equicontinuousAt_nat_split {F : ℕ → X → ℂ} {x : X} (N : ℕ)
    (hhead : EquicontinuousAt (fun k : Fin N => F k) x)
    (htail : EquicontinuousAt (fun k : {k : ℕ // N ≤ k} => F k) x) :
    EquicontinuousAt F x := by
  intro U hU
  have h1 := hhead U hU
  have h2 := htail U hU
  filter_upwards [h1, h2] with y hy1 hy2 k
  rcases lt_or_ge k N with hk | hk
  · exact hy1 ⟨k, hk⟩
  · exact hy2 ⟨k, hk⟩

/-- Equicontinuity at a point only depends on the family near that point. -/
theorem equicontinuousAt_congr {ι : Type*} {F G : ι → X → ℂ} {x : X}
    (h : ∀ᶠ y in 𝓝 x, ∀ i, F i y = G i y) (hx : ∀ i, F i x = G i x)
    (hG : EquicontinuousAt G x) : EquicontinuousAt F x := by
  intro U hU
  filter_upwards [hG U hU, h] with y hy hcongr i
  rw [hx i, hcongr i]; exact hy i

/-- **Tail equicontinuity (Cauchy estimates).** If `x ∈ Vⱼ` and the tail `{ψₖ : k ≥ j}` is
uniformly bounded on compacts of `Vⱼ`, the tail is equicontinuous at `x`. -/
theorem equicontinuousAt_tail {ψ : ℕ → X → ℂ} {V : ℕ → Set X} (x : X) {j : ℕ}
    (hVo : ∀ n, IsOpen (V n)) (hmono : ∀ ⦃n m⦄, n ≤ m → V n ⊆ V m)
    (hholo : ∀ n, HolomorphicOn (ψ n) (V n)) (hxVj : x ∈ V j)
    (hbound : ∀ (L : Set X), IsCompact L → L ⊆ V j → ∃ C, ∀ m, j ≤ m → ∀ y ∈ L, ‖ψ m y‖ ≤ C) :
    EquicontinuousAt (fun k : {k : ℕ // j ≤ k} => ψ k.val) x := by
  set e := chartAt ℂ x with he
  set p := e x with hp
  have hxe : x ∈ e.source := mem_chart_source ℂ x
  have hpt : p ∈ e.target := e.map_source hxe
  have hNnhd : e.target ∩ e.symm ⁻¹' (V j) ∈ 𝓝 p := by
    refine (e.symm.continuousOn.isOpen_inter_preimage e.open_target (hVo j)).mem_nhds ?_
    exact ⟨hpt, by show e.symm (e x) ∈ V j; rw [e.left_inv hxe]; exact hxVj⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hNnhd
  set r := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  have hcball_sub : closedBall p r ⊆ e.target ∩ e.symm ⁻¹' (V j) := by
    intro z hz; apply hball
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hz; linarith
  set L := e.symm '' closedBall p r with hL
  have hLcomp : IsCompact L :=
    (isCompact_closedBall p r).image_of_continuousOn
      (e.symm.continuousOn.mono (fun z hz => (hcball_sub hz).1))
  have hLV : L ⊆ V j := by rintro _ ⟨z, hz, rfl⟩; exact (hcball_sub hz).2
  obtain ⟨C, hC⟩ := hbound L hLcomp hLV
  have hUnhd : ball p r ∈ 𝓝 p := ball_mem_nhds p hrpos
  have hEq : EquicontinuousAt (fun k : {k : ℕ // j ≤ k} => (ψ k.val ∘ e.symm)) p := by
    apply Complex.equicontinuousAt_of_forall_norm_le hUnhd
    · intro i z hz
      have hzU : z ∈ e.target ∩ e.symm ⁻¹' (V j) := hcball_sub (ball_subset_closedBall hz)
      have hzt : z ∈ e.target := hzU.1
      have han : AnalyticAt ℂ (ψ i.val ∘ e.symm) z := by
        have hh := (hholo i.val).analyticAt_comp_symm (chartAt_mem_riemannAtlas x)
          (x := e.symm z) ⟨hmono i.2 hzU.2, e.map_target hzt⟩
        rwa [e.right_inv hzt] at hh
      exact han.differentiableAt.differentiableWithinAt
    · refine ⟨C, fun i z hz => ?_⟩
      exact hC i.val i.2 (e.symm z) ⟨z, ball_subset_closedBall hz, rfl⟩
  have hcont : ContinuousAt (⇑e) x := e.continuousOn.continuousAt (e.open_source.mem_nhds hxe)
  have hcomp := equicontinuousAt_comp_right hEq hcont
  refine equicontinuousAt_congr ?_ ?_ hcomp
  · filter_upwards [e.open_source.mem_nhds hxe] with y hy i
    show ψ i.val y = (ψ i.val ∘ e.symm) (e y)
    simp only [Function.comp_apply, e.left_inv hy]
  · intro i
    show ψ i.val x = (ψ i.val ∘ e.symm) (e x)
    simp only [Function.comp_apply, e.left_inv hxe]

/-- **Montel extraction.** A pointwise-relatively-compact, equicontinuous family of functions on
`X` has a subsequence converging uniformly on every compact set. -/
theorem montel_extraction {F : ℕ → X → ℂ} (heqc : Equicontinuous F)
    (hbdd : ∀ x : X, ∃ Q : Set ℂ, IsCompact Q ∧ ∀ k, F k x ∈ Q) :
    ∃ (σ : ℕ → ℕ) (f : X → ℂ), StrictMono σ ∧
      ∀ K : Set X, IsCompact K → TendstoUniformlyOn (fun k => F (σ k)) f atTop K := by
  haveI := Rado.locallyCompactSpace (X := X)
  set 𝔖 : Set (Set X) := {K | IsCompact K} with h𝔖
  haveI hcnt : (𝓤 (X →ᵤ[𝔖] ℂ)).IsCountablyGenerated := by
    set φ : CompactExhaustion X := CompactExhaustion.choice X
    exact UniformOnFun.isCountablyGenerated_uniformity (𝔖 := 𝔖) (t := fun n => φ n)
      (fun n => φ.isCompact n) φ.subset (fun K hK => φ.exists_superset_of_isCompact hK)
  set g : ℕ → (X →ᵤ[𝔖] ℂ) := fun k => UniformOnFun.ofFun 𝔖 (F k) with hg
  set s : Set (X →ᵤ[𝔖] ℂ) := Set.range g with hs
  have hcompact : IsCompact (closure s) := by
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (F := UniformOnFun.toFun 𝔖)
      (fun K hK => hK) .id ?_ ?_
    · intro K hK
      have hEq_s : Equicontinuous (fun idx : s => UniformOnFun.toFun 𝔖 idx.val) := by
        intro x U hU
        filter_upwards [heqc x U hU] with y hy idx
        obtain ⟨k, hk⟩ := idx.2
        have h1 : UniformOnFun.toFun 𝔖 idx.val = F k := by rw [← hk]; simp [hg]
        show (UniformOnFun.toFun 𝔖 idx.val x, UniformOnFun.toFun 𝔖 idx.val y) ∈ U
        rw [h1]; exact hy k
      exact hEq_s.equicontinuousOn K
    · intro K hK x hx
      obtain ⟨Q, hQc, hQ⟩ := hbdd x
      refine ⟨Q, hQc, ?_⟩
      rintro i ⟨k, rfl⟩
      exact hQ k
  have hseq : IsSeqCompact (closure s) := hcompact.isSeqCompact
  have hmem : ∀ k, g k ∈ closure s := fun k => subset_closure ⟨k, rfl⟩
  obtain ⟨ĝ, -, σ, hσ, htend⟩ := hseq hmem
  refine ⟨σ, UniformOnFun.toFun 𝔖 ĝ, hσ, ?_⟩
  intro K hK
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at htend
  have := htend K hK
  simpa only [hg, Function.comp_def, UniformOnFun.toFun_ofFun] using this

/-- **Local uniform bound (Koebe).** On a compact `L ⊆ Vₙ`, the tail family `{ψₘ : m ≥ n}` is
uniformly bounded. -/
theorem family_bound {ψ : ℕ → X → ℂ} {R : ℕ → ℝ} {V : ℕ → Set X} (x₀ : X)
    (hmono : ∀ ⦃n m⦄, n ≤ m → V n ⊆ V m)
    (hVo : ∀ n, IsOpen (V n)) (hRpos : ∀ n, 0 < R n)
    (hholo : ∀ n, HolomorphicOn (ψ n) (V n)) (hinjn : ∀ n, InjOn (ψ n) (V n))
    (hmem : ∀ n, x₀ ∈ V n) (hz : ∀ n, ψ n x₀ = 0)
    (hbij : ∀ n, BijOn (ψ n) (V n) (ball 0 (R n)))
    (hd : ∀ n, deriv (ψ n ∘ (chartAt ℂ x₀).symm) (chartAt ℂ x₀ x₀) = 1)
    (n : ℕ) {L : Set X} (hL : IsCompact L) (hLV : L ⊆ V n) :
    ∃ C, ∀ m, n ≤ m → ∀ x ∈ L, ‖ψ m x‖ ≤ C := by
  rcases L.eq_empty_or_nonempty with hLe | hLne
  · exact ⟨0, by intro m _ x hx; rw [hLe] at hx; exact absurd hx (notMem_empty x)⟩
  -- `ψ n '' L` is a compact subset of `ball 0 (R n)`.
  have hcontn : ContinuousOn (ψ n) L := (hholo n).continuousOn.mono hLV
  have himgc : IsCompact (ψ n '' L) := hL.image_of_continuousOn hcontn
  have himgne : (ψ n '' L).Nonempty := hLne.image _
  have himgsub : ψ n '' L ⊆ ball 0 (R n) := by
    rintro _ ⟨x, hx, rfl⟩; exact (hbij n).mapsTo (hLV hx)
  obtain ⟨y₀, hy₀mem, hy₀max⟩ := himgc.exists_isMaxOn himgne continuous_norm.continuousOn
  set ρ : ℝ := ‖y₀‖ with hρ
  have hρlt : ρ < R n := by
    have := himgsub hy₀mem; rwa [mem_ball_zero_iff] at this
  have hρnn : 0 ≤ ρ := norm_nonneg _
  have hden_pos : 0 < 1 - ρ / R n := by
    rw [sub_pos, div_lt_one (hRpos n)]; exact hρlt
  refine ⟨ρ / (1 - ρ / R n) ^ 2, ?_⟩
  intro m hnm x hx
  -- comparison map for the pair `(n, m)`
  obtain ⟨h, hhdiff, hhinj, hh0, hhd1, hhmap⟩ :=
    exists_comparison x₀ (hVo n) (hmono hnm) (hholo n) (hholo m) (hinjn n) (hinjn m)
      (hmem n) (hz n) (hz m) (hbij n) (hd n) (hd m)
  set w : ℂ := ψ n x with hw
  have hwmem : w ∈ ψ n '' L := ⟨x, hx, rfl⟩
  have hwρ : ‖w‖ ≤ ρ := hy₀max hwmem
  have hwball : w ∈ ball (0 : ℂ) (R n) := himgsub hwmem
  have hgrow := growth_scaled (hRpos n) hhdiff hhinj hh0 hhd1 hwball
  have hval : ψ m x = h w := (hhmap x (hLV hx)).symm
  rw [hval]
  refine hgrow.trans ?_
  have hwr : ‖w‖ / R n ≤ ρ / R n := (div_le_div_iff_of_pos_right (hRpos n)).mpr hwρ
  have hle : 1 - ρ / R n ≤ 1 - ‖w‖ / R n := by linarith
  have hwpos : 0 < 1 - ‖w‖ / R n := by linarith
  have hApos : 0 < (1 - ‖w‖ / R n) ^ 2 := by positivity
  have hBpos : 0 < (1 - ρ / R n) ^ 2 := by positivity
  have hden2 : (1 - ρ / R n) ^ 2 ≤ (1 - ‖w‖ / R n) ^ 2 := by nlinarith [hden_pos, hle, hwpos]
  rw [div_le_div_iff₀ hApos hBpos]
  nlinarith [hwρ, hden2, hBpos.le, hρnn]

/-- **Piece exhaustion.** A noncompact connected simply connected surface has an increasing
exhaustion by good pieces `Vₙ` with `closure Vₙ ⊆ Vₙ₊₁` and `⋃ Vₙ = univ`. -/
theorem exists_piece_exhaustion (hnc : ¬ CompactSpace X) (x₀ : X) :
    ∃ V : ℕ → Set X, (∀ n, GoodPiece x₀ (V n)) ∧ (∀ n, closure (V n) ⊆ V (n + 1)) ∧
      (⋃ n, V n) = univ := by
  haveI := Rado.locallyCompactSpace (X := X)
  let K : CompactExhaustion X := CompactExhaustion.choice X
  refine ⟨fun n => (gPiece hnc x₀ K n).1, fun n => (gPiece hnc x₀ K n).2, ?_, ?_⟩
  · -- chain: closure (V n) ⊆ V (n+1)
    intro n
    show closure (gPiece hnc x₀ K n).1 ⊆ (gPiece hnc x₀ K (n + 1)).1
    have hs :
        (K (n + 1) ∪ closure (gPiece hnc x₀ K n).1) ⊆
          (stepPiece hnc x₀ (K (n + 1) ∪ closure (gPiece hnc x₀ K n).1)
            ((K.isCompact (n + 1)).union (gPiece hnc x₀ K n).2.compactClosure)
            (Or.inr (subset_closure (gPiece hnc x₀ K n).2.mem))).1 :=
      (stepPiece hnc x₀ _ _ _).2.2
    calc closure (gPiece hnc x₀ K n).1
        ⊆ K (n + 1) ∪ closure (gPiece hnc x₀ K n).1 := subset_union_right
      _ ⊆ (gPiece hnc x₀ K (n + 1)).1 := hs
  · -- union is everything, since K n ⊆ V n and ⋃ K n = univ
    rw [eq_univ_iff_forall]
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine mem_iUnion.mpr ⟨n, ?_⟩
    -- K n ⊆ V n
    have hKV : K n ⊆ (gPiece hnc x₀ K n).1 := by
      cases n with
      | zero =>
          have := (stepPiece hnc x₀ (K 0 ∪ {x₀}) ((K.isCompact 0).union isCompact_singleton)
            (Or.inr rfl)).2.2
          exact fun y hy => this (subset_union_left hy)
      | succ m =>
          have := (stepPiece hnc x₀ (K (m + 1) ∪ closure (gPiece hnc x₀ K m).1)
            ((K.isCompact (m + 1)).union (gPiece hnc x₀ K m).2.compactClosure)
            (Or.inr (subset_closure (gPiece hnc x₀ K m).2.mem))).2.2
          exact fun y hy => this (subset_union_left hy)
    exact hKV hn

/-- **Existence of a global injective holomorphic function** on a noncompact connected simply
connected surface: the uniformizer produced by the Montel/exhaustion argument. -/
theorem exists_uniformizer (hnc : ¬ CompactSpace X) :
    ∃ ψ : X → ℂ, HolomorphicOn ψ univ ∧ Function.Injective ψ := by
  haveI := Rado.locallyCompactSpace (X := X)
  haveI : NormalSpace X := inferInstance
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨V, hgood, hchain, hunion⟩ := exists_piece_exhaustion hnc x₀
  choose ψ R hRpos hholo hinjn hz hbij hd using fun n =>
    exists_normalized x₀ (hgood n).isOpen (hgood n).isConnected (hgood n).compactClosure
      (hgood n).simplyConnected (hgood n).frontierNonempty (hgood n).exteriorDisk (hgood n).mem
  have hVo : ∀ n, IsOpen (V n) := fun n => (hgood n).isOpen
  have hstep : ∀ n, V n ⊆ V (n + 1) := fun n => subset_closure.trans (hchain n)
  have hmono : ∀ ⦃n m⦄, n ≤ m → V n ⊆ V m := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact subset_rfl
    | succ m _ ih => exact ih.trans (hstep m)
  have hmemV : ∀ n, x₀ ∈ V n := fun n => (hgood n).mem
  -- uniform bound on compacts (Koebe)
  have hbnd : ∀ j, ∀ (L : Set X), IsCompact L → L ⊆ V j →
      ∃ C, ∀ m, j ≤ m → ∀ y ∈ L, ‖ψ m y‖ ≤ C :=
    fun j L hL hLV => family_bound x₀ hmono hVo hRpos hholo hinjn hmemV hz hbij hd j hL hLV
  -- pinned compact sets for Tietze
  set S : ℕ → Set X := fun k => Nat.rec ∅ (fun j _ => closure (V j)) k with hSdef
  have hS0 : S 0 = ∅ := rfl
  have hSsucc : ∀ k, S (k + 1) = closure (V k) := fun _ => rfl
  have hVsubS : ∀ j k, j < k → V j ⊆ S k := by
    intro j k hjk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_lt hjk
    rw [show j + k' + 1 = (j + k') + 1 from rfl, hSsucc]
    exact (hmono (by omega)).trans subset_closure
  -- Tietze extensions
  have htietze : ∀ k, ∃ Ψk : C(X, ℂ), ∀ y ∈ S k, Ψk y = ψ k y := by
    intro k
    cases k with
    | zero =>
        exact ⟨⟨fun _ => 0, continuous_const⟩,
          fun y hy => absurd hy (by rw [hS0]; exact notMem_empty y)⟩
    | succ j =>
        have hcl : IsClosed (S (j + 1)) := by rw [hSsucc]; exact isClosed_closure
        have hsub : S (j + 1) ⊆ V (j + 1) := by rw [hSsucc]; exact hchain j
        have hcont : ContinuousOn (ψ (j + 1)) (S (j + 1)) := (hholo (j + 1)).continuousOn.mono hsub
        obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hcl
          ⟨(S (j + 1)).restrict (ψ (j + 1)), hcont.restrict⟩
        refine ⟨g, fun y hy => ?_⟩
        have := DFunLike.congr_fun hg ⟨y, hy⟩
        simpa using this
  choose Ψ hΨ using htietze
  set F : ℕ → X → ℂ := fun k => (Ψ k : X → ℂ) with hF
  -- equicontinuity of the extended family
  have heqc : Equicontinuous F := by
    intro x
    obtain ⟨j, hxj⟩ : ∃ j, x ∈ V j := by
      have : x ∈ ⋃ n, V n := by rw [hunion]; trivial
      exact mem_iUnion.mp this
    -- head: finitely many continuous functions
    have hhead : EquicontinuousAt (fun k : Fin (j + 1) => F k.val) x :=
      equicontinuousAt_finite.mpr (fun i => (Ψ i.val).continuous.continuousAt)
    -- tail: `ψ` is equicontinuous, and `Ψ = ψ` near `x`
    have htailψ : EquicontinuousAt (fun k : {k : ℕ // j ≤ k} => ψ k.val) x :=
      equicontinuousAt_tail x hVo hmono hholo hxj (hbnd j)
    have htailψ' : EquicontinuousAt (fun k : {k : ℕ // j + 1 ≤ k} => ψ k.val) x :=
      htailψ.comp (fun k : {k : ℕ // j + 1 ≤ k} =>
        (⟨k.val, by have := k.2; omega⟩ : {k : ℕ // j ≤ k}))
    have htail : EquicontinuousAt (fun k : {k : ℕ // j + 1 ≤ k} => F k.val) x := by
      refine equicontinuousAt_congr ?_ ?_ htailψ'
      · filter_upwards [(hVo j).mem_nhds hxj] with y hy i
        exact hΨ i.val y (hVsubS j i.val (by omega) hy)
      · intro i; exact hΨ i.val x (hVsubS j i.val (by omega) hxj)
    exact equicontinuousAt_nat_split (j + 1) hhead htail
  -- pointwise boundedness
  have hbdd : ∀ x : X, ∃ Q : Set ℂ, IsCompact Q ∧ ∀ k, F k x ∈ Q := by
    intro x
    obtain ⟨j, hxj⟩ : ∃ j, x ∈ V j := by
      have : x ∈ ⋃ n, V n := by rw [hunion]; trivial
      exact mem_iUnion.mp this
    obtain ⟨C, hC⟩ := hbnd j {x} isCompact_singleton (singleton_subset_iff.mpr hxj)
    set C' : ℝ := (Finset.range (j + 1)).sup' (by simp) (fun k => ‖F k x‖) with hC'
    refine ⟨closedBall 0 (max C C'), isCompact_closedBall _ _, fun k => ?_⟩
    rw [mem_closedBall_zero_iff]
    rcases le_or_gt (j + 1) k with hk | hk
    · have hkj : j ≤ k := by omega
      have : F k x = ψ k x := hΨ k x (hVsubS j k (by omega) hxj)
      rw [this]
      exact le_trans (hC k hkj x rfl) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right C C')
      exact Finset.le_sup' (fun k => ‖F k x‖) (Finset.mem_range.mpr hk)
  -- Montel: extract a locally uniform limit
  obtain ⟨σ, f, hσ, hunif⟩ := montel_extraction heqc hbdd
  -- convergence of the ψ-subsequence on each `V n`
  have hconvψ : ∀ n, ∀ (K : Set X), IsCompact K → K ⊆ V n →
      TendstoUniformlyOn (fun k => ψ (σ k)) f atTop K := by
    intro n K hKc hKV
    have hbase := hunif K hKc
    refine hbase.congr ?_
    -- eventually `F (σ k) = ψ (σ k)` on `K`
    have hσtop : ∀ᶠ k in atTop, n < σ k := by
      have := hσ.tendsto_atTop
      exact this.eventually_gt_atTop n
    filter_upwards [hσtop] with k hk y hy
    show F (σ k) y = ψ (σ k) y
    exact hΨ (σ k) y (hVsubS n (σ k) hk (hKV hy))
  -- locally uniform convergence of chart reps around any point of `V n`
  have hchartloc : ∀ (b : X) (n : ℕ), b ∈ V n →
      TendstoLocallyUniformlyOn (fun k => ψ (σ k) ∘ (chartAt ℂ b).symm)
        (f ∘ (chartAt ℂ b).symm) atTop (chartImage (chartAt ℂ b) (V n)) := by
    intro b n _
    set e := chartAt ℂ b
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_chartImage e (hVo n))]
    intro K hKU hKc
    have hKsub : e.symm '' K ⊆ V n := by
      rintro _ ⟨z, hz, rfl⟩; exact mapsTo_symm_chartImage (hKU hz)
    have hKcomp : IsCompact (e.symm '' K) :=
      hKc.image_of_continuousOn
        (e.symm.continuousOn.mono (fun z hz => chartImage_subset_target e (V n) (hKU hz)))
    have hc := (hconvψ n (e.symm '' K) hKcomp hKsub).comp e.symm
    exact hc.mono (fun z hz => ⟨z, hz, rfl⟩)
  -- eventual differentiability of chart reps
  have hchartdiff : ∀ (b : X) (n : ℕ),
      ∀ᶠ k in atTop, DifferentiableOn ℂ (ψ (σ k) ∘ (chartAt ℂ b).symm)
        (chartImage (chartAt ℂ b) (V n)) := by
    intro b n
    set e := chartAt ℂ b
    have hσtop : ∀ᶠ k in atTop, n ≤ σ k := (hσ.tendsto_atTop).eventually_ge_atTop n
    filter_upwards [hσtop] with k hk z hz
    have hzt : z ∈ e.target := chartImage_subset_target e (V n) hz
    have hzV : e.symm z ∈ V n := mapsTo_symm_chartImage hz
    have han : AnalyticAt ℂ (ψ (σ k) ∘ e.symm) z := by
      have hh := (hholo (σ k)).analyticAt_comp_symm (chartAt_mem_riemannAtlas b)
        (x := e.symm z) ⟨hmono hk hzV, e.map_target hzt⟩
      rwa [e.right_inv hzt] at hh
    exact han.differentiableAt.differentiableWithinAt
  -- HolomorphicOn f univ
  have hfholo : HolomorphicOn f univ := by
    intro x _
    obtain ⟨n, hxn⟩ : ∃ n, x ∈ V n := by
      have : x ∈ ⋃ n, V n := by rw [hunion]; trivial
      exact mem_iUnion.mp this
    set e := chartAt ℂ x
    have hUopen : IsOpen (chartImage e (V n)) := isOpen_chartImage e (hVo n)
    have hdiff : DifferentiableOn ℂ (f ∘ e.symm) (chartImage e (V n)) :=
      (hchartloc x n hxn).differentiableOn (hchartdiff x n) hUopen
    exact (hdiff.analyticOnNhd hUopen) (e x)
      (mem_chartImage_of_mem hxn (mem_chart_source ℂ x))
  -- chart-derivative of `f` at `x₀` equals 1 (so `f` is nonconstant)
  have hfderiv : deriv (f ∘ (chartAt ℂ x₀).symm) (chartAt ℂ x₀ x₀) = 1 := by
    have hUopen : IsOpen (chartImage (chartAt ℂ x₀) (V 0)) := isOpen_chartImage _ (hVo 0)
    have hex0 : chartAt ℂ x₀ x₀ ∈ chartImage (chartAt ℂ x₀) (V 0) :=
      mem_chartImage_of_mem (hmemV 0) (mem_chart_source ℂ x₀)
    have hderivloc := (hchartloc x₀ 0 (hmemV 0)).deriv (hchartdiff x₀ 0) hUopen
    have htend := hderivloc.tendsto_at hex0
    have hc1 : Tendsto (fun i => (deriv ∘ fun k => ψ (σ k) ∘ (chartAt ℂ x₀).symm) i
        (chartAt ℂ x₀ x₀)) atTop (𝓝 1) := by
      have hconst : (fun i => (deriv ∘ fun k => ψ (σ k) ∘ (chartAt ℂ x₀).symm) i
          (chartAt ℂ x₀ x₀)) = fun _ => (1 : ℂ) := by
        funext i; exact hd (σ i)
      rw [hconst]; exact tendsto_const_nhds
    exact tendsto_nhds_unique htend hc1
  refine ⟨f, hfholo, ?_⟩
  -- Function.Injective f
  intro a b hab
  by_contra hne
  -- both `a, b` lie in some `V n`
  obtain ⟨p, hap⟩ : ∃ p, a ∈ V p := by
    have : a ∈ ⋃ n, V n := by rw [hunion]; trivial
    exact mem_iUnion.mp this
  obtain ⟨q, hbq⟩ : ∃ q, b ∈ V q := by
    have : b ∈ ⋃ n, V n := by rw [hunion]; trivial
    exact mem_iUnion.mp this
  set n := max p q with hn
  have haV : a ∈ V n := hmono (le_max_left p q) hap
  have hbV : b ∈ V n := hmono (le_max_right p q) hbq
  set e := chartAt ℂ b with he
  have hbe : b ∈ e.source := mem_chart_source ℂ b
  -- a small preconnected chart ball around `b` inside `V n`, avoiding `a`
  have hNnhd : e.target ∩ e.symm ⁻¹' (V n \ {a}) ∈ 𝓝 (e b) := by
    refine (e.symm.continuousOn.isOpen_inter_preimage e.open_target
      ((hVo n).sdiff isClosed_singleton)).mem_nhds ?_
    refine ⟨e.map_source hbe, ?_⟩
    show e.symm (e b) ∈ V n \ {a}
    rw [e.left_inv hbe]
    exact ⟨hbV, fun h => hne (Set.mem_singleton_iff.mp h).symm⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hNnhd
  set W : Set ℂ := ball (e b) r with hW
  have hWo : IsOpen W := isOpen_ball
  have hWc : IsPreconnected W := (convex_ball _ _).isPreconnected
  have hWsub : W ⊆ e.target ∩ e.symm ⁻¹' (V n \ {a}) := hrsub
  have hebW : e b ∈ W := mem_ball_self hr
  have hWchart : W ⊆ chartImage e (V n) := by
    intro w hw
    have hwt : w ∈ e.target := (hWsub hw).1
    have hwV : e.symm w ∈ V n := (hWsub hw).2.1
    rw [← e.right_inv hwt]
    exact mem_chartImage_of_mem hwV (e.map_target hwt)
  -- the shifted family and its limit
  set G : ℕ → ℂ → ℂ := fun k w => (ψ (σ k) ∘ e.symm) w - ψ (σ k) a with hG
  set g : ℂ → ℂ := fun w => (f ∘ e.symm) w - f a with hg
  have hσtop : ∀ᶠ k in atTop, n ≤ σ k := (hσ.tendsto_atTop).eventually_ge_atTop n
  -- nonvanishing of `G k` on `W`
  have hGne : ∀ᶠ k in atTop, ∀ w ∈ W, G k w ≠ 0 := by
    filter_upwards [hσtop] with k hk w hw
    have hzV : e.symm w ∈ V n := (hWsub hw).2.1
    have hzne : e.symm w ≠ a := (hWsub hw).2.2
    show (ψ (σ k) ∘ e.symm) w - ψ (σ k) a ≠ 0
    rw [sub_ne_zero]
    intro heq
    exact hzne (hinjn (σ k) (hmono hk hzV) (hmono hk haV) heq)
  -- differentiability of `G k` on `W`
  have hGd : ∀ᶠ k in atTop, DifferentiableOn ℂ (G k) W := by
    filter_upwards [hchartdiff b n] with k hk
    exact (hk.mono hWchart).sub_const _
  -- `ψ (σ k) a → f a`
  have hψa : Tendsto (fun k => ψ (σ k) a) atTop (𝓝 (f a)) :=
    (hconvψ n {a} isCompact_singleton (singleton_subset_iff.mpr haV)).tendsto_at rfl
  -- locally uniform convergence `G k → g`
  have hA : TendstoLocallyUniformlyOn (fun k => ψ (σ k) ∘ e.symm) (f ∘ e.symm) atTop W :=
    (hchartloc b n hbV).mono hWchart
  have hB : TendstoLocallyUniformlyOn (fun k (_ : ℂ) => ψ (σ k) a) (fun _ => f a) atTop W :=
    (hψa.tendstoUniformly_fun_const).tendstoUniformlyOn.tendstoLocallyUniformlyOn
  have hglob : TendstoLocallyUniformlyOn G g atTop W := hA.sub hB
  -- Hurwitz
  rcases Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn hWo hWc hGne hGd hglob
    with hzero | hnonzero
  · -- `g ≡ 0` on `W` ⟹ `f` is locally constant at `b` ⟹ constant, contradicting `deriv = 1`
    have hfconst : f =ᶠ[𝓝 b] (fun _ => f a) := by
      have hWnhd : ⇑e ⁻¹' W ∩ e.source ∈ 𝓝 b :=
        inter_mem ((e.continuousOn.continuousAt (e.open_source.mem_nhds hbe)).preimage_mem_nhds
          (hWo.mem_nhds hebW)) (e.open_source.mem_nhds hbe)
      filter_upwards [hWnhd] with y hy
      have hgy := hzero hy.1
      simp only [hg] at hgy
      rw [Function.comp_apply, e.left_inv hy.2] at hgy
      exact sub_eq_zero.mp hgy
    have hconstuniv : EqOn f (fun _ => f a) univ :=
      hfholo.eqOn_of_eventuallyEq (fun _ _ => analyticAt_const) isOpen_univ
        isPreconnected_univ (mem_univ b) hfconst
    have hderiv0 : deriv (f ∘ (chartAt ℂ x₀).symm) (chartAt ℂ x₀ x₀) = 0 := by
      have hfc : (f ∘ (chartAt ℂ x₀).symm) = fun _ => f a := by
        funext z; exact hconstuniv (mem_univ _)
      rw [hfc, deriv_const]
    rw [hfderiv] at hderiv0
    exact one_ne_zero hderiv0
  · -- `g (e b) ≠ 0` means `f b ≠ f a`, contradicting `f a = f b`
    refine (hnonzero (e b) hebW) ?_
    show (f ∘ e.symm) (e b) - f a = 0
    rw [Function.comp_apply, e.left_inv hbe, hab, sub_self]

end Exhaustion

end Uniformization
