/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.PhiCover
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Injectivity of the Green-modulus map `φ` (Anghel–Stan Theorem 10)

Given a Green's function `G` on a relatively compact connected open `U ∋ x₀`
and a holomorphic `φ` on `U` with `φ x₀ = 0` and `‖φ x‖ = e^{−G x}` away from
`x₀`, the map `φ` is injective on `U`.

The proof follows Anghel–Stan: the set
`A = {x ∈ U | dφ_x ≠ 0 ∧ φ⁻¹(φ x) ∩ U = {x}}` is open, relatively closed in
`U`, and nonempty (it contains `x₀`), hence equals `U` by connectedness;
injectivity is the fiber condition of `A`.
-/

open Set Metric Topology Filter Complex

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Local normal form: injectivity forces a nonvanishing derivative

Copied from `Uniformization.Surface.Packaging` (where it is `private`). -/

/-- **Local injectivity forces a nonvanishing derivative.** -/
private theorem deriv_ne_zero_of_injOn {F : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀)
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

/-- **Multiplicity ≥ 2 gives doubled values.** If `F` is analytic at `z₀` with
`deriv F z₀ = 0` and `F` is not locally constant, then every value `w ≠ F z₀`
sufficiently close to `F z₀` has (at least) two distinct preimages arbitrarily
close to `z₀`. -/
private theorem exists_two_preimages_of_deriv_zero {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F z₀) (hderiv : deriv F z₀ = 0)
    (hncst : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀) {s : Set ℂ} (hs : s ∈ 𝓝 z₀) :
    ∃ η > 0, ∀ w : ℂ, ‖w - F z₀‖ < η → w ≠ F z₀ →
      ∃ z₁ ∈ s, ∃ z₂ ∈ s, z₁ ≠ z₂ ∧ F z₁ = w ∧ F z₂ = w := by
  set G : ℂ → ℂ := fun z => F z - F z₀ with hGdef
  have hGan : AnalyticAt ℂ G z₀ := hF.sub analyticAt_const
  have hGderiv : deriv G z₀ = 0 := by
    simp only [hGdef]; rw [deriv_sub_const]; exact hderiv
  have hGne : ¬ (∀ᶠ z in 𝓝 z₀, G z = 0) := by
    intro hev; apply hncst
    filter_upwards [hev] with z hz; simpa [hGdef, sub_eq_zero] using hz
  obtain ⟨n, g, hgan, hgne, hfact⟩ :=
    (hGan.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hGne
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hgg : G =ᶠ[𝓝 z₀] g := by filter_upwards [hfact] with z hz; simpa using hz
    have := hgg.eq_of_nhds
    simp only [hGdef, sub_self] at this; exact hgne this.symm
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
  set c : ℂ := g z₀ with hcdef
  have hc0 : c ≠ 0 := hgne
  set root : ℂ → ℂ := fun z => (g z / c) ^ ((n : ℂ)⁻¹) with hrootdef
  have hbase_an : AnalyticAt ℂ (fun z => g z / c) z₀ := hgan.div analyticAt_const hc0
  have hroot_an : AnalyticAt ℂ root z₀ := by
    apply hbase_an.cpow analyticAt_const
    show g z₀ / c ∈ slitPlane
    rw [← hcdef, div_self hc0]; exact one_mem_slitPlane
  have hroot_pow : ∀ z, root z ^ n = g z / c := fun z => Complex.cpow_nat_inv_pow _ hn0
  have hroot_z₀ : root z₀ = 1 := by simp only [hrootdef]; rw [← hcdef, div_self hc0, one_cpow]
  set w0 : ℂ := c ^ ((n : ℂ)⁻¹) with hw0def
  have hwn : w0 ^ n = c := Complex.cpow_nat_inv_pow c hn0
  have hw00 : w0 ≠ 0 := by intro h; apply hc0; rw [← hwn, h, zero_pow hn0]
  set h : ℂ → ℂ := fun z => w0 * root z with hhdef
  have hh_an : AnalyticAt ℂ h z₀ := analyticAt_const.mul hroot_an
  have hh_z₀ : h z₀ = w0 := by simp [hhdef, hroot_z₀]
  have hh_pow : ∀ z, h z ^ n = g z := by
    intro z
    simp only [hhdef, mul_pow, hwn, hroot_pow z]
    rw [mul_comm, div_mul_cancel₀ _ hc0]
  set H : ℂ → ℂ := fun z => (z - z₀) * h z with hHdef
  have hH_an : AnalyticAt ℂ H z₀ := (analyticAt_id.sub analyticAt_const).mul hh_an
  have hH_z₀ : H z₀ = 0 := by simp [hHdef]
  have hHpow : ∀ᶠ z in 𝓝 z₀, F z = F z₀ + H z ^ n := by
    filter_upwards [hfact] with z hz
    have hGH : G z = H z ^ n := by simp only [hHdef, mul_pow, hh_pow z]; rw [hz, smul_eq_mul]
    simpa [hGdef, sub_eq_iff_eq_add'] using hGH
  have hHderiv : HasStrictDerivAt H w0 z₀ := by
    have hsd := hH_an.hasStrictDerivAt
    have hderivH : deriv H z₀ = w0 := by
      have hd : HasDerivAt H (h z₀) z₀ := by
        simp only [hHdef]
        have h1 : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
        have h2 : HasDerivAt h (deriv h z₀) z₀ := hh_an.differentiableAt.hasDerivAt
        have h3 := h1.mul h2
        rw [show (1:ℂ) * h z₀ + (z₀ - z₀) * deriv h z₀ = h z₀ from by ring] at h3
        exact h3
      rw [hd.deriv, hh_z₀]
    rwa [hderivH] at hsd
  let i : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 w0 hw00)
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
    apply hsymm_cont.preimage_mem_nhds; rw [hsymm0]; exact hWnhd
  have hN : R.target ∩ R.symm ⁻¹' W ∈ 𝓝 (0 : ℂ) := inter_mem hRtgt_nhds hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / n) with hζdef
  have hζprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζpow : ζ ^ n = 1 := hζprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζprim.ne_one (by omega)
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζpow hn0
  refine ⟨ε ^ n, by positivity, ?_⟩
  intro w hw hwne
  set δ : ℂ := w - F z₀ with hδ_def
  have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hwne
  set s₀ : ℂ := δ ^ ((n : ℂ)⁻¹) with hs₀_def
  have hs₀pow : s₀ ^ n = δ := Complex.cpow_nat_inv_pow δ hn0
  have hs₀norm : ‖s₀‖ < ε := by
    have h1 : ‖s₀‖ ^ n = ‖δ‖ := by rw [← norm_pow, hs₀pow]
    have h2 : ‖s₀‖ ^ n < ε ^ n := by rw [h1, hδ_def]; exact hw
    exact lt_of_pow_lt_pow_left₀ n (le_of_lt hε) h2
  have hs₀0 : s₀ ≠ 0 := by intro hh; apply hδ0; rw [← hs₀pow, hh, zero_pow hn0]
  have hs₀ball : s₀ ∈ ball (0:ℂ) ε := by
    simpa [Metric.mem_ball, dist_zero_right] using hs₀norm
  have hζs₀ball : ζ * s₀ ∈ ball (0:ℂ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul]; exact hs₀norm
  have hs₀mem : s₀ ∈ R.target ∩ R.symm ⁻¹' W := hball hs₀ball
  have hζmem : ζ * s₀ ∈ R.target ∩ R.symm ⁻¹' W := hball hζs₀ball
  set z₁ : ℂ := R.symm s₀ with hz₁_def
  set z₂ : ℂ := R.symm (ζ * s₀) with hz₂_def
  have hz₁W : z₁ ∈ W := hs₀mem.2
  have hz₂W : z₂ ∈ W := hζmem.2
  have hHz₁ : H z₁ = s₀ := by rw [← hRcoe z₁]; exact R.right_inv hs₀mem.1
  have hHz₂ : H z₂ = ζ * s₀ := by rw [← hRcoe z₂]; exact R.right_inv hζmem.1
  have hFz₁ : F z₁ = w := by
    rw [show F z₁ = F z₀ + H z₁ ^ n from hz₁W.1, hHz₁, hs₀pow, hδ_def]; ring
  have hFz₂ : F z₂ = w := by
    rw [show F z₂ = F z₀ + H z₂ ^ n from hz₂W.1, hHz₂, mul_pow, hζpow, one_mul, hs₀pow, hδ_def]; ring
  have hne12 : z₁ ≠ z₂ := by
    intro he
    have heqH : H z₁ = H z₂ := by rw [he]
    rw [hHz₁, hHz₂] at heqH
    have h0 : (1 - ζ) * s₀ = 0 := by rw [sub_mul, one_mul, ← heqH, sub_self]
    rcases mul_eq_zero.mp h0 with hh | hh
    · exact hζ1 (sub_eq_zero.mp hh).symm
    · exact hs₀0 hh
  exact ⟨z₁, hz₁W.2, z₂, hz₂W.2, hne12, hFz₁, hFz₂⟩

/-! ## Chart independence of the nonvanishing-derivative condition -/

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Transition maps have nonvanishing derivative (they are local biholomorphisms). -/
private theorem transition_deriv_ne_zero {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) (he' : e' ∈ riemannAtlas X) {x : X}
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) :
    deriv (e ∘ e'.symm) (e' x) ≠ 0 := by
  have han : AnalyticAt ℂ (e ∘ e'.symm) (e' x) :=
    transition_analyticAt he' he ⟨hxe', hxe⟩
  set s : Set ℂ := e'.target ∩ e'.symm ⁻¹' e.source with hs_def
  have hso : IsOpen s := e'.symm.continuousOn.isOpen_inter_preimage e'.open_target e.open_source
  have hmem : e' x ∈ s := by
    refine ⟨e'.map_source hxe', ?_⟩
    show e'.symm (e' x) ∈ e.source
    rw [e'.left_inv hxe']; exact hxe
  have hinj : Set.InjOn (e ∘ e'.symm) s := by
    intro a ha b hb hab
    simp only [Function.comp_apply] at hab
    have hea : e'.symm a ∈ e.source := ha.2
    have heb : e'.symm b ∈ e.source := hb.2
    have : e'.symm a = e'.symm b := e.injOn hea heb hab
    calc a = e' (e'.symm a) := (e'.right_inv ha.1).symm
      _ = e' (e'.symm b) := by rw [this]
      _ = b := e'.right_inv hb.1
  exact deriv_ne_zero_of_injOn han (hso.mem_nhds hmem) hinj

/-- The nonvanishing of the chart derivative of a holomorphic map does not depend
on the choice of chart. -/
private theorem deriv_comp_symm_ne_zero_congr {φ : X → ℂ} {s : Set X}
    (hφ : HolomorphicOn φ s) {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) (he' : e' ∈ riemannAtlas X) {x : X}
    (hxs : x ∈ s) (hxe : x ∈ e.source) (hxe' : x ∈ e'.source)
    (hne : deriv (φ ∘ e.symm) (e x) ≠ 0) : deriv (φ ∘ e'.symm) (e' x) ≠ 0 := by
  set τ : ℂ → ℂ := e ∘ e'.symm with hτ_def
  have hτan : AnalyticAt ℂ τ (e' x) := transition_analyticAt he' he ⟨hxe', hxe⟩
  have hτval : τ (e' x) = e x := by
    simp only [hτ_def, Function.comp_apply, e'.left_inv hxe']
  have hφan : AnalyticAt ℂ (φ ∘ e.symm) (e x) := hφ.analyticAt_comp_symm he ⟨hxs, hxe⟩
  -- `φ ∘ e'.symm` agrees with `(φ ∘ e.symm) ∘ τ` near `e' x`
  have hN : e'.target ∩ e'.symm ⁻¹' e.source ∈ 𝓝 (e' x) := by
    refine (e'.symm.continuousOn.isOpen_inter_preimage e'.open_target e.open_source).mem_nhds ?_
    exact ⟨e'.map_source hxe', by show e'.symm (e' x) ∈ e.source; rw [e'.left_inv hxe']; exact hxe⟩
  have hcongr : (φ ∘ e'.symm) =ᶠ[𝓝 (e' x)] (φ ∘ e.symm) ∘ τ := by
    filter_upwards [hN] with w hw
    simp only [hτ_def, Function.comp_apply]
    rw [e.left_inv hw.2]
  rw [hcongr.deriv_eq]
  rw [deriv_comp _ (hτval ▸ hφan.differentiableAt) hτan.differentiableAt, hτval]
  exact mul_ne_zero hne (transition_deriv_ne_zero he he' hxe hxe')

/-! ## Nonvanishing derivative at the pole -/

/-- At the pole `x₀`, the chart derivative of `φ` is nonzero: in the log-pole
chart, `‖φ ∘ e.symm z‖ = ‖z‖·e^{−H z}` vanishes to order exactly `1`. -/
private theorem deriv_ne_zero_at_pole {U : Set X} {x₀ : X} {G : X → ℝ} {φ : X → ℂ}
    (hx₀ : x₀ ∈ U) (hG : IsGreenFunction U x₀ G) (hφ : HolomorphicOn φ U) (hφ0 : φ x₀ = 0)
    (hmod : ∀ x ∈ U \ {x₀}, ‖φ x‖ = Real.exp (-G x)) :
    ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ deriv (φ ∘ e.symm) (e x₀) ≠ 0 := by
  obtain ⟨e, he, hx₀e, hex₀, r, hr, htgt, hDU, H, hHharm, hHpole⟩ := hG.log_pole
  set g : ℂ → ℂ := φ ∘ e.symm with hg_def
  have hball_tgt : ball (0 : ℂ) r ⊆ e.target := ball_subset_closedBall.trans htgt
  have hx₀0 : e.symm 0 = x₀ := by rw [← hex₀, e.left_inv hx₀e]
  -- `g` analytic at `0`
  have hgan : AnalyticAt ℂ g 0 := by
    have := hφ.analyticAt_comp_symm he ⟨hx₀, hx₀e⟩
    rwa [hex₀] at this
  have hg0 : g 0 = 0 := by simp only [hg_def, Function.comp_apply, hx₀0, hφ0]
  -- modulus identity in the chart
  have hmodz : ∀ z ∈ ball (0 : ℂ) r \ {0}, ‖g z‖ = ‖z‖ * Real.exp (-H z) := by
    rintro z ⟨hz, hz0⟩
    have hz0' : z ≠ 0 := hz0
    have hzt : z ∈ e.target := hball_tgt hz
    have h0t : (0 : ℂ) ∈ e.target := hball_tgt (mem_ball_self hr)
    have hsymm_ne : e.symm z ≠ x₀ := by
      rw [← hx₀0]; intro hc
      apply hz0'
      have := congrArg e hc
      rwa [e.right_inv hzt, e.right_inv h0t] at this
    have hsymmU : e.symm z ∈ U \ {x₀} :=
      ⟨hDU ⟨z, ball_subset_closedBall hz, rfl⟩, hsymm_ne⟩
    have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0'
    calc ‖g z‖ = ‖φ (e.symm z)‖ := rfl
      _ = Real.exp (-G (e.symm z)) := hmod _ hsymmU
      _ = Real.exp (-(-Real.log ‖z‖ + H z)) := by rw [hHpole z ⟨hz, hz0⟩]
      _ = ‖z‖ * Real.exp (-H z) := by
          rw [neg_add, neg_neg, Real.exp_add, Real.exp_log hznorm]
  -- `g` is not eventually zero near `0`
  have hgne : ¬ (∀ᶠ z in 𝓝 (0 : ℂ), g z = 0) := by
    intro hev
    have hnb : (𝓝[≠] (0 : ℂ)).NeBot := inferInstance
    have hmem : (ball (0 : ℂ) r \ {0}) ∈ 𝓝[≠] (0 : ℂ) :=
      inter_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)))
        self_mem_nhdsWithin
    obtain ⟨z, ⟨hzb, hz0⟩, hzev⟩ :=
      hnb.nonempty_of_mem (inter_mem hmem (mem_nhdsWithin_of_mem_nhds hev))
    have h1 : ‖g z‖ = ‖z‖ * Real.exp (-H z) := hmodz z ⟨hzb, hz0⟩
    rw [hzev, norm_zero] at h1
    have : (0:ℝ) < ‖z‖ * Real.exp (-H z) :=
      mul_pos (norm_pos_iff.mpr hz0) (Real.exp_pos _)
    linarith
  -- factorization `g z = z ^ n • u z`
  obtain ⟨n, u, huan, hune, hfact⟩ :=
    (hgan.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hgne
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : g =ᶠ[𝓝 0] u := by filter_upwards [hfact] with z hz; simpa using hz
    have := this.eq_of_nhds; rw [hg0] at this; exact hune this.symm
  -- the modulus rules out order `≥ 2`, so `n = 1`
  have hn1 : n = 1 := by
    by_contra hne1
    have hn2 : 2 ≤ n := by omega
    -- eventual equality `‖z‖^(n-1) * ‖u z‖ = e^{-H z}` on `𝓝[≠] 0`
    set F1 : ℂ → ℝ := fun z => ‖z‖ ^ (n - 1) * ‖u z‖ with hF1_def
    set F2 : ℂ → ℝ := fun z => Real.exp (-H z) with hF2_def
    have hev : F1 =ᶠ[𝓝[≠] (0:ℂ)] F2 := by
      have hmem1 : (ball (0 : ℂ) r \ {0}) ∈ 𝓝[≠] (0 : ℂ) :=
        inter_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)))
          self_mem_nhdsWithin
      filter_upwards [hmem1, hfact.filter_mono nhdsWithin_le_nhds] with z hz hzfac
      have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz.2
      have h1 : ‖g z‖ = ‖z‖ ^ n * ‖u z‖ := by
        rw [hzfac, sub_zero, smul_eq_mul, norm_mul, norm_pow]
      have h2 : ‖g z‖ = ‖z‖ * Real.exp (-H z) := hmodz z hz
      have h3 : ‖z‖ ^ n * ‖u z‖ = ‖z‖ * Real.exp (-H z) := by rw [← h1, h2]
      have hpow : ‖z‖ ^ n = ‖z‖ * ‖z‖ ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hpow, mul_assoc] at h3
      show ‖z‖ ^ (n - 1) * ‖u z‖ = Real.exp (-H z)
      exact mul_left_cancel₀ (ne_of_gt hznorm) h3
    -- `F1 → 0`
    have hF1lim : Tendsto F1 (𝓝[≠] (0:ℂ)) (𝓝 0) := by
      have hcont : ContinuousAt F1 0 := by
        apply ContinuousAt.mul
        · exact (continuous_norm.continuousAt).pow _
        · exact (huan.continuousAt).norm
      have h0 : F1 0 = 0 := by
        show ‖(0:ℂ)‖ ^ (n - 1) * ‖u 0‖ = 0
        rw [norm_zero, zero_pow (by omega : n - 1 ≠ 0), zero_mul]
      have htend : Tendsto F1 (𝓝[≠] (0:ℂ)) (𝓝 (F1 0)) := hcont.continuousWithinAt
      rw [h0] at htend
      exact htend
    -- `F2 → e^{-H 0}`
    have hF2lim : Tendsto F2 (𝓝[≠] (0:ℂ)) (𝓝 (Real.exp (-H 0))) := by
      have hHc : ContinuousAt H 0 := (hHharm 0 (mem_ball_self hr)).1.continuousAt
      have : ContinuousAt F2 0 := (Real.continuous_exp.continuousAt).comp (hHc.neg)
      exact this.continuousWithinAt
    have hlim : Tendsto F1 (𝓝[≠] (0:ℂ)) (𝓝 (Real.exp (-H 0))) := hF2lim.congr' hev.symm
    have : (0:ℝ) = Real.exp (-H 0) := tendsto_nhds_unique hF1lim hlim
    exact (Real.exp_pos _).ne this
  -- `n = 1` ⇒ `deriv g 0 = u 0 ≠ 0`
  refine ⟨e, he, hx₀e, ?_⟩
  rw [hex₀]
  have hev1 : g =ᶠ[𝓝 0] fun z => z * u z := by
    filter_upwards [hfact] with z hz; rw [hz, hn1]; simp [smul_eq_mul]
  have hd : HasDerivAt (fun z => z * u z) (u 0) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => z) 1 0 := hasDerivAt_id 0
    have h2 : HasDerivAt u (deriv u 0) 0 := huan.differentiableAt.hasDerivAt
    have h3 := h1.mul h2
    rw [show (1:ℂ) * u 0 + 0 * deriv u 0 = u 0 from by ring] at h3
    exact h3
  rw [hev1.deriv_eq, hd.deriv]
  exact hune

/-! ## Compact sublevel sets of `‖φ‖` -/

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- For `t < 1`, the sublevel set `{y ∈ U | ‖φ y‖ ≤ t}` is compact: it is closed
in `X` (limit points on `frontier U` would force `‖φ‖ = 1 > t`) and contained in
the compact `closure U`. -/
private theorem isCompact_sublevel [T2Space X] {U : Set X} {x₀ : X} {G : X → ℝ} {φ : X → ℂ}
    (hUo : IsOpen U) (hUc : IsCompact (closure U)) (hx₀ : x₀ ∈ U)
    (hG : IsGreenFunction U x₀ G)
    (hmod : ∀ x ∈ U \ {x₀}, ‖φ x‖ = Real.exp (-G x))
    (hφ : HolomorphicOn φ U) {t : ℝ} (ht : t < 1) :
    IsCompact {y | y ∈ U ∧ ‖φ y‖ ≤ t} := by
  set K : Set X := {y | y ∈ U ∧ ‖φ y‖ ≤ t} with hK_def
  have hKsub : K ⊆ closure U := fun y hy ↦ subset_closure hy.1
  refine hUc.of_isClosed_subset ?_ hKsub
  rw [← closure_subset_iff_isClosed]
  intro p hp
  have : (𝓝[K] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hpclU : p ∈ closure U := by
    have := closure_mono hKsub hp; rwa [closure_closure] at this
  by_cases hpU : p ∈ U
  · have hca : ContinuousAt φ p := (hφ.continuousOn).continuousAt (hUo.mem_nhds hpU)
    have hlim : Tendsto (fun y ↦ ‖φ y‖) (𝓝[K] p) (𝓝 (‖φ p‖)) :=
      (hca.norm).continuousWithinAt
    have hev : ∀ᶠ y in 𝓝[K] p, ‖φ y‖ ≤ t := by
      filter_upwards [self_mem_nhdsWithin] with y hy; exact hy.2
    exact ⟨hpU, le_of_tendsto hlim hev⟩
  · exfalso
    have hpfr : p ∈ frontier U := by
      rw [frontier, hUo.interior_eq]; exact ⟨hpclU, hpU⟩
    have hpne : p ≠ x₀ := fun h ↦ hpU (h ▸ hx₀)
    have hGp : G p = 0 := hG.zero_frontier hpfr
    have hcompl : ({x₀}ᶜ : Set X) ∈ 𝓝 p :=
      (isClosed_singleton).isOpen_compl.mem_nhds hpne
    have hGcw : Tendsto G (𝓝[closure U \ {x₀}] p) (𝓝 (G p)) :=
      hG.continuousOn p ⟨hpclU, hpne⟩
    rw [hGp] at hGcw
    have hsub : K ∩ {x₀}ᶜ ⊆ closure U \ {x₀} := by
      rintro y ⟨hyK, hyne⟩; exact ⟨hKsub hyK, hyne⟩
    have hGK : Tendsto G (𝓝[K] p) (𝓝 0) := by
      have h1 : Tendsto G (𝓝[K ∩ {x₀}ᶜ] p) (𝓝 0) := hGcw.mono_left (nhdsWithin_mono p hsub)
      rwa [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hcompl)] at h1
    have hexp : Tendsto (fun y ↦ Real.exp (-G y)) (𝓝[K] p) (𝓝 1) := by
      have h0 : Tendsto (fun y ↦ -G y) (𝓝[K] p) (𝓝 0) := by simpa using hGK.neg
      have := (Real.continuous_exp.tendsto 0).comp h0
      simpa [Function.comp_def] using this
    have hev : ∀ᶠ y in 𝓝[K] p, Real.exp (-G y) ≤ t := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hcompl] with y hy hyne
      rw [← hmod y ⟨hy.1, hyne⟩]; exact hy.2
    have : (1:ℝ) ≤ t := le_of_tendsto hexp hev
    linarith

/-! ## Local injectivity from a nonvanishing derivative -/

/-- If the chart derivative of `φ` at `x ∈ U` is nonzero, then `φ` is injective
on an open neighborhood of `x` contained in `U`. -/
private theorem exists_inj_nhd {U : Set X} (hUo : IsOpen U) {φ : X → ℂ}
    (hφ : HolomorphicOn φ U) {x : X} (hxU : x ∈ U)
    (hnd : deriv (φ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0) :
    ∃ D, IsOpen D ∧ x ∈ D ∧ D ⊆ U ∧ Set.InjOn φ D := by
  set e := chartAt ℂ x with he_def
  have he : e ∈ riemannAtlas X := chartAt_mem_riemannAtlas x
  have hxe : x ∈ e.source := mem_chart_source ℂ x
  set g : ℂ → ℂ := φ ∘ e.symm with hg_def
  have hgan : AnalyticAt ℂ g (e x) := hφ.analyticAt_comp_symm he ⟨hxU, hxe⟩
  have hsd : HasStrictDerivAt g (deriv g (e x)) (e x) := hgan.hasStrictDerivAt
  set i : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hnd) with hi_def
  have hfd : HasStrictFDerivAt g (i : ℂ →L[ℂ] ℂ) (e x) := hsd
  set R : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph g with hR_def
  have hRcoe : (↑R : ℂ → ℂ) = g := hfd.toOpenPartialHomeomorph_coe
  have hexR : e x ∈ R.source := hfd.mem_toOpenPartialHomeomorph_source
  have hRinj : Set.InjOn g R.source := by rw [← hRcoe]; exact R.injOn
  -- open set in the chart target where `g` is injective and preimages land in `U`
  set V : Set ℂ := R.source ∩ (e.target ∩ e.symm ⁻¹' U) with hV_def
  have hVo : IsOpen V :=
    R.open_source.inter (e.symm.continuousOn.isOpen_inter_preimage e.open_target hUo)
  have hexV : e x ∈ V := by
    refine ⟨hexR, e.map_source hxe, ?_⟩
    show e.symm (e x) ∈ U; rw [e.left_inv hxe]; exact hxU
  have hVsub : V ⊆ e.target := fun w hw ↦ hw.2.1
  set D : Set X := e.symm '' V with hD_def
  have hDo : IsOpen D :=
    e.symm.isOpen_image_of_subset_source hVo (by simpa using hVsub)
  have hxD : x ∈ D := ⟨e x, hexV, e.left_inv hxe⟩
  have hDU : D ⊆ U := by
    rintro _ ⟨w, hw, rfl⟩; exact hw.2.2
  have hinj : Set.InjOn φ D := by
    rintro _ ⟨wa, hwa, rfl⟩ _ ⟨wb, hwb, rfl⟩ hab
    have hga : g wa = φ (e.symm wa) := rfl
    have hgb : g wb = φ (e.symm wb) := rfl
    have : g wa = g wb := by rw [hga, hgb]; exact hab
    rw [hRinj hwa.1 hwb.1 this]
  exact ⟨D, hDo, hxD, hDU, hinj⟩

/-! ## The main theorem -/

theorem phi_injOn [T2Space X] {U : Set X} {x₀ : X} {G : X → ℝ} {φ : X → ℂ}
    (hUo : IsOpen U) (hUconn : IsPreconnected U) (hUc : IsCompact (closure U))
    (hx₀ : x₀ ∈ U) (hG : IsGreenFunction U x₀ G)
    (hφ : HolomorphicOn φ U) (hφ0 : φ x₀ = 0)
    (hmod : ∀ x ∈ U \ {x₀}, ‖φ x‖ = Real.exp (-G x)) :
    Set.InjOn φ U := by
  -- basic facts
  have hnormlt : ∀ x ∈ U, ‖φ x‖ < 1 := by
    intro x hx
    by_cases hxx₀ : x = x₀
    · rw [hxx₀, hφ0, norm_zero]; exact one_pos
    · rw [hmod x ⟨hx, hxx₀⟩]
      have : 0 < G x := hG.pos x ⟨hx, hxx₀⟩
      calc Real.exp (-G x) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
  have hzero : ∀ y ∈ U, φ y = 0 → y = x₀ := by
    intro y hy hy0
    by_contra hne
    have h := hmod y ⟨hy, hne⟩
    rw [hy0, norm_zero] at h
    exact (Real.exp_pos _).ne' h.symm
  by_cases hsingle : ∀ y ∈ U, y = x₀
  · intro a ha b hb _; rw [hsingle a ha, hsingle b hb]
  push Not at hsingle
  obtain ⟨x₁, hx₁U, hx₁ne⟩ := hsingle
  have hφx₁ : φ x₁ ≠ 0 := fun h ↦ hx₁ne (hzero x₁ hx₁U h)
  -- `φ` is not eventually constant near any point of `U`
  have hncst : ∀ z ∈ U, ¬ (φ =ᶠ[𝓝 z] fun _ ↦ φ z) := by
    intro z hz hev
    have hconst : HolomorphicOn (fun _ : X ↦ φ z) U := fun x _ ↦ analyticAt_const
    have heq : Set.EqOn φ (fun _ ↦ φ z) U := hφ.eqOn_of_eventuallyEq hconst hUo hUconn hz hev
    have h1 : φ x₁ = φ z := heq hx₁U
    have h2 : φ x₀ = φ z := heq hx₀
    rw [h1, ← h2, hφ0] at hφx₁
    exact hφx₁ rfl
  -- the good set
  set A : Set X := {x | x ∈ U ∧
      deriv (φ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 ∧
      ∀ y ∈ U, φ y = φ x → y = x} with hA_def
  -- `x₀ ∈ A`
  have hx₀A : x₀ ∈ A := by
    refine ⟨hx₀, ?_, ?_⟩
    · obtain ⟨e, he, hx₀e, hde⟩ := deriv_ne_zero_at_pole hx₀ hG hφ hφ0 hmod
      exact deriv_comp_symm_ne_zero_congr hφ he (chartAt_mem_riemannAtlas x₀) hx₀ hx₀e
        (mem_chart_source ℂ x₀) hde
    · intro y hy hφy
      rw [hφ0] at hφy
      exact hzero y hy hφy
  -- `A` is open
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hxA
    obtain ⟨hxU, hnd_x, hsf_x⟩ := hxA
    obtain ⟨D, hDo, hxD, hDU, hDinj⟩ := exists_inj_nhd hUo hφ hxU hnd_x
    set e := chartAt ℂ x with he_def
    have he : e ∈ riemannAtlas X := chartAt_mem_riemannAtlas x
    have hxe : x ∈ e.source := mem_chart_source ℂ x
    set g : ℂ → ℂ := φ ∘ e.symm with hg_def
    have hgan : AnalyticAt ℂ g (e x) := hφ.analyticAt_comp_symm he ⟨hxU, hxe⟩
    have hderiv_cont : ContinuousAt (deriv g) (e x) := hgan.deriv.continuousAt
    have hcont_ex : ContinuousAt (e : X → ℂ) x :=
      e.continuousOn.continuousAt (e.open_source.mem_nhds hxe)
    have hdne : ∀ᶠ z in 𝓝 (e x), deriv g z ≠ 0 := hderiv_cont.eventually_ne hnd_x
    have hWd : {w | deriv g (e w) ≠ 0} ∈ 𝓝 x := hcont_ex.preimage_mem_nhds hdne
    -- threshold `t < 1` with `‖φ x‖ < t`
    have hnx : ‖φ x‖ < 1 := hnormlt x hxU
    set ε : ℝ := (1 - ‖φ x‖) / 2 with hε_def
    have hεpos : 0 < ε := by rw [hε_def]; linarith
    set t : ℝ := 1 - ε with ht_def
    have ht1 : t < 1 := by rw [ht_def]; linarith
    have hxt : ‖φ x‖ < t := by rw [ht_def, hε_def]; linarith
    have hKc : IsCompact {y | y ∈ U ∧ ‖φ y‖ ≤ t} :=
      isCompact_sublevel hUo hUc hx₀ hG hmod hφ ht1
    set C : Set X := {y | y ∈ U ∧ ‖φ y‖ ≤ t} ∩ Dᶜ with hC_def
    have hCc : IsCompact C := hKc.inter_right hDo.isClosed_compl
    have hCU : C ⊆ U := fun y hy ↦ hy.1.1
    have hφCcl : IsClosed (φ '' C) := (hCc.image_of_continuousOn (hφ.continuousOn.mono hCU)).isClosed
    have hxnotC : φ x ∉ φ '' C := by
      rintro ⟨y, hyC, hyφ⟩
      have hyx : y = x := hsf_x y hyC.1.1 hyφ
      exact hyC.2 (hyx ▸ hxD)
    have hφcx : ContinuousAt φ x := hφ.continuousOn.continuousAt (hUo.mem_nhds hxU)
    have hW1 : D ∈ 𝓝 x := hDo.mem_nhds hxD
    have hW2 : {y | ‖φ y‖ < t} ∈ 𝓝 x := (hφcx.norm).preimage_mem_nhds (Iio_mem_nhds hxt)
    have hW3 : {y | φ y ∉ φ '' C} ∈ 𝓝 x :=
      hφcx.preimage_mem_nhds (hφCcl.isOpen_compl.mem_nhds hxnotC)
    have hW4 : e.source ∈ 𝓝 x := e.open_source.mem_nhds hxe
    filter_upwards [hW1, hW2, hW3, hWd, hW4, hUo.mem_nhds hxU] with w hwD hwt hwC hwd hwe hwU
    refine ⟨hwU, ?_, ?_⟩
    · exact deriv_comp_symm_ne_zero_congr hφ he (chartAt_mem_riemannAtlas w) hwU hwe
        (mem_chart_source ℂ w) hwd
    · intro y hyU hφy
      have hyt : ‖φ y‖ ≤ t := by rw [hφy]; exact le_of_lt hwt
      by_cases hyD : y ∈ D
      · exact hDinj hyD hwD hφy
      · have hyC : y ∈ C := ⟨⟨hyU, hyt⟩, hyD⟩
        have hmem : φ y ∈ φ '' C := ⟨y, hyC, rfl⟩
        rw [hφy] at hmem
        exact absurd hmem hwC
  -- `A` is relatively closed in `U`
  have hAclosed : U ∩ closure A ⊆ A := by
    rintro p ⟨hpU, hpcl⟩
    have hacc : (𝓝[A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hpcl
    have hφcp : ContinuousAt φ p := hφ.continuousOn.continuousAt (hUo.mem_nhds hpU)
    refine ⟨hpU, ?_, ?_⟩
    · -- nonvanishing derivative at `p` (else the `k ≥ 2` normal form breaks fibers)
      by_contra hnd0
      set e := chartAt ℂ p with he_def
      have he : e ∈ riemannAtlas X := chartAt_mem_riemannAtlas p
      have hpe : p ∈ e.source := mem_chart_source ℂ p
      set g : ℂ → ℂ := φ ∘ e.symm with hg_def
      have hgan : AnalyticAt ℂ g (e p) := hφ.analyticAt_comp_symm he ⟨hpU, hpe⟩
      have hgep : g (e p) = φ p := by rw [hg_def]; simp only [Function.comp_apply, e.left_inv hpe]
      have hg_ncst : ¬ ∀ᶠ z in 𝓝 (e p), g z = g (e p) := by
        intro hev
        apply hncst p hpU
        have hcont : ContinuousAt (e : X → ℂ) p :=
          e.continuousOn.continuousAt (e.open_source.mem_nhds hpe)
        filter_upwards [hcont.preimage_mem_nhds hev, e.open_source.mem_nhds hpe] with w hw hwsrc
        have h1 : φ w = g (e w) := by rw [hg_def]; simp only [Function.comp_apply, e.left_inv hwsrc]
        rw [h1, hw, hgep]
      have hpnotA : p ∉ A := fun hh ↦ hh.2.1 hnd0
      have hsnhd : (e.target ∩ e.symm ⁻¹' U) ∈ 𝓝 (e p) := by
        refine (e.symm.continuousOn.isOpen_inter_preimage e.open_target hUo).mem_nhds ?_
        exact ⟨e.map_source hpe, by show e.symm (e p) ∈ U; rw [e.left_inv hpe]; exact hpU⟩
      obtain ⟨η, hη, hpre⟩ := exists_two_preimages_of_deriv_zero hgan hnd0 hg_ncst hsnhd
      -- a nearby `A`-point `a` with `φ a ≠ φ p` and close to `φ p`
      have hclose : {y | ‖φ y - φ p‖ < η} ∈ 𝓝 p := by
        have hc : ContinuousAt (fun y ↦ ‖φ y - φ p‖) p := (hφcp.sub continuousAt_const).norm
        have hmem : Iio η ∈ 𝓝 ((fun y ↦ ‖φ y - φ p‖) p) := by
          simp only [sub_self, norm_zero]; exact Iio_mem_nhds hη
        exact hc.preimage_mem_nhds hmem
      obtain ⟨a, haA, haclose⟩ :=
        hacc.nonempty_of_mem (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hclose))
      have hane : a ≠ p := fun h ↦ hpnotA (h ▸ haA)
      have hφane : φ a ≠ φ p := by
        intro hh
        exact hane (haA.2.2 p hpU hh.symm).symm
      obtain ⟨z₁, hz₁s, z₂, hz₂s, hz12, hFz₁, hFz₂⟩ :=
        hpre (φ a) (by rw [hgep]; exact haclose) (by rw [hgep]; exact hφane)
      set xu := e.symm z₁ with hxu_def
      set xv := e.symm z₂ with hxv_def
      have hφxu : φ xu = φ a := hFz₁
      have hφxv : φ xv = φ a := hFz₂
      have hxua : xu = a := haA.2.2 xu hz₁s.2 hφxu
      have hxva : xv = a := haA.2.2 xv hz₂s.2 hφxv
      apply hz12
      have hxuxv : xu = xv := by rw [hxua, hxva]
      have := congrArg e hxuxv
      rwa [e.right_inv hz₁s.1, e.right_inv hz₂s.1] at this
    · -- singleton fiber at `p` (else the open mapping theorem at the second preimage breaks)
      intro q hqU hφq
      by_contra hqp
      set e := chartAt ℂ q with he_def
      have he : e ∈ riemannAtlas X := chartAt_mem_riemannAtlas q
      have hqe : q ∈ e.source := mem_chart_source ℂ q
      set g : ℂ → ℂ := φ ∘ e.symm with hg_def
      have hgan : AnalyticAt ℂ g (e q) := hφ.analyticAt_comp_symm he ⟨hqU, hqe⟩
      have hgeq : g (e q) = φ q := by rw [hg_def]; simp only [Function.comp_apply, e.left_inv hqe]
      have hg_ncst : ¬ ∀ᶠ z in 𝓝 (e q), g z = g (e q) := by
        intro hev
        apply hncst q hqU
        have hcont : ContinuousAt (e : X → ℂ) q :=
          e.continuousOn.continuousAt (e.open_source.mem_nhds hqe)
        filter_upwards [hcont.preimage_mem_nhds hev, e.open_source.mem_nhds hqe] with w hw hwsrc
        have h1 : φ w = g (e w) := by rw [hg_def]; simp only [Function.comp_apply, e.left_inv hwsrc]
        rw [h1, hw, hgeq]
      -- `φ` is an open map near `q`
      have hmap : Filter.map φ (𝓝 q) = Filter.map g (𝓝 (e q)) := by
        have h1 : Filter.map e.symm (𝓝 (e q)) = 𝓝 q := by
          rw [e.symm.map_nhds_eq (by rw [OpenPartialHomeomorph.symm_source]; exact e.map_source hqe),
            e.left_inv hqe]
        calc Filter.map φ (𝓝 q)
            = Filter.map φ (Filter.map e.symm (𝓝 (e q))) := by rw [h1]
          _ = Filter.map g (𝓝 (e q)) := by rw [Filter.map_map]
      have hopen_q : 𝓝 (φ q) ≤ Filter.map φ (𝓝 q) := by
        rw [hmap, ← hgeq]
        exact (hgan.eventually_constant_or_nhds_le_map_nhds).resolve_left hg_ncst
      -- separate `p` and `q`
      have hpq : p ≠ q := fun h ↦ hqp h.symm
      obtain ⟨Np, Nq, hNpo, hNqo, hpNp, hqNq, hdisj⟩ := t2_separation hpq
      have himg : φ '' (Nq ∩ U) ∈ 𝓝 (φ q) := by
        apply hopen_q
        show φ ⁻¹' (φ '' (Nq ∩ U)) ∈ 𝓝 q
        exact Filter.mem_of_superset ((hNqo.inter hUo).mem_nhds ⟨hqNq, hqU⟩)
          (fun y hy ↦ ⟨y, hy, rfl⟩)
      have hφc : Tendsto φ (𝓝[A] p) (𝓝 (φ q)) := by
        have h : Tendsto φ (𝓝[A] p) (𝓝 (φ p)) := hφcp.continuousWithinAt
        rwa [← hφq] at h
      obtain ⟨a, ⟨haA, haimg⟩, haNp⟩ :=
        hacc.nonempty_of_mem (inter_mem (inter_mem self_mem_nhdsWithin (hφc.eventually himg))
          (mem_nhdsWithin_of_mem_nhds (hNpo.mem_nhds hpNp)))
      obtain ⟨y, hyNqU, hφya⟩ := haimg
      have hya : y = a := haA.2.2 y hyNqU.2 hφya
      have haNq : a ∈ Nq := hya ▸ hyNqU.1
      exact hdisj.ne_of_mem haNp haNq rfl
  -- `A = U` by connectedness
  have hAU : U ⊆ A := by
    by_contra hnsub
    have hcover : U ⊆ A ∪ (closure A)ᶜ := by
      intro z hz
      by_cases hzc : z ∈ closure A
      · exact Or.inl (hAclosed ⟨hz, hzc⟩)
      · exact Or.inr hzc
    have hne1 : (U ∩ A).Nonempty := ⟨x₀, hx₀, hx₀A⟩
    have hne2 : (U ∩ (closure A)ᶜ).Nonempty := by
      rw [Set.not_subset] at hnsub
      obtain ⟨z, hzU, hzA⟩ := hnsub
      exact ⟨z, hzU, fun hzcl ↦ hzA (hAclosed ⟨hzU, hzcl⟩)⟩
    obtain ⟨w, _, hwA, hwc⟩ :=
      hUconn A (closure A)ᶜ hAopen isClosed_closure.isOpen_compl hcover hne1 hne2
    exact hwc (subset_closure hwA)
  -- injectivity from the fiber condition of `A`
  intro a ha b hb hab
  exact ((hAU ha).2.2 b hb hab.symm).symm

end Uniformization

