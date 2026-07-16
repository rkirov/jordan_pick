/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Rado.Surface.Charts
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Packaging an injective holomorphic map as a diffeomorphism onto its image

An injective holomorphic function `φ : X → ℂ` on a Riemann surface has open
image `D` and induces `X ≃ₘ⟮mℂ, mℂ⟯ D` (a `Diffeomorph … ∞`). This is the
final packaging step of `uniformization_key`.

Ingredients: injectivity forces the chart derivative of `φ` to be nonvanishing
(otherwise the local normal form `z ↦ c·zᵏ`, `k ≥ 2`, kills injectivity), so
`φ` is a local biholomorphism; the image is open (open mapping theorem), the
inverse is holomorphic, and both directions are `ContMDiff … ∞`.

⚠ Regularity subtlety: `X` carries only `IsManifold mℂ 1 X`, and the pin has
no `1 ⇒ ω` upgrade instance over `ℂ`. `ContMDiff`-composition lemmas that
require `[IsManifold I ∞ M]` are therefore unavailable; prove `ContMDiffAt`
statements directly from analyticity in the canonical charts (`contMDiffAt_iff`
-style unfolding + `AnalyticAt.contDiffAt`), and use
`Rado.transition_analyticAt` for chart changes.
-/

open Set Metric Topology Filter Complex
open scoped Manifold ContDiff

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- A map `X → ℂ` (target the model space) is `C^∞` at `x` provided it is continuous there
and analytic in the chart. Proved directly from `contMDiffAt_iff`, avoiding any
`[IsManifold … ∞]` hypothesis. -/
private theorem contMDiffAt_target_C {f : X → ℂ} {x : X} (hc : ContinuousAt f x)
    (ha : ContDiffAt ℂ ∞ (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ f x := by
  rw [contMDiffAt_iff]
  refine ⟨hc, ?_⟩
  simp only [extChartAt_self_eq, modelWithCornersSelf_coe, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, range_id, Function.id_comp, Function.comp_id,
    contDiffWithinAt_univ]
  exact ha

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- A map `ℂ → X` (source the model space) is `C^∞` at `w` provided it is continuous there
and analytic in the chart. Proved directly from `contMDiffAt_iff`, avoiding any
`[IsManifold … ∞]` hypothesis. -/
private theorem contMDiffAt_source_C {g : ℂ → X} {w : ℂ} (hc : ContinuousAt g w)
    (ha : ContDiffAt ℂ ∞ (chartAt ℂ (g w) ∘ g) w) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ g w := by
  rw [contMDiffAt_iff]
  refine ⟨hc, ?_⟩
  simp only [extChartAt_self_eq, modelWithCornersSelf_coe, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, range_id, Function.id_comp, Function.comp_id,
    contDiffWithinAt_univ]
  exact ha

/-- **Local injectivity forces a nonvanishing derivative.** If `F` is analytic at `z₀` and
injective on a neighborhood of `z₀`, then `deriv F z₀ ≠ 0`. If the derivative vanished, the
local normal form `F z = F z₀ + H z ^ n` with `n ≥ 2` and `H` a local biholomorphism would
supply two distinct nearby points (related by a primitive `n`-th root of unity) with equal
`F`-value, contradicting injectivity. -/
private theorem deriv_ne_zero_of_injOn {F : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀)
    {s : Set ℂ} (hs : s ∈ 𝓝 z₀) (hinj : Set.InjOn F s) : deriv F z₀ ≠ 0 := by
  intro hderiv
  have hz₀s : z₀ ∈ s := mem_of_mem_nhds hs
  set G : ℂ → ℂ := fun z => F z - F z₀ with hGdef
  have hGan : AnalyticAt ℂ G z₀ := hF.sub analyticAt_const
  have hGz₀ : G z₀ = 0 := by simp [hGdef]
  have hGderiv : deriv G z₀ = 0 := by
    simp only [hGdef]; rw [deriv_sub_const]; exact hderiv
  -- `G` cannot be eventually zero: otherwise `F` would be locally constant, contradicting
  -- injectivity on a punctured neighborhood.
  have hGne : ¬ (∀ᶠ z in 𝓝 z₀, G z = 0) := by
    intro hev
    have hFev : ∀ᶠ z in 𝓝 z₀, F z = F z₀ := by
      filter_upwards [hev] with z hz; simpa [hGdef, sub_eq_zero] using hz
    have ht : s ∩ {z | F z = F z₀} ∈ 𝓝 z₀ := inter_mem hs hFev
    have hnb : (𝓝[≠] z₀).NeBot := inferInstance
    obtain ⟨z₁, ⟨hz₁s, hz₁F⟩, hz₁ne⟩ :=
      hnb.nonempty_of_mem (inter_mem (mem_nhdsWithin_of_mem_nhds ht) self_mem_nhdsWithin)
    exact hz₁ne (hinj hz₁s hz₀s hz₁F)
  -- local factorization `G z = (z - z₀) ^ n • g z`, `g z₀ ≠ 0`
  obtain ⟨n, g, hgan, hgne, hfact⟩ :=
    (hGan.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hGne
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hgg : G =ᶠ[𝓝 z₀] g := by filter_upwards [hfact] with z hz; simpa using hz
    have := hgg.eq_of_nhds
    rw [hGz₀] at this; exact hgne this.symm
  -- `deriv F z₀ = 0` rules out order `1`, hence the vanishing order is `≥ 2`
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
  -- an analytic `n`-th root `h` of `g` near `z₀`, `h z₀ ≠ 0`
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
  -- `H z = (z - z₀) · h z` satisfies `F z = F z₀ + H z ^ n` and `H' z₀ = w ≠ 0`
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
  -- `H` is a local homeomorphism near `z₀`
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
  -- a small ball in the image over which `F z = F z₀ + H z ^ n` and `z ∈ s`
  set W : Set ℂ := {z | F z = F z₀ + H z ^ n} ∩ s with hWdef
  have hWnhd : W ∈ 𝓝 z₀ := inter_mem hHpow hs
  have hpre : R.symm ⁻¹' W ∈ 𝓝 (0 : ℂ) := by
    apply hsymm_cont.preimage_mem_nhds
    rw [hsymm0]; exact hWnhd
  have hN : R.target ∩ R.symm ⁻¹' W ∈ 𝓝 (0 : ℂ) := inter_mem hRtgt_nhds hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  -- a primitive `n`-th root of unity, `ζ ≠ 1`, `‖ζ‖ = 1`
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / n) with hζdef
  have hζprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζpow : ζ ^ n = 1 := hζprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζprim.ne_one hn_ge2
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζpow hn0
  -- a small nonzero point `u`, together with `ζ · u`, both in the ball
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
  -- the two distinct preimage points with equal `F`-value
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

set_option linter.unusedSectionVars false in
/-- **Packaging**: an injective globally holomorphic map from a Riemann
surface to `ℂ` is a diffeomorphism onto an open subset of `ℂ`.

The `[IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]` instance is part of the frozen milestone
signature; the proof routes through `HolomorphicOn` and `contMDiffAt_iff` and never needs it,
so the section-variable linter is disabled here. -/
theorem exists_diffeomorph_opens_of_injective [T2Space X] {φ : X → ℂ}
    (hφ : HolomorphicOn φ univ) (hinj : Function.Injective φ) :
    ∃ D : TopologicalSpace.Opens ℂ,
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ D) := by
  have hFan : ∀ x : X, AnalyticAt ℂ (φ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
    fun x => hφ x (mem_univ x)
  have hcont : Continuous φ := continuousOn_univ.mp hφ.continuousOn
  -- injectivity forces a nonvanishing chart derivative everywhere
  have hderiv : ∀ x : X, deriv (φ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 := by
    intro x
    apply deriv_ne_zero_of_injOn (hFan x)
      ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
    intro a ha b hb hab
    have hsymm : (chartAt ℂ x).symm a = (chartAt ℂ x).symm b := hinj hab
    calc a = (chartAt ℂ x) ((chartAt ℂ x).symm a) := ((chartAt ℂ x).right_inv ha).symm
      _ = (chartAt ℂ x) ((chartAt ℂ x).symm b) := by rw [hsymm]
      _ = b := (chartAt ℂ x).right_inv hb
  -- `φ` is an open map: its derivative is a local homeomorphism in each chart
  have hmapeq : ∀ x : X, map φ (𝓝 x) = 𝓝 (φ x) := by
    intro x
    have hxs : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hxt : (chartAt ℂ x) x ∈ (chartAt ℂ x).target := mem_chart_target ℂ x
    have h1 : map (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) = 𝓝 x := by
      rw [(chartAt ℂ x).symm.map_nhds_eq (by rw [OpenPartialHomeomorph.symm_source]; exact hxt),
        (chartAt ℂ x).left_inv hxs]
    calc map φ (𝓝 x)
        = map φ (map (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x))) := by rw [h1]
      _ = map (φ ∘ (chartAt ℂ x).symm) (𝓝 ((chartAt ℂ x) x)) := by rw [Filter.map_map]
      _ = 𝓝 ((φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :=
            (hFan x).hasStrictDerivAt.map_nhds_eq (hderiv x)
      _ = 𝓝 (φ x) := by rw [Function.comp_apply, (chartAt ℂ x).left_inv hxs]
  have hopen : IsOpenMap φ := isOpenMap_iff_nhds_le.mpr (fun x => (hmapeq x).ge)
  have hrange : IsOpen (range φ) := hopen.isOpen_range
  refine ⟨⟨range φ, hrange⟩, ?_⟩
  set D : TopologicalSpace.Opens ℂ := ⟨range φ, hrange⟩ with hDdef
  -- the corestriction `φ' : X → D` and its inverse
  set φ' : X → D := fun x => ⟨φ x, mem_range_self x⟩ with hφ'def
  have hφ'inj : Function.Injective φ' := by
    intro a b hab; exact hinj (congrArg Subtype.val hab)
  have hφ'surj : Function.Surjective φ' := by
    rintro ⟨w, x, rfl⟩; exact ⟨x, rfl⟩
  set eqv : X ≃ D := Equiv.ofBijective φ' ⟨hφ'inj, hφ'surj⟩ with heqvdef
  have hφinv : ∀ q : D, φ (eqv.symm q) = (q : ℂ) := by
    intro q; exact congrArg Subtype.val (eqv.apply_symm_apply q)
  -- forward direction is `C^∞`
  have hfwd : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (eqv : X → D) := by
    rw [← ContMDiff.subtypeVal_comp_iff D (eqv : X → D)]
    show ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (φ : X → ℂ)
    intro x
    exact contMDiffAt_target_C hcont.continuousAt (hFan x).contDiffAt
  -- inverse direction is `C^∞`, via the analytic local inverse in each chart
  have hinv : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (eqv.symm : D → X) := by
    intro p
    set x₀ : X := eqv.symm p with hx₀def
    have hFanx := hFan x₀
    have hderivx := hderiv x₀
    set Finv : ℂ → ℂ := hFanx.hasStrictDerivAt.localInverse _ _ _ hderivx with hFinvdef
    have hFinv_an : AnalyticAt ℂ Finv ((φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)) :=
      hFanx.analyticAt_localInverse hderivx
    have hFinv_z₀ : Finv ((φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)) = (chartAt ℂ x₀) x₀ :=
      (hFanx.hasStrictDerivAt.eventually_left_inverse hderivx).self_of_nhds
    have hFinv_rinv : ∀ᶠ v in 𝓝 ((φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)),
        (φ ∘ (chartAt ℂ x₀).symm) (Finv v) = v :=
      hFanx.hasStrictDerivAt.eventually_right_inverse hderivx
    set g : ℂ → X := fun v => (chartAt ℂ x₀).symm (Finv v) with hgdef
    have hFz₀ : (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = (p : ℂ) := by
      rw [Function.comp_apply, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)]
      exact hφinv p
    have hgp : g (p : ℂ) = x₀ := by
      show (chartAt ℂ x₀).symm (Finv (p : ℂ)) = x₀
      rw [← hFz₀, hFinv_z₀, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)]
    have hFinvcont : ContinuousAt Finv (p : ℂ) := hFz₀ ▸ hFinv_an.continuousAt
    have hFinv_p : Finv (p : ℂ) = (chartAt ℂ x₀) x₀ := by rw [← hFz₀, hFinv_z₀]
    have hgcont : ContinuousAt g (p : ℂ) := by
      have hsymmcont : ContinuousAt (chartAt ℂ x₀).symm (Finv (p : ℂ)) := by
        rw [hFinv_p]; exact (chartAt ℂ x₀).continuousAt_symm (mem_chart_target ℂ x₀)
      exact hsymmcont.comp hFinvcont
    have htgt : ∀ᶠ v in 𝓝 (p : ℂ), Finv v ∈ (chartAt ℂ x₀).target := by
      apply hFinvcont.preimage_mem_nhds
      rw [hFinv_p]
      exact (chartAt ℂ x₀).open_target.mem_nhds (mem_chart_target ℂ x₀)
    have hcongr : (fun v => (chartAt ℂ x₀) ((chartAt ℂ x₀).symm (Finv v)))
        =ᶠ[𝓝 (p : ℂ)] Finv := by
      filter_upwards [htgt] with v hv
      exact (chartAt ℂ x₀).right_inv hv
    have hFinvcda : ContDiffAt ℂ ∞ Finv (p : ℂ) := hFz₀ ▸ hFinv_an.contDiffAt
    have hcda : ContDiffAt ℂ ∞ (chartAt ℂ (g (p : ℂ)) ∘ g) (p : ℂ) := by
      rw [hgp]
      exact hFinvcda.congr_of_eventuallyEq hcongr
    have hg_cmd : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ g (p : ℂ) := contMDiffAt_source_C hgcont hcda
    have hg_sub : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (fun q : D => g q.val) p :=
      (contMDiffAt_subtype_iff).mpr hg_cmd
    -- `g ∘ val` agrees with `eqv.symm` near `p`, so `eqv.symm` is `C^∞` at `p`
    have heqψ : (fun q : D => g q.val) =ᶠ[𝓝 p] (eqv.symm : D → X) := by
      have hset : {v : ℂ | (φ ∘ (chartAt ℂ x₀).symm) (Finv v) = v}
          ∈ 𝓝 ((φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)) := hFinv_rinv
      have hpull : (fun q : D => (q : ℂ)) ⁻¹' {v | (φ ∘ (chartAt ℂ x₀).symm) (Finv v) = v}
          ∈ 𝓝 p := by
        apply (continuous_subtype_val.continuousAt).preimage_mem_nhds
        rw [show ((p : D) : ℂ) = (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) from hFz₀.symm]
        exact hset
      filter_upwards [hpull] with q hq
      apply hinj
      show φ (g (q : ℂ)) = φ (eqv.symm q)
      have hφg : φ (g (q : ℂ)) = (q : ℂ) := hq
      rw [hφg, hφinv q]
    exact (heqψ.contMDiffAt_iff).mp hg_sub
  exact ⟨⟨eqv, hfwd, hinv⟩⟩

end Uniformization
