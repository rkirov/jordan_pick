/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Main
import Uniformization.RMT.RiemannMapping

/-!
# The uniformization dichotomy for simply connected surfaces

From the "key step" (`uniformization_key`: a simply connected noncompact surface is
biholomorphic to an open subset `D ⊆ ℂ`) we finish the uniformization theorem by the
Riemann mapping theorem:

* if `D = ℂ` (as a set), then `X ≃ₘ ℂ`;
* if `D ≠ ℂ`, then `D` is open, simply connected and `≠ univ`, so the ported Riemann
  mapping theorem `Complex.exists_bijOn_unitBall_map_eq_zero` provides a holomorphic
  bijection `D → ball 0 1`, hence `X ≃ₘ ball`, and the Cayley transform gives
  `ball ≃ₘ ℍ`.

The main results are `dichotomy_of_diffeo_opens` (the packaging) and the wrapper
`uniformization_of_key`, which combines it with `uniformization_key` under a genuine
`SimplyConnectedSpace X` hypothesis (the future `H¹`-generalization consumes this).

The regularity bookkeeping mirrors `Uniformization/Surface/Packaging.lean`: since `X`
carries only `IsManifold … 1`, all `ContMDiff` facts are proved directly from analyticity
in the (trivial, subtype-restricted) charts of open subsets of `ℂ` and of `ℍ`, using the
reduction lemmas `contMDiffAt_subtype_iff` / `ContMDiffAt.subtypeVal_comp_iff` /
`contMDiffAt_iff_contDiffAt`.
-/

open Set Metric Topology Filter Complex TopologicalSpace
open scoped Manifold ContDiff UpperHalfPlane

namespace Uniformization

/-! ### Chartwise reduction lemmas for open subsets of `ℂ` and for `ℍ` -/

/-- A map `↥U → ℂ` (target the model space) given by an analytic `F : ℂ → ℂ` in the
coordinate is `C^∞`. -/
private theorem contMDiffAt_opens_toC {U : Opens ℂ} {F : ℂ → ℂ} {q : U}
    (hF : ContDiffAt ℂ ∞ F (q : ℂ)) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (fun x : U => F (x : ℂ)) q :=
  contMDiffAt_subtype_iff.mpr hF.contMDiffAt

/-- A map `ℂ → ↥U` whose coordinate `z ↦ (g z : ℂ)` is analytic is `C^∞`. -/
private theorem contMDiffAt_toOpens {U : Opens ℂ} {g : ℂ → U} {w : ℂ}
    (hg : ContDiffAt ℂ ∞ (fun z => ((g z : ℂ))) w) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ g w :=
  (ContMDiffAt.subtypeVal_comp_iff U g w).mp hg.contMDiffAt

/-- A map `↥U → ↥V` between open subsets of `ℂ` given by an analytic `F : ℂ → ℂ` in the
coordinate is `C^∞`. -/
private theorem contMDiffAt_opens_to_opens {U V : Opens ℂ} {g : U → V} {F : ℂ → ℂ} {q : U}
    (hF : ContDiffAt ℂ ∞ F (q : ℂ)) (hgF : ∀ x : U, ((g x : ℂ)) = F (x : ℂ)) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ g q := by
  rw [← ContMDiffAt.subtypeVal_comp_iff V g q]
  have hcoe : (Subtype.val ∘ g) = (fun x : U => F (x : ℂ)) := funext fun x => hgF x
  rw [hcoe]
  exact contMDiffAt_opens_toC hF

/-- A map into `ℍ` is `C^∞` provided its complex coordinate `z ↦ (g z : ℂ)` is. -/
private theorem contMDiffAt_toUHP {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {g : M → ℍ} {w : M}
    (hg : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (fun z => ((g z : ℂ))) w) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ g w := by
  have hofc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ UpperHalfPlane.ofComplex ((g w : ℂ)) :=
    UpperHalfPlane.contMDiffAt_ofComplex (g w).im_pos
  have hcomp := hofc.comp w hg
  have hfun : (UpperHalfPlane.ofComplex ∘ fun z => ((g z : ℂ))) = g :=
    funext fun z => UpperHalfPlane.ofComplex_apply (g z)
  rwa [hfun] at hcomp

/-- A map `ℍ → ↥U` is `C^∞` provided its complex coordinate, pulled back along `ofComplex`,
is analytic at `(τ : ℂ)`. -/
private theorem contMDiffAt_fromUHP_toOpens {U : Opens ℂ} {g : ℍ → U} {τ : ℍ}
    (hg : ContDiffAt ℂ ∞ (fun w => ((g (UpperHalfPlane.ofComplex w) : ℂ))) (τ : ℂ)) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ g τ := by
  rw [← ContMDiffAt.subtypeVal_comp_iff U g τ, UpperHalfPlane.contMDiffAt_iff]
  exact hg

/-! ### Injective analytic maps have nonvanishing derivative

Copied from `Uniformization.Surface.Packaging` (where it is `private`); the same statement
appears in `Uniformization/Complex/{KoebeDistortion,AreaWinding}.lean`. -/

/-- **Local injectivity forces a nonvanishing derivative.** -/
private theorem injective_deriv_ne_zero {F : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀)
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

/-! ### `↥D ≃ₘ ℂ` when `D = univ` -/

/-- If the carrier of `D` is all of `ℂ`, then `↥D` is diffeomorphic to `ℂ`. -/
private def diffeoUnivC {D : Opens ℂ} (hDu : (D : Set ℂ) = univ) :
    ↥D ≃ₘ⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ ℂ where
  toEquiv :=
    { toFun := fun x => (x : ℂ)
      invFun := fun z => ⟨z, by have : z ∈ (D : Set ℂ) := by rw [hDu]; trivial
                                exact this⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun z => rfl }
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := fun z => contMDiffAt_toOpens (by
    show ContDiffAt ℂ ∞ (fun z : ℂ => z) z
    exact contDiffAt_id)

/-! ### `↥D ≃ₘ ball` from a holomorphic bijection (Riemann mapping) -/

/-- Given a holomorphic bijection `f : D → ball 0 1` on an open set, `↥D` is diffeomorphic
to `↥(ball 0 1)`. The inverse is smooth via the analytic inverse function theorem. -/
private theorem nonempty_D_diffeo_ball (D : Opens ℂ) {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f (D : Set ℂ)) (hfbij : BijOn f (D : Set ℂ) (ball 0 1)) :
    Nonempty (↥D ≃ₘ⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯
      ↥(⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)) := by
  set B : Opens ℂ := ⟨ball (0 : ℂ) 1, isOpen_ball⟩ with hBdef
  have hUo : IsOpen (D : Set ℂ) := D.2
  have hfan : ∀ z ∈ (D : Set ℂ), AnalyticAt ℂ f z := fun z hz =>
    hfdiff.analyticAt (hUo.mem_nhds hz)
  have hinj : InjOn f (D : Set ℂ) := hfbij.injOn
  have hderiv : ∀ z ∈ (D : Set ℂ), deriv f z ≠ 0 := fun z hz =>
    injective_deriv_ne_zero (hfan z hz) (hUo.mem_nhds hz) hinj
  -- forward and inverse set maps
  set fwd : ↥D → ↥B := fun x => ⟨f (x : ℂ), hfbij.mapsTo x.2⟩ with hfwddef
  set inv : ↥B → ↥D := fun q => ⟨Function.invFunOn f (D : Set ℂ) (q : ℂ),
    Function.invFunOn_mem (hfbij.surjOn q.2)⟩ with hinvdef
  have hleft : Function.LeftInverse inv fwd := by
    intro x
    apply Subtype.ext
    show Function.invFunOn f (D : Set ℂ) (f (x : ℂ)) = (x : ℂ)
    exact hinj.leftInvOn_invFunOn x.2
  have hright : Function.RightInverse inv fwd := by
    intro q
    apply Subtype.ext
    show f (Function.invFunOn f (D : Set ℂ) (q : ℂ)) = (q : ℂ)
    exact Function.invFunOn_eq (hfbij.surjOn q.2)
  set eqv : ↥D ≃ ↥B := ⟨fwd, inv, hleft, hright⟩ with heqvdef
  refine ⟨⟨eqv, ?_, ?_⟩⟩
  · -- forward is `C^∞`
    intro x
    exact contMDiffAt_opens_to_opens (F := f) ((hfan (x : ℂ) x.2).contDiffAt)
      (fun x => rfl)
  · -- inverse is `C^∞`
    intro q
    -- analyticity of `invFunOn f D` at `(q : ℂ)`
    set z₀ : ℂ := Function.invFunOn f (D : Set ℂ) (q : ℂ) with hz₀def
    have hz₀D : z₀ ∈ (D : Set ℂ) := Function.invFunOn_mem (hfbij.surjOn q.2)
    have hfz₀ : f z₀ = (q : ℂ) := Function.invFunOn_eq (hfbij.surjOn q.2)
    have hfan₀ := hfan z₀ hz₀D
    have hd₀ := hderiv z₀ hz₀D
    set r : ℂ → ℂ := hfan₀.hasStrictDerivAt.localInverse _ _ _ hd₀ with hrdef
    have hr_an : AnalyticAt ℂ r (f z₀) := hfan₀.analyticAt_localInverse hd₀
    have hrr : ∀ᶠ w in 𝓝 (f z₀), f (r w) = w :=
      hfan₀.hasStrictDerivAt.eventually_right_inverse hd₀
    have hr_pt : r (f z₀) = z₀ :=
      (hfan₀.hasStrictDerivAt.eventually_left_inverse hd₀).self_of_nhds
    have hr_cont : ContinuousAt r (f z₀) := hr_an.continuousAt
    have hrD : ∀ᶠ w in 𝓝 (f z₀), r w ∈ (D : Set ℂ) := by
      apply hr_cont.preimage_mem_nhds
      rw [hr_pt]; exact hUo.mem_nhds hz₀D
    have hball : ∀ᶠ w in 𝓝 (f z₀), w ∈ ball (0 : ℂ) 1 := by
      apply isOpen_ball.mem_nhds; rw [hfz₀]; exact q.2
    have heq : Function.invFunOn f (D : Set ℂ) =ᶠ[𝓝 (f z₀)] r := by
      filter_upwards [hrr, hrD, hball] with w hfrw hrwD hwball
      have hwimg : w ∈ f '' (D : Set ℂ) := hfbij.surjOn hwball
      have h1 : f (Function.invFunOn f (D : Set ℂ) w) = w := Function.invFunOn_eq hwimg
      have h2 : Function.invFunOn f (D : Set ℂ) w ∈ (D : Set ℂ) := Function.invFunOn_mem hwimg
      exact hinj h2 hrwD (h1.trans hfrw.symm)
    have hcda : ContDiffAt ℂ ∞ (Function.invFunOn f (D : Set ℂ)) (q : ℂ) := by
      rw [← hfz₀]
      exact hr_an.contDiffAt.congr_of_eventuallyEq heq
    exact contMDiffAt_opens_to_opens (F := Function.invFunOn f (D : Set ℂ)) hcda (fun q => rfl)

/-! ### The Cayley transform `ball ≃ₘ ℍ` -/

/-- Cayley transform `ball 0 1 → ℍ`. -/
private noncomputable def cayley (z : ℂ) : ℂ := Complex.I * (1 + z) / (1 - z)

/-- Inverse Cayley transform `ℍ → ball 0 1`. -/
private noncomputable def cayleyInv (w : ℂ) : ℂ := (w - Complex.I) / (w + Complex.I)

private theorem one_sub_ne {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : (1 : ℂ) - z ≠ 0 := by
  rw [sub_ne_zero]
  rintro rfl
  rw [mem_ball_zero_iff] at hz
  simp at hz

private theorem w_add_I_ne {w : ℂ} (hw : 0 < w.im) : w + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private theorem cayley_im_pos {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : 0 < (cayley z).im := by
  have h1 : (1 : ℂ) - z ≠ 0 := one_sub_ne hz
  rw [mem_ball_zero_iff] at hz
  have hden : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr h1
  have hnum : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z, hz]
  have key : (cayley z).im = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [cayley, Complex.div_im]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re,
      Complex.sub_im]
    ring
  rw [key]
  exact div_pos (by linarith) hden

private theorem cayleyInv_mem_ball {w : ℂ} (hw : 0 < w.im) : cayleyInv w ∈ ball (0 : ℂ) 1 := by
  have hwI : w + Complex.I ≠ 0 := w_add_I_ne hw
  rw [mem_ball_zero_iff, cayleyInv, norm_div, div_lt_one (norm_pos_iff.mpr hwI)]
  have hsq : ‖w - Complex.I‖ ^ 2 < ‖w + Complex.I‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, sub_zero, add_zero]
    nlinarith [hw]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

private theorem cayleyInv_cayley {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : cayleyInv (cayley z) = z := by
  have h1 : (1 : ℂ) - z ≠ 0 := one_sub_ne hz
  have h2 : Complex.I * (1 + z) / (1 - z) + Complex.I ≠ 0 := by
    have he : Complex.I * (1 + z) / (1 - z) + Complex.I = 2 * Complex.I / (1 - z) := by
      field_simp; ring
    rw [he]
    exact div_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) h1
  rw [cayleyInv, cayley]
  field_simp
  ring

private theorem cayley_cayleyInv {w : ℂ} (hw : 0 < w.im) : cayley (cayleyInv w) = w := by
  have hwI : w + Complex.I ≠ 0 := w_add_I_ne hw
  have h3 : (1 : ℂ) - (w - Complex.I) / (w + Complex.I) ≠ 0 := by
    have he : (1 : ℂ) - (w - Complex.I) / (w + Complex.I) = 2 * Complex.I / (w + Complex.I) := by
      field_simp; ring
    rw [he]
    exact div_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hwI
  rw [cayley, cayleyInv]
  field_simp
  ring

private theorem cayley_contDiffAt {z : ℂ} (h : (1 : ℂ) - z ≠ 0) : ContDiffAt ℂ ∞ cayley z := by
  show ContDiffAt ℂ ∞ (fun z => Complex.I * (1 + z) / (1 - z)) z
  exact ContDiffAt.div (by fun_prop) (by fun_prop) h

private theorem cayleyInv_contDiffAt {w : ℂ} (h : w + Complex.I ≠ 0) :
    ContDiffAt ℂ ∞ cayleyInv w := by
  show ContDiffAt ℂ ∞ (fun w => (w - Complex.I) / (w + Complex.I)) w
  exact ContDiffAt.div (by fun_prop) (by fun_prop) h

/-- The unit ball is diffeomorphic to the upper half plane via the Cayley transform. -/
private theorem nonempty_ball_diffeo_uhp :
    Nonempty (↥(⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) ≃ₘ⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ ℍ) := by
  set B : Opens ℂ := ⟨ball (0 : ℂ) 1, isOpen_ball⟩ with hBdef
  set fwd : ↥B → ℍ := fun x => ⟨cayley (x : ℂ), cayley_im_pos x.2⟩ with hfwddef
  set inv : ℍ → ↥B := fun τ => ⟨cayleyInv (τ : ℂ), cayleyInv_mem_ball τ.im_pos⟩ with hinvdef
  have hleft : Function.LeftInverse inv fwd := by
    intro x; exact Subtype.ext (cayleyInv_cayley x.2)
  have hright : Function.RightInverse inv fwd := by
    intro τ; exact UpperHalfPlane.ext (cayley_cayleyInv τ.im_pos)
  set eqv : ↥B ≃ ℍ := ⟨fwd, inv, hleft, hright⟩ with heqvdef
  refine ⟨⟨eqv, ?_, ?_⟩⟩
  · -- forward `↥B → ℍ`
    intro x
    exact contMDiffAt_toUHP (contMDiffAt_opens_toC (cayley_contDiffAt (one_sub_ne x.2)))
  · -- inverse `ℍ → ↥B`
    intro τ
    refine contMDiffAt_fromUHP_toOpens ?_
    have heq : (fun w => cayleyInv ((UpperHalfPlane.ofComplex w : ℍ) : ℂ)) =ᶠ[𝓝 (τ : ℂ)] cayleyInv := by
      filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with w hw
      have hval : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w := hw
      rw [hval]
    exact (cayleyInv_contDiffAt (w_add_I_ne τ.im_pos)).congr_of_eventuallyEq heq

/-! ### The dichotomy -/

/-- **Uniformization dichotomy (packaging).** If a simply connected surface `X` is
diffeomorphic to an open subset `D ⊆ ℂ`, then `X ≃ₘ ℂ` or `X ≃ₘ ℍ`. -/
theorem dichotomy_of_diffeo_opens {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    [SimplyConnectedSpace X]
    (h : ∃ D : Opens ℂ, Nonempty (X ≃ₘ⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ D)) :
    Nonempty (X ≃ₘ⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ ℂ) ∨
    Nonempty (X ≃ₘ⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ ℍ) := by
  obtain ⟨D, ⟨e⟩⟩ := h
  haveI hDsc : SimplyConnectedSpace ↥D :=
    (e.toHomeomorph.symm.toHomotopyEquiv).simplyConnectedSpace
  by_cases hDu : (D : Set ℂ) = univ
  · exact Or.inl ⟨e.trans (diffeoUnivC hDu)⟩
  · refine Or.inr ?_
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hDne : ((D : Set ℂ)).Nonempty := ⟨((e x : ↥D) : ℂ), (e x).2⟩
    obtain ⟨x₀, hx₀⟩ := hDne
    have hDsc' : IsSimplyConnected (D : Set ℂ) := hDsc
    obtain ⟨f, hfdiff, hfbij, -⟩ :=
      Complex.exists_bijOn_unitBall_map_eq_zero D.2 hDsc' hDu hx₀
    obtain ⟨eB⟩ := nonempty_D_diffeo_ball D hfdiff hfbij
    obtain ⟨eC⟩ := nonempty_ball_diffeo_uhp
    exact ⟨e.trans (eB.trans eC)⟩

/-- **Wrapper for the future `H¹`-generalization.** A simply connected, noncompact,
second countable Riemann surface is biholomorphic to `ℂ` or to the upper half plane. -/
theorem uniformization_of_key {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [SimplyConnectedSpace X] (hX : ¬ CompactSpace X) :
    Nonempty (X ≃ₘ⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ ℂ) ∨
    Nonempty (X ≃ₘ⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ ℍ) :=
  dichotomy_of_diffeo_opens (LeanEval.Geometry.uniformization_key hX)

end Uniformization
