/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Uniformization.Complex.Bieberbach

/-!
# Koebe distortion and growth: supporting development
-/

open Set Metric Topology Filter Complex intervalIntegral MeasureTheory

namespace Uniformization

/-- **Local injectivity forces a nonvanishing derivative.**
(Copied from `Uniformization.Surface.Injective`, where it is `private`.) -/
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

/-- The disk automorphism `φ_w z = (z+w)/(1+w̄z)` maps the unit ball into itself. -/
private theorem mobius_maps_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∀ z ∈ ball (0 : ℂ) 1,
      (z + w) / (1 + (starRingEnd ℂ) w * z) ∈ ball (0 : ℂ) 1 := by
  intro z hz
  rw [mem_ball_zero_iff] at hw hz
  set cw := (starRingEnd ℂ) w with hcw
  have hden_ne : (1 + cw * z) ≠ 0 := by
    intro h
    have : ‖cw * z‖ = 1 := by
      have : cw * z = -1 := by linear_combination h
      rw [this]; simp
    rw [norm_mul, hcw, RCLike.norm_conj] at this
    nlinarith [norm_nonneg w, norm_nonneg z]
  rw [mem_ball_zero_iff, norm_div]
  rw [div_lt_one (by rw [norm_pos_iff]; exact hden_ne)]
  -- compare squares
  have hsq : ‖z + w‖ ^ 2 < ‖1 + cw * z‖ ^ 2 := by
    have key : (‖1 + cw * z‖ ^ 2 - ‖z + w‖ ^ 2 : ℝ)
        = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
      have hcast : ((‖1 + cw * z‖ ^ 2 - ‖z + w‖ ^ 2 : ℝ) : ℂ)
          = (((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) : ℝ) : ℂ) := by
        have e1 : ∀ a : ℂ, ((‖a‖ ^ 2 : ℝ) : ℂ) = a * (starRingEnd ℂ) a := by
          intro a
          rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
        push_cast [e1]
        simp only [hcw, map_add, map_mul, map_one, Complex.conj_conj]
        ring
      exact_mod_cast hcast
    nlinarith [key, sq_nonneg (1 - ‖z‖ ^ 2), sq_nonneg (1 - ‖w‖ ^ 2),
      mul_pos (by nlinarith [norm_nonneg z] : (0:ℝ) < 1 - ‖z‖ ^ 2)
        (by nlinarith [norm_nonneg w] : (0:ℝ) < 1 - ‖w‖ ^ 2)]
  nlinarith [hsq, norm_nonneg (z + w), norm_nonneg (1 + cw * z)]

/-- An analytic logarithm branch of a nonvanishing analytic function on the ball. -/
theorem exists_log {u : ℂ → ℂ} (hu : DifferentiableOn ℂ u (ball 0 1))
    (hu0 : ∀ z ∈ ball (0 : ℂ) 1, u z ≠ 0) :
    ∃ ℓ : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) 1, HasDerivAt ℓ (deriv u z / u z) z) ∧
      (∀ z ∈ ball (0 : ℂ) 1, Complex.exp (ℓ z) = u z) := by
  have hmem0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have huan : AnalyticOnNhd ℂ u (ball 0 1) := hu.analyticOnNhd isOpen_ball
  have hlog : DifferentiableOn ℂ (logDeriv u) (ball 0 1) :=
    (huan.deriv.div huan hu0).differentiableOn
  obtain ⟨L, hL0, hL⟩ := hlog.isExactOn_ball.with_val_at 0 0
  have hC_ne : u 0 ≠ 0 := hu0 0 hmem0
  refine ⟨fun z => Complex.log (u 0) + L z, ?_, ?_⟩
  · intro z hz
    have h2 := (hasDerivAt_const z (Complex.log (u 0))).add (hL z hz)
    rw [zero_add] at h2
    exact h2
  · -- `u z = u 0 * exp (L z)` via the constant-ratio argument
    have hveq : ∀ z ∈ ball (0 : ℂ) 1, u z = u 0 * Complex.exp (L z) := by
      set W : ℂ → ℂ := fun z => u z * Complex.exp (- L z) with hWdef
      have hWderiv : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt W 0 z := by
        intro z hz
        have huz : HasDerivAt u (deriv u z) z :=
          (hu.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
        have hLz : HasDerivAt L (logDeriv u z) z := hL z hz
        have hexp : HasDerivAt (fun z => Complex.exp (- L z))
            (Complex.exp (- L z) * (- logDeriv u z)) z := by
          have := (hLz.neg).cexp
          simpa using this
        have hprod := huz.mul hexp
        have huz0 : u z ≠ 0 := hu0 z hz
        have hval : deriv u z * Complex.exp (-L z)
            + u z * (Complex.exp (-L z) * (-logDeriv u z)) = 0 := by
          have hld : logDeriv u z = deriv u z / u z := rfl
          rw [hld]; field_simp; ring
        rw [hval] at hprod; exact hprod
      have hWdiff : DifferentiableOn ℂ W (ball 0 1) :=
        fun z hz => (hWderiv z hz).differentiableAt.differentiableWithinAt
      have hWfd : ∀ x ∈ ball (0 : ℂ) 1, fderivWithin ℂ W (ball 0 1) x = 0 := by
        intro x hx
        rw [fderivWithin_of_isOpen isOpen_ball hx, (hWderiv x hx).hasFDerivAt.fderiv]
        ext1; simp
      intro z hz
      have hconst : W z = W 0 :=
        (convex_ball 0 1).is_const_of_fderivWithin_eq_zero hWdiff hWfd hz hmem0
      have hW0 : W 0 = u 0 := by simp [hWdef, hL0]
      rw [hW0] at hconst
      have : u z * Complex.exp (- L z) = u 0 := hconst
      have hkey : u z = u 0 * (Complex.exp (- L z))⁻¹ := by
        field_simp; linear_combination this
      rw [hkey, Complex.exp_neg, inv_inv]
    intro z hz
    rw [Complex.exp_add, Complex.exp_log hC_ne, ← hveq z hz]

/-- **Distortion inequality.** For a schlicht `f` and `w ∈ ball 0 1`, applying
Bieberbach to the Koebe transform at `w` gives
`‖(1-‖w‖²) f''(w)/f'(w) − 2 w̄‖ ≤ 4`. -/
theorem distortion_bound {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0) (hd : deriv f 0 = 1)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ‖(1 - (starRingEnd ℂ) w * w) * deriv (deriv f) w / deriv f w
        - 2 * (starRingEnd ℂ) w‖ ≤ 4 := by
  have hmem0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have hwnhd : ball (0 : ℂ) 1 ∈ 𝓝 w := isOpen_ball.mem_nhds hw
  have hwn : ‖w‖ < 1 := by rwa [mem_ball_zero_iff] at hw
  set cw : ℂ := (starRingEnd ℂ) w with hcw
  set A : ℂ := deriv f w with hAdef
  have hA_ne : A ≠ 0 := deriv_ne_zero_of_injOn (hfan w hw) hwnhd hinj
  set q : ℂ := 1 - cw * w with hqdef
  have hqr : q = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [hqdef, hcw]
    have : (starRingEnd ℂ) w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this]; push_cast; ring
  have hq_ne : q ≠ 0 := by
    rw [hqr]; exact_mod_cast (by nlinarith [norm_nonneg w] : (1 - ‖w‖ ^ 2 : ℝ) ≠ 0)
  -- the Möbius automorphism and its derivatives
  set den : ℂ → ℂ := fun z => 1 + cw * z with hdendef
  have hden_ne : ∀ z ∈ ball (0 : ℂ) 1, den z ≠ 0 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    intro h
    have h1 : cw * z = -1 := by rw [hdendef] at h; linear_combination h
    have : ‖cw * z‖ = 1 := by rw [h1]; simp
    rw [norm_mul, hcw, RCLike.norm_conj] at this
    nlinarith [norm_nonneg w, norm_nonneg z]
  set φ : ℂ → ℂ := fun z => (z + w) / den z with hφdef
  have hφmap : ∀ z ∈ ball (0 : ℂ) 1, φ z ∈ ball (0 : ℂ) 1 := by
    intro z hz; exact mobius_maps_ball hw z hz
  have hφ0 : φ 0 = w := by rw [hφdef, hdendef]; simp
  have hden0 : HasDerivAt den cw 0 := by
    have : HasDerivAt den (0 + cw * 1) 0 :=
      (hasDerivAt_const 0 1).add ((hasDerivAt_id 0).const_mul cw)
    simpa using this
  have hden0val : den 0 = 1 := by rw [hdendef]; simp
  have hφ_deriv : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt φ (q / (den z) ^ 2) z := by
    intro z hz
    have hnum : HasDerivAt (fun z => z + w) 1 z := (hasDerivAt_id z).add_const w
    have hd2 : HasDerivAt den cw z := by
      have : HasDerivAt den (0 + cw * 1) z :=
        (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul cw)
      simpa using this
    have hdiv := hnum.div hd2 (hden_ne z hz)
    have hval : (1 * den z - (z + w) * cw) / (den z) ^ 2 = q / (den z) ^ 2 := by
      rw [hdendef, hqdef]; ring
    rw [hval] at hdiv; exact hdiv
  have hφ_deriv0 : HasDerivAt φ q 0 := by
    have := hφ_deriv 0 hmem0
    rwa [hden0val, one_pow, div_one] at this
  -- injectivity of `φ` on the ball
  have hφ_inj : InjOn φ (ball 0 1) := by
    intro a ha b hb hab
    have hda := hden_ne a ha
    have hdb := hden_ne b hb
    rw [hφdef] at hab
    simp only at hab
    rw [div_eq_div_iff hda hdb, hdendef] at hab
    -- (a+w)(1+cw b) = (b+w)(1+cw a) ⇒ (a-b)q = 0
    have hkey : (a - b) * q = 0 := by rw [hqdef, hcw]; ring_nf; ring_nf at hab; linear_combination hab
    rcases mul_eq_zero.mp hkey with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hq_ne
  -- the Koebe transform `T z = (f (φ z) - f w)/(A q)`
  set T : ℂ → ℂ := fun z => (f (φ z) - f w) / (A * q) with hTdef
  have hAq_ne : A * q ≠ 0 := mul_ne_zero hA_ne hq_ne
  -- differentiability of the composition
  have hf_at : ∀ p ∈ ball (0 : ℂ) 1, HasDerivAt f (deriv f p) p :=
    fun p hp => (hf.differentiableAt (isOpen_ball.mem_nhds hp)).hasDerivAt
  have hcomp_diff : DifferentiableOn ℂ (fun z => f (φ z)) (ball 0 1) := by
    intro z hz
    exact ((hf_at (φ z) (hφmap z hz)).comp z (hφ_deriv z hz)).differentiableAt.differentiableWithinAt
  have hT_diff : DifferentiableOn ℂ T (ball 0 1) := by
    rw [hTdef]
    exact (hcomp_diff.sub_const (f w)).div_const (A * q)
  have hT0 : T 0 = 0 := by simp only [hTdef, hφ0, sub_self, zero_div]
  -- `deriv T 0 = 1`
  have hcomp_hasderiv : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun z => f (φ z)) (deriv f (φ z) * (q / (den z) ^ 2)) z :=
    fun z hz => (hf_at (φ z) (hφmap z hz)).comp z (hφ_deriv z hz)
  have hT_hasderiv : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt T (deriv f (φ z) * (q / (den z) ^ 2) / (A * q)) z := by
    intro z hz
    have := ((hcomp_hasderiv z hz).sub_const (f w)).div_const (A * q)
    rw [hTdef]; exact this
  have hT_deriv1 : deriv T 0 = 1 := by
    rw [(hT_hasderiv 0 hmem0).deriv, hφ0, hden0val, ← hAdef]
    field_simp
  -- injectivity of `T`
  have hT_inj : InjOn T (ball 0 1) := by
    intro a ha b hb hab
    rw [hTdef] at hab
    simp only at hab
    have h1 : f (φ a) = f (φ b) := by
      rw [div_eq_div_iff hAq_ne hAq_ne] at hab
      have := mul_right_cancel₀ hAq_ne hab
      linear_combination this
    have h2 : φ a = φ b := hinj (hφmap a ha) (hφmap b hb) h1
    exact hφ_inj ha hb h2
  -- Bieberbach on the transform
  have hbT := bieberbach hT_diff hT_inj hT0 hT_deriv1
  -- `‖(T)''(0)‖ ≤ 4`
  have hddT : ‖deriv (deriv T) 0‖ ≤ 4 := by
    rw [deriv_dslope_zero isOpen_ball hmem0 hT_diff, norm_mul,
      show ‖(2 : ℂ)‖ = 2 from by norm_num]
    nlinarith [hbT, norm_nonneg (deriv (dslope T 0) 0)]
  -- compute `(T)''(0)`
  have hderivf_diff : DifferentiableOn ℂ (deriv f) (ball 0 1) := hfan.deriv.differentiableOn
  have hf''_at : HasDerivAt (deriv f) (deriv (deriv f) w) w :=
    (hderivf_diff.differentiableAt hwnhd).hasDerivAt
  have hf''_atφ : HasDerivAt (deriv f) (deriv (deriv f) w) (φ 0) := by rw [hφ0]; exact hf''_at
  have hG : HasDerivAt (fun z => deriv f (φ z)) (deriv (deriv f) w * q) 0 :=
    hf''_atφ.comp 0 hφ_deriv0
  have hden2 : HasDerivAt (fun z => (den z) ^ 2) (2 * (den 0) ^ (2 - 1) * cw) 0 := hden0.pow 2
  have hden2ne : (den 0) ^ 2 ≠ 0 := by rw [hden0val]; norm_num
  have hK : HasDerivAt (fun z => q / (den z) ^ 2)
      ((0 * (den 0) ^ 2 - q * (2 * (den 0) ^ (2 - 1) * cw)) / ((den 0) ^ 2) ^ 2) 0 :=
    (hasDerivAt_const 0 q).div hden2 hden2ne
  have hGK : HasDerivAt (fun z => deriv f (φ z) * (q / (den z) ^ 2) / (A * q))
      ((deriv (deriv f) w * q * (q / (den 0) ^ 2)
        + deriv f (φ 0) * ((0 * (den 0) ^ 2 - q * (2 * (den 0) ^ (2 - 1) * cw)) / ((den 0) ^ 2) ^ 2))
        / (A * q)) 0 :=
    (hG.mul hK).div_const (A * q)
  have hderivT_ev : deriv T =ᶠ[𝓝 0] fun z => deriv f (φ z) * (q / (den z) ^ 2) / (A * q) := by
    filter_upwards [isOpen_ball.mem_nhds hmem0] with z hz using (hT_hasderiv z hz).deriv
  have hval : deriv (deriv T) 0 = q * deriv (deriv f) w / A - 2 * cw := by
    rw [hderivT_ev.deriv_eq, hGK.deriv, hφ0, hden0val]
    field_simp
    ring
  rw [hval] at hddT
  exact hddT

/-- **Distortion bound on `f'`.** `‖f'(z)‖ ≤ (1+‖z‖)/(1-‖z‖)³`. -/
theorem deriv_norm_le {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0) (hd : deriv f 0 = 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
  have hmem0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have hderivf_diff : DifferentiableOn ℂ (deriv f) (ball 0 1) := hfan.deriv.differentiableOn
  have hu0 : ∀ p ∈ ball (0 : ℂ) 1, deriv f p ≠ 0 :=
    fun p hp => deriv_ne_zero_of_injOn (hfan p hp) (isOpen_ball.mem_nhds hp) hinj
  obtain ⟨ℓ, hℓ_deriv, hℓ_exp⟩ := exists_log hderivf_diff hu0
  -- `‖f' p‖ = exp ((ℓ p).re)`
  have hnorm_eq : ∀ p ∈ ball (0 : ℂ) 1, ‖deriv f p‖ = Real.exp ((ℓ p).re) := by
    intro p hp; rw [← hℓ_exp p hp, Complex.norm_exp]
  rcases eq_or_ne z 0 with hz0 | hz0
  · subst hz0; rw [hd]; norm_num
  -- set up the radial path
  have hr0 : 0 < ‖z‖ := by rwa [norm_pos_iff]
  have hr1 : ‖z‖ < 1 := by rwa [mem_ball_zero_iff] at hz
  set u : ℂ := z / (‖z‖ : ℂ) with hudef
  have hznC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr0
  have hun : ‖u‖ = 1 := by rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr0, div_self (ne_of_gt hr0)]
  have hcuu : (starRingEnd ℂ) u * u = 1 := by
    have : u * (starRingEnd ℂ) u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [mul_comm]; rw [this, hun]; norm_num
  set p : ℝ → ℂ := fun ρ => (ρ : ℂ) * u with hpdef
  have hpnorm : ∀ ρ : ℝ, ‖p ρ‖ = |ρ| := by
    intro ρ; rw [hpdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, hun, mul_one]
  have hpmem : ∀ ρ ∈ Set.Icc (0 : ℝ) ‖z‖, p ρ ∈ ball (0 : ℂ) 1 := by
    intro ρ hρ
    rw [mem_ball_zero_iff, hpnorm, abs_of_nonneg hρ.1]
    exact lt_of_le_of_lt hρ.2 hr1
  have hpz : p ‖z‖ = z := by
    rw [hpdef, hudef]; field_simp
  -- radial derivative of `ψ ρ := (ℓ (p ρ)).re`
  set ψ : ℝ → ℝ := fun ρ => (ℓ (p ρ)).re with hψdef
  set ψd : ℝ → ℝ := fun ρ => (u * (deriv (deriv f) (p ρ) / deriv f (p ρ))).re with hψddef
  have hp_deriv : ∀ ρ : ℝ, HasDerivAt p u ρ := by
    intro ρ
    have h1 : HasDerivAt (fun ρ : ℝ => (ρ : ℂ)) 1 ρ := Complex.ofRealCLM.hasDerivAt
    have := h1.mul_const u
    rw [one_mul] at this; exact this
  have hre_le_norm : ∀ w : ℂ, w.re ≤ ‖w‖ := by
    intro w
    by_cases h : w.re ≤ 0
    · exact le_trans h (norm_nonneg w)
    · push Not at h
      have h1 : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [mul_self_nonneg w.im, norm_nonneg w, h1, h]
  have hψ_deriv : ∀ ρ ∈ Set.Icc (0 : ℝ) ‖z‖, HasDerivAt ψ (ψd ρ) ρ := by
    intro ρ hρ
    have hpm := hpmem ρ hρ
    have hsc := HasDerivAt.scomp (x := ρ) (hℓ_deriv (p ρ) hpm) (hp_deriv ρ)
    rw [smul_eq_mul] at hsc
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt ρ hsc
  -- the comparison bound `ψd ρ ≤ 1/(1+ρ) + 3/(1-ρ)`
  set Ad : ℝ → ℝ := fun ρ => 1 / (1 + ρ) + 3 / (1 - ρ) with hAddef
  have hbound : ∀ ρ ∈ Set.Icc (0 : ℝ) ‖z‖, ψd ρ ≤ Ad ρ := by
    intro ρ hρ
    have hpm := hpmem ρ hρ
    have hρ0 : 0 ≤ ρ := hρ.1
    have hρ1 : ρ < 1 := lt_of_le_of_lt hρ.2 hr1
    have hdist := distortion_bound hf hinj h0 hd hpm
    -- rewrite the distortion inequality in terms of `p ρ = ρ u`
    have hcw : (starRingEnd ℂ) (p ρ) = (ρ : ℂ) * (starRingEnd ℂ) u := by
      rw [hpdef, map_mul, Complex.conj_ofReal]
    have hqval : (1 - (starRingEnd ℂ) (p ρ) * (p ρ)) = ((1 - ρ ^ 2 : ℝ) : ℂ) := by
      rw [hcw, hpdef]
      have : (ρ : ℂ) * (starRingEnd ℂ) u * ((ρ : ℂ) * u) = (ρ : ℂ) ^ 2 * ((starRingEnd ℂ) u * u) := by
        ring
      rw [this, hcuu]; push_cast; ring
    set dl : ℂ := deriv (deriv f) (p ρ) / deriv f (p ρ) with hdldef
    rw [hqval, hcw] at hdist
    -- rewrite the distortion into the `dl` form
    have hdist2 : ‖((1 - ρ ^ 2 : ℝ) : ℂ) * dl - 2 * ((ρ : ℂ) * (starRingEnd ℂ) u)‖ ≤ 4 := by
      have heq2 : ((1 - ρ ^ 2 : ℝ) : ℂ) * dl
          = ((1 - ρ ^ 2 : ℝ) : ℂ) * deriv (deriv f) (p ρ) / deriv f (p ρ) := by
        rw [hdldef]; ring
      rw [heq2]; exact hdist
    -- multiply inside by `u`
    have hmul : ‖((1 - ρ ^ 2 : ℝ) : ℂ) * (u * dl) - 2 * (ρ : ℂ)‖ ≤ 4 := by
      have heq : ((1 - ρ ^ 2 : ℝ) : ℂ) * (u * dl) - 2 * (ρ : ℂ)
          = (((1 - ρ ^ 2 : ℝ) : ℂ) * dl - 2 * ((ρ : ℂ) * (starRingEnd ℂ) u)) * u := by
        linear_combination (2 * (ρ : ℂ)) * hcuu
      rw [heq, norm_mul, hun, mul_one]; exact hdist2
    -- take real parts
    have hre : (1 - ρ ^ 2) * ψd ρ - 2 * ρ ≤ 4 := by
      have h2 : (((1 - ρ ^ 2 : ℝ) : ℂ) * (u * dl) - 2 * (ρ : ℂ)).re ≤ 4 :=
        le_trans (hre_le_norm _) hmul
      have h3 : (((1 - ρ ^ 2 : ℝ) : ℂ) * (u * dl) - 2 * (ρ : ℂ)).re
          = (1 - ρ ^ 2) * (u * dl).re - 2 * ρ := by
        have hrw : ((1 - ρ ^ 2 : ℝ) : ℂ) * (u * dl) - 2 * (ρ : ℂ)
            = ((1 - ρ ^ 2 : ℝ) : ℂ) * (u * dl) - ((2 * ρ : ℝ) : ℂ) := by push_cast; ring
        rw [hrw, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re]
      rw [h3] at h2
      rw [hψddef]; exact h2
    have hpos : (0 : ℝ) < 1 - ρ ^ 2 := by nlinarith
    show ψd ρ ≤ 1 / (1 + ρ) + 3 / (1 - ρ)
    rw [div_add_div _ _ (by linarith : (1 + ρ : ℝ) ≠ 0) (by linarith : (1 - ρ : ℝ) ≠ 0),
      le_div_iff₀ (by nlinarith : (0 : ℝ) < (1 + ρ) * (1 - ρ))]
    nlinarith [hre, hpos]
  -- the antiderivative `A` with `A' = Ad`
  set A : ℝ → ℝ := fun ρ => Real.log (1 + ρ) - 3 * Real.log (1 - ρ) with hAdef
  have hA_hasderiv : ∀ ρ ∈ Set.Icc (0 : ℝ) ‖z‖, HasDerivAt A (Ad ρ) ρ := by
    intro ρ hρ
    have h1p : (0 : ℝ) < 1 + ρ := by linarith [hρ.1]
    have h1m : (0 : ℝ) < 1 - ρ := by linarith [lt_of_le_of_lt hρ.2 hr1]
    have hlog1 : HasDerivAt (fun ρ => Real.log (1 + ρ)) (1 / (1 + ρ)) ρ := by
      have hc := (Real.hasDerivAt_log (ne_of_gt h1p)).comp ρ ((hasDerivAt_id ρ).const_add 1)
      rw [mul_one] at hc; rw [one_div]; exact hc
    have hlog2 : HasDerivAt (fun ρ => Real.log (1 - ρ)) (-(1 / (1 - ρ))) ρ := by
      have hc := (Real.hasDerivAt_log (ne_of_gt h1m)).comp ρ ((hasDerivAt_id ρ).const_sub 1)
      rw [show (1 - ρ)⁻¹ * (-1 : ℝ) = -(1 / (1 - ρ)) from by rw [one_div]; ring] at hc
      exact hc
    have hval : 1 / (1 + ρ) - 3 * (-(1 / (1 - ρ))) = Ad ρ := by rw [hAddef]; ring
    rw [← hval]
    exact hlog1.sub (hlog2.const_mul 3)
  -- monotonicity of `k = A - ψ`
  set k : ℝ → ℝ := fun ρ => A ρ - ψ ρ with hkdef
  have hk_hasderiv : ∀ ρ ∈ Set.Icc (0 : ℝ) ‖z‖, HasDerivAt k (Ad ρ - ψd ρ) ρ :=
    fun ρ hρ => (hA_hasderiv ρ hρ).sub (hψ_deriv ρ hρ)
  have hmono : MonotoneOn k (Set.Icc 0 ‖z‖) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 ‖z‖)
    · exact fun ρ hρ => (hk_hasderiv ρ hρ).continuousAt.continuousWithinAt
    · intro ρ hρ
      rw [interior_Icc] at hρ
      exact (hk_hasderiv ρ (Set.mem_Icc.mpr ⟨le_of_lt hρ.1, le_of_lt hρ.2⟩)).differentiableAt.differentiableWithinAt
    · intro ρ hρ
      rw [interior_Icc] at hρ
      have hρ' : ρ ∈ Set.Icc (0 : ℝ) ‖z‖ := Set.mem_Icc.mpr ⟨le_of_lt hρ.1, le_of_lt hρ.2⟩
      rw [(hk_hasderiv ρ hρ').deriv]
      linarith [hbound ρ hρ']
  -- `k 0 = 0`
  have hp0 : p 0 = 0 := by rw [hpdef]; simp
  have hℓ0re : (ℓ (p 0)).re = 0 := by
    rw [hp0]
    have hexp1 : Complex.exp (ℓ 0) = 1 := by rw [hℓ_exp 0 hmem0, hd]
    have hnrm : Real.exp ((ℓ 0).re) = 1 := by rw [← Complex.norm_exp, hexp1, norm_one]
    have : (ℓ 0).re = Real.log 1 := by rw [← hnrm, Real.log_exp]
    rwa [Real.log_one] at this
  have hk0 : k 0 = 0 := by
    rw [hkdef]; simp only [hAdef, hψdef]
    rw [hℓ0re]; simp
  have hmemz : ‖z‖ ∈ Set.Icc (0 : ℝ) ‖z‖ := Set.mem_Icc.mpr ⟨hr0.le, le_refl _⟩
  have hmem0' : (0 : ℝ) ∈ Set.Icc (0 : ℝ) ‖z‖ := Set.mem_Icc.mpr ⟨le_refl _, hr0.le⟩
  have hmono_le : k 0 ≤ k ‖z‖ := hmono hmem0' hmemz hr0.le
  -- translate back
  have h1p : (0 : ℝ) < 1 + ‖z‖ := by linarith [norm_nonneg z]
  have h1m : (0 : ℝ) < 1 - ‖z‖ := by linarith
  have hψle : ψ ‖z‖ ≤ A ‖z‖ := by
    rw [hk0, hkdef] at hmono_le; simp only at hmono_le; linarith
  rw [hnorm_eq z hz]
  have hψz : (ℓ z).re = ψ ‖z‖ := by rw [hψdef]; simp only [hpz]
  rw [hψz]
  calc Real.exp (ψ ‖z‖) ≤ Real.exp (A ‖z‖) := Real.exp_le_exp.mpr hψle
    _ = (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
        rw [hAdef]; simp only []
        rw [Real.exp_sub, Real.exp_log h1p,
          show (3 : ℝ) * Real.log (1 - ‖z‖) = Real.log ((1 - ‖z‖) ^ 3) from by
            rw [Real.log_pow]; push_cast; ring,
          Real.exp_log (by positivity)]

/-- **Koebe growth bound.** `‖f z‖ ≤ ‖z‖/(1-‖z‖)²`. -/
theorem growth_bound {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0) (hd : deriv f 0 = 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have hr1 : ‖z‖ < 1 := by rwa [mem_ball_zero_iff] at hz
  have hderivf_cont : ContinuousOn (deriv f) (ball 0 1) := hfan.deriv.continuousOn
  set r : ℝ := ‖z‖ with hrdef
  set pt : ℝ → ℂ := fun t => (t : ℂ) * z with hptdef
  have hpt_cont : Continuous pt := by
    rw [hptdef]; exact Complex.continuous_ofReal.mul continuous_const
  have hptnorm : ∀ t : ℝ, ‖pt t‖ = |t| * r := by
    intro t; rw [hptdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, hrdef]
  have htmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, pt t ∈ ball (0 : ℂ) 1 := by
    intro t ht
    rw [mem_ball_zero_iff, hptnorm, abs_of_nonneg ht.1]
    calc t * r ≤ 1 * r := by nlinarith [ht.2, norm_nonneg z]
      _ = r := one_mul r
      _ < 1 := hr1
  have htmaps : Set.MapsTo pt (Set.Icc (0 : ℝ) 1) (ball (0 : ℂ) 1) := htmem
  -- integrand `g t = z * f'(pt t)` and `f z = ∫₀¹ g`
  set g : ℝ → ℂ := fun t => z * deriv f (pt t) with hgdef
  have hpt_deriv : ∀ t : ℝ, HasDerivAt pt z t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      have hc := (hasDerivAt_id t).ofReal_comp
      rw [Complex.ofReal_one] at hc; exact hc
    have h2 := h1.mul_const z
    rw [one_mul] at h2; exact h2
  have hf_at : ∀ q ∈ ball (0 : ℂ) 1, HasDerivAt f (deriv f q) q :=
    fun q hq => (hf.differentiableAt (isOpen_ball.mem_nhds hq)).hasDerivAt
  have hF1_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t => f (pt t)) (g t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have hsc := HasDerivAt.scomp (x := t) (hf_at (pt t) (htmem t ht)) (hpt_deriv t)
    rw [smul_eq_mul] at hsc
    exact hsc
  have hg_cont : ContinuousOn g (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact continuousOn_const.mul (hderivf_cont.comp hpt_cont.continuousOn htmaps)
  have hg_int : IntervalIntegrable g volume 0 1 := hg_cont.intervalIntegrable
  have hpt1 : pt 1 = z := by rw [hptdef]; simp
  have hpt0 : pt 0 = 0 := by rw [hptdef]; simp
  have hfz : (∫ t in (0 : ℝ)..1, g t) = f z := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF1_deriv hg_int, hpt1, hpt0, h0, sub_zero]
  -- bound function and its antiderivative
  set bd : ℝ → ℝ := fun t => r * ((1 + t * r) / (1 - t * r) ^ 3) with hbddef
  set F2 : ℝ → ℝ := fun t => r * (t / (1 - t * r) ^ 2) with hF2def
  have hrnn : 0 ≤ r := norm_nonneg z
  have hden_pos : ∀ t ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < 1 - t * r := by
    intro t ht
    have : t * r ≤ r := by nlinarith [ht.1, ht.2, hrnn]
    linarith
  have hbd_cont : ContinuousOn bd (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply continuousOn_const.mul
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact pow_ne_zero 3 (ne_of_gt (hden_pos t ht))
  have hbd_int : IntervalIntegrable bd volume 0 1 := hbd_cont.intervalIntegrable
  have hF2_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F2 (bd t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have hdp := hden_pos t ht
    have hlin : HasDerivAt (fun t : ℝ => 1 - t * r) (-r) t := by
      have := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const r)
      rw [zero_sub, one_mul] at this; exact this
    have h2 : HasDerivAt (fun t : ℝ => (1 - t * r) ^ 2) (2 * (1 - t * r) ^ (2 - 1) * -r) t :=
      hlin.pow 2
    have hne : (1 - t * r) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hdp)
    have h3 := (hasDerivAt_id t).div h2 hne
    have h4 := h3.const_mul r
    have hval : r * ((1 * (1 - t * r) ^ 2 - t * (2 * (1 - t * r) ^ (2 - 1) * -r)) / ((1 - t * r) ^ 2) ^ 2)
        = bd t := by
      simp only [hbddef, Nat.reduceSub, pow_one]; field_simp [hdp.ne']; ring
    rw [← hval]; exact h4
  have hbdint_eq : (∫ t in (0 : ℝ)..1, bd t) = r / (1 - r) ^ 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF2_deriv hbd_int]
    simp only [hF2def, mul_one, one_mul, mul_zero, zero_mul, zero_div, sub_zero]
    rw [mul_one_div]
  -- assemble
  rw [← hfz]
  calc ‖∫ t in (0 : ℝ)..1, g t‖
      ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, bd t := by
        apply intervalIntegral.integral_mono_on (by norm_num) hg_int.norm hbd_int
        intro t ht
        simp only [hgdef, hbddef, norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
        have hdn := deriv_norm_le hf hinj h0 hd (htmem t ht)
        rw [hptnorm, abs_of_nonneg ht.1] at hdn
        exact hdn
    _ = r / (1 - r) ^ 2 := hbdint_eq
    _ = ‖z‖ / (1 - ‖z‖) ^ 2 := by rw [hrdef]

end Uniformization
