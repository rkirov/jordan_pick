/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Winding-number infrastructure for the area theorem (Stage A)

This file develops the winding-number layer that the Grönwall area theorem
(`Uniformization/Complex/AreaTheorem.lean`, lemma `groenwall_radius`) is built on,
following the route recorded there.  Working in exterior coordinates `w = 1/z`, the
univalent map `g z = z⁻¹ + h z` on the punctured unit ball becomes

  `extMap h w := w + h w⁻¹`  (`= g (w⁻¹)`),

holomorphic and injective on the exterior `{w | 1 < ‖w‖}`.  For a radius `t > 1` and
a point `p` the winding number of the image circle `extMap h '' {‖w‖ = t}` around `p`
is

  `winding h t p := (2πi)⁻¹ ∮_{|w|=t} (extMap h)'(w) / (extMap h w − p) dw`.

## What is proved here (sorry-free)

* `extMap_analyticOnNhd` : `extMap h` is analytic on `{1 < ‖w‖}`.
* `extMap_injOn` : `extMap h` is injective on `{1 < ‖w‖}` (transported from the
  injectivity of `g` on the punctured ball).
* `winding_eq_of_forall_ne` (**A1**) : the winding is constant across a zero-free
  closed annulus — if `extMap h w ≠ p` for all `w` with `s ≤ ‖w‖ ≤ t`, then
  `winding h t p = winding h s p`.  Direct from the annulus Cauchy–Goursat theorem.
* `winding_jump` (**A2**) : the winding jumps by exactly `1` across a simple zero —
  if `extMap h w₀ = p` with `s < ‖w₀‖ < t` the unique preimage of `p` in the closed
  annulus, then `winding h t p − winding h s p = 1`.  Route: injectivity ⇒
  `deriv (extMap h) w₀ ≠ 0` (private `deriv_ne_zero_of_injOn`, the `n`-to-`1` normal
  form), giving the order-`1` factorization `extMap h − p = (· − w₀) • u` with `u`
  analytic non-vanishing on the annulus; then
  `(extMap h)'/(extMap h − p) = (· − w₀)⁻¹ + u'/u` on the two circles, the `(·−w₀)⁻¹`
  part contributing `2πi` on the outer circle and `0` on the inner, and the `u'/u`
  part cancelling by A1-style annulus Cauchy.

## Roadmap for the remaining stages (not yet formalized)

* **A3** (value at infinity): for fixed `p`, `winding h t p = 1` for all large `t`.
* **A4** (winding equals indicator): `winding h t p = 𝟙_{E_t}(p)` a.e., where
  `E_t := (extMap h '' {‖w‖ > t})ᶜ`, by A1/A2/A3 case analysis + injectivity.
* **B** (integral identity): `∫_{p ∈ ball 0 R} winding h t p = shoelace h t` where
  `shoelace h t := (2i)⁻¹ ∮_{|w|=t} conj(extMap h w) · (extMap h)'(w) dw`, via Fubini
  and the Cauchy transform of the disk `∫_{ball 0 R} (ζ − p)⁻¹ = π conj ζ`.
* **C** (shoelace evaluation + finish): `shoelace h t = π(t² − ∑ n, n‖b n‖² t^{-2n})`
  by termwise circle integration; then `0 ≤ vol(E_t) = ∫ winding = shoelace h t` gives
  `∑ n, n‖b n‖² t^{-2n} ≤ t²`, i.e. `groenwall_radius` after `ρ = 1/t`.
-/

open Set Metric Complex MeasureTheory Topology Filter

noncomputable section

namespace Uniformization

/-- The exterior form of the univalent map: `extMap h w = w + h w⁻¹ = g (w⁻¹)` where
`g z = z⁻¹ + h z`.  Holomorphic and injective on `{w | 1 < ‖w‖}`. -/
def extMap (h : ℂ → ℂ) : ℂ → ℂ := fun w => w + h w⁻¹

/-- The open exterior of the closed unit ball, `{w | 1 < ‖w‖}`. -/
def exteriorUnit : Set ℂ := {w : ℂ | 1 < ‖w‖}

theorem isOpen_exteriorUnit : IsOpen exteriorUnit := by
  have : exteriorUnit = (closedBall (0 : ℂ) 1)ᶜ := by
    ext w
    simp only [exteriorUnit, mem_setOf_eq, mem_compl_iff, mem_closedBall_zero_iff, not_le]
  rw [this]; exact isClosed_closedBall.isOpen_compl

/-- The exterior map is analytic on `{1 < ‖w‖}`. -/
theorem extMap_analyticOnNhd (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h (ball 0 1)) :
    AnalyticOnNhd ℂ (extMap h) exteriorUnit := by
  have hinvA : AnalyticOnNhd ℂ (fun w : ℂ => w⁻¹) exteriorUnit := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0] at hw
      simp only [exteriorUnit, mem_setOf_eq, norm_zero] at hw; linarith
    exact analyticAt_inv hw0
  have hmaps : Set.MapsTo (fun w : ℂ => w⁻¹) exteriorUnit (ball 0 1) := by
    intro w hw
    simp only [exteriorUnit, mem_setOf_eq] at hw
    rw [mem_ball_zero_iff, norm_inv, inv_lt_one_iff₀]; right; exact hw
  exact analyticOnNhd_id.add (hh.comp hinvA hmaps)

/-- The winding number of the image circle `extMap h '' {‖w‖ = t}` around `p`:
`winding h t p = (2πi)⁻¹ ∮_{|w|=t} (extMap h)'(w) / (extMap h w − p) dw`. -/
def winding (h : ℂ → ℂ) (t : ℝ) (p : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * ∮ w in C(0, t), deriv (extMap h) w / (extMap h w - p)

/-- **A1**: the winding number is constant across a zero-free closed annulus.
If `extMap h w ≠ p` for every `w` with `s ≤ ‖w‖ ≤ t` (and `1 < s ≤ t`), then the
winding numbers at radii `t` and `s` agree. -/
theorem winding_eq_of_forall_ne (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h (ball 0 1))
    {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) {p : ℂ}
    (hne : ∀ w : ℂ, s ≤ ‖w‖ → ‖w‖ ≤ t → extMap h w ≠ p) :
    winding h t p = winding h s p := by
  have hG := extMap_analyticOnNhd h hh
  have hG' : AnalyticOnNhd ℂ (deriv (extMap h)) exteriorUnit := hG.deriv
  set f : ℂ → ℂ := fun w => deriv (extMap h) w / (extMap h w - p) with hf
  have hfA : ∀ z : ℂ, s ≤ ‖z‖ → ‖z‖ ≤ t → AnalyticAt ℂ f z := by
    intro z hz1 hz2
    have hzExt : z ∈ exteriorUnit := by
      simp only [exteriorUnit, mem_setOf_eq]; linarith
    have hden : extMap h z - p ≠ 0 := sub_ne_zero.mpr (hne z hz1 hz2)
    exact (hG' z hzExt).div ((hG z hzExt).sub analyticAt_const) hden
  have hcont : ContinuousOn f (closedBall (0 : ℂ) t \ ball (0 : ℂ) s) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [mem_closedBall_zero_iff] at hz1
    rw [mem_ball_zero_iff, not_lt] at hz2
    exact ((hfA z hz2 hz1).continuousAt).continuousWithinAt
  have hdiff : ∀ z ∈ (ball (0 : ℂ) t \ closedBall (0 : ℂ) s) \ (∅ : Set ℂ),
      DifferentiableAt ℂ f z := by
    intro z hz
    simp only [sdiff_empty] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [mem_ball_zero_iff] at hz1
    rw [mem_closedBall_zero_iff, not_le] at hz2
    exact (hfA z hz2.le hz1.le).differentiableAt
  have hkey := circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (by linarith : (0 : ℝ) < s) hst countable_empty hcont hdiff
  simp only [winding]
  rw [hkey]

/-- An injective analytic function has nonvanishing derivative (planar `n`-to-`1`
normal form).  Copied from `Uniformization/Surface/Injective.lean` (private there). -/
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
  have hw0 : w ≠ 0 := by intro hh0; apply hc0; rw [← hwn, hh0, zero_pow hn0]
  set hloc : ℂ → ℂ := fun z => w * root z with hhdef
  have hh_an : AnalyticAt ℂ hloc z₀ := analyticAt_const.mul hroot_an
  have hh_z₀ : hloc z₀ = w := by simp [hhdef, hroot_z₀]
  have hh_pow : ∀ z, hloc z ^ n = g z := by
    intro z
    simp only [hhdef, mul_pow, hwn, hroot_pow z]
    rw [mul_comm, div_mul_cancel₀ _ hc0]
  set H : ℂ → ℂ := fun z => (z - z₀) * hloc z with hHdef
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
      have hd : HasDerivAt H (hloc z₀) z₀ := by
        simp only [hHdef]
        have h1 : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
        have h2 : HasDerivAt hloc (deriv hloc z₀) z₀ := hh_an.differentiableAt.hasDerivAt
        have h3 := h1.mul h2
        rw [show (1:ℂ) * hloc z₀ + (z₀ - z₀) * deriv hloc z₀ = hloc z₀ from by ring] at h3
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
    have hh2 := hfd.image_mem_toOpenPartialHomeomorph_target
    rwa [show H z₀ = (0 : ℂ) from hH_z₀] at hh2
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
  set uu : ℂ := (↑(ε / 2) : ℂ) with hudef
  have hu0 : uu ≠ 0 := by
    simp only [hudef, ne_eq, Complex.ofReal_eq_zero]; positivity
  have hunorm : ‖uu‖ < ε := by
    simp only [hudef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < ε/2)]
    linarith
  have huball : uu ∈ ball (0 : ℂ) ε := by simpa [Metric.mem_ball, dist_zero_right] using hunorm
  have hζuball : ζ * uu ∈ ball (0 : ℂ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul]
    exact hunorm
  have hu_mem : uu ∈ R.target ∩ R.symm ⁻¹' W := hball huball
  have hζu_mem : ζ * uu ∈ R.target ∩ R.symm ⁻¹' W := hball hζuball
  set z₁ : ℂ := R.symm uu with hz₁def
  set z₂ : ℂ := R.symm (ζ * uu) with hz₂def
  have hz₁W : z₁ ∈ W := hu_mem.2
  have hz₂W : z₂ ∈ W := hζu_mem.2
  have hHz₁ : H z₁ = uu := by rw [← hRcoe, hz₁def, R.right_inv hu_mem.1]
  have hHz₂ : H z₂ = ζ * uu := by rw [← hRcoe, hz₂def, R.right_inv hζu_mem.1]
  have hFeq : F z₁ = F z₂ := by
    rw [hz₁W.1, hz₂W.1, hHz₁, hHz₂, mul_pow, hζpow, one_mul]
  have hz_eq : z₁ = z₂ := hinj hz₁W.2 hz₂W.2 hFeq
  have huζu : uu ≠ ζ * uu := by
    intro he
    have h1 : (1 - ζ) * uu = 0 := by rw [sub_mul, one_mul, ← he, sub_self]
    rcases mul_eq_zero.mp h1 with hz | hz
    · exact hζ1 (sub_eq_zero.mp hz).symm
    · exact hu0 hz
  have hz_ne : z₁ ≠ z₂ := by
    intro he
    apply huζu
    calc uu = H z₁ := hHz₁.symm
      _ = H z₂ := by rw [he]
      _ = ζ * uu := hHz₂
  exact hz_ne hz_eq

/-- The exterior map is injective on `{1 < ‖w‖}` (from injectivity of `g` on the
punctured ball, via `w ↦ w⁻¹`). -/
theorem extMap_injOn (h : ℂ → ℂ)
    (hinj : Set.InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) :
    Set.InjOn (extMap h) exteriorUnit := by
  have hmem : ∀ w : ℂ, w ∈ exteriorUnit → w⁻¹ ∈ ball 0 1 \ {0} := by
    intro w hw
    simp only [exteriorUnit, mem_setOf_eq] at hw
    have hw0 : w ≠ 0 := by rintro rfl; simp only [norm_zero] at hw; linarith
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_inv, inv_lt_one_iff₀]; right; exact hw
    · simp only [mem_singleton_iff]; exact inv_ne_zero hw0
  intro w₁ hw₁ w₂ hw₂ heq
  have e1 : extMap h w₁ = (fun z => z⁻¹ + h z) w₁⁻¹ := by simp only [extMap, inv_inv]
  have e2 : extMap h w₂ = (fun z => z⁻¹ + h z) w₂⁻¹ := by simp only [extMap, inv_inv]
  rw [e1, e2] at heq
  exact inv_injective (hinj (hmem w₁ hw₁) (hmem w₂ hw₂) heq)

/-- **A2**: the winding number jumps by exactly `1` across a simple zero.
If `extMap h w₀ = p` with `s < ‖w₀‖ < t` and `w₀` is the unique preimage of `p` in
the closed annulus `s ≤ ‖w‖ ≤ t`, then `winding h t p − winding h s p = 1`. -/
theorem winding_jump (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (hinj : Set.InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0}))
    {s t : ℝ} (hs : 1 < s) (hst : s < t) {p w₀ : ℂ}
    (hw₀ : extMap h w₀ = p) (hw₀s : s < ‖w₀‖) (hw₀t : ‖w₀‖ < t)
    (huniq : ∀ w : ℂ, s ≤ ‖w‖ → ‖w‖ ≤ t → extMap h w = p → w = w₀) :
    winding h t p - winding h s p = 1 := by
  have hs0 : (0:ℝ) < s := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hst' : s ≤ t := le_of_lt hst
  simp only [winding]
  set G : ℂ → ℂ := extMap h with hGdef
  have hGA : AnalyticOnNhd ℂ G exteriorUnit := extMap_analyticOnNhd h hh
  have hw₀ext : w₀ ∈ exteriorUnit := by simp only [exteriorUnit, mem_setOf_eq]; linarith
  have hGw₀ : AnalyticAt ℂ G w₀ := hGA w₀ hw₀ext
  have hderiv0 : deriv G w₀ ≠ 0 :=
    deriv_ne_zero_of_injOn hGw₀ (isOpen_exteriorUnit.mem_nhds hw₀ext) (extMap_injOn h hinj)
  set u : ℂ → ℂ := fun w => if w = w₀ then deriv G w₀ else (G w - p) / (w - w₀) with hudef
  have hfactor : ∀ z : ℂ, G z - p = (z - w₀) * u z := by
    intro z
    by_cases hz : z = w₀
    · subst hz; simp only [hudef, if_pos rfl]; rw [hw₀, sub_self, sub_self, zero_mul]
    · simp only [hudef, if_neg hz]
      rw [← mul_div_assoc, mul_div_cancel_left₀ (G z - p) (sub_ne_zero.mpr hz)]
  have hu_an_ne : ∀ z : ℂ, z ∈ exteriorUnit → z ≠ w₀ → AnalyticAt ℂ u z := by
    intro z hzext hzne
    have hcong : (fun y => (G y - p) / (y - w₀)) =ᶠ[𝓝 z] u := by
      have hne : ∀ᶠ y in 𝓝 z, y ≠ w₀ :=
        isOpen_compl_singleton.mem_nhds (by simpa using hzne)
      filter_upwards [hne] with y hy; simp only [hudef, if_neg hy]
    exact (((hGA z hzext).sub analyticAt_const).div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzne)).congr hcong
  have hGmp_an : AnalyticAt ℂ (fun z => G z - p) w₀ := hGw₀.sub analyticAt_const
  have hGmp0 : (fun z => G z - p) w₀ = 0 := by show G w₀ - p = 0; rw [hw₀, sub_self]
  have hGmp_deriv : deriv (fun z => G z - p) w₀ ≠ 0 := by rw [deriv_sub_const]; exact hderiv0
  have hord : analyticOrderAt (fun z => G z - p) w₀ = 1 :=
    hGmp_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hGmp0 hGmp_deriv
  obtain ⟨g, hgan, hg0, hgfeq0⟩ :=
    (hGmp_an.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast hord)
  have hgfeq : (fun z => G z - p) =ᶠ[𝓝 w₀] (fun z => (z - w₀) * g z) := by
    filter_upwards [hgfeq0] with z hz; simpa [pow_one, smul_eq_mul] using hz
  have hgw₀ : g w₀ = deriv G w₀ := by
    have hd : HasDerivAt (fun z => (z - w₀) * g z) (g w₀) w₀ := by
      have h1 : HasDerivAt (fun z : ℂ => z - w₀) 1 w₀ := (hasDerivAt_id w₀).sub_const w₀
      have h2 : HasDerivAt g (deriv g w₀) w₀ := hgan.differentiableAt.hasDerivAt
      have h3 := h1.mul h2
      rw [show (1:ℂ) * g w₀ + (w₀ - w₀) * deriv g w₀ = g w₀ from by ring] at h3
      exact h3
    have e1 : deriv (fun z => G z - p) w₀ = deriv (fun z => (z - w₀) * g z) w₀ := hgfeq.deriv_eq
    rw [deriv_sub_const] at e1
    rw [e1, hd.deriv]
  have hug : u =ᶠ[𝓝 w₀] g := by
    filter_upwards [hgfeq] with z hzeq
    by_cases hz : z = w₀
    · subst hz; simp only [hudef, if_pos rfl]; exact hgw₀.symm
    · simp only [hudef, if_neg hz]
      rw [hzeq, mul_div_cancel_left₀ (g z) (sub_ne_zero.mpr hz)]
  have hu_an_w₀ : AnalyticAt ℂ u w₀ := hgan.congr hug.symm
  have hu_an : ∀ z : ℂ, s ≤ ‖z‖ → ‖z‖ ≤ t → AnalyticAt ℂ u z := by
    intro z hz1 hz2
    have hzext : z ∈ exteriorUnit := by simp only [exteriorUnit, mem_setOf_eq]; linarith
    by_cases hz : z = w₀
    · subst hz; exact hu_an_w₀
    · exact hu_an_ne z hzext hz
  have hu_ne : ∀ z : ℂ, s ≤ ‖z‖ → ‖z‖ ≤ t → u z ≠ 0 := by
    intro z hz1 hz2
    by_cases hz : z = w₀
    · subst hz; simp only [hudef, if_pos rfl]; exact hderiv0
    · simp only [hudef, if_neg hz]
      refine div_ne_zero ?_ (sub_ne_zero.mpr hz)
      rw [sub_ne_zero]; intro he; exact hz (huniq z hz1 hz2 he)
  have hGfun : G = fun y => (y - w₀) * u y + p := funext fun y => by rw [← hfactor y]; ring
  have hderivG : ∀ z : ℂ, DifferentiableAt ℂ u z → deriv G z = u z + (z - w₀) * deriv u z := by
    intro z huz
    have ha : HasDerivAt (fun y : ℂ => y - w₀) 1 z := (hasDerivAt_id z).sub_const w₀
    have hb : HasDerivAt u (deriv u z) z := huz.hasDerivAt
    have h1 : HasDerivAt G (1 * u z + (z - w₀) * deriv u z) z := by
      rw [hGfun]; exact (ha.mul hb).add_const p
    rw [h1.deriv]; ring
  set IG : ℂ → ℂ := fun w => deriv G w / (G w - p) with hIGdef
  set F1 : ℂ → ℂ := fun w => (w - w₀)⁻¹ with hF1def
  set F2 : ℂ → ℂ := fun w => deriv u w / u w with hF2def
  have hInt : ∀ r : ℝ, s ≤ r → r ≤ t → ‖w₀‖ ≠ r →
      EqOn IG (fun w => F1 w + F2 w) (sphere (0 : ℂ) r) := by
    intro r hr1 hr2 hrne w hw
    have hwn : ‖w‖ = r := by rwa [mem_sphere_zero_iff_norm] at hw
    have hwne : w ≠ w₀ := by intro he; rw [he] at hwn; exact hrne hwn
    have hz1 : s ≤ ‖w‖ := by rw [hwn]; exact hr1
    have hz2 : ‖w‖ ≤ t := by rw [hwn]; exact hr2
    have huw : u w ≠ 0 := hu_ne w hz1 hz2
    have hww₀ : w - w₀ ≠ 0 := sub_ne_zero.mpr hwne
    have hd := hderivG w (hu_an w hz1 hz2).differentiableAt
    simp only [hIGdef, hF1def, hF2def]
    rw [show G w - p = (w - w₀) * u w from hfactor w, hd]
    field_simp
  have hF1ci : ∀ r : ℝ, 0 < r → ‖w₀‖ ≠ r → CircleIntegrable F1 0 r := by
    intro r hr hrne
    apply ContinuousOn.circleIntegrable'
    apply ContinuousOn.inv₀
    · exact (continuousOn_id.sub continuousOn_const)
    · intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      rw [sub_ne_zero]; intro he; rw [he] at hz; rw [abs_of_pos hr] at hz; exact hrne hz
  have hF2ci : ∀ r : ℝ, s ≤ r → r ≤ t → CircleIntegrable F2 0 r := by
    intro r hr1 hr2
    have hrpos : 0 < r := by linarith
    apply ContinuousOn.circleIntegrable'
    intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hrpos] at hz
    have hz1 : s ≤ ‖z‖ := by rw [hz]; exact hr1
    have hz2 : ‖z‖ ≤ t := by rw [hz]; exact hr2
    exact ((((hu_an z hz1 hz2).deriv).div (hu_an z hz1 hz2)
      (hu_ne z hz1 hz2)).continuousAt).continuousWithinAt
  have hF1t : (∮ w in C(0, t), F1 w) = 2 * ↑Real.pi * I := by
    have : w₀ ∈ ball (0:ℂ) t := by rw [mem_ball_zero_iff]; exact hw₀t
    simpa [hF1def] using circleIntegral.integral_sub_inv_of_mem_ball this
  have hF1s : (∮ w in C(0, s), F1 w) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable hs0.le countable_empty
    · apply ContinuousOn.inv₀
      · exact (continuousOn_id.sub continuousOn_const)
      · intro z hz
        rw [mem_closedBall_zero_iff] at hz
        rw [sub_ne_zero]; intro he; rw [he] at hz; linarith
    · intro z hz
      rw [sdiff_empty, mem_ball_zero_iff] at hz
      have hzne : z ≠ w₀ := by intro he; rw [he] at hz; linarith
      exact (differentiableAt_id.sub_const w₀).inv (sub_ne_zero.mpr hzne)
  have hF2eq : (∮ w in C(0, t), F2 w) = ∮ w in C(0, s), F2 w := by
    apply circleIntegral_eq_of_differentiable_on_annulus_off_countable hs0 hst' countable_empty
    · intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [mem_closedBall_zero_iff] at hz1
      rw [mem_ball_zero_iff, not_lt] at hz2
      exact ((((hu_an z hz2 hz1).deriv).div (hu_an z hz2 hz1)
        (hu_ne z hz2 hz1)).continuousAt).continuousWithinAt
    · intro z hz
      rw [sdiff_empty] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [mem_ball_zero_iff] at hz1
      rw [mem_closedBall_zero_iff, not_le] at hz2
      exact (((hu_an z hz2.le hz1.le).deriv).div (hu_an z hz2.le hz1.le)
        (hu_ne z hz2.le hz1.le)).differentiableAt
  have et : (∮ w in C(0, t), IG w) = (2 * ↑Real.pi * I) + ∮ w in C(0, t), F2 w := by
    rw [circleIntegral.integral_congr ht0.le (hInt t hst' le_rfl (ne_of_lt hw₀t))]
    rw [circleIntegral.integral_add (hF1ci t ht0 (ne_of_lt hw₀t)) (hF2ci t hst' le_rfl)]
    rw [hF1t]
  have es : (∮ w in C(0, s), IG w) = ∮ w in C(0, s), F2 w := by
    rw [circleIntegral.integral_congr hs0.le (hInt s le_rfl hst' (ne_of_lt hw₀s).symm)]
    rw [circleIntegral.integral_add (hF1ci s hs0 (ne_of_lt hw₀s).symm) (hF2ci s le_rfl hst')]
    rw [hF1s, zero_add]
  have key : (∮ w in C(0, t), IG w) - (∮ w in C(0, s), IG w) = 2 * ↑Real.pi * I := by
    rw [et, es, hF2eq]; ring
  have hne0 : (2 * ↑Real.pi * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [← mul_sub, key, inv_mul_cancel₀ hne0]

end Uniformization
