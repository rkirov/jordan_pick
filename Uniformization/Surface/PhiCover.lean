/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Green

/-!
# Branches of `exp(−G−iF)` and their rigidity (support file for `Phi.lean`)

This file develops the *local* theory of "modulus-`e^{−G}` branches": local
holomorphic maps `ψ` with `‖ψ‖ = exp (−G)` away from the pole `x₀`.  These are
the building blocks of the multiplicative étale space used to produce a global
`φ` with `‖φ‖ = e^{−G}` (see `Phi.lean`).

The three key local facts (mirroring the additive conjugate theory of
`Rado/Surface/Germs.lean`):

* `exists_branch_away`: away from the pole a branch exists (from a harmonic
  conjugate `F` of `G`, take `ψ = exp(−F)`);
* `exists_branch_pole`: at the pole a branch exists (in the log-pole chart,
  `ψ = ξ·exp(−W)` with `Re W = H`);
* `IsModulusBranch.exists_unimodular`: two branches over a preconnected open
  agree up to a unimodular constant.
-/

open Set Metric Topology MeasureTheory InnerProductSpace Complex Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The branch predicate -/

/-- `ψ` is a *modulus-`e^{−G}` branch* on `V`: holomorphic there, with
`‖ψ x‖ = exp (−G x)` for every `x ∈ V` away from the pole `x₀`. -/
def IsModulusBranch (G : X → ℝ) (x₀ : X) (ψ : X → ℂ) (V : Set X) : Prop :=
  HolomorphicOn ψ V ∧ ∀ x ∈ V \ {x₀}, ‖ψ x‖ = Real.exp (-G x)

namespace IsModulusBranch

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem mono {G : X → ℝ} {x₀ : X} {ψ : X → ℂ} {V W : Set X}
    (hψ : IsModulusBranch G x₀ ψ V) (hWV : W ⊆ V) : IsModulusBranch G x₀ ψ W :=
  ⟨hψ.1.mono hWV, fun x hx ↦ hψ.2 x ⟨hWV hx.1, hx.2⟩⟩

end IsModulusBranch

/-! ## Holomorphy helpers -/

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Scaling a holomorphic map by a constant stays holomorphic. -/
theorem HolomorphicOn.const_mul {F : X → ℂ} {s : Set X} (hF : HolomorphicOn F s) (c : ℂ) :
    HolomorphicOn (fun x ↦ c * F x) s :=
  fun x hx ↦ analyticAt_const.mul (hF x hx)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `exp (−F)` is holomorphic wherever `F` is. -/
theorem HolomorphicOn.cexp_neg {F : X → ℂ} {s : Set X} (hF : HolomorphicOn F s) :
    HolomorphicOn (fun x ↦ Complex.exp (-(F x))) s := by
  intro x hx
  have h1 : AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hF x hx
  exact h1.neg.cexp'

/-- If `ψ` reads through a maximal-atlas chart `e` as an analytic function `g`
on an open `O ⊆ e.target`, then `ψ` is holomorphic on `e.symm '' O`. -/
theorem holomorphicOn_comp_chart {e : OpenPartialHomeomorph X ℂ} (he : e ∈ riemannAtlas X)
    {g : ℂ → ℂ} {O : Set ℂ} (hOt : O ⊆ e.target) (hg : AnalyticOnNhd ℂ g O)
    {ψ : X → ℂ} (hψ : ∀ x ∈ e.source, ψ x = g (e x)) :
    HolomorphicOn ψ (e.symm '' O) := by
  intro x hx
  obtain ⟨w, hwO, hwx⟩ := hx
  have hwt : w ∈ e.target := hOt hwO
  have hxsrc : x ∈ e.source := hwx ▸ e.map_target hwt
  have hex : e x = w := by rw [← hwx, e.right_inv hwt]
  set c := chartAt ℂ x with hc
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have htrans : AnalyticAt ℂ (e ∘ c.symm) (c x) :=
    transition_analyticAt (chartAt_mem_riemannAtlas x) he ⟨hcx, hxsrc⟩
  have hval : (e ∘ c.symm) (c x) = w := by
    simp only [Function.comp_apply, c.left_inv hcx, hex]
  have hg' : AnalyticAt ℂ g ((e ∘ c.symm) (c x)) := by rw [hval]; exact hg w hwO
  have hcomp : AnalyticAt ℂ (g ∘ (e ∘ c.symm)) (c x) := hg'.comp htrans
  have hUopen : IsOpen (c.target ∩ c.symm ⁻¹' e.source) :=
    c.isOpen_inter_preimage_symm e.open_source
  have hmem : c x ∈ c.target ∩ c.symm ⁻¹' e.source :=
    ⟨c.map_source hcx, by rw [mem_preimage, c.left_inv hcx]; exact hxsrc⟩
  refine hcomp.congr (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hmem) fun z hz ↦ ?_)
  simp only [Function.comp_apply, hψ (c.symm z) hz.2]

/-! ## Fact 1: branch existence away from the pole -/

/-- Away from the pole, `G` is harmonic, so it has a local holomorphic conjugate
`F` (`Re F = G`); then `ψ = exp(−F)` is a branch (`‖ψ‖ = exp(−Re F) = exp(−G)`). -/
theorem exists_branch_away [T2Space X] {U : Set X} {x₀ : X} {G : X → ℝ}
    (hUo : IsOpen U) (hG : IsGreenFunction U x₀ G) {y : X} (hy : y ∈ U \ {x₀}) :
    ∃ V ψ, IsOpen V ∧ IsPreconnected V ∧ y ∈ V ∧ V ⊆ U \ {x₀} ∧
      IsModulusBranch G x₀ ψ V := by
  have hso : IsOpen (U \ {x₀}) := hUo.sdiff isClosed_singleton
  obtain ⟨V, F, hVo, hVc, hyV, hVs, hFconj⟩ :=
    exists_conjugate hG.harmonicOn hso hy
  refine ⟨V, fun x ↦ Complex.exp (-(F x)), hVo, hVc, hyV, hVs,
    HolomorphicOn.cexp_neg hFconj.1, ?_⟩
  intro x hx
  have hxV : x ∈ V := hx.1
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.neg_re, hFconj.2 x hxV]

/-! ## Fact 2: branch existence at the pole -/

/-- At the pole, using the log-pole chart `e` (`e x₀ = 0`,
`G(e.symm z) = −log‖z‖ + H z`), take a conjugate `W` of `H` (`Re W = H`) and set
`ψ = ξ·exp(−W)` in the chart: then `‖ψ‖ = ‖ξ‖·exp(−H) = exp(−G)` and `ψ x₀ = 0`. -/
theorem exists_branch_pole {U : Set X} {x₀ : X} {G : X → ℝ}
    (hG : IsGreenFunction U x₀ G) :
    ∃ V ψ, IsOpen V ∧ IsPreconnected V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      IsModulusBranch G x₀ ψ V ∧ ψ x₀ = 0 ∧
      ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
        deriv (ψ ∘ e.symm) 0 ≠ 0 := by
  obtain ⟨e, he, hx₀e, hex₀, r, hr, htgt, hDU, H, hHharm, hHpole⟩ := hG.log_pole
  -- a holomorphic conjugate `W` of `H` on the ball
  obtain ⟨W, hWan, hWre⟩ := hHharm.exists_analyticOnNhd_ball_re_eq
  -- the branch, in the chart: `g z = z·exp(−W z)`
  set g : ℂ → ℂ := fun z ↦ z * Complex.exp (-(W z)) with hg_def
  set ψ : X → ℂ := fun x ↦ (e x) * Complex.exp (-(W (e x))) with hψ_def
  have hψe : ∀ x ∈ e.source, ψ x = g (e x) := fun x _ ↦ rfl
  set V : Set X := e.symm '' ball (0 : ℂ) r with hV_def
  have hball_tgt : ball (0 : ℂ) r ⊆ e.target := ball_subset_closedBall.trans htgt
  have hVo : IsOpen V :=
    e.symm.isOpen_image_of_subset_source isOpen_ball (by simpa using hball_tgt)
  have hVc : IsPreconnected V :=
    (isPreconnected_ball.image _ (e.symm.continuousOn.mono (by simpa using hball_tgt)))
  have hx₀0 : e.symm 0 = x₀ := by rw [← hex₀, e.left_inv hx₀e]
  have hx₀V : x₀ ∈ V := ⟨0, mem_ball_self hr, hx₀0⟩
  have hVU : V ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hDU ⟨z, ball_subset_closedBall hz, rfl⟩
  -- `g` is analytic on the ball
  have hgan : AnalyticOnNhd ℂ g (ball (0 : ℂ) r) := by
    intro z hz
    exact analyticAt_id.mul ((hWan z hz).neg.cexp')
  have hψholo : HolomorphicOn ψ V := holomorphicOn_comp_chart he hball_tgt hgan hψe
  -- the modulus identity
  have hmod : ∀ x ∈ V \ {x₀}, ‖ψ x‖ = Real.exp (-G x) := by
    rintro x ⟨⟨z, hz, rfl⟩, hxne⟩
    have hzt : z ∈ e.target := hball_tgt hz
    have hez : e (e.symm z) = z := e.right_inv hzt
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hxne (by rw [mem_singleton_iff, hx₀0])
    have hzball : z ∈ ball (0 : ℂ) r \ {0} := ⟨hz, hz0⟩
    have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    -- value of `ψ` at `e.symm z`
    have hψval : ψ (e.symm z) = z * Complex.exp (-(W z)) := by
      simp only [hψ_def, hez]
    have hWzre : (W z).re = H z := hWre hz
    rw [hψval, norm_mul, Complex.norm_exp, Complex.neg_re, hWzre]
    -- `G (e.symm z) = −log‖z‖ + H z`
    rw [hHpole z hzball]
    rw [neg_add, neg_neg, Real.exp_add, Real.exp_log hznorm]
  -- value at the pole
  have hψx₀ : ψ x₀ = 0 := by simp only [hψ_def, hex₀, zero_mul]
  -- nonzero chart derivative at `0`: `d/dz [z·exp(−W z)]|₀ = exp(−W 0) ≠ 0`
  have hderiv : deriv (ψ ∘ e.symm) 0 ≠ 0 := by
    have hWderiv : HasDerivAt W (deriv W 0) 0 :=
      (hWan 0 (mem_ball_self hr)).differentiableAt.hasDerivAt
    have hv : HasDerivAt (fun z ↦ Complex.exp (-(W z)))
        (Complex.exp (-(W 0)) * -(deriv W 0)) 0 := by
      have := (hWderiv.neg).cexp
      simpa using this
    have hprod : HasDerivAt g
        (1 * Complex.exp (-(W 0)) + id (0 : ℂ) * (Complex.exp (-(W 0)) * -(deriv W 0))) 0 :=
      (hasDerivAt_id 0).mul hv
    have hcongr : (ψ ∘ e.symm) =ᶠ[𝓝 (0 : ℂ)] g := by
      have hmem : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds (mem_ball_self hr)
      filter_upwards [hmem] with z hz
      simp only [Function.comp_apply, hψ_def, hg_def, e.right_inv (hball_tgt hz)]
    have hgderiv : deriv g 0 = Complex.exp (-(W 0)) := by
      rw [hprod.deriv, id_eq]; ring
    rw [hcongr.deriv_eq, hgderiv]
    exact Complex.exp_ne_zero _
  exact ⟨V, ψ, hVo, hVc, hx₀V, hVU, ⟨hψholo, hmod⟩, hψx₀, e, he, hx₀e, hex₀, hderiv⟩

/-! ## Fact 3: rigidity of branches -/

/-- Two analytic functions on a ball with equal modulus, the second nonvanishing,
differ by a unimodular constant (maximum modulus principle applied to their
ratio). -/
theorem exists_unimodular_const_of_norm_eq {a b : ℂ → ℂ} {w₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : AnalyticOnNhd ℂ a (ball w₀ ρ)) (hb : AnalyticOnNhd ℂ b (ball w₀ ρ))
    (hbne : ∀ w ∈ ball w₀ ρ, b w ≠ 0) (hnorm : ∀ w ∈ ball w₀ ρ, ‖a w‖ = ‖b w‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ w ∈ ball w₀ ρ, a w = c * b w := by
  set q : ℂ → ℂ := fun w ↦ a w / b w with hq_def
  have hqan : AnalyticOnNhd ℂ q (ball w₀ ρ) := ha.div hb hbne
  have hcenter : w₀ ∈ ball w₀ ρ := mem_ball_self hρ
  have hqnorm : ∀ w ∈ ball w₀ ρ, ‖q w‖ = 1 := by
    intro w hw
    rw [hq_def, norm_div, hnorm w hw, div_self (norm_ne_zero_iff.mpr (hbne w hw))]
  have hmax : IsMaxOn (norm ∘ q) (ball w₀ ρ) w₀ := by
    refine isMaxOn_iff.mpr (fun w hw ↦ ?_)
    simp only [Function.comp_apply]
    rw [hqnorm w hw, hqnorm w₀ hcenter]
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    isPreconnected_ball isOpen_ball hqan.differentiableOn hcenter hmax
  refine ⟨q w₀, hqnorm w₀ hcenter, fun w hw ↦ ?_⟩
  have h1 : a w / b w = q w₀ := heq hw
  exact (div_eq_iff (hbne w hw)).mp h1

/-- **Rigidity of branches**: two modulus-`e^{−G}` branches on a preconnected
open `V` agree up to a unimodular constant. (Their ratio, near a point away
from the pole, is holomorphic of modulus `1`, hence a unimodular constant; the
identity theorem propagates the relation over `V`.) -/
theorem IsModulusBranch.exists_unimodular [T2Space X] {G : X → ℝ} {x₀ : X}
    {ψ₁ ψ₂ : X → ℂ} {V : Set X} (hVo : IsOpen V) (hVc : IsPreconnected V)
    (h₁ : IsModulusBranch G x₀ ψ₁ V) (h₂ : IsModulusBranch G x₀ ψ₂ V)
    {y₀ : X} (hy₀V : y₀ ∈ V) (hy₀ : y₀ ≠ x₀) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn ψ₁ (fun x ↦ c * ψ₂ x) V := by
  set c := chartAt ℂ y₀ with hc_def
  have hce : c ∈ riemannAtlas X := chartAt_mem_riemannAtlas y₀
  have hy₀src : y₀ ∈ c.source := mem_chart_source ℂ y₀
  -- the punctured domain, open by `T2`
  have hVpo : IsOpen (V \ {x₀}) := hVo.sdiff isClosed_singleton
  have hy₀Vp : y₀ ∈ V \ {x₀} := ⟨hy₀V, hy₀⟩
  have hmem : c y₀ ∈ chartImage c (V \ {x₀}) := mem_chartImage_of_mem hy₀Vp hy₀src
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_chartImage c hVpo) _ hmem
  -- points of the ball map back into `V \ {x₀}` and into the chart source
  have hsymm_mem : ∀ w ∈ ball (c y₀) ρ, c.symm w ∈ V \ {x₀} := fun w hw ↦
    mapsTo_symm_chartImage (hball hw)
  have hwt : ∀ w ∈ ball (c y₀) ρ, w ∈ c.target := fun w hw ↦
    chartImage_subset_target c _ (hball hw)
  have hsymm_src : ∀ w ∈ ball (c y₀) ρ, c.symm w ∈ c.source := fun w hw ↦
    c.map_target (hwt w hw)
  -- chart representatives
  set a : ℂ → ℂ := ψ₁ ∘ c.symm with ha_def
  set b : ℂ → ℂ := ψ₂ ∘ c.symm with hb_def
  have haan : AnalyticOnNhd ℂ a (ball (c y₀) ρ) := by
    intro w hw
    have h := h₁.1.analyticAt_comp_symm hce ⟨(hsymm_mem w hw).1, hsymm_src w hw⟩
    rwa [c.right_inv (hwt w hw)] at h
  have hban : AnalyticOnNhd ℂ b (ball (c y₀) ρ) := by
    intro w hw
    have h := h₂.1.analyticAt_comp_symm hce ⟨(hsymm_mem w hw).1, hsymm_src w hw⟩
    rwa [c.right_inv (hwt w hw)] at h
  have hbne : ∀ w ∈ ball (c y₀) ρ, b w ≠ 0 := by
    intro w hw
    have : ‖b w‖ = Real.exp (-G (c.symm w)) := h₂.2 _ (hsymm_mem w hw)
    rw [← norm_ne_zero_iff, this]
    exact (Real.exp_pos _).ne'
  have hnorm : ∀ w ∈ ball (c y₀) ρ, ‖a w‖ = ‖b w‖ := by
    intro w hw
    simp only [ha_def, hb_def, Function.comp_apply]
    rw [h₁.2 _ (hsymm_mem w hw), h₂.2 _ (hsymm_mem w hw)]
  obtain ⟨cst, hcst_norm, hcst⟩ :=
    exists_unimodular_const_of_norm_eq hρ haan hban hbne hnorm
  refine ⟨cst, hcst_norm, ?_⟩
  -- eventual equality near `y₀`, then identity theorem
  have hev : ψ₁ =ᶠ[𝓝 y₀] fun x ↦ cst * ψ₂ x := by
    have hmemnhds : c.source ∩ c ⁻¹' ball (c y₀) ρ ∈ 𝓝 y₀ :=
      (c.continuousOn.isOpen_inter_preimage c.open_source isOpen_ball).mem_nhds
        ⟨hy₀src, mem_ball_self hρ⟩
    filter_upwards [hmemnhds] with z hz
    have hcz : c z ∈ ball (c y₀) ρ := hz.2
    have h := hcst (c z) hcz
    simp only [ha_def, hb_def, Function.comp_apply, c.left_inv hz.1] at h
    exact h
  exact HolomorphicOn.eqOn_of_eventuallyEq h₁.1 (HolomorphicOn.const_mul h₂.1 cst)
    hVo hVc hy₀V hev

end Uniformization
