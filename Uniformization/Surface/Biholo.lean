/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Injective
import Uniformization.Surface.Phi
import Uniformization.Surface.Regularity
import Uniformization.RMT.RiemannMapping

/-!
# Biholomorphism of a simply connected regular piece onto the unit ball

Anghel–Stan Theorem 10 + 11 packaged: a simply connected regular piece `V`
(from `exists_simply_connected_piece`) with `x₀ ∈ V` carries a holomorphic
bijection onto `ball 0 1` sending `x₀` to `0`.

Route: `exists_green_function` (M1) → `exists_phi_of_green` (M2a) gives
holomorphic `φ` with `‖φ‖ = e^{−G} < 1`, simple zero at `x₀`; `phi_injOn`
(M2b) gives injectivity; `φ` is an open embedding onto `φ '' V ⊆ ball 0 1`
(nonvanishing derivative from injectivity, as in `Packaging.lean`);
`IsSimplyConnected (φ '' V)` transfers along the homeomorphism-onto-image;
`φ '' V ≠ univ` (bounded); the ported RMT
`Complex.exists_bijOn_unitBall_map_eq_zero` upgrades to a bijection onto the
ball; compose.
-/

open Set Metric Topology Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Every simply connected regular piece is biholomorphic to the unit ball**
(Anghel–Stan Theorems 10 and 11). -/
theorem exists_biholo_ball [T2Space X]
    {V : Set X} (hVo : IsOpen V) (hVconn : IsConnected V)
    (hVcl : IsCompact (closure V)) (hVsc : IsSimplyConnected V)
    (hfr : (frontier V).Nonempty)
    (hreg : ∀ ξ ∈ frontier V, ExteriorDiskAt V ξ)
    {x₀ : X} (hx₀ : x₀ ∈ V) :
    ∃ φ : X → ℂ, HolomorphicOn φ V ∧ BijOn φ V (ball (0 : ℂ) 1) ∧ φ x₀ = 0 := by
  -- Step 1: the Green's function `G`.
  obtain ⟨G, hG⟩ :=
    exists_green_function hVo hVcl hVconn.isPreconnected hfr hreg hx₀
  -- Step 2: the modulus map `φ₀` with `‖φ₀‖ = e^{−G}`, simple zero at `x₀`.
  obtain ⟨φ₀, hφ₀holo, hφ₀0, hφ₀mod, -⟩ := exists_phi_of_green hVo hVsc hx₀ hG
  -- Step 3: injectivity of `φ₀`.
  have hinj : Set.InjOn φ₀ V :=
    phi_injOn hVo hVconn.isPreconnected hVcl hx₀ hG hφ₀holo hφ₀0 hφ₀mod
  -- `‖φ₀‖ < 1` on `V`.
  have hnormlt : ∀ x ∈ V, ‖φ₀ x‖ < 1 := by
    intro x hx
    by_cases hxx₀ : x = x₀
    · rw [hxx₀, hφ₀0, norm_zero]; exact one_pos
    · rw [hφ₀mod x ⟨hx, hxx₀⟩]
      have hpos : 0 < G x := hG.pos x ⟨hx, hxx₀⟩
      calc Real.exp (-G x) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
  -- Step 4a: `φ₀` is an open map on `V` (injective + analytic ⇒ locally non-constant
  -- ⇒ the open mapping theorem in charts gives `𝓝 (φ₀ x) ≤ map φ₀ (𝓝 x)`).
  have hle : ∀ x ∈ V, 𝓝 (φ₀ x) ≤ Filter.map φ₀ (𝓝 x) := by
    intro x hx
    set e := chartAt ℂ x with he_def
    have hxe : x ∈ e.source := mem_chart_source ℂ x
    set g : ℂ → ℂ := φ₀ ∘ e.symm with hg_def
    have hgan : AnalyticAt ℂ g (e x) := hφ₀holo x hx
    have hgex : g (e x) = φ₀ x := by
      simp only [hg_def, Function.comp_apply, e.left_inv hxe]
    have hsnhd : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e x) := by
      refine (e.symm.continuousOn.isOpen_inter_preimage e.open_target hVo).mem_nhds ?_
      exact ⟨e.map_source hxe, by show e.symm (e x) ∈ V; rw [e.left_inv hxe]; exact hx⟩
    have hginj : Set.InjOn g (e.target ∩ e.symm ⁻¹' V) := by
      intro a ha b hb hab
      simp only [hg_def, Function.comp_apply] at hab
      have hsymm : e.symm a = e.symm b := hinj ha.2 hb.2 hab
      calc a = e (e.symm a) := (e.right_inv ha.1).symm
        _ = e (e.symm b) := by rw [hsymm]
        _ = b := e.right_inv hb.1
    have hncst : ¬ ∀ᶠ z in 𝓝 (e x), g z = g (e x) := by
      intro hev
      have ht : (e.target ∩ e.symm ⁻¹' V) ∩ {z | g z = g (e x)} ∈ 𝓝 (e x) :=
        inter_mem hsnhd hev
      have hnb : (𝓝[≠] (e x)).NeBot := inferInstance
      obtain ⟨z, ⟨hzs, hzg⟩, hzne⟩ :=
        hnb.nonempty_of_mem (inter_mem (mem_nhdsWithin_of_mem_nhds ht) self_mem_nhdsWithin)
      exact hzne (hginj hzs (mem_of_mem_nhds hsnhd) hzg)
    have hmap : Filter.map φ₀ (𝓝 x) = Filter.map g (𝓝 (e x)) := by
      have h1 : Filter.map e.symm (𝓝 (e x)) = 𝓝 x := by
        rw [e.symm.map_nhds_eq (by rw [OpenPartialHomeomorph.symm_source]; exact e.map_source hxe),
          e.left_inv hxe]
      calc Filter.map φ₀ (𝓝 x)
          = Filter.map φ₀ (Filter.map e.symm (𝓝 (e x))) := by rw [h1]
        _ = Filter.map g (𝓝 (e x)) := by rw [Filter.map_map]
    rw [hmap, ← hgex]
    exact (hgan.eventually_constant_or_nhds_le_map_nhds).resolve_left hncst
  -- open images of open subsets of `V`.
  have hopenW : ∀ {W : Set X}, IsOpen W → W ⊆ V → IsOpen (φ₀ '' W) := by
    intro W hWopen hWV
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hxW, rfl⟩
    refine hle x (hWV hxW) ?_
    rw [Filter.mem_map]
    exact Filter.mem_of_superset (hWopen.mem_nhds hxW) (fun z hz ↦ ⟨z, hz, rfl⟩)
  have hU₀open : IsOpen (φ₀ '' V) := hopenW hVo subset_rfl
  -- Step 4b: `φ₀ '' V ⊆ ball 0 1` and is not all of `ℂ`; contains `0`.
  have hsub : φ₀ '' V ⊆ ball (0 : ℂ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hnormlt x hx
  have hzeroU₀ : (0 : ℂ) ∈ φ₀ '' V := ⟨x₀, hx₀, hφ₀0⟩
  have hU₀ne : φ₀ '' V ≠ univ := by
    rw [Set.ne_univ_iff_exists_notMem]
    refine ⟨2, fun hmem ↦ ?_⟩
    have h2 : (2 : ℂ) ∈ ball (0 : ℂ) 1 := hsub hmem
    rw [Metric.mem_ball, dist_zero_right, RCLike.norm_two] at h2
    norm_num at h2
  -- Step 5: `IsSimplyConnected (φ₀ '' V)` via the homeomorphism `↥V ≃ₜ ↥(φ₀ '' V)`.
  have hcont_g : Continuous (V.restrict φ₀) := hφ₀holo.continuousOn.restrict
  have hg_open : IsOpenMap (V.restrict φ₀) := by
    intro W hW
    have hsubW : Subtype.val '' W ⊆ V := by rintro _ ⟨a, -, rfl⟩; exact a.2
    have hopenSub : IsOpen (Subtype.val '' W) := hVo.isOpenMap_subtype_val _ hW
    have heq : V.restrict φ₀ '' W = φ₀ '' (Subtype.val '' W) := Set.image_comp φ₀ Subtype.val W
    rw [heq]; exact hopenW hopenSub hsubW
  let p : ↥V → ↥(φ₀ '' V) := fun x ↦ ⟨φ₀ x.1, mem_image_of_mem φ₀ x.2⟩
  have hp_cont : Continuous p := hcont_g.subtype_mk (fun x ↦ mem_image_of_mem φ₀ x.2)
  have hp_inj : Function.Injective p := by
    intro a b hab
    exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
  have hp_surj : Function.Surjective p := by
    rintro ⟨w, x, hxV, rfl⟩; exact ⟨⟨x, hxV⟩, rfl⟩
  have hp_open : IsOpenMap p := by
    rw [(hU₀open.isOpenEmbedding_subtypeVal).isOpenMap_iff]; exact hg_open
  have hom : ↥V ≃ₜ ↥(φ₀ '' V) :=
    IsHomeomorph.homeomorph p ⟨hp_cont, hp_open, hp_inj, hp_surj⟩
  haveI hSCV : SimplyConnectedSpace ↥V := hVsc
  have hU₀sc : IsSimplyConnected (φ₀ '' V) :=
    (hom.symm.toHomotopyEquiv).simplyConnectedSpace
  -- Step 7: the ported Riemann mapping theorem.
  obtain ⟨gR, hgRdiff, hgRbij, hgR0⟩ :=
    Complex.exists_bijOn_unitBall_map_eq_zero hU₀open hU₀sc hU₀ne hzeroU₀
  -- Step 8: `φ := gR ∘ φ₀`.
  refine ⟨fun x ↦ gR (φ₀ x), ?_, ?_, ?_⟩
  · -- holomorphy
    intro x hx
    have hf : AnalyticAt ℂ (φ₀ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hφ₀holo x hx
    have hgR_an : AnalyticAt ℂ gR ((φ₀ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) := by
      have hval : (φ₀ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = φ₀ x := by
        simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      rw [hval]
      exact hgRdiff.analyticAt (hU₀open.mem_nhds (mem_image_of_mem φ₀ hx))
    exact hgR_an.comp hf
  · -- bijection
    have h1 : BijOn φ₀ V (φ₀ '' V) := hinj.bijOn_image
    exact hgRbij.comp h1
  · -- value at the pole
    show gR (φ₀ x₀) = 0
    rw [hφ₀0]; exact hgR0

end Uniformization
