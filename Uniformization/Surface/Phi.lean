/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.PhiEtale

/-!
# The map `φ = exp (−G − iF)` via a covering-space section

Given a Green's function `G` for a simply connected piece `U`, we produce a
global holomorphic `φ : U → ℂ` with `‖φ‖ = exp (−G)` on `U \ {x₀}` and a
simple zero at `x₀`. This replaces Anghel–Stan's period-quantization argument
(their Thm 10, first half, which uses Sard + Stokes).

Design (see PLAN.md "Design decisions v2"): build the étale space of germs of
local holomorphic `ψ` with `‖ψ‖ = exp (−G)` away from `x₀`, on domains that
may include `x₀` (where such `ψ` must vanish; locally `ψ = ξ·e^{−(H+iH̃)}`
in the pole chart). Two branches over a connected open agree up to a unimodular
constant (their ratio is holomorphic with constant modulus `1`, hence locally
constant), so:
* fibers are discrete;
* over a small disk in `U \ {x₀}` the sheets are `{c·ψ₀ : c ∈ S¹}` — trivial
  `S¹`-torsor;
* over the pole chart every branch on the punctured disk extends across `x₀`
  (its ratio to the distinguished branch `ξ·e^{−(H+iH̃)}` is constant), so the
  covering is trivialized there too — the integer residue of the log pole, in
  multiplicative form.
Hence the projection is an `IsCoveringMap` over ALL of `U`; `U` simply
connected (+ locally path-connected) gives a global section through the
distinguished germ at `x₀`, and `φ := eval ∘ section`. Mirror the étale-space
implementation of `Rado/Surface/Germs.lean` (sheets, basic sets, `proj`,
`eval`) in multiplicative form, then use path/homotopy lifting
(`Mathlib/Topology/Homotopy/Lifting.lean`, `IsCoveringMap`) or the
monodromy-style argument to produce the section.
-/

open Set Metric Topology InnerProductSpace Filter

namespace Uniformization

open Rado ModEtale

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Global holomorphic `φ` with `‖φ‖ = e^{−G}`** on a simply connected piece
(Anghel–Stan Theorem 10, existence half — Sard-free). -/
theorem exists_phi_of_green [T2Space X] {U : Set X} {x₀ : X} {G : X → ℝ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hx₀ : x₀ ∈ U)
    (hG : IsGreenFunction U x₀ G) :
    ∃ φ : X → ℂ, HolomorphicOn φ U ∧ φ x₀ = 0 ∧
      (∀ x ∈ U \ {x₀}, ‖φ x‖ = Real.exp (-G x)) ∧
      ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
        deriv (φ ∘ e.symm) 0 ≠ 0 := by
  classical
  -- the covering map `proj : ModEtale G x₀ U → X` over `U`
  have hcov : IsCoveringMapOn (proj (G := G) (x₀ := x₀) (U := U)) U :=
    ModEtale.isCoveringMapOn_proj hUo hx₀ hG
  -- the pole branch and the distinguished germ `e₀` over `x₀`
  obtain ⟨V₀, ψpole, hV₀o, hV₀c, hx₀V₀, hV₀U, hpolebranch, hpole0, epole, hepole,
    hx₀epole, hepole0, hderivpole⟩ := exists_branch_pole hG
  set e₀ : ModEtale G x₀ U :=
    ⟨⟨x₀, (ψpole : Germ (𝓝 x₀) ℂ)⟩, hx₀, V₀, ψpole, hV₀o, hx₀V₀, hV₀U, hpolebranch, rfl⟩
    with he₀_def
  have he₀sheet : e₀ ∈ sheet V₀ ψpole := ⟨hx₀V₀, rfl⟩
  -- instances for the lifting theorem
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  haveI : LocallyPathConnectedSpace (↥U) := hUo.locallyPathConnectedSpace
  haveI : SimplyConnectedSpace (↥U) := hUsc
  -- the global section, from simple connectedness
  set incl : C(↥U, X) := ⟨Subtype.val, continuous_subtype_val⟩ with hincl_def
  obtain ⟨F, ⟨hFa₀, hFlift⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts incl (a₀ := ⟨x₀, hx₀⟩) (e₀ := e₀)
      (rfl) (fun a ↦ a.2)
  have hprojF : ∀ a : ↥U, proj (F a) = (a : X) := fun a ↦ congrFun hFlift a
  -- the map `φ`
  set φ : X → ℂ := fun x ↦ if hx : x ∈ U then eval (F ⟨x, hx⟩) else 0 with hφ_def
  -- near every point of `U`, `φ` coincides with a local branch
  have hlocal : ∀ y (hy : y ∈ U), ∃ V ψ, IsOpen V ∧ V ⊆ U ∧
      IsModulusBranch G x₀ ψ V ∧ y ∈ V ∧ φ =ᶠ[𝓝 y] ψ := by
    intro y hy
    obtain ⟨V, ψ, hVo, hVc, hVU, hψ, hqV⟩ := exists_basic_sheet_mem (F ⟨y, hy⟩)
    have hSopen : IsOpen (sheet V ψ : Set (ModEtale G x₀ U)) :=
      isOpen_of_mem_basicSets ⟨V, ψ, hVo, hVc, hVU, hψ, rfl⟩
    have hpre : IsOpen (F ⁻¹' (sheet V ψ)) := hSopen.preimage F.continuous
    have hWopen : IsOpen (Subtype.val '' (F ⁻¹' (sheet V ψ))) :=
      hUo.isOpenEmbedding_subtypeVal.isOpenMap _ hpre
    have hyW : y ∈ Subtype.val '' (F ⁻¹' (sheet V ψ)) := ⟨⟨y, hy⟩, hqV, rfl⟩
    have hyV : y ∈ V := by
      have hmemV : proj (F ⟨y, hy⟩) ∈ V := hqV.1
      rwa [hprojF ⟨y, hy⟩] at hmemV
    refine ⟨V, ψ, hVo, hVU, hψ, hyV, ?_⟩
    filter_upwards [hWopen.mem_nhds hyW] with x hx
    obtain ⟨a, ha_pre, rfl⟩ := hx
    have hxU : (↑a : X) ∈ U := a.2
    simp only [hφ_def, dif_pos hxU]
    rw [show (⟨(↑a : X), hxU⟩ : ↥U) = a from Subtype.ext rfl,
      eval_eq_of_mem_sheet ha_pre, hprojF a]
  refine ⟨φ, ?_, ?_, ?_, epole, hepole, hx₀epole, hepole0, ?_⟩
  · -- holomorphy on `U`
    intro y hy
    obtain ⟨V, ψ, hVo, hVU, hψ, hyV, hev⟩ := hlocal y hy
    have htend : Filter.Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) :=
      ((chartAt ℂ y).symm_map_nhds_eq (mem_chart_source ℂ y)).le
    exact (hψ.1 y hyV).congr ((hev.symm).comp_tendsto htend)
  · -- value at the pole
    show φ x₀ = 0
    simp only [hφ_def, dif_pos hx₀]
    rw [hFa₀, eval_eq_of_mem_sheet he₀sheet]
    exact hpole0
  · -- modulus on `U \ {x₀}`
    rintro x ⟨hxU, hxne⟩
    obtain ⟨V, ψ, hVo, hVU, hψ, hxV, hev⟩ := hlocal x hxU
    rw [hev.eq_of_nhds]
    exact hψ.2 x ⟨hxV, hxne⟩
  · -- nonzero chart derivative at the pole
    have hevpole : φ =ᶠ[𝓝 x₀] ψpole := by
      have hSopen : IsOpen (sheet V₀ ψpole : Set (ModEtale G x₀ U)) :=
        isOpen_of_mem_basicSets ⟨V₀, ψpole, hV₀o, hV₀c, hV₀U, hpolebranch, rfl⟩
      have hpre : IsOpen (F ⁻¹' (sheet V₀ ψpole)) := hSopen.preimage F.continuous
      have hypre : (⟨x₀, hx₀⟩ : ↥U) ∈ F ⁻¹' (sheet V₀ ψpole) := by
        rw [Set.mem_preimage, hFa₀]; exact he₀sheet
      have hWopen : IsOpen (Subtype.val '' (F ⁻¹' (sheet V₀ ψpole))) :=
        hUo.isOpenEmbedding_subtypeVal.isOpenMap _ hpre
      have hyW : x₀ ∈ Subtype.val '' (F ⁻¹' (sheet V₀ ψpole)) := ⟨⟨x₀, hx₀⟩, hypre, rfl⟩
      filter_upwards [hWopen.mem_nhds hyW] with x hx
      obtain ⟨a, ha_pre, rfl⟩ := hx
      have hxU : (↑a : X) ∈ U := a.2
      simp only [hφ_def, dif_pos hxU]
      rw [show (⟨(↑a : X), hxU⟩ : ↥U) = a from Subtype.ext rfl,
        eval_eq_of_mem_sheet ha_pre, hprojF a]
    have h0tgt : (0 : ℂ) ∈ epole.target := hepole0 ▸ epole.map_source hx₀epole
    have hsymm0 : epole.symm 0 = x₀ := by rw [← hepole0]; exact epole.left_inv hx₀epole
    have htend : Filter.Tendsto epole.symm (𝓝 (0 : ℂ)) (𝓝 x₀) := by
      rw [← hsymm0]; exact epole.continuousAt_symm h0tgt
    have hderiv_congr : (φ ∘ epole.symm) =ᶠ[𝓝 (0 : ℂ)] (ψpole ∘ epole.symm) :=
      hevpole.comp_tendsto htend
    rw [hderiv_congr.deriv_eq]
    exact hderivpole

end Uniformization
