/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Phi
import Uniformization.RMT.HomTrivial

/-!
# The map `φ = exp(−G−iF)` via the general lifting criterion (monodromy form)

`Uniformization/Surface/Phi.lean` produces the global holomorphic `φ` with `‖φ‖ = e^{−G}`
on a piece `U` under the hypothesis `IsSimplyConnected U`, by taking a global section of the
modulus covering `ModEtale.proj` (an `IsCoveringMapOn` over `U`, proven in `PhiEtale.lean`).
Simple connectivity is used there in exactly one place: the section-existence step
`IsCoveringMapOn.existsUnique_continuousMap_lifts`.

This file **refactors** that step through the *general lifting criterion*
(`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`, Hatcher Prop 1.33), isolating the
precise hypothesis it consumes as a named `Prop`:

* `ModulusMonodromyTrivial G x₀ U` — *the modulus covering has trivial monodromy over `U`*:
  every loop in `↥U` lifts to a **closed** loop through `ModEtale.proj`, for every basepoint in the
  total space.  Formally: the covering-induced map on fundamental groups
  `π₁(proj⁻¹'U, e₀) → π₁(↥U, proj e₀)` is surjective for each `e₀`.

The main theorem `exists_phi_of_green_of_monodromyTrivial` proves `φ`-existence from this condition
(plus `IsConnected U`), and `exists_phi_of_green_isSimplyConnected` re-derives the original
simply-connected theorem from it (a simply connected `↥U` has trivial `π₁`, so any covering-induced
map into it is surjective).

## The open mathematical question (T3)

The intended downstream use is the uniformization hypothesis `H¹(X, ℝ) = 0`, formalized here as
`HomTrivialLoops U` (every additive `ℝ`-valued hom out of `π₁(U)` vanishes; see
`Uniformization/RMT/HomTrivial.lean`).  To weaken `IsSimplyConnected U` to `HomTrivialLoops U`
one must derive `ModulusMonodromyTrivial G x₀ U` from `HomTrivialLoops U + IsConnected U`.

This derivation is **not** carried out here, and is genuinely subtle.  The deck group of the modulus
covering is the discrete unit circle `UC ⊆ S¹` (`PhiEtale.ModEtale.UC`, branch rigidity), so the
monodromy of a loop `γ` is a unimodular constant `c(γ)`.  Away from the pole this constant is
`Circle.exp(−per γ)` where `per : π₁(U∖{x₀}) → ℝ` is the additive period of the conjugate branch
(the `Rado.ConjEtale` theory + the `CircleParam` shift machinery).  The period of the small loop
around `x₀` is `−2π`, so the monodromy over `U` (pole included) descends to a homomorphism
`p̄ : π₁(↥U) → ℝ/2πℤ`.

`HomTrivialLoops U` kills `ℝ`-valued homs, but `p̄` is `ℝ/2πℤ`-valued, and abstract group theory does
**not** force `p̄ = 0`: e.g. `π₁ = ℤ/2` has `Hom(ℤ/2, ℝ) = 0` yet `Hom(ℤ/2, ℝ/2πℤ) ≠ 0`.  Hubbard's
Theorem 1.1.2 asserts `H¹(X, ℝ) = 0` *is* sufficient, so the resolution must use more than the
abstract vanishing of `ℝ`-homs — presumably the actual construction of §1.5–1.7 (which we do not have
in text).  **This is flagged for the orchestrator to source Hubbard §1.5–1.7.**  The period-hom
bridge (`monodromy = Circle.exp(−period)`, T2) is partially set up below.
-/

open Set Metric Topology InnerProductSpace Filter

namespace FundamentalGroup

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- `mapOfEq f rfl` is the plain induced map `map f x`. -/
theorem mapOfEq_rfl (f : C(A, B)) (x : A) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  ext ζ
  obtain ⟨p, rfl⟩ := Quot.exists_rep ζ
  rw [show (Quot.mk _ p : FundamentalGroup A x) = fromPath (Path.Homotopic.Quotient.mk p) from rfl,
    mapOfEq_apply, map_apply]
  rfl

/-- If the covering-induced map `map f x` is surjective, then `mapOfEq f h` has full range. -/
theorem range_mapOfEq_eq_top {f : C(A, B)} {x : A} {y : B} (h : f x = y)
    (hsurj : Function.Surjective (FundamentalGroup.map f x)) :
    (FundamentalGroup.mapOfEq f h).range = ⊤ := by
  subst h
  rw [mapOfEq_rfl, MonoidHom.range_eq_top]
  exact hsurj

end FundamentalGroup

namespace Uniformization

open Rado ModEtale

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable (G : X → ℝ) (x₀ : X) (U : Set X) in
/-- **Trivial modulus monodromy over `U`.** Every loop in `↥U` lifts to a *closed* loop through the
modulus covering `ModEtale.proj`, whatever the chosen lift of the basepoint: for every basepoint
`e₀` in the total space `proj ⁻¹' U`, the covering-induced map on fundamental groups
`π₁(proj⁻¹'U, e₀) → π₁(↥U, proj e₀)` is surjective.

This is exactly the range hypothesis consumed by the general lifting criterion
(`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`) applied to the modulus covering; see
`exists_phi_of_green_of_monodromyTrivial`. -/
def ModulusMonodromyTrivial : Prop :=
  ∀ e₀ : ↥(proj (G := G) (x₀ := x₀) (U := U) ⁻¹' U),
    Function.Surjective (FundamentalGroup.map
      (⟨U.restrictPreimage (proj (G := G) (x₀ := x₀) (U := U)),
        continuous_proj.restrictPreimage⟩ : C(_, ↥U)) e₀)

/-- **Global holomorphic `φ` with `‖φ‖ = e^{−G}`** from trivial modulus monodromy (Sard-free).

This is the exact statement of `exists_phi_of_green` with `IsSimplyConnected U` replaced by the pair
`IsConnected U` + `ModulusMonodromyTrivial G x₀ U`.  The proof produces the section of the modulus
covering through the general lifting criterion instead of simple connectivity, then is identical to
`exists_phi_of_green`. -/
theorem exists_phi_of_green_of_monodromyTrivial [T2Space X] {U : Set X} {x₀ : X} {G : X → ℝ}
    (hUo : IsOpen U) (hx₀ : x₀ ∈ U) (hG : IsGreenFunction U x₀ G)
    (hUconn : IsConnected U) (hMono : ModulusMonodromyTrivial G x₀ U) :
    ∃ φ : X → ℂ, HolomorphicOn φ U ∧ φ x₀ = 0 ∧
      (∀ x ∈ U \ {x₀}, ‖φ x‖ = Real.exp (-G x)) ∧
      ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
        deriv (φ ∘ e.symm) 0 ≠ 0 := by
  classical
  -- the covering map `proj : ModEtale G x₀ U → X` over `U`, and its subtype restriction
  have hcov : IsCoveringMapOn (proj (G := G) (x₀ := x₀) (U := U)) U :=
    ModEtale.isCoveringMapOn_proj hUo hx₀ hG
  have hcovR : IsCoveringMap (U.restrictPreimage (proj (G := G) (x₀ := x₀) (U := U))) :=
    hcov.isCoveringMap_restrictPreimage
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
  haveI : ConnectedSpace ↥U := Subtype.connectedSpace hUconn
  haveI : PathConnectedSpace ↥U := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  -- basepoints for the criterion
  set a₀ : ↥U := ⟨x₀, hx₀⟩ with ha₀_def
  set eR₀ : ↥(proj (G := G) (x₀ := x₀) (U := U) ⁻¹' U) := ⟨e₀, hx₀⟩ with heR₀_def
  have he : U.restrictPreimage (proj (G := G) (x₀ := x₀) (U := U)) eR₀
      = (ContinuousMap.id ↥U) a₀ := rfl
  -- the range condition, from `ModulusMonodromyTrivial`
  have hsurj : Function.Surjective (FundamentalGroup.map
      (⟨U.restrictPreimage (proj (G := G) (x₀ := x₀) (U := U)), hcovR.continuous⟩ : C(_, ↥U)) eR₀) :=
    hMono eR₀
  have hrange : (FundamentalGroup.mapOfEq
      (⟨U.restrictPreimage (proj (G := G) (x₀ := x₀) (U := U)), hcovR.continuous⟩ : C(_, ↥U))
      he).range = ⊤ :=
    FundamentalGroup.range_mapOfEq_eq_top he hsurj
  have le : (FundamentalGroup.map (ContinuousMap.id ↥U) a₀).range ≤
      (FundamentalGroup.mapOfEq
        (⟨U.restrictPreimage (proj (G := G) (x₀ := x₀) (U := U)), hcovR.continuous⟩ : C(_, ↥U))
        he).range := by
    rw [hrange]; exact le_top
  -- the global section, from the general lifting criterion
  obtain ⟨FR, ⟨hFRa, hFRlift⟩, -⟩ :=
    hcovR.existsUnique_continuousMap_lifts_of_range_le he le
  set F : C(↥U, ModEtale G x₀ U) :=
    ⟨fun a ↦ (FR a : ModEtale G x₀ U), continuous_subtype_val.comp FR.continuous⟩ with hF_def
  have hFa₀ : F a₀ = e₀ := by
    show (FR a₀ : ModEtale G x₀ U) = e₀
    rw [hFRa]
  have hprojF : ∀ a : ↥U, proj (F a) = (a : X) := by
    intro a
    have h1 : U.restrictPreimage (proj (G := G) (x₀ := x₀) (U := U)) (FR a) = a :=
      congrFun hFRlift a
    exact congrArg Subtype.val h1
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

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- A simply connected piece has trivial modulus monodromy: `π₁(↥U)` is trivial, so any
covering-induced map into it is surjective. -/
theorem modulusMonodromyTrivial_of_isSimplyConnected {U : Set X} {x₀ : X} {G : X → ℝ}
    (hUsc : IsSimplyConnected U) : ModulusMonodromyTrivial G x₀ U := by
  haveI : SimplyConnectedSpace ↥U := hUsc
  intro e₀ ζ
  exact ⟨1, Subsingleton.elim _ _⟩

/-- **Re-derivation of `exists_phi_of_green`** (the original simply-connected statement) from the
monodromy form. -/
theorem exists_phi_of_green_isSimplyConnected [T2Space X] {U : Set X} {x₀ : X} {G : X → ℝ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hx₀ : x₀ ∈ U)
    (hG : IsGreenFunction U x₀ G) :
    ∃ φ : X → ℂ, HolomorphicOn φ U ∧ φ x₀ = 0 ∧
      (∀ x ∈ U \ {x₀}, ‖φ x‖ = Real.exp (-G x)) ∧
      ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
        deriv (φ ∘ e.symm) 0 ≠ 0 := by
  haveI : SimplyConnectedSpace ↥U := hUsc
  have hUconn : IsConnected U := isConnected_iff_connectedSpace.mpr inferInstance
  exact exists_phi_of_green_of_monodromyTrivial hUo hx₀ hG hUconn
    (modulusMonodromyTrivial_of_isSimplyConnected hUsc)

end Uniformization
