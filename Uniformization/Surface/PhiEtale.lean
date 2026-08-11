/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.PhiCover
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting

/-!
# The multiplicative étale space of branches, and the covering map

The étale space `ModEtale G x₀ U` of germs of modulus-`e^{−G}` branches over a
simply connected piece `U`, mirroring `Rado/Surface/Germs.lean`'s `ConjEtale`
in multiplicative form.  Sheets over preconnected opens form a basis; the
projection `proj` is a continuous open map, and — using branch existence
(`PhiCover`) and branch rigidity — is a covering map over `U`.  A global section
(from simple connectedness) yields the map `φ` (in `Phi.lean`).
-/

open Set Metric Topology MeasureTheory InnerProductSpace Complex Filter Bundle

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Branch existence at every point of `U`: away from the pole from
`exists_branch_away`, at the pole from `exists_branch_pole`. -/
theorem exists_branch_mem [T2Space X] {U : Set X} {x₀ : X} {G : X → ℝ}
    (hUo : IsOpen U) (hG : IsGreenFunction U x₀ G) {y : X} (hy : y ∈ U) :
    ∃ V ψ, IsOpen V ∧ IsPreconnected V ∧ y ∈ V ∧ V ⊆ U ∧ IsModulusBranch G x₀ ψ V := by
  by_cases hyx₀ : y = x₀
  · subst hyx₀
    obtain ⟨V, ψ, hVo, hVc, hyV, hVU, hbranch, _, _⟩ := exists_branch_pole hG
    exact ⟨V, ψ, hVo, hVc, hyV, hVU, hbranch⟩
  · obtain ⟨V, ψ, hVo, hVc, hyV, hVU, hbranch⟩ :=
      exists_branch_away hUo hG ⟨hy, hyx₀⟩
    exact ⟨V, ψ, hVo, hVc, hyV, hVU.trans sdiff_subset, hbranch⟩

variable (G : X → ℝ) (x₀ : X) (U : Set X)

/-- The étale space of germs of modulus-`e^{−G}` branches of `U`: pairs of a
point `y ∈ U` and the germ at `y` of a branch defined on some open neighbourhood
inside `U`. -/
def ModEtale : Type _ :=
  {p : Σ y : X, Germ (𝓝 y) ℂ // p.1 ∈ U ∧
    ∃ V ψ, IsOpen V ∧ p.1 ∈ V ∧ V ⊆ U ∧ IsModulusBranch G x₀ ψ V ∧
      p.2 = (ψ : Germ (𝓝 p.1) ℂ)}

namespace ModEtale

variable {G x₀ U}

/-- The sheet of a branch `ψ` over `V`. -/
def sheet (V : Set X) (ψ : X → ℂ) : Set (ModEtale G x₀ U) :=
  {q | q.1.1 ∈ V ∧ q.1.2 = (ψ : Germ (𝓝 q.1.1) ℂ)}

variable (G x₀ U) in
/-- Basic open sets: sheets of branches over preconnected opens inside `U`. -/
def basicSets : Set (Set (ModEtale G x₀ U)) :=
  {S | ∃ V ψ, IsOpen V ∧ IsPreconnected V ∧ V ⊆ U ∧ IsModulusBranch G x₀ ψ V ∧ S = sheet V ψ}

instance : TopologicalSpace (ModEtale G x₀ U) :=
  TopologicalSpace.generateFrom (basicSets G x₀ U)

/-- The projection to the surface. -/
def proj (q : ModEtale G x₀ U) : X := q.1.1

/-- The evaluation map. -/
noncomputable def eval (q : ModEtale G x₀ U) : ℂ := Rado.germValue q.1.2

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem mem_sheet_iff {V : Set X} {ψ : X → ℂ} {q : ModEtale G x₀ U} :
    q ∈ sheet V ψ ↔ q.1.1 ∈ V ∧ q.1.2 = (ψ : Germ (𝓝 q.1.1) ℂ) := Iff.rfl

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem isOpen_of_mem_basicSets {S : Set (ModEtale G x₀ U)} (hS : S ∈ basicSets G x₀ U) :
    IsOpen S :=
  TopologicalSpace.isOpen_generateFrom_of_mem hS

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The sheets form a topological basis. -/
theorem isTopologicalBasis_basicSets :
    TopologicalSpace.IsTopologicalBasis (basicSets G x₀ U) := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  refine ⟨?_, ?_, rfl⟩
  · rintro S₁ ⟨V₁, ψ₁, hV₁o, _, hV₁U, hψ₁, rfl⟩ S₂ ⟨V₂, ψ₂, hV₂o, _, hV₂U, hψ₂, rfl⟩
      q ⟨⟨hy₁, hg₁⟩, ⟨hy₂, hg₂⟩⟩
    have hev : ψ₁ =ᶠ[𝓝 q.1.1] ψ₂ := Filter.Germ.coe_eq.mp (hg₁.symm.trans hg₂)
    have hOopen : IsOpen {x : X | ψ₁ =ᶠ[𝓝 x] ψ₂} := Rado.isOpen_eventuallyEq_nhds
    set W := connectedComponentIn (V₁ ∩ V₂ ∩ {x : X | ψ₁ =ᶠ[𝓝 x] ψ₂}) q.1.1 with hW
    have hWsub : W ⊆ V₁ ∩ V₂ ∩ {x : X | ψ₁ =ᶠ[𝓝 x] ψ₂} := connectedComponentIn_subset _ _
    have hWo : IsOpen W := ((hV₁o.inter hV₂o).inter hOopen).connectedComponentIn
    have hqW : q.1.1 ∈ W := mem_connectedComponentIn ⟨⟨hy₁, hy₂⟩, hev⟩
    refine ⟨sheet W ψ₁, ⟨W, ψ₁, hWo, isPreconnected_connectedComponentIn,
      fun z hz ↦ hV₁U (hWsub hz).1.1, hψ₁.mono fun z hz ↦ (hWsub hz).1.1, rfl⟩,
      ⟨hqW, hg₁⟩, ?_⟩
    rintro p ⟨hpW, hpF⟩
    have hp12 := hWsub hpW
    refine ⟨⟨hp12.1.1, hpF⟩, hp12.1.2, ?_⟩
    rw [hpF]
    exact Filter.Germ.coe_eq.mpr hp12.2
  · rw [sUnion_eq_univ_iff]
    intro q
    obtain ⟨hqU, V, ψ, hVo, hqV, hVU, hψ, hgerm⟩ := q.2
    set W := connectedComponentIn V q.1.1 with hW
    have hWsub : W ⊆ V := connectedComponentIn_subset _ _
    exact ⟨sheet W ψ, ⟨W, ψ, hVo.connectedComponentIn, isPreconnected_connectedComponentIn,
      hWsub.trans hVU, hψ.mono hWsub, rfl⟩, mem_connectedComponentIn hqV, hgerm⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem continuous_proj : Continuous (proj (G := G) (x₀ := x₀) (U := U)) := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  rw [continuous_def]
  intro O hO
  rw [(isTopologicalBasis_basicSets (G := G) (x₀ := x₀) (U := U)).isOpen_iff]
  intro q hq
  obtain ⟨hqU, V, ψ, hVo, hqV, hVU, hψ, hgerm⟩ := q.2
  have hsub : connectedComponentIn (V ∩ O) q.1.1 ⊆ V ∩ O := connectedComponentIn_subset _ _
  refine ⟨sheet (connectedComponentIn (V ∩ O) q.1.1) ψ,
    ⟨_, ψ, (hVo.inter hO).connectedComponentIn, isPreconnected_connectedComponentIn,
      fun z hz ↦ hVU (hsub hz).1, hψ.mono fun z hz ↦ (hsub hz).1, rfl⟩,
    ⟨mem_connectedComponentIn ⟨hqV, hq⟩, hgerm⟩, ?_⟩
  rintro p ⟨hpW, _⟩
  exact (hsub hpW).2

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem isOpenMap_proj : IsOpenMap (proj (G := G) (x₀ := x₀) (U := U)) := by
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨q, hqO, rfl⟩
  obtain ⟨S, hSb, hqS, hSO⟩ :=
    (isTopologicalBasis_basicSets (G := G) (x₀ := x₀) (U := U)).isOpen_iff.mp hO q hqO
  obtain ⟨V, ψ, hVo, hVc, hVU, hψ, rfl⟩ := hSb
  have himg : V ⊆ proj (G := G) (x₀ := x₀) (U := U) '' O := fun z hz ↦
    ⟨⟨⟨z, (ψ : Germ (𝓝 z) ℂ)⟩, hVU hz, V, ψ, hVo, hz, hVU, hψ, rfl⟩, hSO ⟨hz, rfl⟩, rfl⟩
  exact Filter.mem_of_superset (hVo.mem_nhds hqS.1) himg

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `proj` restricted to a sheet is injective (germs of a single `ψ`). -/
theorem injOn_proj_sheet {V : Set X} {ψ : X → ℂ} :
    InjOn (proj (G := G) (x₀ := x₀) (U := U)) (sheet V ψ) := by
  rintro ⟨⟨y, γ⟩, hq⟩ hmem ⟨⟨y', γ'⟩, hq'⟩ hmem' h
  have hyy : y = y' := h
  subst hyy
  obtain ⟨-, hγ⟩ := hmem
  obtain ⟨-, hγ'⟩ := hmem'
  simp only at hγ hγ'
  subst hγ
  subst hγ'
  rfl

/-- Every point of `U` has a branch germ over it. -/
theorem exists_mk [T2Space X] (hUo : IsOpen U) (hG : IsGreenFunction U x₀ G)
    {y : X} (hy : y ∈ U) : ∃ q : ModEtale G x₀ U, proj q = y := by
  obtain ⟨V, ψ, hVo, hVc, hyV, hVU, hψ⟩ := exists_branch_mem hUo hG hy
  exact ⟨⟨⟨y, (ψ : Germ (𝓝 y) ℂ)⟩, hy, V, ψ, hVo, hyV, hVU, hψ, rfl⟩, rfl⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Every étale point lies on a basic sheet. -/
theorem exists_basic_sheet_mem (q : ModEtale G x₀ U) :
    ∃ V ψ, IsOpen V ∧ IsPreconnected V ∧ V ⊆ U ∧ IsModulusBranch G x₀ ψ V ∧ q ∈ sheet V ψ := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  obtain ⟨hqU, V, ψ, hVo, hqV, hVU, hψ, hgerm⟩ := q.2
  exact ⟨connectedComponentIn V q.1.1, ψ, hVo.connectedComponentIn,
    isPreconnected_connectedComponentIn, (connectedComponentIn_subset _ _).trans hVU,
    hψ.mono (connectedComponentIn_subset _ _), mem_connectedComponentIn hqV, hgerm⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem continuous_eval : Continuous (eval (G := G) (x₀ := x₀) (U := U)) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨V, ψ, hVo, hVc, hVU, hψ, hqV⟩ := exists_basic_sheet_mem q
  have hopen : IsOpen (sheet V ψ : Set (ModEtale G x₀ U)) :=
    isOpen_of_mem_basicSets ⟨V, ψ, hVo, hVc, hVU, hψ, rfl⟩
  have hproj : ContinuousAt (proj (G := G) (x₀ := x₀) (U := U)) q := continuous_proj.continuousAt
  have hFc : ContinuousAt ψ (proj (G := G) (x₀ := x₀) (U := U) q) :=
    hψ.1.continuousOn.continuousAt (hVo.mem_nhds hqV.1)
  have h1 : ContinuousAt (ψ ∘ proj (G := G) (x₀ := x₀) (U := U)) q := hFc.comp hproj
  refine h1.congr ?_
  filter_upwards [hopen.mem_nhds hqV] with p hp
  simp only [Function.comp_apply, eval, hp.2, Rado.germValue_coe]
  rfl

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- On a sheet of `ψ`, `eval` evaluates `ψ` at the base point. -/
theorem eval_eq_of_mem_sheet {V : Set X} {ψ : X → ℂ} {q : ModEtale G x₀ U}
    (hq : q ∈ sheet V ψ) : eval q = ψ (proj q) := by
  simp only [eval, proj, hq.2, Rado.germValue_coe]

end ModEtale

/-! ## The covering map -/

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- A unimodular multiple of a branch is a branch. -/
theorem isModulusBranch_const_mul {G : X → ℝ} {x₀ : X} {ψ : X → ℂ} {V : Set X}
    (hψ : IsModulusBranch G x₀ ψ V) {c : ℂ} (hc : ‖c‖ = 1) :
    IsModulusBranch G x₀ (fun z ↦ c * ψ z) V := by
  refine ⟨HolomorphicOn.const_mul hψ.1 c, fun x hx ↦ ?_⟩
  rw [norm_mul, hc, one_mul, hψ.2 x hx]

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- A nonempty open set contains a point different from `x₀` (no isolated
points on a surface). -/
theorem exists_mem_ne_pole {x₀ : X} {N : Set X} (hN : IsOpen N) {w : X} (hw : w ∈ N) :
    ∃ w' ∈ N, w' ≠ x₀ := by
  set c := chartAt ℂ w with hc_def
  have hcw : w ∈ c.source := mem_chart_source ℂ w
  have himg : IsOpen (c '' (N ∩ c.source)) :=
    c.isOpen_image_of_subset_source (hN.inter c.open_source) inter_subset_right
  have hmem : c w ∈ c '' (N ∩ c.source) := ⟨w, ⟨hw, hcw⟩, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg _ hmem
  set p : ℂ := c w + ((ε / 2 : ℝ) : ℂ) with hp_def
  have hpne : p ≠ c w := by
    rw [hp_def]; intro h
    have h0 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination h
    rw [Complex.ofReal_eq_zero] at h0; linarith
  have hpball : p ∈ ball (c w) ε := by
    rw [mem_ball, dist_eq_norm, hp_def, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith
  obtain ⟨w', hw'mem, hw'eq⟩ := hball hpball
  have hww' : w' ≠ w := by
    intro h; rw [h] at hw'eq; exact hpne hw'eq.symm
  by_cases hwx : w = x₀
  · exact ⟨w', hw'mem.1, by rw [← hwx]; exact hww'⟩
  · exact ⟨w, hw, hwx⟩

namespace ModEtale

variable {G x₀ U}

/-- The discrete unit circle: the fibre type of the covering. -/
def UC : Type := {c : ℂ // ‖c‖ = 1}

instance : TopologicalSpace UC := ⊥
instance : DiscreteTopology UC := ⟨rfl⟩
instance : Nonempty UC := ⟨⟨1, by simp⟩⟩

/-- The étale point on the sheet of a branch `ψ` over `v`. -/
def mkPt {V : Set X} {ψ : X → ℂ} (hVo : IsOpen V) (hVU : V ⊆ U)
    (hb : IsModulusBranch G x₀ ψ V) {v : X} (hv : v ∈ V) : ModEtale G x₀ U :=
  ⟨⟨v, (ψ : Germ (𝓝 v) ℂ)⟩, hVU hv, V, ψ, hVo, hv, hVU, hb, rfl⟩

/-- `proj` is a covering map over `U`. Trivialized over each branch domain `V`
by the sheets `{c·ψ₀ : ‖c‖ = 1}` (unimodular multiples of a fixed branch), which
are pairwise disjoint (rigidity) and exhaust `proj⁻¹ V` (rigidity + branch
existence). -/
theorem isCoveringMapOn_proj [T2Space X] (hUo : IsOpen U) (hx₀ : x₀ ∈ U)
    (hG : IsGreenFunction U x₀ G) :
    IsCoveringMapOn (proj (G := G) (x₀ := x₀) (U := U)) U := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  obtain ⟨q₀, -⟩ := exists_mk hUo hG hx₀
  have : Nonempty (ModEtale G x₀ U) := ⟨q₀⟩
  have : Nonempty (X → ModEtale G x₀ U) := ⟨fun _ ↦ q₀⟩
  have key : ∀ x : U, ∃ t : Trivialization UC (proj (G := G) (x₀ := x₀) (U := U)),
      (x : X) ∈ t.baseSet := by
    intro x
    obtain ⟨V, ψ₀, hVo, hVc, hxV, hVU, hbranch⟩ := exists_branch_mem hUo hG x.2
    set Usheet : UC → Set (ModEtale G x₀ U) := fun c ↦ sheet V (fun z ↦ c.1 * ψ₀ z) with hU_def
    have hcψbranch : ∀ c : UC, IsModulusBranch G x₀ (fun z ↦ c.1 * ψ₀ z) V :=
      fun c ↦ isModulusBranch_const_mul hbranch c.2
    refine ⟨IsOpen.trivializationDiscrete (f := proj (G := G) (x₀ := x₀) (U := U))
      Usheet V hVo ?_ ?_ ?_ ?_ ?_, hxV⟩
    · -- open_iff
      intro c W hWV
      constructor
      · intro hW
        exact (hW.preimage continuous_proj).inter
          (isOpen_of_mem_basicSets ⟨V, _, hVo, hVc, hVU, hcψbranch c, rfl⟩)
      · intro hWo
        have himg : proj (G := G) (x₀ := x₀) (U := U) '' (proj ⁻¹' W ∩ Usheet c) = W := by
          apply subset_antisymm
          · rintro _ ⟨q, ⟨hqW, _⟩, rfl⟩; exact hqW
          · intro v hv
            exact ⟨mkPt hVo hVU (hcψbranch c) (hWV hv), ⟨hv, hWV hv, rfl⟩, rfl⟩
        rw [← himg]
        exact isOpenMap_proj _ hWo
    · -- inj
      exact fun c ↦ injOn_proj_sheet
    · -- surj
      intro c v hv
      exact ⟨mkPt hVo hVU (hcψbranch c) hv, ⟨hv, rfl⟩, rfl⟩
    · -- disjoint
      intro c₁ c₂ hne
      rw [Function.onFun, Set.disjoint_left]
      rintro q hq1 hq2
      have hev : (fun z ↦ c₁.1 * ψ₀ z) =ᶠ[𝓝 q.1.1] (fun z ↦ c₂.1 * ψ₀ z) :=
        Filter.Germ.coe_eq.mp (hq1.2.symm.trans hq2.2)
      have heqOn : EqOn (fun z ↦ c₁.1 * ψ₀ z) (fun z ↦ c₂.1 * ψ₀ z) V :=
        HolomorphicOn.eqOn_of_eventuallyEq (hcψbranch c₁).1 (hcψbranch c₂).1 hVo hVc hq1.1 hev
      obtain ⟨w₁, hw₁V, hw₁ne⟩ := exists_mem_ne_pole hVo hxV
      have h1 : c₁.1 * ψ₀ w₁ = c₂.1 * ψ₀ w₁ := heqOn hw₁V
      have hψ0ne : ψ₀ w₁ ≠ 0 := by
        rw [← norm_ne_zero_iff, hbranch.2 w₁ ⟨hw₁V, hw₁ne⟩]; exact (Real.exp_pos _).ne'
      exact hne (Subtype.ext (mul_right_cancel₀ hψ0ne h1))
    · -- exhaustive
      intro p hp
      obtain ⟨W, ψ', hWo, hWc, hWU, hψ', hpW⟩ := exists_basic_sheet_mem p
      have hvV : p.1.1 ∈ V := hp
      set W'' := connectedComponentIn (V ∩ W) p.1.1 with hW''
      have hW''sub : W'' ⊆ V ∩ W := connectedComponentIn_subset _ _
      have hW''o : IsOpen W'' := (hVo.inter hWo).connectedComponentIn
      have hW''c : IsPreconnected W'' := isPreconnected_connectedComponentIn
      have hvW'' : p.1.1 ∈ W'' := mem_connectedComponentIn ⟨hvV, hpW.1⟩
      have hb0 : IsModulusBranch G x₀ ψ₀ W'' := hbranch.mono (fun z hz ↦ (hW''sub hz).1)
      have hb' : IsModulusBranch G x₀ ψ' W'' := hψ'.mono (fun z hz ↦ (hW''sub hz).2)
      obtain ⟨y₀, hy₀W'', hy₀ne⟩ := exists_mem_ne_pole hW''o hvW''
      obtain ⟨c, hcnorm, hEq⟩ :=
        IsModulusBranch.exists_unimodular hW''o hW''c hb' hb0 hy₀W'' hy₀ne
      have hev : ψ' =ᶠ[𝓝 p.1.1] (fun z ↦ c * ψ₀ z) := by
        filter_upwards [hW''o.mem_nhds hvW''] with z hz
        exact hEq hz
      refine Set.mem_iUnion.mpr ⟨⟨c, hcnorm⟩, hvV, ?_⟩
      rw [hpW.2]
      exact Filter.Germ.coe_eq.mpr hev
  choose e he using key
  exact IsCoveringMapOn.mk (proj (G := G) (x₀ := x₀) (U := U)) U (fun _ ↦ UC) e he

end ModEtale

end Uniformization
