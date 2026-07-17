/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.CircleChain
import Uniformization.Surface.Fill.HoleFill

/-!
# End-frontier connectivity: infrastructure toward the crossing-parity core (W7 step L5.4)

This file develops the point-set topology feeding the crossing-parity argument
that each noncompact complement end of a level piece `V` has **connected
frontier**.  The end is taken as a connected component `Z` of the open set
`(closure V)ᶜ` (the interior of the complement); the target is
`IsPreconnected (frontier Z)`.

The full argument (see `W7_PLAN.md` §L5.4 / the plan attached to this file)
builds, for each connected component `C` of `frontier V`, a collar phase
`τ_C : X → Circle` that winds once across `C` and is trivial elsewhere, then
derives a contradiction from `SimplyConnectedSpace X` via the abstract lifting
engine `lift_endpoint_eq_of_simplyConnected` (`Fill/Parity.lean`) applied to a
loop that crosses two putatively distinct components.

What is delivered here, **sorry-free**:

* `frontier_component_compl_closure_subset` — the frontier of a component `Z` of
  `(closure V)ᶜ` lies in `frontier V` (locally connected ambient space);
* `isCompact_frontier_component_compl_closure` — that frontier is compact once
  `closure V` is;
* `exists_open_isCompact_closure_inter_eq` — the **clopen separation lemma**:
  a set `C` that is clopen in a compact `S` (with `C ⊆ M`, `M` open) has an open
  neighbourhood `N` with compact closure inside `M` whose closure meets `S`
  exactly in `C`.  This is the separation step that pins the collar phase to a
  single frontier component (it isolates `C` from the rest of the level set,
  phantom points included, using the box-free equality `{f = c} ∩ box = ∂V ∩ box`
  only implicitly through `S = frontier V`).

The `Circle`-phase construction and the winding contradiction (`W7` steps L5.4b/c)
are the surface-topology core and are **not** discharged here; they consume the
separation lemma above.
-/

open Set Metric Topology Filter

namespace Uniformization

open Rado

/-! ## Clopen separation inside a compact set (general topology) -/

section Separation

variable {X : Type*} [TopologicalSpace X]

/-- **Clopen separation lemma.**  Let `S` be compact and `C ⊆ S` be *clopen in
`S`* — closed (`hCcl`) and open in the subspace (`hCopenS : C = S ∩ U` for an
open `U`).  Given an open `M ⊇ C`, there is an open `N ⊇ C` with compact closure
`closure N ⊆ M` such that `closure N ∩ S = C`.  Thus `N` isolates `C` from the
rest of `S` even after passing to the closure — the exact separation that binds a
collar phase to a single component `C` of the level set `frontier V`.

Requires the ambient space to be locally compact and (for `T2 + LC ⇒`) regular
Hausdorff, so that disjoint compacts are separated by disjoint opens and a
relatively compact open collar can be interposed. -/
theorem exists_open_isCompact_closure_inter_eq [T2Space X] [LocallyCompactSpace X]
    {S C M U : Set X} (hS : IsCompact S) (hCcl : IsClosed C) (hCS : C ⊆ S)
    (hU : IsOpen U) (hCU : C = S ∩ U) (hM : IsOpen M) (hCM : C ⊆ M) :
    ∃ N : Set X, IsOpen N ∧ C ⊆ N ∧ IsCompact (closure N) ∧ closure N ⊆ M ∧
      closure N ∩ S = C := by
  -- `C` is compact (closed subset of the compact `S`)
  have hCcpt : IsCompact C := hS.of_isClosed_subset hCcl hCS
  -- `S` is closed (compact in a T2 space)
  have hSclosed : IsClosed S := hS.isClosed
  -- the complementary part `D = S \ C = S ∩ Uᶜ` is compact and closed
  set D := S ∩ Uᶜ with hDdef
  have hDclosed : IsClosed D := hSclosed.inter hU.isClosed_compl
  have hDcpt : IsCompact D := hS.of_isClosed_subset hDclosed inter_subset_left
  -- `C` and `D` are disjoint
  have hdisj : Disjoint C D := by
    rw [hCU, hDdef]
    rw [Set.disjoint_left]
    rintro x ⟨_, hxU⟩ ⟨_, hxUc⟩
    exact hxUc hxU
  -- separate them by disjoint opens (`T2` + compactness)
  obtain ⟨G₁, G₂, hG₁o, hG₂o, hCG₁, hDG₂, hG₁₂⟩ :=
    SeparatedNhds.of_isCompact_isCompact hCcpt hDcpt hdisj
  -- interpose a relatively compact open `N` between `C` and the open `G₁ ∩ M`
  obtain ⟨N, hNo, hCN, hNcl, hNcpt⟩ :=
    exists_open_between_and_isCompact_closure hCcpt (hG₁o.inter hM)
      (subset_inter hCG₁ hCM)
  refine ⟨N, hNo, hCN, hNcpt, hNcl.trans inter_subset_right, ?_⟩
  -- `closure N ⊆ G₁`, disjoint from `G₂ ⊇ D`, so `closure N ∩ S ⊆ C`
  have hNG₁ : closure N ⊆ G₁ := hNcl.trans inter_subset_left
  apply Subset.antisymm
  · rintro x ⟨hxN, hxS⟩
    by_contra hxC
    -- `x ∈ S \ C = D`, hence in `G₂`, contradicting disjointness with `G₁`
    have hxD : x ∈ D := by
      rw [hDdef]
      refine ⟨hxS, ?_⟩
      intro hxU
      exact hxC (hCU ▸ ⟨hxS, hxU⟩)
    exact Set.disjoint_left.mp hG₁₂ (hNG₁ hxN) (hDG₂ hxD)
  · exact fun x hx => ⟨subset_closure (hCN hx), hCS hx⟩

end Separation

/-! ## Frontier of a complement end -/

section Surface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **The frontier of a complement end lies in `frontier V`.**  For a connected
component `Z` of the *open* set `(closure V)ᶜ` (the interior of the complement,
i.e. a "complement end"), `frontier Z ⊆ frontier V`.  This lets the crossing
parity argument work with `frontier V` throughout. -/
theorem frontier_component_compl_closure_subset [LocallyConnectedSpace X]
    {V : Set X} {x : X} :
    frontier (connectedComponentIn (closure V)ᶜ x) ⊆ frontier V := by
  have h1 : frontier (connectedComponentIn (closure V)ᶜ x) ⊆ frontier (closure V)ᶜ :=
    frontier_connectedComponentIn_subset (isClosed_closure.isOpen_compl)
  rw [frontier_compl] at h1
  exact h1.trans frontier_closure_subset

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The frontier of a complement end is compact once `closure V` is. -/
theorem isCompact_frontier_component_compl_closure [LocallyConnectedSpace X]
    {V : Set X} (hVcl : IsCompact (closure V)) {x : X} :
    IsCompact (frontier (connectedComponentIn (closure V)ᶜ x)) := by
  have hsub : frontier (connectedComponentIn (closure V)ᶜ x) ⊆ frontier V :=
    frontier_component_compl_closure_subset
  refine (hVcl.of_isClosed_subset isClosed_frontier frontier_subset_closure).of_isClosed_subset
    isClosed_frontier hsub

/-! ## Phantom-free collar neighbourhood of the frontier

The straightening boxes of `BoundaryCircle.lean` have the decisive property that
*inside a box* the level set `{f = c}` coincides with `frontier V` (the box
middle segment): there are **no phantom level points** with `f = c` off the
frontier.  Unioning finitely many boxes over the compact `frontier V` produces a
single open neighbourhood `M` on which `f` is continuous and phantom-free.  This
is the "excision is free from D1" simplification of the collar phase construction
(it removes the need for a maximum-principle argument to exclude interior level
patches). -/

/-- Per-frontier-point straightening box on which `f` is continuous and
phantom-free: any box point with `f = c` already lies on `frontier V`. -/
theorem exists_box_nbhd [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {ξ : X} (hξ : ξ ∈ frontier V) :
    ∃ W : Set X, IsOpen W ∧ ξ ∈ W ∧ ContinuousOn f W ∧
      (∀ x ∈ W, f x = c → x ∈ frontier V) := by
  obtain ⟨ψ, δ, ε, hψ, hξψ, hδ, hε, hqre, hbox_tgt, hWopen, hξW, hf_eq, hVeq, hfront⟩ :=
    exists_straight_box hVo hdich hfc hchart hξ
  set box := straightBox (ψ ξ) c δ ε with hboxdef
  set W := ψ.symm '' box with hWdef
  have hWsrc : W ⊆ ψ.source := by
    rintro x ⟨z, hz, rfl⟩; exact ψ.map_target (hbox_tgt hz)
  refine ⟨W, hWopen, hξW, ?_, ?_⟩
  · -- `f = Re ∘ ψ` on `W`, hence continuous there
    exact (Complex.continuous_re.comp_continuousOn (ψ.continuousOn.mono hWsrc)).congr
      (fun x hx => (re_eq_f_of_mem_boxImage hbox_tgt hf_eq hx).symm)
  · -- phantom-free: a box point with `f = c` is a middle-segment (frontier) point
    intro x hxW hfx
    obtain ⟨z, hz, rfl⟩ := hxW
    have hzre : z.re = c := by rw [← hf_eq z hz]; exact hfx
    have : ψ.symm z ∈ frontier V ∩ W := by
      rw [hfront]; exact ⟨z, ⟨hz, hzre⟩, rfl⟩
    exact this.1

/-- **Phantom-free collar neighbourhood.**  Under the piece hypotheses there is a
single open `M ⊇ frontier V` on which the collar coordinate `f` is continuous and
the level set is phantom-free: `f x = c ↔ x ∈ frontier V` for every `x ∈ M`. -/
theorem exists_phantom_free_nbhd [T2Space X] {V : Set X} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0) :
    ∃ M : Set X, IsOpen M ∧ frontier V ⊆ M ∧ ContinuousOn f M ∧
      (∀ x ∈ M, (f x = c ↔ x ∈ frontier V)) := by
  classical
  have hfrcpt : IsCompact (frontier V) :=
    hVcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  choose! Wf hWopen hWmem hWcont hWphantom using
    fun ξ (hξ : ξ ∈ frontier V) => exists_box_nbhd hVo hdich hfc hchart hξ
  obtain ⟨t, htsub, htfin, htcov⟩ := hfrcpt.elim_finite_subcover_image hWopen
    (fun ξ hξ => Set.mem_biUnion hξ (hWmem ξ hξ))
  refine ⟨⋃ ξ ∈ t, Wf ξ, isOpen_biUnion (fun ξ hξ => hWopen ξ (htsub hξ)), htcov, ?_, ?_⟩
  · -- continuity: `M` is open and `f` is continuous at each point via its box
    intro x hxM
    obtain ⟨ξ, hξt, hxW⟩ := mem_iUnion₂.mp hxM
    exact ((hWcont ξ (htsub hξt)).continuousAt
      ((hWopen ξ (htsub hξt)).mem_nhds hxW)).continuousWithinAt
  · -- phantom-free level set
    intro x hxM
    obtain ⟨ξ, hξt, hxW⟩ := mem_iUnion₂.mp hxM
    exact ⟨fun hfx => hWphantom ξ (htsub hξt) x hxW hfx, fun hxfr => hfc x hxfr⟩

/-- **Collar substrate for one frontier component.**  Bundling the phantom-free
neighbourhood with the clopen separation lemma, a component
`C = connectedComponentIn (frontier V) x₀` acquires an open collar `N` with:

* `C ⊆ N`, `closure N` compact and `⊆ M` (the phantom-free nbhd);
* `closure N ∩ frontier V = C` (the collar isolates exactly `C`);
* `f` continuous and phantom-free on `M`;
* `f ≠ c` on `frontier N`.

The last fact is the nonvanishing input that makes `δ₀ = inf {|f x − c| : x ∈
frontier N}` positive (compact `frontier N`), which sets the collar phase's width
in the crossing-parity construction. -/
theorem exists_component_collar_substrate [T2Space X] {V : Set X} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {x₀ : X} :
    ∃ (M N : Set X), IsOpen M ∧ IsOpen N ∧ ContinuousOn f M ∧
      (∀ x ∈ M, (f x = c ↔ x ∈ frontier V)) ∧
      connectedComponentIn (frontier V) x₀ ⊆ N ∧
      IsCompact (closure N) ∧ closure N ⊆ M ∧
      closure N ∩ frontier V = connectedComponentIn (frontier V) x₀ ∧
      (∀ x ∈ frontier N, f x ≠ c) := by
  haveI : LocallyCompactSpace X := Rado.locallyCompactSpace
  set C := connectedComponentIn (frontier V) x₀ with hCeq
  obtain ⟨M, hMopen, hfrM, hfcont, hphantom⟩ :=
    exists_phantom_free_nbhd hVo hVcl hdich hfc hchart
  have hfrcpt : IsCompact (frontier V) :=
    hVcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hCcl : IsClosed C := isClosed_frontier.connectedComponentIn
  have hCsub : C ⊆ frontier V := connectedComponentIn_subset _ _
  obtain ⟨U, hUo, hCU⟩ := isOpen_component_in_frontier hVo hdich hfc hchart (x₀ := x₀)
  obtain ⟨N, hNo, hCN, hNcpt, hNM, hNfr⟩ :=
    exists_open_isCompact_closure_inter_eq hfrcpt hCcl hCsub hUo hCU hMopen (hCsub.trans hfrM)
  refine ⟨M, N, hMopen, hNo, hfcont, hphantom, hCN, hNcpt, hNM, hNfr, ?_⟩
  intro x hxfrN hfx
  rw [hNo.frontier_eq] at hxfrN
  have hxfr : x ∈ frontier V := (hphantom x (hNM hxfrN.1)).mp hfx
  have hxC : x ∈ C := hNfr ▸ ⟨hxfrN.1, hxfr⟩
  exact hxfrN.2 (hCN hxC)

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **A complement end has nonempty frontier.**  If `X` is connected and `V` is
nonempty, then for a point `x ∉ closure V` the complement end
`Z = connectedComponentIn (closure V)ᶜ x` has nonempty frontier: `Z` is a
nonempty proper open subset of the connected `X`, hence not clopen. -/
theorem nonempty_frontier_component_compl_closure [LocallyConnectedSpace X]
    [ConnectedSpace X] {V : Set X} (hVne : V.Nonempty) {x : X} (hx : x ∉ closure V) :
    (frontier (connectedComponentIn (closure V)ᶜ x)).Nonempty := by
  set Z := connectedComponentIn (closure V)ᶜ x with hZ
  have hZopen : IsOpen Z := isClosed_closure.isOpen_compl.connectedComponentIn
  have hxZ : x ∈ Z := mem_connectedComponentIn hx
  have hZne : Z.Nonempty := ⟨x, hxZ⟩
  -- `Z ≠ univ`: any point of the nonempty `closure V` misses `Z`
  have hZnu : Z ≠ univ := by
    obtain ⟨v, hv⟩ := hVne
    have hvcl : v ∈ closure V := subset_closure hv
    intro hZu
    have : v ∈ Z := by rw [hZu]; trivial
    exact (connectedComponentIn_subset _ _ this) hvcl
  by_contra hfr
  rw [not_nonempty_iff_eq_empty] at hfr
  have hclopen : IsClopen Z := isClopen_iff_frontier_eq_empty.mpr hfr
  rcases isClopen_iff.mp hclopen with h | h
  · exact absurd (h ▸ hxZ) (notMem_empty x)
  · exact hZnu h

end Surface

end Uniformization
