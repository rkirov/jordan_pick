/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.EndParity
import Mathlib.Analysis.Complex.Convex

/-!
# End-frontier: a complement end absorbs whole frontier components (W7 step L5.4a)

For a connected component `Z = connectedComponentIn (closure V)ᶜ x₀` of the
*open* complement of `closure V` (a "complement end"), this file proves the
point-set backbone of the crossing-parity argument: **`frontier Z` is a union of
whole connected components of `frontier V`.**

The engine is the straightening box of `BoundaryCircle.lean`.  At a frontier
point `ξ` the box `W` splits into three pieces along the level line
`{re = c}`: the `{re > c}` half is `V ∩ W`, the middle segment `{re = c}` is
`frontier V ∩ W`, and the `{re < c}` half is exactly the *local complement end*
`W ∩ (closure V)ᶜ` — a **connected** open set whose closure contains both `ξ`
and every frontier point of `W`.

This "lower half" is the key local object (`exists_lower_half`).  Feeding it into
the component `Z`:

* if `ξ ∈ frontier Z`, then `W` meets `Z`, so the connected lower half lands
  inside `Z`; hence every frontier point of `W` lies in `closure Z`, and being
  off `Z` it lies in `frontier Z`.  Thus `frontier Z` is **open in `frontier V`**
  (`frontier_component_compl_closure_open_in_frontier`).

Since `frontier Z` is always closed and `⊆ frontier V`
(`frontier_component_compl_closure_subset`), it is *clopen in `frontier V`*, so by
`IsClopen.biUnion_connectedComponentIn` it is a union of components
(`frontier_component_compl_closure_biUnion`), and in particular absorbs the whole
component of `frontier V` through any of its points
(`frontier_component_compl_closure_component_subset`).

This is exactly step L5.4a — the reduction that lets the winding contradiction
pick two *distinct components* `C ≠ C'` of `frontier V` inside `frontier Z`.
-/

open Set Metric Topology Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The local complement end (lower half of a straightening box) -/

/-- **Lower half of a straightening box.**  Under the collar hypotheses, each
frontier point `ξ` has a straightening box `W` whose intersection with the open
complement `(closure V)ᶜ` — the `{re < c}` half of the box — is *preconnected*,
has `ξ` in its closure, and has every frontier point of `W` in its closure.

This is the local model of a complement end: near `ξ`, the set `(closure V)ᶜ`
looks like a single connected half-box, and the whole level segment
`frontier V ∩ W` sits on its boundary. -/
theorem exists_lower_half [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {ξ : X} (hξ : ξ ∈ frontier V) :
    ∃ W : Set X, IsOpen W ∧ ξ ∈ W ∧
      IsPreconnected (W ∩ (closure V)ᶜ) ∧
      ξ ∈ closure (W ∩ (closure V)ᶜ) ∧
      (∀ η ∈ frontier V ∩ W, η ∈ closure (W ∩ (closure V)ᶜ)) := by
  obtain ⟨ψ, δ, ε, hψ, hξψ, hδ, hε, hqre, hbox_tgt, hWopen, hξW,
    hf_eq, hVeq, hfront⟩ := exists_straight_box hVo hdich hfc hchart hξ
  set q := ψ ξ with hq
  set box := straightBox q c δ ε with hboxdef
  set W := ψ.symm '' box with hWdef
  set Lo := box ∩ {z : ℂ | z.re < c} with hLodef
  have hboxopen : IsOpen box := by rw [hboxdef]; exact isOpen_straightBox q c δ ε
  -- injectivity of `ψ.symm` on the box
  have hinj : ∀ z ∈ box, ∀ z' ∈ box, ψ.symm z = ψ.symm z' → z = z' := by
    intro z hz z' hz' h
    calc z = ψ (ψ.symm z) := (ψ.right_inv (hbox_tgt hz)).symm
      _ = ψ (ψ.symm z') := by rw [h]
      _ = z' := ψ.right_inv (hbox_tgt hz')
  -- `closure V = V ∪ frontier V`
  have hcl : closure V = V ∪ frontier V := by
    rw [hVo.frontier_eq]; exact (Set.union_sdiff_cancel subset_closure).symm
  have hmemV : ∀ z ∈ box, c < z.re → ψ.symm z ∈ closure V := by
    intro z hz hlt
    have : ψ.symm z ∈ V ∩ W := by rw [hVeq]; exact ⟨z, ⟨hz, hlt⟩, rfl⟩
    exact subset_closure this.1
  have hmemF : ∀ z ∈ box, z.re = c → ψ.symm z ∈ closure V := by
    intro z hz heq
    have : ψ.symm z ∈ frontier V ∩ W := by rw [hfront]; exact ⟨z, ⟨hz, heq⟩, rfl⟩
    exact frontier_subset_closure this.1
  -- **Fact A**: the lower half is exactly `W ∩ (closure V)ᶜ`.
  have hA : W ∩ (closure V)ᶜ = ψ.symm '' Lo := by
    apply Subset.antisymm
    · rintro x ⟨⟨z, hz, rfl⟩, hxc⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rcases lt_trichotomy z.re c with h | h | h
      · exact h
      · exact absurd (hmemF z hz h) hxc
      · exact absurd (hmemV z hz h) hxc
    · rintro x ⟨z, ⟨hz, hlt⟩, rfl⟩
      rw [Set.mem_setOf_eq] at hlt
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [hcl]
      rintro (hV | hF)
      · have hmem : ψ.symm z ∈ V ∩ W := ⟨hV, z, hz, rfl⟩
        rw [hVeq] at hmem
        obtain ⟨z', ⟨hz', hlt'⟩, hzz'⟩ := hmem
        rw [hinj z' hz' z hz hzz'] at hlt'
        exact absurd hlt' (not_lt.mpr (le_of_lt hlt))
      · have hmem : ψ.symm z ∈ frontier V ∩ W := ⟨hF, z, hz, rfl⟩
        rw [hfront] at hmem
        obtain ⟨z', ⟨hz', heq'⟩, hzz'⟩ := hmem
        rw [hinj z' hz' z hz hzz'] at heq'
        rw [heq'] at hlt; exact lt_irrefl c hlt
  -- **Fact B**: the lower half is preconnected (image of a convex box).
  have hboxconv : Convex ℝ box := by
    have hbox_eq : box = ({z : ℂ | z.re < c + δ} ∩ {z : ℂ | c - δ < z.re}) ∩
        ({z : ℂ | z.im < q.im + ε} ∩ {z : ℂ | q.im - ε < z.im}) := by
      ext z
      simp only [hboxdef, straightBox, mem_setOf_eq, mem_inter_iff, abs_lt]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    rw [hbox_eq]
    exact ((convex_halfSpace_re_lt _).inter (convex_halfSpace_re_gt _)).inter
      ((convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _))
  have hLoconv : Convex ℝ Lo := hboxconv.inter (convex_halfSpace_re_lt c)
  have hLopre : IsPreconnected (ψ.symm '' Lo) := by
    have hcont : ContinuousOn ψ.symm Lo := ψ.continuousOn_symm.mono (fun z hz => hbox_tgt hz.1)
    exact hLoconv.isPreconnected.image _ hcont
  -- **Fact C/D**: a middle point of the box is a limit of the lower half.
  have hclos_Lo : ∀ z₀ ∈ box, z₀.re = c → z₀ ∈ closure Lo := by
    intro z₀ hz₀ hz₀re
    rw [_root_.mem_closure_iff]
    intro O hO hz₀O
    have hcontat : ContinuousAt (fun t : ℝ => z₀ + (t : ℂ)) 0 := by fun_prop
    have hz_mem : (fun t : ℝ => z₀ + (t : ℂ)) 0 ∈ O ∩ box := by
      simp only [Complex.ofReal_zero, add_zero]; exact ⟨hz₀O, hz₀⟩
    have hev : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), (z₀ + (t : ℂ)) ∈ O ∩ box :=
      hcontat.preimage_mem_nhds ((hO.inter hboxopen).mem_nhds hz_mem)
    have hev' : ∀ᶠ (t : ℝ) in 𝓝[<] (0 : ℝ), (z₀ + (t : ℂ)) ∈ O ∩ box :=
      hev.filter_mono nhdsWithin_le_nhds
    obtain ⟨t, htmem, htneg⟩ := (hev'.and self_mem_nhdsWithin).exists
    have htlt : t < 0 := htneg
    refine ⟨z₀ + (t : ℂ), htmem.1, htmem.2, ?_⟩
    show (z₀ + (t : ℂ)).re < c
    rw [Complex.add_re, Complex.ofReal_re, hz₀re]; linarith
  have hclos_img : ∀ z₀ ∈ box, z₀.re = c → ψ.symm z₀ ∈ closure (ψ.symm '' Lo) := by
    intro z₀ hz₀ hz₀re
    have hcw : ContinuousWithinAt ψ.symm Lo z₀ :=
      (ψ.continuousAt_symm (hbox_tgt hz₀)).continuousWithinAt
    exact hcw.mem_closure_image (hclos_Lo z₀ hz₀ hz₀re)
  -- `q ∈ box` and `ψ.symm q = ξ`
  have hqbox : q ∈ box := by
    rw [hboxdef, mem_straightBox]
    exact ⟨by rw [hqre, sub_self, abs_zero]; exact hδ, by rw [sub_self, abs_zero]; exact hε⟩
  have hξclos : ξ ∈ closure (W ∩ (closure V)ᶜ) := by
    rw [hA]
    have h := hclos_img q hqbox hqre
    rwa [show ψ.symm q = ξ from ψ.left_inv hξψ] at h
  have hηclos : ∀ η ∈ frontier V ∩ W, η ∈ closure (W ∩ (closure V)ᶜ) := by
    intro η hη
    rw [hfront] at hη
    obtain ⟨z₀, ⟨hz₀, hz₀re⟩, rfl⟩ := hη
    rw [hA]; exact hclos_img z₀ hz₀ hz₀re
  exact ⟨W, hWopen, hξW, by rw [hA]; exact hLopre, hξclos, hηclos⟩

/-! ## `frontier Z` is open in `frontier V` -/

/-- **`frontier Z` is open in `frontier V`.**  For a complement end
`Z = connectedComponentIn (closure V)ᶜ x₀`, there is an open `U ⊆ X` with
`frontier Z = frontier V ∩ U`.

Proof: every `ξ ∈ frontier Z` has a straightening box `W` (from
`exists_lower_half`).  Since `ξ ∈ closure Z`, `W` meets `Z`; the lower half
`W ∩ (closure V)ᶜ` is connected and meets `Z`, so lands inside the component `Z`.
Then every point of `frontier V ∩ W` lies in `closure Z` (it is in the closure of
the lower half) and off `Z` (it lies in `closure V`), hence in `frontier Z`.
Taking the union of these boxes over `frontier Z` gives `U`. -/
theorem frontier_component_compl_closure_open_in_frontier [T2Space X] {V : Set X}
    (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {x₀ : X} :
    ∃ U : Set X, IsOpen U ∧
      frontier (connectedComponentIn (closure V)ᶜ x₀) = frontier V ∩ U := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  set Z := connectedComponentIn (closure V)ᶜ x₀ with hZdef
  have hZopen : IsOpen Z := isClosed_closure.isOpen_compl.connectedComponentIn
  have hfrZsub : frontier Z ⊆ frontier V := frontier_component_compl_closure_subset
  have hZcompl : Z ⊆ (closure V)ᶜ := connectedComponentIn_subset _ _
  -- per point of `frontier Z`, a box whose frontier slice lies in `frontier Z`
  have hbox : ∀ ξ ∈ frontier Z, ∃ W : Set X, IsOpen W ∧ ξ ∈ W ∧
      frontier V ∩ W ⊆ frontier Z := by
    intro ξ hξ
    have hξfr : ξ ∈ frontier V := hfrZsub hξ
    obtain ⟨W, hWopen, hξW, hHpre, hξH, hηH⟩ := exists_lower_half hVo hdich hfc hchart hξfr
    refine ⟨W, hWopen, hξW, ?_⟩
    -- the lower half `H = W ∩ (closure V)ᶜ` lands in `Z`
    have hξZbar : ξ ∈ closure Z := frontier_subset_closure hξ
    obtain ⟨p, hpW, hpZ⟩ := mem_closure_iff.1 hξZbar W hWopen hξW
    have hpH : p ∈ W ∩ (closure V)ᶜ := ⟨hpW, hZcompl hpZ⟩
    have hHZ : W ∩ (closure V)ᶜ ⊆ Z := by
      have hsub := hHpre.subset_connectedComponentIn hpH (fun y hy => hy.2)
      rw [hZdef, connectedComponentIn_eq hpZ]; exact hsub
    -- every frontier point of `W` lies in `frontier Z`
    intro η hη
    have hηZbar : η ∈ closure Z := closure_mono hHZ (hηH η hη)
    have hηnZ : η ∉ Z := fun hηZ => hZcompl hηZ (frontier_subset_closure hη.1)
    have hηnint : η ∉ interior Z := by rw [hZopen.interior_eq]; exact hηnZ
    exact (⟨hηZbar, hηnint⟩ : η ∈ closure Z \ interior Z)
  choose! Wf hWfopen hWfmem hWfsub using hbox
  refine ⟨⋃ ξ ∈ frontier Z, Wf ξ, isOpen_biUnion (fun ξ hξ => hWfopen ξ hξ), ?_⟩
  apply Subset.antisymm
  · intro η hη
    exact ⟨hfrZsub hη, mem_biUnion hη (hWfmem η hη)⟩
  · rintro η ⟨hηfr, hηU⟩
    obtain ⟨ξ, hξ, hηW⟩ := mem_iUnion₂.mp hηU
    exact hWfsub ξ hξ ⟨hηfr, hηW⟩

/-! ## `frontier Z` is a union of whole components of `frontier V` -/

/-- **A complement end absorbs whole frontier components.**  `frontier Z` is
clopen in `frontier V`, hence (by `IsClopen.biUnion_connectedComponentIn`) a union
of connected components of `frontier V`. -/
theorem frontier_component_compl_closure_biUnion [T2Space X] {V : Set X}
    (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {x₀ : X} :
    frontier (connectedComponentIn (closure V)ᶜ x₀)
      = ⋃ ξ ∈ frontier (connectedComponentIn (closure V)ᶜ x₀),
          connectedComponentIn (frontier V) ξ := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  set Z := connectedComponentIn (closure V)ᶜ x₀ with hZdef
  have hfrZsub : frontier Z ⊆ frontier V := frontier_component_compl_closure_subset
  obtain ⟨U, hUopen, hUeq⟩ :=
    frontier_component_compl_closure_open_in_frontier hVo hdich hfc hchart (x₀ := x₀)
  rw [← hZdef] at hUeq
  refine IsClopen.biUnion_connectedComponentIn ?_ hfrZsub
  constructor
  · exact isClosed_frontier.preimage continuous_subtype_val
  · have hsub_eq : (Subtype.val : ↥(frontier V) → X) ⁻¹' frontier Z
        = Subtype.val ⁻¹' U := by
      rw [hUeq]
      simp only [Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter]
    show IsOpen ((Subtype.val : ↥(frontier V) → X) ⁻¹' frontier Z)
    rw [hsub_eq]
    exact hUopen.preimage continuous_subtype_val

/-- **The component of `frontier V` through a frontier-Z point stays inside
`frontier Z`.**  Immediate corollary of the clopen description: this is the
form the crossing-parity step consumes, letting it treat `frontier Z` as a union
of full components `C` of `frontier V`. -/
theorem frontier_component_compl_closure_component_subset [T2Space X] {V : Set X}
    (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {x₀ ξ : X} (hξ : ξ ∈ frontier (connectedComponentIn (closure V)ᶜ x₀)) :
    connectedComponentIn (frontier V) ξ ⊆ frontier (connectedComponentIn (closure V)ᶜ x₀) := by
  rw [frontier_component_compl_closure_biUnion hVo hdich hfc hchart (x₀ := x₀)]
  exact subset_biUnion_of_mem hξ

end Uniformization
