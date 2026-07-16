/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Regularity

/-!
# Hole-filling (W7 step L4)

`fill U` adds to `U` every point whose connected component in `Uᶜ` is compact
(the "holes"); the complement of `fill U` is exactly the union of the
noncompact components of `Uᶜ`. Main point-set facts, all consumed downstream
by W7 steps L3/L5–L10 (see `Uniformization/W7_PLAN.md` §L4):

* `subset_fill` : `U ⊆ fill U`;
* `isOpen_fill` : `U` open ⇒ `fill U` open (locally compact T2; via the
  compact-clopen swallowing lemma `exists_compact_isClopenIn`);
* `frontier_fill_subset` : filling only shrinks the frontier;
* `isCompact_closure_fill` : `closure U` compact ⇒ `closure (fill U)` compact
  (connected noncompact ambient space);
* `isPreconnected_fill` / `isConnected_fill` : filling preserves connectedness;
* `connectedComponentIn_compl_fill` + `not_isCompact_connectedComponentIn_compl_fill`
  : the components of `(fill U)ᶜ` are exactly the noncompact components of
  `Uᶜ`; in particular `(fill U)ᶜ` has no compact component (`fill_fill`);
* `nonempty_frontier_fill` : the filled piece has nonempty frontier;
* `ExteriorDiskAt.fill` : the exterior disk condition survives filling
  (the disk's interior is connected and misses `U`, hence would be swallowed
  into a compact complement component — impossible at a frontier point).

Everything except the last lemma is pure point-set topology and is stated for
a general topological space `Y` (with `[T2Space Y]`, `[LocallyCompactSpace Y]`,
`[LocallyConnectedSpace Y]`, `[ConnectedSpace Y]` added per lemma), so the
piece layer can also apply it inside chart targets if convenient.
-/

open Set Metric Topology

namespace Uniformization

/-! ## Hole filling in a general topological space -/

section HoleFill

variable {Y : Type*} [TopologicalSpace Y] {U : Set Y} {x : Y}

/-- `fill U`: `U` together with every point whose connected component in `Uᶜ`
is compact. The added components are the "holes" of `U`. -/
def fill (U : Set Y) : Set Y :=
  U ∪ {x | x ∉ U ∧ IsCompact (connectedComponentIn Uᶜ x)}

theorem subset_fill (U : Set Y) : U ⊆ fill U := subset_union_left

theorem mem_fill_iff :
    x ∈ fill U ↔ x ∈ U ∨ (x ∉ U ∧ IsCompact (connectedComponentIn Uᶜ x)) :=
  Iff.rfl

theorem notMem_fill_iff :
    x ∉ fill U ↔ x ∉ U ∧ ¬ IsCompact (connectedComponentIn Uᶜ x) := by
  rw [mem_fill_iff]
  by_cases hx : x ∈ U <;> simp [hx]

/-- All points of a compact component of `Uᶜ` lie in `fill U`. -/
theorem connectedComponentIn_subset_fill (_hx : x ∉ U)
    (hC : IsCompact (connectedComponentIn Uᶜ x)) :
    connectedComponentIn Uᶜ x ⊆ fill U := by
  intro y hy
  have hyU : y ∉ U := connectedComponentIn_subset Uᶜ x hy
  have heq : connectedComponentIn Uᶜ y = connectedComponentIn Uᶜ x :=
    (connectedComponentIn_eq hy).symm
  exact Or.inr ⟨hyU, by rw [heq]; exact hC⟩

/-- All points of a noncompact component of `Uᶜ` lie outside `fill U`. -/
theorem connectedComponentIn_subset_compl_fill (hx : x ∉ fill U) :
    connectedComponentIn Uᶜ x ⊆ (fill U)ᶜ := by
  obtain ⟨hxU, hxC⟩ := notMem_fill_iff.mp hx
  intro y hy
  have hyU : y ∉ U := connectedComponentIn_subset Uᶜ x hy
  have heq : connectedComponentIn Uᶜ y = connectedComponentIn Uᶜ x :=
    (connectedComponentIn_eq hy).symm
  exact notMem_fill_iff.mpr ⟨hyU, by rw [heq]; exact hxC⟩

/-- Connected components of a closed set are closed. -/
protected theorem _root_.IsClosed.connectedComponentIn {F : Set Y} (hF : IsClosed F) :
    IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
      isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- In a compact T2 space a clopen set can be interposed between a point and
any open superset of its connected component. -/
private theorem exists_isClopen_of_connectedComponent_subset {α : Type*} [TopologicalSpace α]
    [T2Space α] [CompactSpace α] {x : α} {W : Set α} (hW : IsOpen W)
    (h : connectedComponent x ⊆ W) :
    ∃ Z : Set α, IsClopen Z ∧ x ∈ Z ∧ Z ⊆ W := by
  have hint : (Wᶜ ∩ ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, (Z : Set α)) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen x, ← Set.disjoint_iff_inter_eq_empty]
    exact disjoint_compl_left_iff_subset.mpr h
  obtain ⟨t, ht⟩ := hW.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun Z : { Z : Set α // IsClopen Z ∧ x ∈ Z } => (Z : Set α))
    (fun Z => Z.2.1.isClosed) hint
  refine ⟨⋂ Z ∈ t, (Z : Set α), isClopen_biInter_finset fun Z _ => Z.2.1,
    mem_iInter₂.mpr fun Z _ => Z.2.2, ?_⟩
  intro z hz
  by_contra hzW
  have : z ∈ (Wᶜ ∩ ⋂ Z ∈ t, (Z : Set α)) := ⟨hzW, hz⟩
  rw [ht] at this
  exact this

variable [T2Space Y] [LocallyCompactSpace Y]

/-- **Swallowing lemma**: a compact connected component of a closed set `F` is
contained in a compact set of the form `F ∩ O` (`O` open), which is clopen in
`F` and may be taken inside any open superset `Ω` of the component. -/
theorem exists_compact_isClopenIn {F : Set Y} (hF : IsClosed F) (hx : x ∈ F)
    (hC : IsCompact (connectedComponentIn F x)) {Ω : Set Y} (hΩ : IsOpen Ω)
    (hCΩ : connectedComponentIn F x ⊆ Ω) :
    ∃ O : Set Y, IsOpen O ∧ IsCompact (F ∩ O) ∧
      connectedComponentIn F x ⊆ F ∩ O ∧ F ∩ O ⊆ Ω := by
  obtain ⟨L, hL, hCL⟩ := exists_compact_superset hC
  set F' := L ∩ F with hF'def
  have hF'cpt : IsCompact F' := hL.inter_right hF
  have hxF' : x ∈ F' := ⟨interior_subset (hCL (mem_connectedComponentIn hx)), hx⟩
  -- the component of `x` in `F'` is the same set
  have hcc : connectedComponentIn F' x = connectedComponentIn F x := by
    apply Subset.antisymm (connectedComponentIn_mono x inter_subset_right)
    refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx) ?_
    intro y hy
    exact ⟨interior_subset (hCL hy), connectedComponentIn_subset F x hy⟩
  -- move to the compact subtype
  haveI : CompactSpace F' := isCompact_iff_compactSpace.mp hF'cpt
  set W : Set F' := ((↑) : F' → Y) ⁻¹' (Ω ∩ interior L) with hWdef
  have hWo : IsOpen W := (hΩ.inter isOpen_interior).preimage continuous_subtype_val
  have hccW : connectedComponent (⟨x, hxF'⟩ : F') ⊆ W := by
    intro z hz
    have hzC : (z : Y) ∈ connectedComponentIn F' x := by
      rw [connectedComponentIn_eq_image hxF']
      exact ⟨z, hz, rfl⟩
    rw [hcc] at hzC
    exact ⟨hCΩ hzC, hCL hzC⟩
  obtain ⟨Z, hZclopen, hxZ, hZW⟩ := exists_isClopen_of_connectedComponent_subset hWo hccW
  obtain ⟨O₀, hO₀, hO₀Z⟩ := isOpen_induced_iff.mp hZclopen.isOpen
  set O := O₀ ∩ interior L ∩ Ω with hOdef
  have hAeq : ((↑) : F' → Y) '' Z = F ∩ O := by
    apply Subset.antisymm
    · rintro _ ⟨z, hzZ, rfl⟩
      have h2 : (z : Y) ∈ O₀ := by
        rw [← hO₀Z] at hzZ
        exact hzZ
      have h3 := hZW hzZ
      exact ⟨z.2.2, ⟨h2, h3.2⟩, h3.1⟩
    · rintro y ⟨hyF, ⟨hyO₀, hyintL⟩, hyΩ⟩
      have hyF' : y ∈ F' := ⟨interior_subset hyintL, hyF⟩
      have hyZ : (⟨y, hyF'⟩ : F') ∈ Z := by
        rw [← hO₀Z]
        exact hyO₀
      exact ⟨⟨y, hyF'⟩, hyZ, rfl⟩
  have hZcpt : IsCompact (((↑) : F' → Y) '' Z) :=
    hZclopen.isClosed.isCompact.image continuous_subtype_val
  refine ⟨O, (hO₀.inter isOpen_interior).inter hΩ, hAeq ▸ hZcpt, ?_, ?_⟩
  · rw [← hcc, connectedComponentIn_eq_image hxF', ← hAeq]
    exact image_mono (hZclopen.connectedComponent_subset hxZ)
  · rw [← hAeq]
    rintro _ ⟨z, hzZ, rfl⟩
    exact (hZW hzZ).1

omit [LocallyCompactSpace Y] in
/-- A compact clopen-in-`F` piece `F ∩ O` absorbs the whole `F`-component of
each of its points. -/
theorem connectedComponentIn_subset_of_isCompact_inter {F O : Set Y} (_hF : IsClosed F)
    (hO : IsOpen O) (hA : IsCompact (F ∩ O)) {a : Y} (ha : a ∈ F ∩ O) :
    connectedComponentIn F a ⊆ F ∩ O := by
  set C := connectedComponentIn F a with hCdef
  have hCa : IsPreconnected C := isPreconnected_connectedComponentIn
  have hsub : C ⊆ O ∪ (F ∩ O)ᶜ := by
    intro y hy
    by_cases hyA : y ∈ F ∩ O
    · exact Or.inl hyA.2
    · exact Or.inr hyA
  by_cases hv : (C ∩ (F ∩ O)ᶜ).Nonempty
  · have hu : (C ∩ O).Nonempty := ⟨a, mem_connectedComponentIn ha.1, ha.2⟩
    obtain ⟨y, hyC, hyO, hyAc⟩ := hCa O (F ∩ O)ᶜ hO hA.isClosed.isOpen_compl hsub hu hv
    exact absurd ⟨connectedComponentIn_subset F a hyC, hyO⟩ hyAc
  · intro y hy
    by_contra hyA
    exact hv ⟨y, hy, hyA⟩

/-- **Hole-filling is open** (for open `U`, in a locally compact T2 space). -/
theorem isOpen_fill (hU : IsOpen U) : IsOpen (fill U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x (hxU | ⟨hxU, hxC⟩)
  · exact ⟨U, subset_fill U, hU, hxU⟩
  · obtain ⟨O, hOopen, hAcpt, hCA, -⟩ :=
      exists_compact_isClopenIn hU.isClosed_compl hxU hxC isOpen_univ (subset_univ _)
    refine ⟨O, ?_, hOopen, (hCA (mem_connectedComponentIn hxU)).2⟩
    intro y hyO
    by_cases hyU : y ∈ U
    · exact subset_fill U hyU
    · have hyA : y ∈ Uᶜ ∩ O := ⟨hyU, hyO⟩
      have hsub : connectedComponentIn Uᶜ y ⊆ Uᶜ ∩ O :=
        connectedComponentIn_subset_of_isCompact_inter hU.isClosed_compl hOopen hAcpt hyA
      exact Or.inr ⟨hyU, hAcpt.of_isClosed_subset hU.isClosed_compl.connectedComponentIn hsub⟩

/-- **Filling only shrinks the frontier.** -/
theorem frontier_fill_subset [LocallyConnectedSpace Y] (hU : IsOpen U) :
    frontier (fill U) ⊆ frontier U := by
  intro ξ hξ
  rw [(isOpen_fill hU).frontier_eq] at hξ
  obtain ⟨hξcl, hξn⟩ := hξ
  have hξU : ξ ∉ U := fun h => hξn (subset_fill U h)
  rw [hU.frontier_eq]
  refine ⟨?_, hξU⟩
  by_contra hcl
  obtain ⟨O', ⟨hO'o, hξO', hO'c⟩, hO'sub⟩ :=
    (LocallyConnectedSpace.open_connected_basis ξ).mem_iff.mp
      ((isClosed_closure (s := U)).isOpen_compl.mem_nhds hcl)
  have hO'U : O' ⊆ Uᶜ := fun y hy => fun hyU => hO'sub hy (subset_closure hyU)
  have hO'C : O' ⊆ connectedComponentIn Uᶜ ξ :=
    hO'c.isPreconnected.subset_connectedComponentIn hξO' hO'U
  have hO'compl : O' ⊆ (fill U)ᶜ :=
    hO'C.trans (connectedComponentIn_subset_compl_fill hξn)
  obtain ⟨y, hyO', hyfill⟩ := mem_closure_iff.mp hξcl O' hO'o hξO'
  exact hO'compl hyO' hyfill

/-- **The filled set is bounded**: if `closure U` is compact then so is
`closure (fill U)` (ambient space connected, noncompact, locally compact,
locally connected, T2). -/
theorem isCompact_closure_fill [LocallyConnectedSpace Y] [ConnectedSpace Y]
    (hnc : ¬ CompactSpace Y) (hU : IsOpen U) (hUc : IsCompact (closure U)) :
    IsCompact (closure (fill U)) := by
  obtain ⟨L, hL, hUL⟩ := exists_compact_superset hUc
  obtain ⟨L₂, hL₂, hLL₂⟩ := exists_compact_superset hL
  set G := (L : Set Y)ᶜ with hGdef
  have hGopen : IsOpen G := hL.isClosed.isOpen_compl
  have hGU : G ⊆ Uᶜ := compl_subset_compl.mpr
    ((subset_closure.trans (hUL.trans interior_subset)))
  -- the boundary sphere of `L₂` sits inside `G`
  have hfr : frontier L₂ ⊆ G := by
    intro z hz
    have hz2 : z ∉ interior L₂ := hz.2
    exact fun hzL => hz2 (hLL₂ hzL)
  have hfrcpt : IsCompact (frontier L₂) :=
    hL₂.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans hL₂.isClosed.closure_eq.subset)
  -- cover the sphere by finitely many connected open subsets of `G`
  have hnhds : ∀ z ∈ frontier L₂, ∃ N : Set Y, IsOpen N ∧ z ∈ N ∧ IsConnected N ∧ N ⊆ G := by
    intro z hz
    obtain ⟨N, ⟨hNo, hzN, hNc⟩, hNsub⟩ :=
      (LocallyConnectedSpace.open_connected_basis z).mem_iff.mp (hGopen.mem_nhds (hfr hz))
    exact ⟨N, hNo, hzN, hNc, hNsub⟩
  choose! N hNo hNz hNc hNG using hnhds
  obtain ⟨t, htsub⟩ := hfrcpt.elim_nhds_subcover' (fun z hz => N z)
    (fun z hz => (hNo z hz).mem_nhds (hNz z hz))
  -- the candidate compact superset
  set T : Set Y := {z : Y | ∃ hz : (z : Y) ∈ frontier L₂,
    (⟨z, hz⟩ : frontier L₂) ∈ t ∧ IsCompact (closure (connectedComponentIn G z))} with hTdef
  have hTfin : T.Finite := by
    have : T ⊆ (↑) '' (t : Set (frontier L₂)) := by
      rintro z ⟨hz, hzt, -⟩
      exact ⟨⟨z, hz⟩, hzt, rfl⟩
    exact (t.finite_toSet.image _).subset this
  set M : Set Y := L₂ ∪ ⋃ z ∈ T, closure (connectedComponentIn G z) with hMdef
  have hMcpt : IsCompact M := by
    refine hL₂.union (hTfin.isCompact_biUnion ?_)
    rintro z ⟨-, -, hzc⟩
    exact hzc
  -- `fill U ⊆ M`
  have hsub : fill U ⊆ M := by
    intro y hy
    by_cases hyL₂ : y ∈ L₂
    · exact Or.inl hyL₂
    · have hyL : y ∈ G := fun hyL => hyL₂ (interior_subset (hLL₂ hyL))
      have hyU : y ∉ U := hGU hyL
      have hyC : IsCompact (connectedComponentIn Uᶜ y) := by
        rcases hy with hy | ⟨-, hy⟩
        · exact absurd hy hyU
        · exact hy
      set H := connectedComponentIn G y with hHdef
      have hHsub : H ⊆ connectedComponentIn Uᶜ y :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn hyL) ((connectedComponentIn_subset G y).trans hGU)
      have hHclcpt : IsCompact (closure H) :=
        hyC.of_isClosed_subset isClosed_closure
          ((closure_mono hHsub).trans hU.isClosed_compl.connectedComponentIn.closure_eq.subset)
      by_cases hmeet : (H ∩ frontier L₂).Nonempty
      · -- `H` is one of the finitely many boundary components
        obtain ⟨w, hwH, hwfr⟩ := hmeet
        have hwcov := htsub hwfr
        simp only [mem_iUnion] at hwcov
        obtain ⟨z, hzt, hwN⟩ := hwcov
        have hzfr : (z : Y) ∈ frontier L₂ := z.2
        have hNsubH : N z ⊆ H := by
          have h1 : N z ⊆ connectedComponentIn G w :=
            (hNc z hzfr).isPreconnected.subset_connectedComponentIn hwN (hNG z hzfr)
          rw [← connectedComponentIn_eq hwH] at h1
          exact h1
        have hzH : (z : Y) ∈ H := hNsubH (hNz z hzfr)
        have hHz : connectedComponentIn G (z : Y) = H := (connectedComponentIn_eq hzH).symm
        refine Or.inr (mem_biUnion (?_ : (z : Y) ∈ T) ?_)
        · exact ⟨hzfr, by simpa using hzt, by rw [hHz]; exact hHclcpt⟩
        · rw [hHz]
          exact subset_closure (mem_connectedComponentIn hyL)
      · -- `H` misses the sphere: it lies inside `L₂` (or is clopen — impossible)
        have hHsplit : H ⊆ interior L₂ ∪ (L₂ : Set Y)ᶜ := by
          intro w hw
          by_cases hwL₂ : w ∈ L₂
          · rcases (em (w ∈ interior L₂)) with h | h
            · exact Or.inl h
            · exact absurd ⟨w, hw, subset_closure hwL₂, h⟩ hmeet
          · exact Or.inr hwL₂
        rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior
          hL₂.isClosed.isOpen_compl
          (disjoint_compl_right.mono_left interior_subset) hHsplit with hcase | hcase
        · exact absurd (interior_subset (hcase (mem_connectedComponentIn hyL))) hyL₂
        · -- `H ⊆ L₂ᶜ` forces `H` clopen, contradicting connectedness of `Y`
          exfalso
          have hHopen : IsOpen H := hGopen.connectedComponentIn
          have hfrH : frontier H = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            rintro w ⟨hwcl, hwint⟩
            rw [hHopen.interior_eq] at hwint
            have hwG : w ∉ G := by
              intro hwG
              obtain ⟨Nw, ⟨hNwo, hwNw, hNwc⟩, hNwsub⟩ :=
                (LocallyConnectedSpace.open_connected_basis w).mem_iff.mp
                  (hGopen.mem_nhds hwG)
              obtain ⟨q, hqNw, hqH⟩ := mem_closure_iff.mp hwcl Nw hNwo hwNw
              have hNwsubH : Nw ⊆ H := by
                have h1 : Nw ⊆ connectedComponentIn G q :=
                  hNwc.isPreconnected.subset_connectedComponentIn hqNw hNwsub
                rw [← connectedComponentIn_eq hqH] at h1
                exact h1
              exact hwint (hNwsubH hwNw)
            have hwintL₂ : w ∉ interior L₂ := by
              have h1 : w ∈ closure ((L₂ : Set Y)ᶜ) := closure_mono hcase hwcl
              rw [closure_compl] at h1
              exact h1
            rw [hGdef, mem_compl_iff, not_not] at hwG
            exact hwintL₂ (hLL₂ hwG)
          have hHclopen : IsClopen H := isClopen_iff_frontier_eq_empty.mpr hfrH
          rcases isClopen_iff.mp hHclopen with h | h
          · exact absurd (h ▸ mem_connectedComponentIn hyL) (notMem_empty y)
          · have : IsCompact (univ : Set Y) := by
              have := hHclcpt
              rwa [h, closure_univ] at this
            exact hnc (isCompact_univ_iff.mp this)
  exact hMcpt.of_isClosed_subset isClosed_closure (closure_minimal hsub hMcpt.isClosed)

/-- Every compact component of `Uᶜ` meets `closure U` (otherwise it would be a
proper nonempty clopen subset of the connected noncompact ambient space). -/
theorem compact_component_meets_closure [ConnectedSpace Y] (hnc : ¬ CompactSpace Y)
    (hU : IsOpen U) (hxU : x ∉ U) (hxC : IsCompact (connectedComponentIn Uᶜ x)) :
    (connectedComponentIn Uᶜ x ∩ closure U).Nonempty := by
  by_contra hdis
  rw [not_nonempty_iff_eq_empty] at hdis
  have hsub : connectedComponentIn Uᶜ x ⊆ (closure U)ᶜ := fun y hy hycl =>
    notMem_empty y (hdis ▸ (⟨hy, hycl⟩ : y ∈ connectedComponentIn Uᶜ x ∩ closure U))
  obtain ⟨O, hOopen, hAcpt, hCA, hAΩ⟩ :=
    exists_compact_isClopenIn hU.isClosed_compl hxU hxC
      (isClosed_closure (s := U)).isOpen_compl hsub
  -- shrink `O` away from `closure U`; the piece becomes clopen in `Y`
  set O' := O ∩ (closure U)ᶜ with hO'def
  have hAO' : Uᶜ ∩ O = O' := by
    apply Subset.antisymm
    · intro y hy
      exact ⟨hy.2, hAΩ hy⟩
    · intro y hy
      have hyU : y ∉ U := fun h => hy.2 (subset_closure h)
      exact ⟨hyU, hy.1⟩
  have hO'open : IsOpen O' := hOopen.inter (isClosed_closure (s := U)).isOpen_compl
  have hO'cpt : IsCompact O' := hAO' ▸ hAcpt
  have hO'ne : O'.Nonempty := ⟨x, hAO' ▸ hCA (mem_connectedComponentIn hxU)⟩
  have hclopen : IsClopen O' := ⟨hO'cpt.isClosed, hO'open⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact absurd (h ▸ hO'ne) (by simp)
  · exact hnc (isCompact_univ_iff.mp (h ▸ hO'cpt))

omit [T2Space Y] [LocallyCompactSpace Y] in
/-- Preconnected sets can be joined along a closure-touching point. -/
private theorem isPreconnected_union_of_closure_inter {s t : Set Y} (hs : IsPreconnected s)
    (ht : IsPreconnected t) (h : (t ∩ closure s).Nonempty) :
    IsPreconnected (s ∪ t) := by
  intro u v hu hv hcov hneu hnev
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  -- each of `s`, `t` sits inside `u` or `v`
  have hone : ∀ w : Set Y, IsPreconnected w → w ⊆ s ∪ t → w ⊆ u ∨ w ⊆ v := by
    intro w hw hwsub
    by_cases hwu : (w ∩ u).Nonempty
    · by_cases hwv : (w ∩ v).Nonempty
      · obtain ⟨y, hyw, hyuv⟩ := hw u v hu hv (hwsub.trans hcov) hwu hwv
        exact absurd (show y ∈ (s ∪ t) ∩ (u ∩ v) from ⟨hwsub hyw, hyuv⟩)
          fun hyy => notMem_empty y (hempty ▸ hyy)
      · rw [not_nonempty_iff_eq_empty] at hwv
        exact Or.inl fun y hy => (hwsub.trans hcov hy).resolve_right fun h' =>
          notMem_empty y (hwv ▸ (⟨hy, h'⟩ : y ∈ w ∩ v))
    · rw [not_nonempty_iff_eq_empty] at hwu
      exact Or.inr fun y hy => (hwsub.trans hcov hy).resolve_left fun h' =>
        notMem_empty y (hwu ▸ (⟨hy, h'⟩ : y ∈ w ∩ u))
  obtain ⟨p, hpt, hpcl⟩ := h
  rcases hone s hs subset_union_left with hsu | hsv <;>
    rcases hone t ht subset_union_right with htu | htv
  · -- both in `u`: contradicts `(s ∪ t) ∩ v` nonempty
    obtain ⟨y, hyst, hyv⟩ := hnev
    have hyu : y ∈ u := hyst.elim (fun h' => hsu h') fun h' => htu h'
    exact notMem_empty y (hempty ▸ (⟨hyst, hyu, hyv⟩ : y ∈ (s ∪ t) ∩ (u ∩ v)))
  · -- `s ⊆ u`, `t ⊆ v`: the touching point produces a common point
    obtain ⟨q, hqv, hqs⟩ := mem_closure_iff.mp hpcl v hv (htv hpt)
    exact notMem_empty q (hempty ▸ (⟨Or.inl hqs, hsu hqs, hqv⟩ : q ∈ (s ∪ t) ∩ (u ∩ v)))
  · -- `s ⊆ v`, `t ⊆ u`: symmetric
    obtain ⟨q, hqu, hqs⟩ := mem_closure_iff.mp hpcl u hu (htu hpt)
    exact notMem_empty q (hempty ▸ (⟨Or.inl hqs, hqu, hsv hqs⟩ : q ∈ (s ∪ t) ∩ (u ∩ v)))
  · -- both in `v`: contradicts `(s ∪ t) ∩ u` nonempty
    obtain ⟨y, hyst, hyu⟩ := hneu
    have hyv : y ∈ v := hyst.elim (fun h' => hsv h') fun h' => htv h'
    exact notMem_empty y (hempty ▸ (⟨hyst, hyu, hyv⟩ : y ∈ (s ∪ t) ∩ (u ∩ v)))

/-- **Filling preserves connectedness.** -/
theorem isPreconnected_fill [ConnectedSpace Y] (hnc : ¬ CompactSpace Y)
    (hU : IsOpen U) (hUconn : IsPreconnected U) : IsPreconnected (fill U) := by
  by_cases hUne : U.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hUne
    have hcover : fill U = ⋃ x : fill U, (U ∪ connectedComponentIn Uᶜ (x : Y)) := by
      apply Subset.antisymm
      · intro y hy
        refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
        by_cases hyU : y ∈ U
        · exact Or.inl hyU
        · exact Or.inr (mem_connectedComponentIn hyU)
      · refine iUnion_subset ?_
        rintro ⟨y, hy⟩
        refine union_subset (subset_fill U) ?_
        rcases hy with hyU | ⟨hyU, hyC⟩
        · rw [connectedComponentIn_eq_empty (by simpa using hyU)]
          exact empty_subset _
        · exact connectedComponentIn_subset_fill hyU hyC
    rw [hcover]
    refine isPreconnected_iUnion ⟨u₀, mem_iInter.mpr fun x => Or.inl hu₀⟩ ?_
    rintro ⟨y, hy⟩
    rcases hy with hyU | ⟨hyU, hyC⟩
    · rw [connectedComponentIn_eq_empty (by simpa using hyU), union_empty]
      exact hUconn
    · exact isPreconnected_union_of_closure_inter hUconn isPreconnected_connectedComponentIn
        (compact_component_meets_closure hnc hU hyU hyC)
  · rw [not_nonempty_iff_eq_empty] at hUne
    subst hUne
    have h : fill (∅ : Set Y) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro y hy
      rcases hy with hy | ⟨-, hy⟩
      · exact hy
      · rw [compl_empty, connectedComponentIn_univ,
          PreconnectedSpace.connectedComponent_eq_univ y] at hy
        exact hnc (isCompact_univ_iff.mp hy)
    rw [h]
    exact isPreconnected_empty

theorem isConnected_fill [ConnectedSpace Y] (hnc : ¬ CompactSpace Y)
    (hU : IsOpen U) (hUconn : IsConnected U) : IsConnected (fill U) :=
  ⟨hUconn.nonempty.mono (subset_fill U), isPreconnected_fill hnc hU hUconn.isPreconnected⟩

/-! ## Structure of the complement of the filled set -/

omit [T2Space Y] [LocallyCompactSpace Y] in
/-- Components of `(fill U)ᶜ` are components of `Uᶜ`. -/
theorem connectedComponentIn_compl_fill (hx : x ∉ fill U) :
    connectedComponentIn (fill U)ᶜ x = connectedComponentIn Uᶜ x := by
  apply Subset.antisymm
  · exact connectedComponentIn_mono x (compl_subset_compl.mpr (subset_fill U))
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (notMem_fill_iff.mp hx).1)
      (connectedComponentIn_subset_compl_fill hx)

omit [T2Space Y] [LocallyCompactSpace Y] in
/-- **No compact complement components remain after filling.** -/
theorem not_isCompact_connectedComponentIn_compl_fill (hx : x ∉ fill U) :
    ¬ IsCompact (connectedComponentIn (fill U)ᶜ x) := by
  rw [connectedComponentIn_compl_fill hx]
  exact (notMem_fill_iff.mp hx).2

omit [T2Space Y] [LocallyCompactSpace Y] in
/-- Filling is idempotent. -/
theorem fill_fill (U : Set Y) : fill (fill U) = fill U := by
  apply Subset.antisymm
  · intro x hx
    rcases hx with hx | ⟨hxf, hxC⟩
    · exact hx
    · exact absurd hxC (not_isCompact_connectedComponentIn_compl_fill hxf)
  · exact subset_fill (fill U)

/-- On a connected noncompact space, a nonempty `U` with compact closure has a
filled hull with nonempty frontier. -/
theorem nonempty_frontier_fill [LocallyConnectedSpace Y] [ConnectedSpace Y]
    (hnc : ¬ CompactSpace Y) (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUne : U.Nonempty) : (frontier (fill U)).Nonempty := by
  by_contra hfr
  rw [not_nonempty_iff_eq_empty] at hfr
  have hclopen : IsClopen (fill U) := isClopen_iff_frontier_eq_empty.mpr hfr
  rcases isClopen_iff.mp hclopen with h | h
  · obtain ⟨u₀, hu₀⟩ := hUne
    exact absurd (h ▸ subset_fill U hu₀) (notMem_empty u₀)
  · have hcpt := isCompact_closure_fill hnc hU hUc
    rw [h, closure_univ] at hcpt
    exact hnc (isCompact_univ_iff.mp hcpt)

section Components

variable {Y : Type*} [TopologicalSpace Y] [LocallyConnectedSpace Y] {U : Set Y} {x : Y}

/-- The frontier of a connected component of an open set lies in the frontier
of the set (locally connected ambient space). -/
theorem frontier_connectedComponentIn_subset (hU : IsOpen U) :
    frontier (connectedComponentIn U x) ⊆ frontier U := by
  intro ξ hξ
  have hCo : IsOpen (connectedComponentIn U x) := hU.connectedComponentIn
  rw [hCo.frontier_eq] at hξ
  obtain ⟨hξcl, hξn⟩ := hξ
  rw [hU.frontier_eq]
  refine ⟨closure_mono (connectedComponentIn_subset U x) hξcl, fun hξU => hξn ?_⟩
  obtain ⟨N, ⟨hNo, hξN, hNc⟩, hNsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis ξ).mem_iff.mp (hU.mem_nhds hξU)
  obtain ⟨q, hqN, hqC⟩ := mem_closure_iff.mp hξcl N hNo hξN
  have hNC : N ⊆ connectedComponentIn U q :=
    hNc.isPreconnected.subset_connectedComponentIn hqN hNsub
  rw [← connectedComponentIn_eq hqC] at hNC
  exact hNC hξN

end Components

end HoleFill

/-! ## Exterior disks survive filling -/

section Surface

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The exterior disk condition is antitone in the set. -/
theorem ExteriorDiskAt.anti {W W' : Set X} {ξ : X} (h : ExteriorDiskAt W ξ)
    (hsub : W' ⊆ W) : ExteriorDiskAt W' ξ := by
  obtain ⟨e, he, hξe, c, r, hr, hcball, hdist, hmiss⟩ := h
  exact ⟨e, he, hξe, c, r, hr, hcball, hdist,
    fun x hx => hmiss x ⟨hsub hx.1, hx.2⟩⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **Exterior-disk regularity survives hole-filling**: an exterior disk for
`U` at a frontier point of `fill U` is an exterior disk for `fill U`. The
disk's interior is connected and misses `U`; were it to meet `fill U`, it
would lie in one compact complement component, whose closure contains the
frontier point — contradicting openness of `fill U`. -/
theorem ExteriorDiskAt.fill [T2Space X] {U : Set X} (hU : IsOpen U) {ξ : X}
    (hξ : ξ ∈ frontier (Uniformization.fill U)) (hext : ExteriorDiskAt U ξ) :
    ExteriorDiskAt (Uniformization.fill U) ξ := by
  haveI : LocallyCompactSpace X := locallyCompactSpace
  obtain ⟨e, he, hξe, c, r, hr, hcball, hdist, hmiss⟩ := hext
  refine ⟨e, he, hξe, c, r, hr, hcball, hdist, ?_⟩
  rintro x ⟨hxfill, hxe⟩ hxball
  -- the carrier of the exterior disk
  set B := e.symm '' ball c r with hBdef
  have hballt : ball c r ⊆ e.target := ball_subset_closedBall.trans hcball
  have hxB : x ∈ B := ⟨e x, hxball, e.left_inv hxe⟩
  have hBU : B ⊆ Uᶜ := by
    rintro _ ⟨w, hw, rfl⟩ hyU
    have hwt : w ∈ e.target := hballt hw
    have hys : e.symm w ∈ e.source := e.map_target hwt
    have := hmiss (e.symm w) ⟨hyU, hys⟩
    rw [e.right_inv hwt] at this
    exact this hw
  have hBconn : IsPreconnected B :=
    (convex_ball c r).isPreconnected.image _ (e.symm.continuousOn.mono (by simpa using hballt))
  have hxU : x ∉ U := hBU hxB
  -- `x` is a filled point, so its complement component is compact and swallows `B`
  have hxC : IsCompact (connectedComponentIn Uᶜ x) := by
    rcases hxfill with h | ⟨-, h⟩
    · exact absurd h hxU
    · exact h
  have hBC : B ⊆ connectedComponentIn Uᶜ x :=
    hBconn.subset_connectedComponentIn hxB hBU
  -- the frontier point lies in the closure of the disk carrier
  have hξB : ξ ∈ closure B := by
    have hξt : e ξ ∈ closure (ball c r) := by
      rw [closure_ball c hr.ne']
      exact mem_closedBall.mpr hdist.le
    have hsc : ContinuousWithinAt e.symm (ball c r) (e ξ) :=
      (e.continuousAt_symm (e.map_source hξe)).continuousWithinAt
    have := hsc.mem_closure_image hξt
    rwa [e.left_inv hξe] at this
  -- hence in the compact component, hence in `fill U`: contradiction
  have hξC : ξ ∈ connectedComponentIn Uᶜ x :=
    (closure_mono hBC).trans hU.isClosed_compl.connectedComponentIn.closure_eq.subset hξB
  have hξfill : ξ ∈ Uniformization.fill U := connectedComponentIn_subset_fill hxU hxC hξC
  rw [(isOpen_fill hU).frontier_eq] at hξ
  exact hξ.2 hξfill

end Surface

end Uniformization
