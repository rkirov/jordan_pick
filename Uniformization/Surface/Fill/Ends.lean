/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.EndConnectedFinal
import Rado.Surface.Assembly

/-!
# Ends of a level piece: finiteness and escaping rays (W7 step D1/D2)

Two independent point-set deliverables for a connected level piece `V` with
compact closure in a Riemann surface `X`.

* `finite_ends` (**D1**): the set of connected components of `(closure V)ᶜ`
  (the *ends* of the complement) is finite.  Each end has a nonempty frontier
  inside the compact `frontier V`; the local straightening boxes
  (`exists_lower_half`) cover `frontier V` by finitely many pieces, each pinned
  to a single end, and every end is hit — so the ends inject into a finite set.

* `exists_escaping_ray` (**D2**): a noncompact end `Z` admits, from any base
  point `z₀ ∈ Z`, a continuous ray `δ : ℝ → X` (on `Ici 0`) inside `Z` that is
  *proper*: it eventually leaves every compact subset of `Z`.  This is pure
  topology of the open connected σ-compact locally compact locally path
  connected subspace `Z`: a compact exhaustion is refined into a decreasing
  chain of complement components with noncompact closure (the key existence,
  `exists_noncompact_subcomponent`, is a clustering argument on the boundary
  spheres), and the ray is concatenated along the chain.
-/

open Set Topology Filter
open scoped unitInterval

namespace Uniformization

open Rado

/-! ## The noncompact-subcomponent step (abstract topology) -/

/-- **Key existence step for the escaping ray.**  In a locally compact, locally
connected, preconnected Hausdorff space `W` with a compact exhaustion `Kex`, if
`C = connectedComponentIn (Kex n)ᶜ a` is a complement component whose closure is
*not* compact, then inside `C` there is a point `b` outside `Kex (n+1)` whose
component in `(Kex (n+1))ᶜ` again has noncompact closure.

Proof by contradiction: were every such subcomponent to have compact closure,
only finitely many could occur (a finite union of their closures is compact and
lies in some `Kex p`, contradicting that `C` escapes every `Kex m`).  The
infinitely many distinct subcomponents each cross the boundary sphere
`frontier (Kex (n+2))` (they run from `frontier (Kex (n+1))` out past
`Kex (n+2)`); the crossing points, an infinite subset of the compact sphere,
accumulate at a point `y*` outside `Kex (n+1)`, whose connected neighbourhood
lies in a single component — forcing infinitely many distinct components to
coincide, a contradiction. -/
private theorem exists_noncompact_subcomponent {W : Type*} [TopologicalSpace W]
    [T2Space W] [LocallyCompactSpace W] [LocallyConnectedSpace W] [PreconnectedSpace W]
    (Kex : CompactExhaustion W) {n : ℕ} {a : W} (_ha : a ∉ Kex n)
    (hnc : ¬ IsCompact (closure (connectedComponentIn (Kex n)ᶜ a))) :
    ∃ b : W, b ∉ Kex (n + 1) ∧ b ∈ connectedComponentIn (Kex n)ᶜ a ∧
      ¬ IsCompact (closure (connectedComponentIn (Kex (n + 1))ᶜ b)) := by
  classical
  set C := connectedComponentIn (Kex n)ᶜ a with hCdef
  -- basic openness / non-compactness facts
  haveI : Nonempty W := ⟨a⟩
  have hWnc : ¬ CompactSpace W := by
    intro hc; haveI := hc; exact hnc isClosed_closure.isCompact
  have hFopen : IsOpen ((Kex (n + 1))ᶜ) := (Kex.isCompact (n + 1)).isClosed.isOpen_compl
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ b, b ∉ Kex (n+1) → b ∈ C → IsCompact (closure (cc (n+1) b))`
  -- escaping points of `C`
  have hesc : ∀ m, ∃ x, x ∈ C ∧ x ∉ Kex m := by
    intro m
    by_contra h
    push Not at h
    exact hnc ((Kex.isCompact m).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => h x hx) (Kex.isCompact m).isClosed))
  choose c hcC hcK using hesc
  -- the candidate subcomponents
  set D : ℕ → Set W := fun m => connectedComponentIn (Kex (n + 1))ᶜ (c m) with hDdef
  have hcF : ∀ m, n + 1 ≤ m → c m ∈ (Kex (n + 1))ᶜ := by
    intro m hm hmem
    exact hcK m (Kex.subset hm hmem)
  have hcD : ∀ m, n + 1 ≤ m → c m ∈ D m := fun m hm => mem_connectedComponentIn (hcF m hm)
  have hDcompact : ∀ m, n + 1 ≤ m → IsCompact (closure (D m)) := by
    intro m hm
    exact hcon (c m) (hcF m hm) (hcC m)
  -- `R` = set of subcomponents arising at levels `≥ n+2`
  set R : Set (Set W) := {D' | ∃ m, n + 2 ≤ m ∧ D' = D m} with hRdef
  -- `R` is infinite (else its closures cover a compact `Kex p`, contradicting escape)
  have hRinf : R.Infinite := by
    intro hRfin
    have hUcompact : IsCompact (⋃ D' ∈ R, closure D') := by
      refine hRfin.isCompact_biUnion ?_
      rintro D' ⟨m, hm, rfl⟩
      exact hDcompact m (by omega)
    obtain ⟨p, hp⟩ := Kex.exists_superset_of_isCompact hUcompact
    set m := max p (n + 2) with hmdef
    have hm2 : n + 2 ≤ m := le_max_right _ _
    have hmp : p ≤ m := le_max_left _ _
    have hcmDm : c m ∈ D m := hcD m (by omega)
    have hcmU : c m ∈ ⋃ D' ∈ R, closure D' :=
      mem_biUnion ⟨m, hm2, rfl⟩ (subset_closure hcmDm)
    exact hcK m (Kex.subset hmp (hp hcmU))
  -- every subcomponent in `R` meets the boundary sphere `frontier (Kex (n+2))`
  have hcross : ∀ D' ∈ R, (D' ∩ frontier (Kex (n + 2))).Nonempty := by
    rintro D' ⟨m, hm, rfl⟩
    have hDopen : IsOpen (D m) := hFopen.connectedComponentIn
    have hcmDm : c m ∈ D m := hcD m (by omega)
    -- `frontier (D m) ⊆ Kex (n+1) ⊆ interior (Kex (n+2))`
    have hfrsub : frontier (D m) ⊆ Kex (n + 1) := by
      have h1 : frontier (D m) ⊆ frontier ((Kex (n + 1))ᶜ) :=
        frontier_connectedComponentIn_subset (U := (Kex (n + 1))ᶜ) (x := c m) hFopen
      rw [frontier_compl] at h1
      exact h1.trans (Kex.isCompact (n + 1)).isClosed.frontier_subset
    have hfrint : frontier (D m) ⊆ interior (Kex (n + 2)) :=
      hfrsub.trans (Kex.subset_interior_succ (n + 1))
    -- `frontier (D m)` is nonempty (else `D m` is clopen ⇒ `= univ` ⇒ `W` compact)
    have hfrne : (frontier (D m)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hclopen : IsClopen (D m) := isClopen_iff_frontier_eq_empty.mpr hemp
      rcases isClopen_iff.mp hclopen with h | h
      · exact absurd (h ▸ hcmDm) (Set.notMem_empty _)
      · refine hWnc ?_
        rw [← isCompact_univ_iff]
        have := hDcompact m (by omega)
        rwa [h, closure_univ] at this
    obtain ⟨w, hwfr⟩ := hfrne
    have hwcl : w ∈ closure (D m) := hwfr.1
    obtain ⟨w', hw'int, hw'D⟩ :=
      _root_.mem_closure_iff.mp hwcl (interior (Kex (n + 2))) isOpen_interior (hfrint hwfr)
    have hcmnot : c m ∉ Kex (n + 2) := fun h => hcK m (Kex.subset hm h)
    have hpre : IsPreconnected (D m) := isPreconnected_connectedComponentIn
    have hdisj : Disjoint (interior (Kex (n + 2))) ((Kex (n + 2))ᶜ) :=
      disjoint_compl_right.mono_left interior_subset
    have hnotsub : ¬ (D m ⊆ interior (Kex (n + 2)) ∪ (Kex (n + 2))ᶜ) := by
      intro hsub
      rcases hpre.subset_or_subset isOpen_interior
          (Kex.isCompact (n + 2)).isClosed.isOpen_compl hdisj hsub with h | h
      · exact hcmnot (interior_subset (h hcmDm))
      · exact (h hw'D) (interior_subset hw'int)
    obtain ⟨z, hzD, hznotU⟩ := Set.not_subset.mp hnotsub
    rw [Set.mem_union, not_or] at hznotU
    obtain ⟨hzni, hznc⟩ := hznotU
    have hzK : z ∈ Kex (n + 2) := not_not.mp hznc
    have hzfr : z ∈ frontier (Kex (n + 2)) := by
      rw [(Kex.isCompact (n + 2)).isClosed.frontier_eq]
      exact ⟨hzK, hzni⟩
    exact ⟨z, hzD, hzfr⟩
  -- choose one crossing point per subcomponent
  choose! Dpt hDpt using hcross
  set Y : Set W := Dpt '' R with hYdef
  have hYsub : Y ⊆ frontier (Kex (n + 2)) := by
    rintro _ ⟨D', hD'R, rfl⟩; exact (hDpt D' hD'R).2
  -- `Dpt` is injective on `R` (distinct components are disjoint)
  have hInjOn : Set.InjOn Dpt R := by
    rintro D₁ h₁ D₂ h₂ heq
    obtain ⟨m₁, hm₁, rfl⟩ := h₁
    obtain ⟨m₂, hm₂, rfl⟩ := h₂
    have hw1 : Dpt (D m₁) ∈ D m₁ := (hDpt (D m₁) ⟨m₁, hm₁, rfl⟩).1
    have hw2 : Dpt (D m₂) ∈ D m₂ := (hDpt (D m₂) ⟨m₂, hm₂, rfl⟩).1
    have e1 : D m₁ = connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₁)) :=
      connectedComponentIn_eq hw1
    have e2 : D m₂ = connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₂)) :=
      connectedComponentIn_eq hw2
    rw [e1, e2, heq]
  have hYinf : Y.Infinite := (Set.infinite_image_iff hInjOn).mpr hRinf
  -- the sphere is compact ⇒ accumulation point of `Y`
  have hSphcpt : IsCompact (frontier (Kex (n + 2))) :=
    (Kex.isCompact (n + 2)).of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (Kex.isCompact (n + 2)).isClosed.closure_eq.subset)
  obtain ⟨ys, hysmem, hAcc⟩ := hYinf.exists_accPt_of_subset_isCompact hSphcpt hYsub
  -- `ys ∉ Kex (n+1)`
  have hysint : ys ∉ interior (Kex (n + 2)) := by
    have := (Kex.isCompact (n + 2)).isClosed.frontier_eq ▸ hysmem
    exact this.2
  have hysF : ys ∈ (Kex (n + 1))ᶜ := fun hy =>
    hysint (Kex.subset_interior_succ (n + 1) hy)
  -- a connected open neighbourhood of `ys` inside `(Kex (n+1))ᶜ`
  obtain ⟨N, ⟨hNo, hysN, hNconn⟩, hNF⟩ :=
    (LocallyConnectedSpace.open_connected_basis ys).mem_iff.mp (hFopen.mem_nhds hysF)
  have hND : N ⊆ connectedComponentIn (Kex (n + 1))ᶜ ys :=
    hNconn.isPreconnected.subset_connectedComponentIn hysN hNF
  -- `Y ∩ N` accumulates at `ys`, hence is infinite
  have hAcc2 : AccPt ys (𝓟 (Y ∩ N)) := by
    rw [accPt_iff_nhds] at hAcc ⊢
    intro U hU
    obtain ⟨w, ⟨hwU, hwY⟩, hwne⟩ := hAcc (U ∩ N) (Filter.inter_mem hU (hNo.mem_nhds hysN))
    exact ⟨w, ⟨hwU.1, hwY, hwU.2⟩, hwne⟩
  have hYNinf : (Y ∩ N).Infinite := Set.Infinite.of_accPt hAcc2
  -- but every point of `Y ∩ N` lies in the single component through `ys`, so `Y ∩ N`
  -- is a subsingleton
  have hSub : (Y ∩ N).Subsingleton := by
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨hw₁Y, hw₁N⟩ := hw₁
    obtain ⟨hw₂Y, hw₂N⟩ := hw₂
    obtain ⟨D₁, hD₁R, rfl⟩ := hw₁Y
    obtain ⟨D₂, hD₂R, rfl⟩ := hw₂Y
    have hd1 : Dpt D₁ ∈ D₁ := (hDpt D₁ hD₁R).1
    have hd2 : Dpt D₂ ∈ D₂ := (hDpt D₂ hD₂R).1
    -- `D₁ = cc (Dpt D₁) = cc ys = cc (Dpt D₂) = D₂`
    obtain ⟨m₁, _, rfl⟩ := hD₁R
    obtain ⟨m₂, _, rfl⟩ := hD₂R
    have e1 : D m₁ = connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₁)) :=
      connectedComponentIn_eq hd1
    have e2 : D m₂ = connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₂)) :=
      connectedComponentIn_eq hd2
    have f1 : connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₁))
        = connectedComponentIn (Kex (n + 1))ᶜ ys :=
      (connectedComponentIn_eq (hND hw₁N)).symm
    have f2 : connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₂))
        = connectedComponentIn (Kex (n + 1))ᶜ ys :=
      (connectedComponentIn_eq (hND hw₂N)).symm
    have : D m₁ = D m₂ := by rw [e1, f1, ← f2, ← e2]
    rw [this]
  exact hYNinf hSub.finite

/-! ## D1 — finitely many ends -/

section Surface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **D1: finitely many ends.**  Under the standard piece hypotheses (with `V`
nonempty and `X` connected), the set of connected components of the open
complement `(closure V)ᶜ` is finite.

Each end has a nonempty frontier inside the compact `frontier V`; covering
`frontier V` by finitely many straightening boxes (`exists_lower_half`), whose
connected lower halves each land in one end, shows every end is the end of some
box.  Thus the ends inject into a finite index set. -/
theorem finite_ends [T2Space X] [ConnectedSpace X] {V : Set X} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) (hVne : V.Nonempty) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0) :
    {Z : Set X | ∃ x, x ∈ (closure V)ᶜ ∧ Z = connectedComponentIn (closure V)ᶜ x}.Finite := by
  classical
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  set S := (closure V)ᶜ with hSdef
  have hfrcpt : IsCompact (frontier V) :=
    hVcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  -- straightening boxes at each frontier point
  choose! Wf hWo hWmem hWpre hWclos hWfront using
    fun ξ (hξ : ξ ∈ frontier V) => exists_lower_half hVo hdich hfc hchart hξ
  -- finite subcover of `frontier V`
  obtain ⟨t, htsub, htfin, htcov⟩ := hfrcpt.elim_finite_subcover_image hWo
    (fun ξ hξ => Set.mem_biUnion hξ (hWmem ξ hξ))
  -- each box's lower half is nonempty; pick a point
  have hHne : ∀ ξ ∈ frontier V, (Wf ξ ∩ S).Nonempty := fun ξ hξ =>
    closure_nonempty_iff.mp ⟨ξ, hWclos ξ hξ⟩
  set g : X → X := fun ξ => if h : ξ ∈ frontier V then (hHne ξ h).some else ξ with hgdef
  refine Set.Finite.subset (Set.Finite.image (fun ξ => connectedComponentIn S (g ξ)) htfin) ?_
  rintro Z ⟨x, hxS, rfl⟩
  -- the end has a nonempty frontier
  obtain ⟨ζ, hζ⟩ := nonempty_frontier_component_compl_closure hVne hxS
  have hζfrV : ζ ∈ frontier V := frontier_component_compl_closure_subset hζ
  obtain ⟨ξ, hξt, hζW⟩ := mem_iUnion₂.mp (htcov hζfrV)
  -- `Wf ξ` meets the end
  have hζZbar : ζ ∈ closure (connectedComponentIn S x) := frontier_subset_closure hζ
  obtain ⟨p, hpW, hpZ⟩ :=
    _root_.mem_closure_iff.1 hζZbar (Wf ξ) (hWo ξ (htsub hξt)) hζW
  have hpS : p ∈ S := connectedComponentIn_subset _ _ hpZ
  have hpH : p ∈ Wf ξ ∩ S := ⟨hpW, hpS⟩
  have hgH : g ξ ∈ Wf ξ ∩ S := by
    rw [hgdef]; simp only [dif_pos (htsub hξt)]; exact (hHne ξ (htsub hξt)).some_mem
  -- both `p` and `g ξ` lie in the preconnected lower half ⊆ `S`
  have hHpre : IsPreconnected (Wf ξ ∩ S) := hWpre ξ (htsub hξt)
  have hHZg : Wf ξ ∩ S ⊆ connectedComponentIn S (g ξ) :=
    hHpre.subset_connectedComponentIn hgH inter_subset_right
  have hpcomp : connectedComponentIn S p = connectedComponentIn S (g ξ) :=
    (connectedComponentIn_eq (hHZg hpH)).symm
  have : connectedComponentIn S x = connectedComponentIn S (g ξ) := by
    rw [connectedComponentIn_eq hpZ, hpcomp]
  rw [this]
  exact Set.mem_image_of_mem _ hξt

/-! ## D2 — an escaping ray out of a noncompact end -/

/-- **D2: escaping ray.**  For a noncompact end `Z = connectedComponentIn
`(closure V)ᶜ x₀`` and a base point `z₀ ∈ Z`, there is a continuous ray
`δ : ℝ → X` (on `Ici 0`) starting at `z₀`, staying inside `Z`, and *proper*: it
eventually leaves every compact subset `K ⊆ Z`.

The subspace `Z` is open, connected, second countable, locally compact, and
locally path connected.  A compact exhaustion is refined, via
`exists_noncompact_subcomponent`, into a decreasing chain of complement
components `C n` with noncompact closure and `C n ∩ Kex n = ∅`; picking
`z n ∈ C n` and concatenating paths `z n → z (n+1)` inside `C n` gives the ray,
whose tail after time `n+1` avoids `Kex n`, hence escapes. -/
theorem exists_escaping_ray [T2Space X] [ConnectedSpace X] {V : Set X} {x₀ : X}
    (hZnc : ¬ IsCompact (connectedComponentIn (closure V)ᶜ x₀))
    {z₀ : X} (hz₀ : z₀ ∈ connectedComponentIn (closure V)ᶜ x₀) :
    ∃ δ : ℝ → X, ContinuousOn δ (Set.Ici 0) ∧ δ 0 = z₀ ∧
      (∀ t ∈ Set.Ici (0 : ℝ), δ t ∈ connectedComponentIn (closure V)ᶜ x₀) ∧
      ∀ K : Set X, IsCompact K → K ⊆ connectedComponentIn (closure V)ᶜ x₀ →
        ∃ T : ℝ, ∀ t, T ≤ t → δ t ∉ K := by
  classical
  haveI : LocallyCompactSpace X := Rado.locallyCompactSpace
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  haveI : SecondCountableTopology X := Rado.secondCountableTopology_of_riemannSurface
  set Z := connectedComponentIn (closure V)ᶜ x₀ with hZdef
  have hZopen : IsOpen Z := isClosed_closure.isOpen_compl.connectedComponentIn
  have hZconn : IsConnected Z := ⟨⟨z₀, hz₀⟩, isPreconnected_connectedComponentIn⟩
  -- subspace instances
  haveI hWlc : LocallyCompactSpace ↥Z := hZopen.locallyCompactSpace
  haveI hWsc : SecondCountableTopology ↥Z := inferInstance
  haveI hWsigma : SigmaCompactSpace ↥Z := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI hWconn : ConnectedSpace ↥Z := Subtype.connectedSpace hZconn
  haveI hWlpc : LocallyPathConnectedSpace ↥Z := hZopen.locallyPathConnectedSpace
  haveI hWlconn : LocallyConnectedSpace ↥Z := hZopen.locallyConnectedSpace
  have hWncs : ¬ CompactSpace ↥Z := fun hc => hZnc (isCompact_iff_compactSpace.mpr hc)
  -- compact exhaustion of `↥Z` with `Kex 0 = ∅`
  set Kex : CompactExhaustion ↥Z := (default : CompactExhaustion ↥Z).shiftr with hKexdef
  have hK0 : (Kex 0 : Set ↥Z) = ∅ := rfl
  have hbase0 : (⟨z₀, hz₀⟩ : ↥Z) ∉ Kex 0 := by rw [hK0]; exact Set.notMem_empty _
  have hbase : ¬ IsCompact (closure (connectedComponentIn (Kex 0)ᶜ (⟨z₀, hz₀⟩ : ↥Z))) := by
    rw [hK0, compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ, closure_univ, isCompact_univ_iff]
    exact hWncs
  -- the decreasing chain of noncompact-closure complement components
  let A : (m : ℕ) →
      {x : ↥Z // x ∉ Kex m ∧ ¬ IsCompact (closure (connectedComponentIn (Kex m)ᶜ x))} :=
    fun m => Nat.rec
      (motive := fun m =>
        {x : ↥Z // x ∉ Kex m ∧ ¬ IsCompact (closure (connectedComponentIn (Kex m)ᶜ x))})
      ⟨⟨z₀, hz₀⟩, hbase0, hbase⟩
      (fun k ih => ⟨(exists_noncompact_subcomponent Kex ih.2.1 ih.2.2).choose,
        (exists_noncompact_subcomponent Kex ih.2.1 ih.2.2).choose_spec.1,
        (exists_noncompact_subcomponent Kex ih.2.1 ih.2.2).choose_spec.2.2⟩)
      m
  set a : ℕ → ↥Z := fun m => (A m).1 with hadef
  have ha_not : ∀ m, a m ∉ Kex m := fun m => (A m).2.1
  have hlink : ∀ m, a (m + 1) ∈ connectedComponentIn (Kex m)ᶜ (a m) := fun m =>
    (exists_noncompact_subcomponent Kex (A m).2.1 (A m).2.2).choose_spec.2.1
  -- the components and their paths
  have hCopen : ∀ m, IsOpen (connectedComponentIn (Kex m)ᶜ (a m)) := fun m =>
    ((Kex.isCompact m).isClosed.isOpen_compl).connectedComponentIn
  have hanC : ∀ m, a m ∈ connectedComponentIn (Kex m)ᶜ (a m) := fun m =>
    mem_connectedComponentIn (ha_not m)
  have hCconn : ∀ m, IsConnected (connectedComponentIn (Kex m)ᶜ (a m)) := fun m =>
    ⟨⟨a m, hanC m⟩, isPreconnected_connectedComponentIn⟩
  have hCpc : ∀ m, IsPathConnected (connectedComponentIn (Kex m)ᶜ (a m)) := fun m =>
    ((hCopen m).isConnected_iff_isPathConnected).mp (hCconn m)
  have hjoin : ∀ m, JoinedIn (connectedComponentIn (Kex m)ᶜ (a m)) (a m) (a (m + 1)) := fun m =>
    (hCpc m).joinedIn (a m) (hanC m) (a (m + 1)) (hlink m)
  let p : ∀ m, Path (a m) (a (m + 1)) := fun m => (hjoin m).somePath
  have hpmem : ∀ m (t : ↑I), p m t ∈ connectedComponentIn (Kex m)ᶜ (a m) := fun m t =>
    (hjoin m).somePath_mem t
  -- the ray by concatenation of the paths across integer intervals
  let ray : ℝ → ↥Z := fun s => (p ⌊s⌋₊).extend (s - ⌊s⌋₊)
  -- each piece of the ray lies in the corresponding component
  have hraymem : ∀ s : ℝ, ray s ∈ connectedComponentIn (Kex ⌊s⌋₊)ᶜ (a ⌊s⌋₊) := by
    intro s
    have hmem_range : ray s ∈ Set.range (p ⌊s⌋₊) := by
      rw [← Path.extend_range]; exact ⟨s - ⌊s⌋₊, rfl⟩
    obtain ⟨u, hu⟩ := hmem_range
    rw [← hu]; exact hpmem ⌊s⌋₊ u
  -- continuity of the ray on `Ici 0`
  have hcover : Set.Ici (0 : ℝ) = ⋃ n : ℕ, Set.Icc (n : ℝ) (n + 1) := by
    ext t
    simp only [Set.mem_Ici, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · intro ht; exact ⟨⌊t⌋₊, Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
    · rintro ⟨n, hn, _⟩; exact le_trans (Nat.cast_nonneg n) hn
  have hlf : LocallyFinite (fun n : ℕ => Set.Icc (n : ℝ) (n + 1)) := by
    intro x
    refine ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    apply Set.Finite.subset (Set.finite_Iic (⌊x + 1⌋₊ : ℕ))
    intro n hn
    obtain ⟨y, ⟨hy1, _⟩, _, hy4⟩ := hn
    rw [Set.mem_Iic]
    exact Nat.le_floor (le_of_lt (lt_of_le_of_lt hy1 hy4))
  have hcont_piece : ∀ N : ℕ, ContinuousOn ray (Set.Icc (N : ℝ) (N + 1)) := by
    intro N
    have hcont_hn : Continuous (fun s : ℝ => (p N).extend (s - N)) :=
      (p N).continuous_extend.comp (by fun_prop)
    apply hcont_hn.continuousOn.congr
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have hfloor : ⌊t⌋₊ = N := by
        rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg N) ht.1)]; exact ⟨ht.1, hlt⟩
      show (p ⌊t⌋₊).extend (t - (⌊t⌋₊ : ℝ)) = (p N).extend (t - N)
      rw [hfloor]
    · show (p ⌊t⌋₊).extend (t - (⌊t⌋₊ : ℝ)) = (p N).extend (t - N)
      have hfloor : ⌊t⌋₊ = N + 1 := by
        rw [heq, show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
      rw [hfloor, heq, show ((N : ℝ) + 1 - ((N + 1 : ℕ) : ℝ)) = 0 by push_cast; ring,
        show ((N : ℝ) + 1 - (N : ℝ)) = 1 by ring, Path.extend_zero, Path.extend_one]
  have hraycont : ContinuousOn ray (Set.Ici 0) := by
    rw [hcover]
    exact hlf.continuousOn_iUnion (fun _ => isClosed_Icc) hcont_piece
  -- package the ray in `X`
  refine ⟨fun t => (ray t : X), ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp_continuousOn hraycont
  · show (ray 0 : X) = z₀
    have hray0 : ray 0 = a 0 := by
      show (p ⌊(0 : ℝ)⌋₊).extend (0 - (⌊(0 : ℝ)⌋₊ : ℝ)) = a 0
      rw [Nat.floor_zero]
      simp only [Nat.cast_zero, sub_zero]
      rw [Path.extend_zero]
    rw [hray0]; rfl
  · exact fun t _ => (ray t).2
  · intro K hK hKZ
    have hKZrange : K ⊆ Set.range (Subtype.val : ↥Z → X) := by
      rw [Subtype.range_coe]; exact hKZ
    have hpre_compact : IsCompact (Subtype.val ⁻¹' K : Set ↥Z) :=
      IsInducing.subtypeVal.isCompact_preimage' hK hKZrange
    obtain ⟨N, hN⟩ := Kex.exists_superset_of_isCompact hpre_compact
    refine ⟨(N : ℝ), ?_⟩
    intro t htN
    have hfloorN : N ≤ ⌊t⌋₊ := Nat.le_floor htN
    have hnotKt : ray t ∉ Kex ⌊t⌋₊ := connectedComponentIn_subset _ _ (hraymem t)
    have hnotKN : ray t ∉ Kex N := fun h => hnotKt (Kex.subset hfloorN h)
    intro hcontra
    exact hnotKN (hN hcontra)

end Surface

end Uniformization
