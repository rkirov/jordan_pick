/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.Ends
import Uniformization.Surface.Fill.CircleParam

/-!
# Collapse of the complement ends onto `closure V` (W7 steps L5.5–L8)

This file assembles the **retraction** `r : C(X, X)` of the ambient simply
connected surface onto `closure V`, the object that drives the final
simple-connectivity transfer in `Fill.lean`:

* `isSimplyConnected_of_retract` (`Fill/Retraction.lean`) turns the retraction
  into `IsSimplyConnected (closure V)`;
* `isSimplyConnected_of_closure` (`Fill/Push.lean`) pushes that across the
  inner collar to `IsSimplyConnected V`.

The mathematical content is the Anghel–Stan ray-cut Tietze collapse: each end
`Z` (a component of `(closure V)ᶜ`, of which there are finitely many by
`finite_ends`, each noncompact by `not_isCompact_end`) carries a continuous
**collapse** map `h_Z : X → X` fixing everything outside `Z` and mapping `Z`
into `closure V`.  Because distinct ends are disjoint and every `h_Z` fixes
`closure V`, the finitely many collapses **compose** (via `compList`) to a
single retraction — no simultaneous closed-cover pasting is needed.

The per-end collapse `exists_end_collapse` is the remaining geometric input
(escaping ray + two-sided collar + Tietze extension of the angular coordinate);
everything else in this file — the composition bookkeeping
(`compList_collapse`), the noncompactness of every end (`not_isCompact_end`),
and the global assembly (`exists_retraction_onto_closure`) — is discharged here.
-/

open Set Metric Topology

namespace Uniformization

open Rado

section Composition

variable {X : Type*} [TopologicalSpace X]

/-- **Composition of disjoint-support collapses.**  A list of continuous
self-maps, each fixing everything outside its associated set `p.2`, each mapping
`p.2` into a common target `T`, and each with `p.2` disjoint from `T`, composes
(head-first, via `compList`) to a map that fixes `T` pointwise and sends every
point of `T ∪ ⋃ p.2` into `T`. -/
theorem compList_collapse (l : List (C(X, X) × Set X)) {T : Set X}
    (hid : ∀ p ∈ l, ∀ x ∉ p.2, p.1 x = x)
    (hmap : ∀ p ∈ l, ∀ x ∈ p.2, p.1 x ∈ T)
    (hdisj : ∀ p ∈ l, Disjoint T p.2) :
    (∀ x ∈ T, compList l x = x) ∧
    (∀ x, (x ∈ T ∨ ∃ p ∈ l, x ∈ p.2) → compList l x ∈ T) := by
  induction l with
  | nil =>
    refine ⟨fun x _ => rfl, fun x hx => ?_⟩
    rcases hx with h | ⟨p, hp, _⟩
    · simpa using h
    · simp at hp
  | cons p l ih =>
    have hid' := fun q hq => hid q (List.mem_cons_of_mem _ hq)
    have hmap' := fun q hq => hmap q (List.mem_cons_of_mem _ hq)
    have hdisj' := fun q hq => hdisj q (List.mem_cons_of_mem _ hq)
    obtain ⟨ihA, ihB⟩ := ih hid' hmap' hdisj'
    have hpid : ∀ x ∉ p.2, p.1 x = x := hid p (List.mem_cons_self ..)
    have hpmap : ∀ x ∈ p.2, p.1 x ∈ T := hmap p (List.mem_cons_self ..)
    have hpdisj : Disjoint T p.2 := hdisj p (List.mem_cons_self ..)
    have hToff : ∀ x ∈ T, p.1 x = x := fun x hx =>
      hpid x (Set.disjoint_left.mp hpdisj hx)
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [compList_cons, hToff x hx]; exact ihA x hx
    · rw [compList_cons]
      apply ihB
      rcases hx with hxT | ⟨q, hq, hxq⟩
      · left; rw [hToff x hxT]; exact hxT
      · rcases List.mem_cons.mp hq with rfl | hq'
        · left; exact hpmap x hxq
        · by_cases hxp : x ∈ p.2
          · left; exact hpmap x hxp
          · right; exact ⟨q, hq', by rw [hpid x hxp]; exact hxq⟩

end Composition

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **Every complement end is noncompact.**  A connected component `W` of the
open set `(closure V)ᶜ` is open; were it compact it would be clopen, hence
(by connectedness of `X`) all of `X`, forcing `closure V = ∅` and contradicting
`V.Nonempty`. -/
theorem not_isCompact_end [T2Space X] [ConnectedSpace X] {V : Set X}
    (hVne : V.Nonempty) {x : X} (hx : x ∈ (closure V)ᶜ) :
    ¬ IsCompact (connectedComponentIn (closure V)ᶜ x) := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  intro hK
  set W := connectedComponentIn (closure V)ᶜ x with hW
  have hWopen : IsOpen W := isClosed_closure.isOpen_compl.connectedComponentIn
  have hWne : W.Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hclopen : IsClopen W := ⟨hK.isClosed, hWopen⟩
  have hWuniv : W = Set.univ :=
    (isClopen_iff.mp hclopen).resolve_left hWne.ne_empty
  have hsub : W ⊆ (closure V)ᶜ := connectedComponentIn_subset _ _
  rw [hWuniv] at hsub
  have hcvempty : closure V = ∅ := by
    rw [← Set.compl_univ_iff]; exact Set.univ_subset_iff.mp hsub
  exact hVne.ne_empty (Set.subset_eq_empty subset_closure hcvempty)

/-- **Per-end collapse (the remaining geometric input, W7 L5.5–L6).**  For a
noncompact complement end `Z = connectedComponentIn (closure V)ᶜ x`, there is a
continuous self-map `h` fixing everything outside `Z` and mapping all of `Z`
into `closure V` (in fact onto the single frontier circle `frontier Z ⊆
frontier V`).  Constructed by cutting `Z` along an escaping ray, Tietze-extending
the angular coordinate of the periodic frontier parametrisation, and composing
with the parametrisation. -/
theorem exists_end_collapse [T2Space X] [ConnectedSpace X] [SimplyConnectedSpace X]
    {V : Set X} (hVo : IsOpen V) (hVconn : IsConnected V) (hVcl : IsCompact (closure V))
    {f : X → ℝ} {c : ℝ} {A : Set X} (hAo : IsOpen A) (hfrA : frontier V ⊆ A)
    (hharm : SurfaceHarmonicOn f A)
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    {x : X} (hx : x ∈ (closure V)ᶜ)
    (hZnc : ¬ IsCompact (connectedComponentIn (closure V)ᶜ x)) :
    ∃ h : C(X, X),
      (∀ y ∉ connectedComponentIn (closure V)ᶜ x, h y = y) ∧
      (∀ y ∈ connectedComponentIn (closure V)ᶜ x, h y ∈ closure V) := by
  sorry

/-- **The end-collapse retraction onto `closure V`.**  On a noncompact simply
connected surface, a relatively compact open connected `V` with exterior-disk
regular frontier and no compact complement component admits a continuous
retraction `r : X → X` of the whole surface onto `closure V`: `r` fixes
`closure V` pointwise and maps every point into `closure V`.

This is the Anghel–Stan retraction (W7 steps L5.5–L8): collapse each complement
end onto its frontier circle (`exists_end_collapse`), then compose the finitely
many collapses (`finite_ends`, `compList_collapse`). -/
theorem exists_retraction_onto_closure [T2Space X] [ConnectedSpace X]
    [SimplyConnectedSpace X] {V : Set X} (hVo : IsOpen V) (hVconn : IsConnected V)
    (hVcl : IsCompact (closure V))
    (_hVnc : ∀ x ∉ V, ¬ IsCompact (connectedComponentIn Vᶜ x))
    {f : X → ℝ} {c : ℝ} {A : Set X} (hAo : IsOpen A) (hfrA : frontier V ⊆ A)
    (hharm : SurfaceHarmonicOn f A)
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x)) :
    ∃ r : C(X, X), (∀ x, r x ∈ closure V) ∧ (∀ a ∈ closure V, r a = a) := by
  classical
  set Ends := {Z : Set X | ∃ x, x ∈ (closure V)ᶜ ∧ Z = connectedComponentIn (closure V)ᶜ x}
    with hEnds
  have hEfin : Ends.Finite := finite_ends hVo hVcl hVconn.nonempty hdich hfc hchart
  -- Choose a collapse map for every end.
  have hcollapse : ∀ Z ∈ Ends, ∃ h : C(X, X),
      (∀ y ∉ Z, h y = y) ∧ (∀ y ∈ Z, h y ∈ closure V) := by
    rintro Z ⟨z, hz, rfl⟩
    have hnc := not_isCompact_end hVconn.nonempty hz
    exact exists_end_collapse hVo hVconn hVcl hAo hfrA hharm hfc hchart hdich hz hnc
  set H : Set X → C(X, X) :=
    fun Z => if hZ : Z ∈ Ends then (hcollapse Z hZ).choose else ContinuousMap.id X with hHdef
  have hHid : ∀ Z ∈ Ends, ∀ y ∉ Z, H Z y = y := by
    intro Z hZ y hy
    simp only [hHdef, dif_pos hZ]
    exact (hcollapse Z hZ).choose_spec.1 y hy
  have hHmap : ∀ Z ∈ Ends, ∀ y ∈ Z, H Z y ∈ closure V := by
    intro Z hZ y hy
    simp only [hHdef, dif_pos hZ]
    exact (hcollapse Z hZ).choose_spec.2 y hy
  -- The list of (collapse, end) pairs.
  set l : List (C(X, X) × Set X) := hEfin.toFinset.toList.map (fun Z => (H Z, Z)) with hl
  -- Membership analysis for `l`.
  have hmemZ : ∀ Z ∈ Ends, (H Z, Z) ∈ l := by
    intro Z hZ
    rw [hl]
    exact List.mem_map_of_mem (Finset.mem_toList.mpr (hEfin.mem_toFinset.mpr hZ))
  have hmemp : ∀ p ∈ l, ∃ Z ∈ Ends, p = (H Z, Z) := by
    intro p hp
    rw [hl] at hp
    obtain ⟨Z, hZlist, rfl⟩ := List.mem_map.mp hp
    exact ⟨Z, hEfin.mem_toFinset.mp (Finset.mem_toList.mp hZlist), rfl⟩
  -- Verify the composition hypotheses.
  have hid : ∀ p ∈ l, ∀ y ∉ p.2, p.1 y = y := by
    intro p hp y hy
    obtain ⟨Z, hZ, rfl⟩ := hmemp p hp
    exact hHid Z hZ y hy
  have hmap : ∀ p ∈ l, ∀ y ∈ p.2, p.1 y ∈ closure V := by
    intro p hp y hy
    obtain ⟨Z, hZ, rfl⟩ := hmemp p hp
    exact hHmap Z hZ y hy
  have hdisj : ∀ p ∈ l, Disjoint (closure V) p.2 := by
    intro p hp
    obtain ⟨Z, ⟨z, hz, rfl⟩, rfl⟩ := hmemp p hp
    exact Set.disjoint_left.mpr (fun a ha haZ => (connectedComponentIn_subset _ _ haZ) ha)
  obtain ⟨hfix, hinto⟩ := compList_collapse l hid hmap hdisj
  refine ⟨compList l, fun y => ?_, hfix⟩
  by_cases hy : y ∈ closure V
  · exact hinto y (Or.inl hy)
  · -- `y` lies in its own end, which is one of the pieces of `l`.
    have hyc : y ∈ (closure V)ᶜ := hy
    set Zy := connectedComponentIn (closure V)ᶜ y with hZy
    have hZyEnds : Zy ∈ Ends := ⟨y, hyc, rfl⟩
    have hyZy : y ∈ Zy := mem_connectedComponentIn hyc
    exact hinto y (Or.inr ⟨(H Zy, Zy), hmemZ Zy hZyEnds, hyZy⟩)

end Uniformization
