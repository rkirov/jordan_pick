/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.Ends
import Uniformization.Surface.Fill.CircleParam
import Uniformization.Surface.Fill.BoundaryEntry

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
`finite_ends`, and which must be an end at infinity rather than a hole — see the
counterexample in `exists_end_collapse`'s docstring) carries a continuous
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

/-- **The closure of an end is the corresponding component of `Vᶜ`.**

`Z = connectedComponentIn (closure V)ᶜ x` is a component of an *open* set, so `Z` itself
says nothing about compactness at infinity; `W = connectedComponentIn Vᶜ x` is a component
of a *closed* set, so `¬ IsCompact W` genuinely means unbounded.  This identifies the two:
`closure Z = W`.

Consequently `exists_end_collapse`'s hypothesis `hWnc` is exactly `¬ IsCompact (closure Z)`,
which is the form a prover of that theorem wants (the ray edge `R` must be closed in `X`,
so the end has to reach infinity rather than merely fail to be compact).

The proof is a connectedness argument.  `closure Z ⊆ W` because `closure Z` is connected,
contains `x`, and avoids the open `V`.  For the reverse, every point of `closure Z` has an
open neighbourhood `N` with `N ∩ Vᶜ ⊆ closure Z`: interior points use `Z` itself, and a
frontier point `q ∈ frontier Z ⊆ frontier V` uses the half-disk model of
`exists_halfdisk_chart` at `q`, where `Vᶜ` is the closed half-disk `{re ≤ c}` and
`halfdisk_end_eq` identifies `{re < c}` with `Z` and `{re = c}` with `frontier Z` — so the
whole closed half-disk lies in `closure Z`.  The union `U` of these neighbourhoods and the
open set `(closure Z)ᶜ` then cover the preconnected `W`, and `U ∩ W ⊆ closure Z` forces the
second piece to be empty. -/
theorem closure_end_eq_component_compl [T2Space X] [ConnectedSpace X]
    {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    {x : X} (hx : x ∈ (closure V)ᶜ) :
    closure (connectedComponentIn (closure V)ᶜ x) = connectedComponentIn Vᶜ x := by
  classical
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  obtain ⟨A', hA'o, hfrA', hpos, hneg, -⟩ := exists_collar_dichotomy hdich hfc
  set Z : Set X := connectedComponentIn (closure V)ᶜ x with hZdef
  set W : Set X := connectedComponentIn Vᶜ x with hWdef
  have hZo : IsOpen Z := isClosed_closure.isOpen_compl.connectedComponentIn
  have hxZ : x ∈ Z := mem_connectedComponentIn hx
  have hxVc : x ∈ Vᶜ := fun hxV => hx (subset_closure hxV)
  have hfrVc : frontier V ⊆ Vᶜ := fun ξ hξ => (hVo.frontier_eq ▸ hξ).2
  have hfrZ : frontier Z ⊆ frontier V := frontier_component_compl_closure_subset
  -- `closure Z = Z ∪ frontier Z`, and both sides sit in `Vᶜ`
  have hclZsplit : ∀ q ∈ closure Z, q ∈ Z ∨ q ∈ frontier Z := by
    intro q hq
    by_cases h : q ∈ Z
    · exact Or.inl h
    · exact Or.inr (by rw [hZo.frontier_eq]; exact ⟨hq, h⟩)
  have hclZVc : closure Z ⊆ Vᶜ := by
    intro q hq
    rcases hclZsplit q hq with h | h
    · exact fun hqV => (connectedComponentIn_subset _ _ h) (subset_closure hqV)
    · exact hfrVc (hfrZ h)
  have hclZW : closure Z ⊆ W :=
    (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure hxZ) hclZVc
  -- every point of `closure Z` has a neighbourhood meeting `Vᶜ` only inside `closure Z`
  have hlocal : ∀ q ∈ closure Z, ∃ N : Set X, IsOpen N ∧ q ∈ N ∧ N ∩ Vᶜ ⊆ closure Z := by
    intro q hq
    rcases hclZsplit q hq with hqZ | hqfr
    · exact ⟨Z, hZo, hqZ, fun y hy => subset_closure hy.1⟩
    · -- frontier point: use the half-disk model at `q`
      have hqfrV : q ∈ frontier V := hfrZ hqfr
      obtain ⟨e, he, hqe, F, hFan, hFre, hFd⟩ := hchart q hqfrV
      obtain ⟨ψ, hψ, r, hr, hqψ, hψpre, hbtgt, hbA', hclos⟩ :=
        exists_halfdisk_chart hA'o hpos (hfrA' hqfrV) (hfc q hqfrV) he hqe hFan hFre hFd
      obtain ⟨hZiff, hFiff⟩ := halfdisk_end_eq hr hqψ hbtgt hclos hqfr
      refine ⟨ψ.source ∩ ψ ⁻¹' ball (ψ q) r,
        ψ.continuousOn.isOpen_inter_preimage ψ.open_source isOpen_ball,
        ⟨hqψ, mem_ball_self hr⟩, ?_⟩
      rintro y ⟨⟨hys, hyb⟩, hyV⟩
      simp only [mem_preimage] at hyb
      have hy' : ψ.symm (ψ y) = y := ψ.left_inv hys
      obtain ⟨hyA', hyf⟩ := hbA' (ψ y) hyb
      rw [hy'] at hyA' hyf
      have hyle : (ψ y).re ≤ c := by rw [← hyf]; exact (hneg y hyA').mp hyV
      rcases lt_or_eq_of_le hyle with hlt | heq
      · exact subset_closure (by have := (hZiff (ψ y) hyb).mpr hlt; rwa [hy'] at this)
      · exact frontier_subset_closure (by
          have := (hFiff (ψ y) hyb).mpr heq; rwa [hy'] at this)
  choose! N hNo hqN hNsub using hlocal
  set U : Set X := ⋃ q ∈ closure Z, N q with hUdef
  have hUo : IsOpen U := isOpen_biUnion fun q hq => hNo q hq
  have hclU : closure Z ⊆ U := fun q hq => mem_biUnion hq (hqN q hq)
  have hUVc : U ∩ Vᶜ ⊆ closure Z := by
    rintro y ⟨hyU, hyV⟩
    obtain ⟨q, hq, hyN⟩ := mem_iUnion₂.mp hyU
    exact hNsub q hq ⟨hyN, hyV⟩
  -- `W` is preconnected and covered by `U` and `(closure Z)ᶜ`; the second piece is empty
  refine Set.Subset.antisymm hclZW ?_
  by_contra hcon
  obtain ⟨w, hwW, hwn⟩ := Set.not_subset.mp hcon
  have hcover : W ⊆ U ∪ (closure Z)ᶜ := by
    intro v hv
    by_cases h : v ∈ closure Z
    · exact Or.inl (hclU h)
    · exact Or.inr h
  obtain ⟨y, hyW, hyU, hyn⟩ :=
    isPreconnected_connectedComponentIn U (closure Z)ᶜ hUo isClosed_closure.isOpen_compl
      hcover ⟨x, mem_connectedComponentIn hxVc, hclU (subset_closure hxZ)⟩ ⟨w, hwW, hwn⟩
  exact hyn (hUVc ⟨hyU, connectedComponentIn_subset _ _ hyW⟩)

/-- **The `X`-closure invariant forces a set out of the frontier collar.**  If `U` is a
relatively compact open set and `C ⊆ Z` has noncompact closure in `X`, then `C` must meet
`Z \ U`.

This is the crux of the strengthened escape clause (see `SimpleRayData`'s docstring in
`Fill/PolyRay.lean`).  With the exhaustion chosen so that the complement components of `Z`
split into *collar* pieces inside `U` and *far* pieces outside a compact of `X`, this lemma
says the collar pieces are exactly the ones the `X`-closure invariant excludes: anything
trapped in `U` has closure inside the compact `closure U`.  So a ray carrying that invariant
cannot accumulate on `frontier Z`, which is the failure mode the current `hesc` permits.

Note the contrast with the `Z`-closure invariant, which does *not* exclude them: a collar
piece has noncompact closure in `Z`, because its points approach `frontier Z` and so lie in
no compact subset of `Z`. -/
theorem inter_diff_nonempty_of_not_isCompact_closure {Z U C : Set X}
    (hUcl : IsCompact (closure U)) (hCZ : C ⊆ Z) (hC : ¬ IsCompact (closure C)) :
    (C ∩ (Z \ U)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  refine hC (hUcl.of_isClosed_subset isClosed_closure (closure_mono ?_))
  -- `C` misses `Z \ U` and sits in `Z`, so it sits in `U`
  intro y hy
  by_contra hyU
  exact absurd (Set.eq_empty_iff_forall_notMem.mp hempty y ⟨hy, hCZ hy, hyU⟩) not_false

/-- **An end reaches infinity.**  Restatement of `exists_end_collapse`'s hypothesis `hWnc`
in the form its proof needs: the end has noncompact closure, so a cutting ray inside it can
escape every compact set of `X` and the ray edge `R` can be closed in `X`.

This is what fails for the hole in the counterexample recorded on `exists_end_collapse`:
there `closure Z` is the closed unit disk. -/
theorem not_isCompact_closure_end [T2Space X] [ConnectedSpace X]
    {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    {x : X} (hx : x ∈ (closure V)ᶜ)
    (hWnc : ¬ IsCompact (connectedComponentIn Vᶜ x)) :
    ¬ IsCompact (closure (connectedComponentIn (closure V)ᶜ x)) := by
  rw [closure_end_eq_component_compl hVo hfc hchart hdich hx]
  exact hWnc

/-- **An end has unbounded part away from its frontier circle.**  If `U` is any relatively
compact open neighbourhood of `frontier Z`, then `Z \ U` is closed in `X` and still
noncompact.

This is the geometric fact the *strengthened* escape clause rests on.  `SimpleRayData.hesc`
only asks the ray to leave every compact subset of `Z`, which a ray running into the
frontier circle already does — so it does not force the ray edge `R` to be closed in `X`
(see the note on `exists_end_collapse`).  What is needed is a ray escaping every compact of
`X`, and this lemma says there is somewhere for such a ray to go: after deleting a collar
neighbourhood of the boundary circle, what remains is still unbounded, and it is closed, so
a compact exhaustion of it is an exhaustion by sets that stay away from `frontier Z`.

Closedness holds because `closure Z = Z ∪ frontier Z` and `frontier Z ⊆ U`, so
`closure (Z \ U) ⊆ closure Z ∩ Uᶜ = Z \ U`.  Noncompactness because otherwise
`closure Z ⊆ (Z \ U) ∪ closure U` would be compact, contradicting `hWnc` via
`closure_end_eq_component_compl`. -/
theorem not_isCompact_end_diff [T2Space X] [ConnectedSpace X]
    {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    {x : X} (hx : x ∈ (closure V)ᶜ)
    (hWnc : ¬ IsCompact (connectedComponentIn Vᶜ x))
    {U : Set X} (hUo : IsOpen U)
    (hfrU : frontier (connectedComponentIn (closure V)ᶜ x) ⊆ U)
    (hUcl : IsCompact (closure U)) :
    IsClosed (connectedComponentIn (closure V)ᶜ x \ U) ∧
      ¬ IsCompact (connectedComponentIn (closure V)ᶜ x \ U) := by
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  set Z : Set X := connectedComponentIn (closure V)ᶜ x with hZdef
  have hZo : IsOpen Z := isClosed_closure.isOpen_compl.connectedComponentIn
  have hnc : ¬ IsCompact (closure Z) :=
    not_isCompact_closure_end hVo hfc hchart hdich hx hWnc
  -- `closure Z ⊆ Z ∪ frontier Z`
  have hsplit : closure Z ⊆ Z ∪ frontier Z := by
    intro q hq
    by_cases h : q ∈ Z
    · exact Or.inl h
    · exact Or.inr (by rw [hZo.frontier_eq]; exact ⟨hq, h⟩)
  have hcl : IsClosed (Z \ U) := by
    rw [← closure_subset_iff_isClosed]
    intro q hq
    have hq' : q ∈ closure Z ∩ Uᶜ := by
      refine ⟨closure_mono (Set.sdiff_subset (t := U)) hq, ?_⟩
      have : closure (Z \ U) ⊆ closure Uᶜ := closure_mono (Set.sdiff_subset_compl _ _)
      simpa [hUo.isClosed_compl.closure_eq] using this hq
    rcases hsplit hq'.1 with h | h
    · exact ⟨h, hq'.2⟩
    · exact absurd (hfrU h) hq'.2
  refine ⟨hcl, fun hK => hnc ?_⟩
  -- `closure Z ⊆ (Z \ U) ∪ closure U`, a union of two compacts
  have hsub : closure Z ⊆ (Z \ U) ∪ closure U := by
    intro q hq
    by_cases hqU : q ∈ U
    · exact Or.inr (subset_closure hqU)
    · rcases hsplit hq with h | h
      · exact Or.inl ⟨h, hqU⟩
      · exact absurd (hfrU h) hqU
  exact (hK.union hUcl).of_isClosed_subset isClosed_closure hsub

/-- **Per-end collapse (the remaining geometric input, W7 L5.5–L6).**  For a
complement end `Z = connectedComponentIn (closure V)ᶜ x` whose *containing component of
`Vᶜ` is noncompact*, there is a
continuous self-map `h` fixing everything outside `Z` and mapping all of `Z`
into `closure V` (in fact onto the single frontier circle `frontier Z ⊆
frontier V`).  Constructed by cutting `Z` along an escaping ray, Tietze-extending
the angular coordinate of the periodic frontier parametrisation, and composing
with the parametrisation.

## The hypothesis `hWnc`, and why `¬ IsCompact Z` will not do

This theorem previously assumed only `¬ IsCompact Z`.  **That is not enough — the
statement is false under it.**  Counterexample:

> `X = ℂ`, `V = {z | 1 < ‖z‖ < 2}`, `c = 0`.  On `{1/2 < ‖z‖ < 3/2}` put `f = log ‖z‖`,
> on `{3/2 < ‖z‖ < 3}` put `f = log 2 - log ‖z‖`; `A` is their (disjoint) union, so `f` is
> harmonic on `A`, vanishes on both frontier circles, and has `V`-side `{f > 0}` at each,
> with `F = Log z` resp. `F = log 2 - Log z` giving `hchart` (`deriv F ≠ 0`).  Take `x = 0`,
> so `Z = {‖z‖ < 1}`, which is **not compact**, so the old hypothesis held.

The conclusion would supply `h : C(ℂ, ℂ)` fixing `{‖z‖ ≥ 1}` with `h '' Z ⊆ closure V`.
Restricted to the closed unit disk this is a map `D̄ → {1 ≤ ‖z‖ ≤ 2}` that is the identity
on `∂D̄`.  No such map exists: `∂D̄ ↪ closure V` generates `π₁(closure V) ≅ ℤ`, yet it would
factor through the contractible `D̄`.

The defect is that `¬ IsCompact Z` does not exclude a *relatively* compact end — a hole
rather than an end at infinity — and a hole cannot be collapsed onto its own boundary.
`not_isCompact_end` proves `¬ IsCompact Z` unconditionally, so it never had any content
here.

The correct hypothesis is on the component of `Vᶜ` (a **closed** set, so its components are
closed and "noncompact" genuinely means unbounded):

    hWnc : ¬ IsCompact (connectedComponentIn Vᶜ x)

which fails for the counterexample, where that component is the closed unit disk.  It is
exactly what `exists_level_piece_regular_frontier` already delivers and what
`exists_retraction_onto_closure` already receives — that hypothesis was being passed in and
then **ignored** (it was named `_hVnc`).  So no caller changes were needed.

A prover of this theorem will want `closure Z = connectedComponentIn Vᶜ x`, which turns
`hWnc` into `¬ IsCompact (closure Z)`.  That equality is a clopen argument in the
`Vᶜ`-component, and the open half of it is exactly `halfdisk_image_subset_end`
(`Fill/BoundaryEntry.lean`): near a frontier point the closed half-disk `{re ≤ c}` is the
closure of the open half-disk `{re < c}`, and the latter lies in `Z`.

## Status: reduced to one construction

Everything downstream of the geometry is now built and sorry-free:

* `Uniformization/Surface/Fill/PolyRay.lean` — `nonempty_simpleRayData` supplies the
  embedded, proper, shell-separated cutting ray (this was W7-P1/P2/P3, closed);
* `RayBuild.lean` — `nonempty_rayCollar_of_tubeData` turns raw tube coordinates into
  a `RayCollar`, discharging all collar-coordinate bookkeeping;
* `RayCollar.lean` — `exists_end_collapse_of_rayCollar` turns a `RayCollar` for the
  end into exactly this theorem.

So the *only* thing still missing is a `TubeData X Z CZ γ (γ 0)`: a two-sided
tubular neighbourhood of the cutting ray, i.e. closed half-collars `Sm`, `Sp`
sharing the ray edge `R`, with transverse/longitudinal coordinates `sm, tm`
(resp. `sp, tp`), matching `γ` on the circle edge (`hCZm`, `hCZp`) and covering
the circle apart from the far arc (`hCZcover`).

**Shape of that construction.**  The ray is a *chart polyline*: each segment is
straight in a chart.  Thicken each segment to a rectangle in its own chart
(`PLSeg.exists_tube_width` gives the uniform half-width), then glue across
junctions.  `SimpleRayData.hshell` is what makes the gluing possible — it gives each
segment a neighbourhood meeting only its two neighbours, so the per-segment tubes
interfere only where intended.

*Side consistency comes for free here.*  One would normally have to transport a
choice of side (which rectangle half is `Sm`, which is `Sp`) along the ray and argue
it is globally coherent.  That is unnecessary: the charts are drawn from
`riemannAtlas X`, so all transition maps are **biholomorphic**, hence
orientation-preserving.  Taking the normal direction as `i · (b - a)` in each chart
therefore already agrees across junctions — the usual orientability side-condition is
discharged by holomorphy of the atlas rather than by simple connectivity.

*The coordinates are not the hard part either.*  `TubeData` constrains `sm, tm`
(resp. `sp, tp`) only by: continuity on the half-collar, range (`sm ∈ [0,1]`,
`tm ≥ 0`), vanishing on the ray edge (`hsm_R`), and the circle-edge relations
`hCZm`/`hCZp`.  Their behaviour in between is unconstrained, so they need not be
faithful transverse/longitudinal coordinates.  The prescription

* `sm = 0` on `R`, `sm = θ/ε` on `Sm ∩ CZ` (where `γ θ = x`),
* `tm = 0` on `Sm ∩ CZ`, `tm` arbitrary `≥ 0` elsewhere,

is continuous on the closed set `R ∪ (Sm ∩ CZ)` — the two pieces meet only at
`p = γ 0`, where both give `0` — so **Tietze** extends it to `Sm`.  `X` is normal
(metrizable, as `RayCollar.lean` already uses), so this is available.

**So the real content of gap #2 is the SETS.**  Construct closed `R, Sm, Sp` with
`R ⊆ Sm ∩ Sp`, `R \ {p} ⊆ Z`, `Sm ∪ Sp ⊆ Z ∪ CZ`, `Sm ∩ Sp ⊆ R`, circle traces
`Sm ∩ CZ = γ '' [0,ε]` and `Sp ∩ CZ = γ '' [1-ε,1]`, and the covering conditions
`hCZcover`, `hcov`, `hcovp`.  Given those, the coordinates follow by Tietze and the
`RayCollar`/collapse layers finish the job.

The delicate point is the circle-edge termination: arranging the half-collars to
meet `CZ` in exactly those two arcs.

**Interface mismatch — the entry segment is now built.**  `nonempty_simpleRayData` produces
a ray starting at a point `z₀ ∈ Z` — the *open* end — whereas `TubeData` needs the ray edge
`R` to satisfy `p ∈ R` and `R \ {p} ⊆ Z` with `p = γ 0` on the frontier circle `CZ`.  The
half of this that enters `Z` through `p` is discharged in `Fill/BoundaryEntry.lean`:

* `exists_halfdisk_chart` puts the frontier into the half-plane normal form at `p`.  The
  lever is `exists_biholo_chart_germ` (`Surface/LevelChart.lean`): promoting `F ∘ e` to a
  maximal-atlas chart `ψ` gives a coordinate whose **real part is `f` itself**, so the
  collar dichotomy `V = {f > c}` reads off as `closure V = {Re ≥ c}` on a disk about `p`.
* `exists_boundary_entry_segment` then produces a *chart-straight* segment from `ψ p` — the
  leftward radius `[ψ p, ψ p − r/2]` — whose punctured image lies in `Z`.  It lands in `Z`
  specifically (not some other component of `(closure V)ᶜ`) because the open half-disk is
  convex, hence connected, and meets `Z` since `p ∈ closure Z`.

Being chart-straight, the entry segment has the same shape as a `PLSeg`, so it can be
prepended to the polyline ray rather than glued as a foreign arc.

`exists_local_collar_of_halfdisk` goes one step further and builds, *inside the model
disk*, the ray edge (the leftward radius) together with the two quarter-disk half-collars,
discharging the set-level `TubeData` fields `hpR`, `hRSm`, `hRSp`, `hRZ`, `hSmZ`, `hSpZ`,
`hSmSp` and `hcovp` near `p`.  `halfdisk_end_eq` is what makes the circle-edge bookkeeping
tractable: near `p` the frontier circle is a straight diameter, so cutting it at `p` into
the two arcs is cutting the diameter into halves.

**What remains.**  Three things, all still open:

1. **`SimpleRayData` is not strong enough as stated.**  Its escape clause is
   `hesc : ∀ K, IsCompact K → K ⊆ Z → ∃ N, ∀ n ≥ N, Disjoint (segment n) K` — escape from
   the compacts *of `Z`*, i.e. properness of the ray as a map into `Z`.  But `TubeData`
   asks for `hRcl : IsClosed R` with `R` closed *in `X`*.  Properness in `Z` permits the
   ray to accumulate on `frontier Z`: a ray running into the boundary circle does leave
   every compact subset of `Z` (points near the frontier lie in no such compact), yet its
   closure in `X` picks up frontier points other than `p`, so `R` is not closed and
   `R \ {p} ⊆ Z` fails.  Compare the open half-disk, where a radius aimed at the diameter
   is proper in the disk but not closed in the plane.  So `PolyRay.lean` needs a
   *strengthened* escape clause — the ray must escape every compact of `X`, equivalently
   eventually avoid a neighbourhood of the compact set `closure V` — and that is a change
   to the construction, not a corollary of it.
2. *Joining* the entry segment to the escaping ray while keeping the concatenation
   injective and closed.  `hesc` bounds how often the ray can revisit a compact subset of
   `Z`, but "finitely often" is not "never", so the join cannot be repaired after the fact.
   Nor can the ray simply be built inside `Z` minus the entry slit: near `p` that slit
   *locally separates* the half-disk into its upper and lower halves — which is exactly
   what the ray cut is for — so `Z ∖ slit` is the wrong ambient space.  The ray
   construction has to be *seeded* with the entry segment as segment `0`, which means
   changing the `Acc`/stage-list accumulation recursion in `PolyRay.lean`.
3. The half-collars `Sm`, `Sp` along the *global* ray (thicken each chart segment to a
   rectangle via `PLSeg.exists_tube_width`, glue at junctions using `hshell`), and the
   circle-edge termination proper: matching the model's `im` coordinate to the circle
   parameter `θ` so that `Sm ∩ CZ = γ '' [0, ε]` and `Sp ∩ CZ = γ '' [1 - ε, 1]`.

This is still a construction of the same order as the ray itself, not a final step. -/
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
    (hWnc : ¬ IsCompact (connectedComponentIn Vᶜ x)) :
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
    (hVnc : ∀ x ∉ V, ¬ IsCompact (connectedComponentIn Vᶜ x))
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
    have hzV : z ∉ V := fun hzV => hz (subset_closure hzV)
    exact exists_end_collapse hVo hVconn hVcl hAo hfrA hharm hfc hchart hdich hz
      (hVnc z hzV)
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
