/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.BoundaryCircle

/-!
# Boundary circle chain (W7 step D2)

Building on the straightened boundary boxes of `BoundaryCircle.lean`
(`exists_straight_box`, `re_transition_eq`), this file develops the local
one-dimensional structure of `frontier V` and analyses its connected
components.

At each frontier point `ξ` the box gives a *middle segment*
`frontier V ∩ W = ψ.symm '' {z ∈ B | z.re = c}`, a vertical segment in the
chart.  Parametrising it by the imaginary coordinate `s ↦ ψ.symm (c + s·i)`
turns the local frontier into an honest open interval:

* `exists_boundary_arc` (S1): a homeomorphism `arc : Ioo a b ≃ frontier V ∩ W`
  onto an open frontier neighbourhood of `ξ`, with continuous inverse
  `linv x = (ψ x).im`.

From S1 we read off the point-set structure of a component `C` of `frontier V`:

* every local arc through a point of `C` lies inside `C` (components absorb the
  connected arcs), so `C` is open in `frontier V` (S2);
* `C` is compact (a closed subset of the compact `frontier V`), hence covered by
  finitely many local arcs, and — crucially — no single arc exhausts `C`, since
  an open interval is not compact (S3).

These are the ingredients of the circle-chain description of `frontier V`.
-/

open Set Metric Topology Filter

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## S1 — the local boundary arc -/

/-- **Local boundary arc (S1).**  Under the collar hypotheses, each frontier
point `ξ` has an open neighbourhood `W` in `X` such that the frontier slice
`frontier V ∩ W` is the homeomorphic image of an open interval `Ioo a b` under
`arc s = ψ.symm (c + s·i)`, with continuous inverse `linv x = (ψ x).im`.
This exhibits `frontier V` as locally an open interval near every point. -/
theorem exists_boundary_arc [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c)
    (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
          (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)
    {ξ : X} (hξ : ξ ∈ frontier V) :
    ∃ (W : Set X) (a b : ℝ) (arc : ℝ → X) (linv : X → ℝ),
      IsOpen W ∧ ξ ∈ W ∧ a < b ∧
      (∃ s ∈ Ioo a b, arc s = ξ) ∧
      ContinuousOn arc (Ioo a b) ∧
      ContinuousOn linv (frontier V ∩ W) ∧
      (∀ s ∈ Ioo a b, arc s ∈ frontier V ∩ W) ∧
      (∀ s ∈ Ioo a b, linv (arc s) = s) ∧
      (∀ x ∈ frontier V ∩ W, arc (linv x) = x) ∧
      (∀ x ∈ frontier V ∩ W, linv x ∈ Ioo a b) ∧
      arc '' (Ioo a b) = frontier V ∩ W := by
  obtain ⟨ψ, δ, ε, hψ, hξψ, hδpos, hεpos, hqre, hbox_tgt, hWopen, hξW,
    hf_eq, hVeq, hfront⟩ := exists_straight_box hVo hdich hfc hchart hξ
  set q := ψ ξ with hq
  set W := ψ.symm '' straightBox q c δ ε with hW
  -- the vertical-segment point at imaginary coordinate `s`
  set seg : ℝ → ℂ := fun s => (c : ℂ) + (s : ℂ) * Complex.I with hseg
  have hseg_re : ∀ s, (seg s).re = c := by intro s; simp [hseg]
  have hseg_im : ∀ s, (seg s).im = s := by intro s; simp [hseg]
  set a := q.im - ε with ha
  set b := q.im + ε with hb
  have hab : a < b := by rw [ha, hb]; linarith
  -- membership of the segment point in the box, for `s ∈ Ioo a b`
  have hseg_box : ∀ s ∈ Ioo a b, seg s ∈ straightBox q c δ ε := by
    intro s hs
    rw [mem_straightBox, hseg_re, hseg_im]
    refine ⟨by rw [sub_self, abs_zero]; exact hδpos, ?_⟩
    rw [abs_lt]; constructor <;> [linarith [hs.1]; linarith [hs.2]]
  have hseg_mid : ∀ s ∈ Ioo a b, seg s ∈ {z ∈ straightBox q c δ ε | z.re = c} :=
    fun s hs => ⟨hseg_box s hs, hseg_re s⟩
  set arc : ℝ → X := fun s => ψ.symm (seg s) with harc
  set linv : X → ℝ := fun x => (ψ x).im with hlinv
  -- `W ⊆ ψ.source`
  have hWsrc : W ⊆ ψ.source := by
    rintro x ⟨z, hz, rfl⟩; exact ψ.map_target (hbox_tgt hz)
  -- `arc s ∈ frontier V ∩ W`
  have harc_mem : ∀ s ∈ Ioo a b, arc s ∈ frontier V ∩ W := by
    intro s hs
    rw [hfront]
    exact ⟨seg s, hseg_mid s hs, rfl⟩
  -- continuity of `arc`
  have hcont_arc : ContinuousOn arc (Ioo a b) := by
    have hsegc : Continuous seg := by rw [hseg]; fun_prop
    have hmaps : MapsTo seg (Ioo a b) ψ.target :=
      fun s hs => hbox_tgt (hseg_box s hs)
    exact ψ.continuousOn_symm.comp hsegc.continuousOn hmaps
  -- continuity of `linv` on the frontier slice
  have hcont_linv : ContinuousOn linv (frontier V ∩ W) := by
    have : ContinuousOn (fun x => (ψ x).im) ψ.source :=
      Complex.continuous_im.comp_continuousOn ψ.continuousOn
    exact this.mono (fun x hx => hWsrc hx.2)
  -- `linv (arc s) = s`
  have hlinv_arc : ∀ s ∈ Ioo a b, linv (arc s) = s := by
    intro s hs
    have h1 : ψ (ψ.symm (seg s)) = seg s := ψ.right_inv (hbox_tgt (hseg_box s hs))
    simp only [hlinv, harc, h1, hseg_im]
  -- `arc (linv x) = x` and `linv x ∈ Ioo a b` on the frontier slice
  have harc_linv : ∀ x ∈ frontier V ∩ W, arc (linv x) = x ∧ linv x ∈ Ioo a b := by
    intro x hx
    rw [hfront] at hx
    obtain ⟨z, ⟨hzbox, hzre⟩, rfl⟩ := hx
    have hpsi : ψ (ψ.symm z) = z := ψ.right_inv (hbox_tgt hzbox)
    have hlz : linv (ψ.symm z) = z.im := by simp only [hlinv, hpsi]
    have hsegz : seg z.im = z := by
      apply Complex.ext
      · rw [hseg_re, hzre]
      · rw [hseg_im]
    refine ⟨?_, ?_⟩
    · show ψ.symm (seg (linv (ψ.symm z))) = ψ.symm z
      rw [hlz, hsegz]
    · rw [hlz]
      rw [mem_straightBox] at hzbox
      have := hzbox.2
      rw [abs_lt] at this
      exact ⟨by rw [ha]; linarith [this.1], by rw [hb]; linarith [this.2]⟩
  -- `arc` hits `ξ`
  have harc_xi : ∃ s ∈ Ioo a b, arc s = ξ := by
    refine ⟨q.im, ⟨by rw [ha]; linarith, by rw [hb]; linarith⟩, ?_⟩
    show ψ.symm (seg q.im) = ξ
    have hsq : seg q.im = q := by
      apply Complex.ext
      · rw [hseg_re, hqre]
      · rw [hseg_im]
    rw [hsq, ψ.left_inv hξψ]
  -- image equality
  have himg : arc '' (Ioo a b) = frontier V ∩ W := by
    apply Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩; exact harc_mem s hs
    · intro x hx
      obtain ⟨hxfix, hxmem⟩ := harc_linv x hx
      exact ⟨linv x, hxmem, hxfix⟩
  exact ⟨W, a, b, arc, linv, hWopen, hξW, hab, harc_xi, hcont_arc, hcont_linv,
    harc_mem, hlinv_arc, fun x hx => (harc_linv x hx).1, fun x hx => (harc_linv x hx).2,
    himg⟩

/-! ## S2 — connected components of the frontier -/

section Component

variable [T2Space X] {V : Set X} (hVo : IsOpen V) {f : X → ℝ} {c : ℝ}
  (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
  (hfc : ∀ ξ ∈ frontier V, f ξ = c)
  (hchart : ∀ ξ ∈ frontier V, ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧
      ∃ F : ℂ → ℂ, AnalyticAt ℂ F (e ξ) ∧
        (∀ᶠ z in 𝓝 (e ξ), (F z).re = f (e.symm z)) ∧ deriv F (e ξ) ≠ 0)

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [T2Space X] in
/-- `frontier V` is compact once `closure V` is. -/
theorem isCompact_frontier (hVcl : IsCompact (closure V)) : IsCompact (frontier V) :=
  hVcl.of_isClosed_subset isClosed_frontier frontier_subset_closure

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [T2Space X] in
/-- A connected component of the compact `frontier V` is compact. -/
theorem isCompact_component (hVcl : IsCompact (closure V)) {x₀ : X} :
    IsCompact (connectedComponentIn (frontier V) x₀) := by
  by_cases hx₀ : x₀ ∈ frontier V
  · rw [connectedComponentIn_eq_image hx₀]
    haveI : CompactSpace (frontier V) :=
      isCompact_iff_compactSpace.mp (isCompact_frontier hVcl)
    exact (isClosed_connectedComponent.isCompact).image continuous_subtype_val
  · rw [connectedComponentIn_eq_empty hx₀]; exact isCompact_empty

include hVo hdich hfc hchart in
/-- **Components absorb local arcs (S2).**  Every point `ξ` of a component `C` of
`frontier V` has an open neighbourhood `W` whose frontier slice `frontier V ∩ W`
is a preconnected subset of `C` (a boundary arc through `ξ`), together with the
full arc parametrisation of that slice. -/
theorem exists_local_arc_in_component {x₀ : X} {ξ : X}
    (hξC : ξ ∈ connectedComponentIn (frontier V) x₀) :
    ∃ (W : Set X) (a b : ℝ) (arc : ℝ → X) (linv : X → ℝ),
      IsOpen W ∧ ξ ∈ W ∧ a < b ∧
      (∃ s ∈ Ioo a b, arc s = ξ) ∧
      ContinuousOn arc (Ioo a b) ∧
      ContinuousOn linv (frontier V ∩ W) ∧
      (∀ s ∈ Ioo a b, arc s ∈ frontier V ∩ W) ∧
      (∀ s ∈ Ioo a b, linv (arc s) = s) ∧
      (∀ x ∈ frontier V ∩ W, arc (linv x) = x) ∧
      (∀ x ∈ frontier V ∩ W, linv x ∈ Ioo a b) ∧
      arc '' (Ioo a b) = frontier V ∩ W ∧
      IsPreconnected (frontier V ∩ W) ∧
      ξ ∈ frontier V ∩ W ∧
      frontier V ∩ W ⊆ connectedComponentIn (frontier V) x₀ := by
  have hξfr : ξ ∈ frontier V := connectedComponentIn_subset _ _ hξC
  obtain ⟨W, a, b, arc, linv, hWopen, hξW, hab, harc_xi, hcont_arc, hcont_linv,
    harc_mem, hlinv_arc, harc_linv, hlinv_mem, himg⟩ :=
    exists_boundary_arc hVo hdich hfc hchart hξfr
  -- the slice is preconnected (continuous image of an interval)
  have hpre : IsPreconnected (frontier V ∩ W) := by
    rw [← himg]; exact (isPreconnected_Ioo).image arc hcont_arc
  have hξslice : ξ ∈ frontier V ∩ W := ⟨hξfr, hξW⟩
  -- slice ⊆ component through `ξ` = component through `x₀`
  have hsub : frontier V ∩ W ⊆ connectedComponentIn (frontier V) x₀ := by
    have h1 : frontier V ∩ W ⊆ connectedComponentIn (frontier V) ξ :=
      hpre.subset_connectedComponentIn hξslice inter_subset_left
    rwa [← connectedComponentIn_eq hξC] at h1
  exact ⟨W, a, b, arc, linv, hWopen, hξW, hab, harc_xi, hcont_arc, hcont_linv,
    harc_mem, hlinv_arc, harc_linv, hlinv_mem, himg, hpre, hξslice, hsub⟩

include hVo hdich hfc hchart in
/-- Neighbourhood form of `exists_local_arc_in_component`: every point of a
component `C` has an open neighbourhood `W` whose frontier slice lies in `C`. -/
theorem exists_local_nbhd_in_component {x₀ : X} {ξ : X}
    (hξC : ξ ∈ connectedComponentIn (frontier V) x₀) :
    ∃ W : Set X, IsOpen W ∧ ξ ∈ W ∧
      frontier V ∩ W ⊆ connectedComponentIn (frontier V) x₀ := by
  obtain ⟨W, a, b, arc, linv, hWopen, hξW, hab, harc_xi, hcont_arc, hcont_linv,
    harc_mem, hlinv_arc, harc_linv, hlinv_mem, himg, hpre, hξslice, hsub⟩ :=
    exists_local_arc_in_component hVo hdich hfc hchart hξC
  exact ⟨W, hWopen, hξW, hsub⟩

include hVo hdich hfc hchart in
/-- **Components are open in `frontier V` (S2 capstone).**  A connected component
`C` of `frontier V` equals `frontier V ∩ U` for an open `U ⊆ X`; since components
are always closed, `C` is clopen in `frontier V`.  (This is the local-connectivity
of the boundary, and drives the clopen argument that a wrapped arc exhausts its
component.) -/
theorem isOpen_component_in_frontier {x₀ : X} :
    ∃ U : Set X, IsOpen U ∧
      connectedComponentIn (frontier V) x₀ = frontier V ∩ U := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  choose! Wf hWfopen hWfmem hWfsub using
    fun ξ (hξ : ξ ∈ C) => exists_local_nbhd_in_component hVo hdich hfc hchart hξ
  refine ⟨⋃ ξ ∈ C, Wf ξ, isOpen_biUnion (fun ξ hξ => hWfopen ξ hξ), ?_⟩
  apply Subset.antisymm
  · intro η hη
    exact ⟨connectedComponentIn_subset _ _ hη, mem_biUnion hη (hWfmem η hη)⟩
  · rintro η ⟨hηfr, hηU⟩
    obtain ⟨ξ, hξC, hηW⟩ := mem_iUnion₂.mp hηU
    exact hWfsub ξ hξC ⟨hηfr, hηW⟩

/-! ## S3 — no component is a single arc -/

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [T2Space X] in
/-- **An open-interval arc is never compact.**  If a set `S` is the homeomorphic
image of an open interval `Ioo a b` (`a < b`) via `arc` with continuous inverse
`linv`, then `S` is not compact.  This is the non-degeneracy input to the circle
chain: it forbids a compact component from coinciding with a single boundary
arc. -/
theorem not_isCompact_arc {a b : ℝ} (hab : a < b) {arc : ℝ → X} {linv : X → ℝ} {S : Set X}
    (hcont_linv : ContinuousOn linv S)
    (hlinv_arc : ∀ s ∈ Ioo a b, linv (arc s) = s)
    (harc_mem : ∀ s ∈ Ioo a b, arc s ∈ S)
    (hlinv_mem : ∀ x ∈ S, linv x ∈ Ioo a b) :
    ¬ IsCompact S := by
  intro hS
  have hcpt : IsCompact (linv '' S) := hS.image_of_continuousOn hcont_linv
  have heq : linv '' S = Ioo a b := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hlinv_mem x hx
    · intro s hs; exact ⟨arc s, harc_mem s hs, hlinv_arc s hs⟩
  rw [heq] at hcpt
  have hcl : IsClosed (Ioo a b) := hcpt.isClosed
  have hclos := hcl.closure_eq
  rw [closure_Ioo (ne_of_lt hab)] at hclos
  have ha : a ∈ Icc a b := ⟨le_refl a, le_of_lt hab⟩
  rw [hclos] at ha
  exact absurd ha.1 (lt_irrefl a)

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [T2Space X] in
/-- **No component is a single arc (S3).**  A local boundary arc `frontier V ∩ W`
is always distinct from a *compact* component `C` of `frontier V`: otherwise `C`
would be a compact open interval, which is impossible. -/
theorem arc_slice_ne_component (hVcl : IsCompact (closure V)) {x₀ : X} {W : Set X}
    (hW : ∃ (a b : ℝ) (arc : ℝ → X) (linv : X → ℝ),
      a < b ∧ ContinuousOn linv (frontier V ∩ W) ∧
      (∀ s ∈ Ioo a b, linv (arc s) = s) ∧
      (∀ s ∈ Ioo a b, arc s ∈ frontier V ∩ W) ∧
      (∀ x ∈ frontier V ∩ W, linv x ∈ Ioo a b)) :
    frontier V ∩ W ≠ connectedComponentIn (frontier V) x₀ := by
  obtain ⟨a, b, arc, linv, hab, hcont_linv, hlinv_arc, harc_mem, hlinv_mem⟩ := hW
  intro hEq
  have hnc : ¬ IsCompact (frontier V ∩ W) :=
    not_isCompact_arc hab hcont_linv hlinv_arc harc_mem hlinv_mem
  rw [hEq] at hnc
  exact hnc (isCompact_component hVcl)

include hVo hdich hfc hchart in
/-- **Finite arc cover (S3).**  A compact component `C = connectedComponentIn
(frontier V) x₀` is covered by finitely many boundary-arc slices, each contained
in `C`.  Together with `arc_slice_ne_component` (each slice `≠ C`) this shows a
nonempty compact component needs at least two arcs. -/
theorem exists_finite_arc_cover (hVcl : IsCompact (closure V)) {x₀ : X} :
    ∃ (T : Set X) (Wf : X → Set X),
      T ⊆ connectedComponentIn (frontier V) x₀ ∧ T.Finite ∧
      (∀ ξ ∈ T, IsOpen (Wf ξ)) ∧
      (∀ ξ ∈ T, frontier V ∩ Wf ξ ⊆ connectedComponentIn (frontier V) x₀) ∧
      connectedComponentIn (frontier V) x₀ ⊆ ⋃ ξ ∈ T, (frontier V ∩ Wf ξ) := by
  classical
  set C := connectedComponentIn (frontier V) x₀ with hC
  choose! Wf hWfopen hWfmem hWfsub using
    fun ξ (hξ : ξ ∈ C) => exists_local_nbhd_in_component hVo hdich hfc hchart hξ
  -- open cover of the compact component
  have hcov : C ⊆ ⋃ ξ ∈ C, Wf ξ := fun η hη => mem_biUnion hη (hWfmem η hη)
  obtain ⟨T, hTsub, hTfin, hTcov⟩ :=
    (isCompact_component hVcl (x₀ := x₀)).elim_finite_subcover_image hWfopen hcov
  refine ⟨T, Wf, hTsub, hTfin, fun ξ hξ => hWfopen ξ (hTsub hξ),
    fun ξ hξ => hWfsub ξ (hTsub hξ), ?_⟩
  intro η hη
  obtain ⟨ξ, hξT, hηW⟩ := mem_iUnion₂.mp (hTcov hη)
  exact mem_iUnion₂.mpr ⟨ξ, hξT, connectedComponentIn_subset _ _ hη, hηW⟩

end Component

end Uniformization
