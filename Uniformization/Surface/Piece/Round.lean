/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Piece.Cover
import Uniformization.Surface.Fill.HoleFill

/-!
# Corner rounding and exterior disks at the frontier (W7 steps L2–L3)

This file rounds the corners of a positive disk union and proves the exterior
disk condition at **every** frontier point of the resulting raw piece; the
capstone `exists_regular_piece` then assembles L1–L4 into a piece satisfying
every conjunct of the frozen `exists_simply_connected_piece` except simple
connectivity (left to W7 steps L5–L9), plus the no-compact-complement-
component property that those steps consume.

## Design (deviation from `W7_PLAN.md` §1.2–§1.4, documented)

The plan obtains regularity from a genericity predicate (transversal
crossings, no triple points, convex corners) realised by countable exclusion
of tangency radii, which requires real-analytic critical-value machinery.
We instead use a **compactness-only rounding** that avoids all of it:

* The *exposed crossing set* `posCross pos` — points on two distinct positive
  boundary circles but in no positive open disk — is **compact** (a finite
  union of intersections of circles, minus an open set, inside a compact
  set). No finiteness or transversality of circle intersections is needed.
* Cover it by finitely many small *negative* chart disks (`exists_rounding`),
  each chosen (in the chart at its center) to miss a prescribed closed set
  `T` (the L1 connector, which contains `K`).
* At a frontier point on a **negative circle**, the exterior disk is the
  internally tangent half-radius ball: its interior lies inside the negative
  open disk, hence misses `raw P` *globally* — pure triangle inequalities.
* At a frontier point on a **single positive circle** (and on no other active
  disk), the exterior disk is a small externally tangent ball: points of
  `raw P` near it must lie in the same positive disk (all other disks are
  excluded by an open guard set carried through the chart), and external
  tangency `dist c' c = ρ + s` keeps that disk out — again triangle
  inequalities only.
* Frontier points on **two or more positive circles** outside the open disks
  lie in `posCross`, hence inside a negative open disk, hence not on the
  frontier at all: the case is vacuous.

Connectivity of `raw P` is *not* proved (subtracting disks can in principle
disconnect a union); instead the capstone passes to the connected component
`W₀` of `raw P` containing `x₀` — the connector `T ⊇ K` survives rounding, so
`K ⊆ W₀` — and hole-fills it. Frontier and regularity transfer by
`frontier_connectedComponentIn_subset`, `ExteriorDiskAt.anti`, and
`ExteriorDiskAt.fill`. The plan's genericity lemmas remain available as a
*refinement* for the later collar/parity steps (L5–L6) and are not needed
for the point-set layer delivered here.
-/

open Set Metric Topology

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The exposed crossing set -/

/-- Exposed crossings of a family of positive disks: points on two distinct
boundary circles that are in no open disk of the family. -/
def posCross (pos : Finset (ChartDisk X)) : Set X :=
  {x | ∃ d ∈ pos, ∃ d' ∈ pos, d ≠ d' ∧ x ∈ d.circ ∧ x ∈ d'.circ} \ ⋃ d ∈ pos, d.odisk

theorem posCross_subset_circles (pos : Finset (ChartDisk X)) :
    posCross pos ⊆ ⋃ d ∈ pos, d.circ := by
  rintro x ⟨⟨d, hd, -, -, -, hx, -⟩, -⟩
  exact mem_biUnion hd hx

/-- The exposed crossing set is compact. -/
theorem isCompact_posCross [T2Space X] (pos : Finset (ChartDisk X)) :
    IsCompact (posCross pos) := by
  classical
  have hcirc : IsCompact (⋃ d ∈ pos, d.circ) :=
    pos.finite_toSet.isCompact_biUnion fun d _ => d.isCompact_circ
  refine hcirc.of_isClosed_subset ?_ (posCross_subset_circles pos)
  have heq : {x : X | ∃ d ∈ pos, ∃ d' ∈ pos, d ≠ d' ∧ x ∈ d.circ ∧ x ∈ d'.circ} =
      ⋃ d ∈ (↑pos : Set (ChartDisk X)),
        ⋃ d' ∈ {d' ∈ (↑pos : Set (ChartDisk X)) | d ≠ d'}, (d.circ ∩ d'.circ) := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨d, hd, d', hd', hne, hx, hx'⟩
      exact ⟨d, hd, d', ⟨hd', hne⟩, hx, hx'⟩
    · rintro ⟨d, hd, d', ⟨hd', hne⟩, hx, hx'⟩
      exact ⟨d, hd, d', hd', hne, hx, hx'⟩
  refine IsClosed.sdiff ?_ (isOpen_biUnion fun d _ => d.isOpen_odisk)
  rw [heq]
  refine pos.finite_toSet.isClosed_biUnion fun d _ => ?_
  refine (pos.finite_toSet.subset (sep_subset _ _)).isClosed_biUnion fun d' _ => ?_
  exact d.isClosed_circ.inter d'.isClosed_circ

/-! ## L2: rounding the exposed crossings by small negative disks -/

/-- **W7 step L2** (compactness-only form): the exposed crossing set can be
covered by finitely many negative chart disks whose closed carriers miss any
prescribed closed set `T` disjoint from it (e.g. the L1 connector). -/
theorem exists_rounding [T2Space X] (pos : Finset (ChartDisk X)) {T : Set X}
    (hTc : IsClosed T) (hTsub : T ⊆ ⋃ d ∈ pos, d.odisk) :
    ∃ neg : Finset (ChartDisk X),
      posCross pos ⊆ (⋃ d ∈ neg, d.odisk) ∧ ∀ d ∈ neg, Disjoint d.disk T := by
  classical
  -- a small negative disk at each exposed crossing point
  have hpoint : ∀ p ∈ posCross pos, ∃ nd : ChartDisk X, p ∈ nd.odisk ∧ Disjoint nd.disk T := by
    intro p hp
    have hpT : p ∉ T := fun hpT => hp.2 (hTsub hpT)
    set e := chartAt ℂ p with he_def
    have hps : p ∈ e.source := mem_chart_source ℂ p
    have himg_open : IsOpen (e '' (Tᶜ ∩ e.source)) :=
      e.isOpen_image_of_subset_source (hTc.isOpen_compl.inter e.open_source)
        inter_subset_right
    have hmem : e p ∈ e '' (Tᶜ ∩ e.source) := ⟨p, ⟨hpT, hps⟩, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg_open _ hmem
    have hseat : closedBall (e p) (ε / 2) ⊆ e.target := by
      refine ((closedBall_subset_ball (by linarith)).trans hball).trans ?_
      rintro _ ⟨x, ⟨-, hxs⟩, rfl⟩
      exact e.map_source hxs
    refine ⟨⟨e, chartAt_mem_riemannAtlas p, e p, ε / 2, by positivity, hseat⟩,
      ⟨e p, mem_ball_self (by positivity), e.left_inv hps⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hxT
    have hwimg : w ∈ e '' (Tᶜ ∩ e.source) :=
      hball ((closedBall_subset_ball (by linarith)) hw)
    obtain ⟨x', hx', hx'w⟩ := hwimg
    rw [← hx'w, e.left_inv hx'.2] at hxT
    exact hx'.1 hxT
  choose nd hnd hnddisj using hpoint
  -- compactness: finitely many negative disks suffice
  obtain ⟨t, ht⟩ := (isCompact_posCross pos).elim_nhds_subcover' (fun p hp => (nd p hp).odisk)
    (fun p hp => (nd p hp).isOpen_odisk.mem_nhds (hnd p hp))
  refine ⟨t.image (fun p => nd p.1 p.2), ?_, ?_⟩
  · intro p hp
    have := ht hp
    simp only [mem_iUnion] at this
    obtain ⟨q, hq, hpq⟩ := this
    exact mem_biUnion (Finset.mem_image_of_mem _ hq) hpq
  · intro d hd
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hd
    exact hnddisj q.1 q.2

/-! ## L3: the exterior disk condition at every frontier point of `raw` -/

/-- Distances from the endpoints of a radius to its midpoint. -/
private theorem midpoint_dist {a c : ℂ} {ρ : ℝ} (h : dist a c = ρ) :
    dist a ((a + c) / 2) = ρ / 2 ∧ dist ((a + c) / 2) c = ρ / 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  constructor
  · rw [dist_eq_norm, show a - (a + c) / 2 = (a - c) / 2 by ring, norm_div, h2,
      ← dist_eq_norm, h]
  · rw [dist_eq_norm, show (a + c) / 2 - c = (a - c) / 2 by ring, norm_div, h2,
      ← dist_eq_norm, h]

/-- Exterior disk at a frontier point on a negative circle: the internally
tangent half-radius ball, whose interior lies inside the negative open disk,
hence misses `raw P` globally. -/
private theorem exteriorDiskAt_raw_of_negCirc [T2Space X] {P : PieceData X} {d : ChartDisk X}
    (hd : d ∈ P.neg) {ξ : X} (hξcirc : ξ ∈ d.circ) : ExteriorDiskAt P.raw ξ := by
  have hξs : ξ ∈ d.e.source := d.circ_subset_source hξcirc
  set a := d.e ξ with ha
  have hsphere : dist a d.c = d.ρ := (d.mem_circ_iff.mp hξcirc).2
  obtain ⟨hma, hmc⟩ := midpoint_dist hsphere
  have hρ := d.ρ_pos
  refine ⟨d.e, d.he, hξs, (a + d.c) / 2, d.ρ / 2, by positivity, ?_, hma, ?_⟩
  · -- seating: the tangent ball sits inside the negative disk's chart target
    refine subset_trans ?_ d.seated
    intro w hw
    rw [mem_closedBall] at hw ⊢
    calc dist w d.c ≤ dist w ((a + d.c) / 2) + dist ((a + d.c) / 2) d.c := dist_triangle _ _ _
      _ ≤ d.ρ / 2 + d.ρ / 2 := add_le_add hw hmc.le
      _ = d.ρ := by ring
  · rintro x ⟨hxraw, hxs⟩ hxball
    -- the ball is inside the negative open disk
    rw [mem_ball] at hxball
    have hxod : x ∈ d.odisk := by
      refine d.mem_odisk_iff.mpr ⟨hxs, ?_⟩
      rw [mem_ball]
      calc dist (d.e x) d.c ≤ dist (d.e x) ((a + d.c) / 2) + dist ((a + d.c) / 2) d.c :=
            dist_triangle _ _ _
        _ < d.ρ / 2 + d.ρ / 2 := by linarith [hmc]
        _ = d.ρ := by ring
    exact hxraw.2 (mem_biUnion hd (d.odisk_subset_disk hxod))

/-- Exterior disk at a frontier point lying on a single positive circle and on
no other active disk: a small externally tangent ball, kept away from the
other disks by an open guard set carried through the chart. -/
private theorem exteriorDiskAt_raw_of_single [T2Space X] {P : PieceData X} {d : ChartDisk X}
    (_hd : d ∈ P.pos) {ξ : X} (hξcirc : ξ ∈ d.circ)
    (hother : ∀ d' ∈ P.pos, d' ≠ d → ξ ∉ d'.disk) (hneg : ξ ∉ P.negUnion) :
    ExteriorDiskAt P.raw ξ := by
  classical
  have hξs : ξ ∈ d.e.source := d.circ_subset_source hξcirc
  set a := d.e ξ with ha
  have hsphere : dist a d.c = d.ρ := (d.mem_circ_iff.mp hξcirc).2
  have hρ := d.ρ_pos
  -- the open guard set: away from all other positive disks and all negative disks
  set O : Set X := {x | ∀ d' ∈ P.pos, d' ≠ d → x ∉ d'.disk} ∩ P.negUnionᶜ with hO_def
  have hOopen : IsOpen O := by
    refine IsOpen.inter ?_ P.isClosed_negUnion.isOpen_compl
    have heq : {x : X | ∀ d' ∈ P.pos, d' ≠ d → x ∉ d'.disk} =
        ⋂ d' ∈ {d' ∈ (↑P.pos : Set (ChartDisk X)) | d' ≠ d}, (d'.disk)ᶜ := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, Finset.mem_coe]
      constructor
      · rintro h d' ⟨hd', hne⟩
        exact h d' hd' hne
      · rintro h d' hd' hne
        exact h d' ⟨hd', hne⟩
    rw [heq]
    exact (P.pos.finite_toSet.subset (sep_subset _ _)).isOpen_biInter
      fun d' _ => d'.isClosed_disk.isOpen_compl
  have hξO : ξ ∈ O := ⟨fun d' hd' hne => hother d' hd' hne, hneg⟩
  -- push the guard set through the chart
  have himg_open : IsOpen (d.e '' (O ∩ d.e.source)) :=
    d.e.isOpen_image_of_subset_source (hOopen.inter d.e.open_source) inter_subset_right
  have haimg : a ∈ d.e '' (O ∩ d.e.source) := ⟨ξ, ⟨hξO, hξs⟩, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg_open a haimg
  -- the externally tangent ball of radius `s`
  set s := ε / 4 with hs_def
  have hspos : 0 < s := by positivity
  set c' : ℂ := a + ((s / d.ρ : ℝ) : ℂ) * (a - d.c) with hc'_def
  have hca : ‖a - d.c‖ = d.ρ := by rw [← dist_eq_norm]; exact hsphere
  have hc'a : dist a c' = s := by
    rw [dist_eq_norm, show a - c' = -(((s / d.ρ : ℝ) : ℂ) * (a - d.c)) from by
      rw [hc'_def]; ring]
    rw [norm_neg, norm_mul, Complex.norm_real, hca, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    field_simp
  have hc'c : dist c' d.c = d.ρ + s := by
    rw [dist_eq_norm, show c' - d.c = ((1 + (s / d.ρ) : ℝ) : ℂ) * (a - d.c) from by
      rw [hc'_def]; push_cast; ring]
    rw [norm_mul, Complex.norm_real, hca, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  -- the tangent ball sits inside the guard-ball
  have hcb : closedBall c' s ⊆ ball a ε := by
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    calc dist w a ≤ dist w c' + dist c' a := dist_triangle _ _ _
      _ ≤ s + s := add_le_add hw (by rw [dist_comm]; exact hc'a.le)
      _ < ε := by rw [hs_def]; linarith
  refine ⟨d.e, d.he, hξs, c', s, hspos, ?_, hc'a, ?_⟩
  · -- seating
    refine (hcb.trans hball).trans ?_
    rintro _ ⟨x, ⟨-, hxs⟩, rfl⟩
    exact d.e.map_source hxs
  · rintro x ⟨hxraw, hxs⟩ hxball
    -- the guard set identifies the disk of `x` as `d` itself
    have hximg : d.e x ∈ d.e '' (O ∩ d.e.source) :=
      hball (hcb (ball_subset_closedBall hxball))
    obtain ⟨x', hx', hx'e⟩ := hximg
    have hxx' : x' = x := d.e.injOn hx'.2 hxs hx'e
    rw [hxx'] at hx'
    obtain ⟨d₁, hd₁, hxod⟩ : ∃ d₁ ∈ P.pos, x ∈ d₁.odisk := by
      have := hxraw.1
      simp only [PieceData.posUnion, mem_iUnion] at this
      obtain ⟨d₁, hd₁, hmem⟩ := this
      exact ⟨d₁, hd₁, hmem⟩
    have hd₁d : d₁ = d := by
      by_contra hne
      exact hx'.1.1 d₁ hd₁ hne (d₁.odisk_subset_disk hxod)
    rw [hd₁d] at hxod
    -- external tangency excludes the disk of `d`
    have hxc : dist (d.e x) d.c < d.ρ := by
      have h := (d.mem_odisk_iff.mp hxod).2
      rwa [mem_ball] at h
    rw [mem_ball] at hxball
    have htri : d.ρ + s ≤ dist c' (d.e x) + dist (d.e x) d.c := by
      rw [← hc'c]
      exact dist_triangle _ _ _
    rw [dist_comm c' (d.e x)] at htri
    linarith

/-- **W7 step L3**: if the exposed crossings of the positive disks are covered
by the negative open disks, then *every* frontier point of the raw piece
satisfies the exterior disk condition. -/
theorem exteriorDiskAt_raw [T2Space X] {P : PieceData X}
    (hcov : posCross P.pos ⊆ ⋃ d ∈ P.neg, d.odisk) :
    ∀ ξ ∈ frontier P.raw, ExteriorDiskAt P.raw ξ := by
  intro ξ hξ
  have hξcl : ξ ∈ closure P.raw := frontier_subset_closure hξ
  have hξnr : ξ ∉ P.raw := by
    rw [P.isOpen_raw.frontier_eq] at hξ
    exact hξ.2
  have hbc : ξ ∈ P.bcircles := P.frontier_raw_subset_bcircles hξ
  by_cases hneg : ξ ∈ P.negUnion
  · -- frontier point in a negative disk: it must be on the circle
    have hnotod : ∀ d ∈ P.neg, ξ ∉ d.odisk := by
      intro d hd hmem
      obtain ⟨q, hq, hqraw⟩ := mem_closure_iff.mp hξcl _ d.isOpen_odisk hmem
      exact hqraw.2 (mem_biUnion hd (d.odisk_subset_disk hq))
    obtain ⟨d, hd, hξd⟩ : ∃ d ∈ P.neg, ξ ∈ d.disk := by
      have := hneg
      simp only [PieceData.negUnion, mem_iUnion] at this
      obtain ⟨d, hd, hmem⟩ := this
      exact ⟨d, hd, hmem⟩
    have hξcirc : ξ ∈ d.circ := by
      rcases d.disk_eq_odisk_union_circ ▸ hξd with h | h
      · exact absurd h (hnotod d hd)
      · exact h
    exact exteriorDiskAt_raw_of_negCirc hd hξcirc
  · -- frontier point outside all negative disks: it is on a positive circle
    have hposcirc : ξ ∈ ⋃ d ∈ P.pos, d.circ := by
      rcases hbc with h | h
      · exact h
      · exfalso
        simp only [mem_iUnion] at h
        obtain ⟨d, hd, hmem⟩ := h
        exact hneg (mem_biUnion hd (d.circ_subset_disk hmem))
    simp only [mem_iUnion] at hposcirc
    obtain ⟨d, hd, hξcirc⟩ := hposcirc
    -- it is in no positive open disk (else it would be interior to `raw`)
    have hnotpos : ξ ∉ P.posUnion := by
      intro hmem
      simp only [PieceData.posUnion, mem_iUnion] at hmem
      obtain ⟨d₁, hd₁, hmem⟩ := hmem
      refine hξnr ⟨?_, hneg⟩
      simp only [PieceData.posUnion, mem_iUnion]
      exact ⟨d₁, hd₁, hmem⟩
    by_cases hmulti : ∃ d' ∈ P.pos, d' ≠ d ∧ ξ ∈ d'.circ
    · -- exposed crossing: swallowed by a negative disk, contradiction
      exfalso
      obtain ⟨d', hd', hne, hξ'⟩ := hmulti
      have hξE : ξ ∈ posCross P.pos := ⟨⟨d, hd, d', hd', (hne.symm : d ≠ d'), hξcirc, hξ'⟩, hnotpos⟩
      have := hcov hξE
      simp only [mem_iUnion] at this
      obtain ⟨dn, hdn, hmem⟩ := this
      exact hneg (mem_biUnion hdn (dn.odisk_subset_disk hmem))
    · -- single circle: the externally tangent ball
      refine exteriorDiskAt_raw_of_single hd hξcirc ?_ hneg
      intro d' hd' hne hmem
      rcases d'.disk_eq_odisk_union_circ ▸ hmem with h | h
      · exact hnotpos (mem_biUnion hd' h)
      · exact hmulti ⟨d', hd', hne, h⟩

/-! ## Capstone: the regular piece (all of L1–L4 assembled) -/

/-- **Regular piece** (W7, L1–L4 assembled): every compact `K ∋ x₀` on a
connected noncompact Riemann surface lies in an open connected set `V` with
compact closure, nonempty frontier, the exterior disk condition at *every*
frontier point, and no relatively compact complement components. This is the
frozen `exists_simply_connected_piece` minus the `IsSimplyConnected V`
conjunct (steps L5–L9), whose proof will consume the final property. -/
theorem exists_regular_piece [T2Space X] [ConnectedSpace X] (hnc : ¬ CompactSpace X)
    {K : Set X} (hK : IsCompact K) {x₀ : X} (hx₀ : x₀ ∈ K) :
    ∃ V : Set X, IsOpen V ∧ IsConnected V ∧ IsCompact (closure V) ∧ K ⊆ V ∧ x₀ ∈ V ∧
      (frontier V).Nonempty ∧ (∀ ξ ∈ frontier V, ExteriorDiskAt V ξ) ∧
      ∀ x ∉ V, ¬ IsCompact (connectedComponentIn Vᶜ x) := by
  have : LocallyCompactSpace X := locallyCompactSpace
  have : LocallyConnectedSpace X := locallyConnectedSpace
  -- L1: cover `K` with a compact connected connector `T`
  obtain ⟨pos, T, hTcpt, hTconn, hx₀T, hKT, hTsub⟩ := exists_pos_cover hK hx₀
  -- L2: round the exposed crossings away from `T`
  obtain ⟨neg, hcov, hdisj⟩ := exists_rounding pos hTcpt.isClosed hTsub
  set P : PieceData X := ⟨pos, neg⟩ with hP_def
  -- the connector survives rounding
  have hTraw : T ⊆ P.raw := by
    intro z hz
    refine ⟨hTsub hz, fun hzneg => ?_⟩
    simp only [PieceData.negUnion, mem_iUnion] at hzneg
    obtain ⟨d, hd, hzd⟩ := hzneg
    exact Set.disjoint_left.mp (hdisj d hd) hzd hz
  have hx₀raw : x₀ ∈ P.raw := hTraw hx₀T
  -- pass to the connected component of `x₀`, then hole-fill
  set W₀ := connectedComponentIn P.raw x₀ with hW₀_def
  have hW₀open : IsOpen W₀ := P.isOpen_raw.connectedComponentIn
  have hW₀conn : IsConnected W₀ := isConnected_connectedComponentIn_iff.mpr hx₀raw
  have hTW₀ : T ⊆ W₀ := hTconn.isPreconnected.subset_connectedComponentIn hx₀T hTraw
  have hW₀cl : IsCompact (closure W₀) :=
    P.isCompact_closure_raw.of_isClosed_subset isClosed_closure
      (closure_mono (connectedComponentIn_subset _ _))
  have hx₀W₀ : x₀ ∈ W₀ := mem_connectedComponentIn hx₀raw
  set V := fill W₀ with hV_def
  have hfr2 : frontier V ⊆ frontier P.raw :=
    (frontier_fill_subset hW₀open).trans (frontier_connectedComponentIn_subset P.isOpen_raw)
  refine ⟨V, isOpen_fill hW₀open, isConnected_fill hnc hW₀open hW₀conn,
    isCompact_closure_fill hnc hW₀open hW₀cl, (hKT.trans hTW₀).trans (subset_fill W₀),
    subset_fill W₀ hx₀W₀, nonempty_frontier_fill hnc hW₀open hW₀cl ⟨x₀, hx₀W₀⟩, ?_, ?_⟩
  · intro ξ hξ
    have h1 : ExteriorDiskAt P.raw ξ := exteriorDiskAt_raw hcov ξ (hfr2 hξ)
    exact (h1.anti (connectedComponentIn_subset _ _)).fill hW₀open hξ
  · intro x hx
    exact not_isCompact_connectedComponentIn_compl_fill hx

end Uniformization
