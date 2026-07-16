/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Regularity

/-!
# Piece geometry: chart disks and boolean disk regions (W7 step L0)

This file is the point-set scaffolding for workstream W7's
`exists_simply_connected_piece` (see `Uniformization/W7_PLAN.md`, §1.1). It is
the base of the DAG `Data → Generic → Cover → Round`, `Data → HoleFill`.

A **chart disk** `ChartDisk X` bundles a maximal-atlas chart `e`, a center
`c : ℂ`, a radius `ρ > 0`, and a seating proof `closedBall c ρ ⊆ e.target`. Its
carriers in `X` are

* `disk  d := e.symm '' closedBall c ρ`   (compact),
* `odisk d := e.symm '' ball c ρ`         (open),
* `circ  d := e.symm '' sphere c ρ`       (compact, `= disk d \ odisk d`).

A **piece** `PieceData X` is a finite set of *positive* disks minus a finite set
of *negative* corner-rounding disks (design decision D1). Its raw region is

  `raw P := (⋃ d ∈ P.pos, odisk d) \ (⋃ d ∈ P.neg, disk d)`  (open),

and the union of all boundary circles is `bcircles P`. The key structural
outputs proved here — and consumed all through L1–L10 — are:

* `raw P` open, `closure (raw P)` compact (`[T2Space X]`),
* `frontier (raw P) ⊆ bcircles P` (filling never grows this; see `HoleFill`).

All carriers are defined via `e.symm '' _` (matching `Rado.IsReplaceDisk`), so
they are honest subsets of `e.source` with no junk-value pitfalls.
-/

open Set Metric Topology

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A **chart disk**: a maximal-atlas chart `e`, center `c`, radius `ρ > 0`,
with the closed disk seated inside `e.target`. -/
structure ChartDisk (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] where
  /-- The underlying chart (a maximal-atlas partial homeomorphism). -/
  e : OpenPartialHomeomorph X ℂ
  /-- The chart lies in the maximal atlas. -/
  he : e ∈ riemannAtlas X
  /-- The disk center, in the chart's target. -/
  c : ℂ
  /-- The disk radius. -/
  ρ : ℝ
  /-- The radius is positive. -/
  ρ_pos : 0 < ρ
  /-- The closed disk is seated inside the chart target. -/
  seated : closedBall c ρ ⊆ e.target

namespace ChartDisk

variable (d : ChartDisk X)

/-- Closed carrier of a chart disk (compact). -/
def disk : Set X := d.e.symm '' closedBall d.c d.ρ

/-- Open carrier of a chart disk (open). -/
def odisk : Set X := d.e.symm '' ball d.c d.ρ

/-- Boundary circle of a chart disk. -/
def circ : Set X := d.e.symm '' sphere d.c d.ρ

theorem ball_seated : ball d.c d.ρ ⊆ d.e.target :=
  ball_subset_closedBall.trans d.seated

theorem sphere_seated : sphere d.c d.ρ ⊆ d.e.target :=
  sphere_subset_closedBall.trans d.seated

theorem odisk_subset_disk : d.odisk ⊆ d.disk :=
  Set.image_mono ball_subset_closedBall

theorem circ_subset_disk : d.circ ⊆ d.disk :=
  Set.image_mono sphere_subset_closedBall

theorem disk_eq_odisk_union_circ : d.disk = d.odisk ∪ d.circ := by
  rw [disk, odisk, circ, ← Set.image_union, ball_union_sphere]

theorem disk_subset_source : d.disk ⊆ d.e.source := by
  rintro _ ⟨w, hw, rfl⟩; exact d.e.map_target (d.seated hw)

theorem odisk_subset_source : d.odisk ⊆ d.e.source :=
  d.odisk_subset_disk.trans d.disk_subset_source

theorem circ_subset_source : d.circ ⊆ d.e.source :=
  d.circ_subset_disk.trans d.disk_subset_source

theorem mem_odisk_iff {x : X} : x ∈ d.odisk ↔ x ∈ d.e.source ∧ d.e x ∈ ball d.c d.ρ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwt : w ∈ d.e.target := d.ball_seated hw
    exact ⟨d.e.map_target hwt, by rw [d.e.right_inv hwt]; exact hw⟩
  · rintro ⟨hs, hb⟩
    exact ⟨d.e x, hb, d.e.left_inv hs⟩

theorem mem_disk_iff {x : X} : x ∈ d.disk ↔ x ∈ d.e.source ∧ d.e x ∈ closedBall d.c d.ρ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwt : w ∈ d.e.target := d.seated hw
    exact ⟨d.e.map_target hwt, by rw [d.e.right_inv hwt]; exact hw⟩
  · rintro ⟨hs, hb⟩
    exact ⟨d.e x, hb, d.e.left_inv hs⟩

theorem mem_circ_iff {x : X} : x ∈ d.circ ↔ x ∈ d.e.source ∧ d.e x ∈ sphere d.c d.ρ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwt : w ∈ d.e.target := d.sphere_seated hw
    exact ⟨d.e.map_target hwt, by rw [d.e.right_inv hwt]; exact hw⟩
  · rintro ⟨hs, hb⟩
    exact ⟨d.e x, hb, d.e.left_inv hs⟩

theorem isOpen_odisk : IsOpen d.odisk :=
  d.e.symm.isOpen_image_of_subset_source isOpen_ball (by simpa using d.ball_seated)

theorem isCompact_disk : IsCompact d.disk :=
  (isCompact_closedBall d.c d.ρ).image_of_continuousOn
    (d.e.symm.continuousOn.mono (by simpa using d.seated))

theorem isCompact_circ : IsCompact d.circ :=
  (isCompact_sphere d.c d.ρ).image_of_continuousOn
    (d.e.symm.continuousOn.mono (by simpa using d.sphere_seated))

theorem isClosed_disk [T2Space X] : IsClosed d.disk := d.isCompact_disk.isClosed

theorem isClosed_circ [T2Space X] : IsClosed d.circ := d.isCompact_circ.isClosed

/-- The open carrier sits inside the interior of the closed carrier. -/
theorem odisk_subset_interior_disk : d.odisk ⊆ interior d.disk :=
  d.isOpen_odisk.subset_interior_iff.mpr d.odisk_subset_disk

/-- The frontier of the open carrier lies on the boundary circle. -/
theorem frontier_odisk_subset_circ [T2Space X] : frontier d.odisk ⊆ d.circ := by
  intro x hx
  have hcl : x ∈ d.disk :=
    (closure_minimal d.odisk_subset_disk d.isClosed_disk) (frontier_subset_closure hx)
  rcases d.disk_eq_odisk_union_circ ▸ hcl with h | h
  · have hnot : x ∉ d.odisk := by
      have := hx.2; rwa [d.isOpen_odisk.interior_eq] at this
    exact absurd h hnot
  · exact h

/-- The frontier of the closed carrier lies on the boundary circle. -/
theorem frontier_disk_subset_circ [T2Space X] : frontier d.disk ⊆ d.circ := by
  intro x hx
  have h1 : x ∈ d.disk := d.isClosed_disk.frontier_subset hx
  have h2 : x ∉ interior d.disk := hx.2
  rcases d.disk_eq_odisk_union_circ ▸ h1 with h | h
  · exact absurd (d.odisk_subset_interior_disk h) h2
  · exact h

end ChartDisk

/-- A **piece**: a finite set of *positive* chart disks (included) minus a
finite set of *negative* corner-rounding chart disks (subtracted). -/
structure PieceData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] where
  /-- Positive (included) disks. -/
  pos : Finset (ChartDisk X)
  /-- Negative (corner-rounding, subtracted) disks. -/
  neg : Finset (ChartDisk X)

namespace PieceData

variable (P : PieceData X)

/-- Union of all positive open carriers. -/
def posUnion : Set X := ⋃ d ∈ P.pos, d.odisk

/-- Union of all negative closed carriers. -/
def negUnion : Set X := ⋃ d ∈ P.neg, d.disk

/-- The raw (unfilled) piece: positive open carriers minus negative closed
carriers. -/
def raw : Set X := P.posUnion \ P.negUnion

/-- Union of all active boundary circles. -/
def bcircles : Set X := (⋃ d ∈ P.pos, d.circ) ∪ (⋃ d ∈ P.neg, d.circ)

theorem isOpen_posUnion : IsOpen P.posUnion :=
  isOpen_biUnion fun d _ ↦ d.isOpen_odisk

theorem isCompact_posClosedUnion : IsCompact (⋃ d ∈ P.pos, d.disk) :=
  P.pos.finite_toSet.isCompact_biUnion fun d _ ↦ d.isCompact_disk

theorem isCompact_negUnion : IsCompact P.negUnion :=
  P.neg.finite_toSet.isCompact_biUnion fun d _ ↦ d.isCompact_disk

theorem isClosed_negUnion [T2Space X] : IsClosed P.negUnion :=
  P.isCompact_negUnion.isClosed

theorem isCompact_bcircles : IsCompact P.bcircles :=
  (P.pos.finite_toSet.isCompact_biUnion fun d _ ↦ d.isCompact_circ).union
    (P.neg.finite_toSet.isCompact_biUnion fun d _ ↦ d.isCompact_circ)

theorem isOpen_raw [T2Space X] : IsOpen P.raw :=
  P.isOpen_posUnion.sdiff P.isClosed_negUnion

theorem posUnion_subset_closedUnion : P.posUnion ⊆ ⋃ d ∈ P.pos, d.disk :=
  Set.iUnion₂_mono fun d _ ↦ d.odisk_subset_disk

theorem raw_subset_posUnion : P.raw ⊆ P.posUnion := sdiff_subset

theorem raw_subset_posClosedUnion : P.raw ⊆ ⋃ d ∈ P.pos, d.disk :=
  P.raw_subset_posUnion.trans P.posUnion_subset_closedUnion

/-- The closed positive union contains the closure of the raw piece. -/
theorem closure_raw_subset [T2Space X] : closure P.raw ⊆ ⋃ d ∈ P.pos, d.disk :=
  closure_minimal P.raw_subset_posClosedUnion P.isCompact_posClosedUnion.isClosed

/-- The raw piece has compact closure. -/
theorem isCompact_closure_raw [T2Space X] : IsCompact (closure P.raw) :=
  P.isCompact_posClosedUnion.of_isClosed_subset isClosed_closure P.closure_raw_subset

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Frontier of a finite union sits inside the union of the frontiers. -/
private theorem frontier_biUnion_subset' {ι : Type*} (s : Finset ι) (f : ι → Set X) :
    frontier (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ s, frontier (f i) := by
  intro x hx
  have hxcl : x ∈ ⋃ i ∈ s, closure (f i) := by
    have := hx.1
    rwa [s.closure_biUnion f] at this
  simp only [Set.mem_iUnion] at hxcl ⊢
  obtain ⟨i, hi, hxi⟩ := hxcl
  refine ⟨i, hi, hxi, ?_⟩
  intro hxint
  exact hx.2 (interior_mono (subset_biUnion_of_mem (u := f) hi) hxint)

/-- **Frontier localisation** (W7 §1.1): every frontier point of the raw piece
lies on some active boundary circle. Filling only shrinks the frontier, so this
transfers to the final piece `V = fill (raw P)`. -/
theorem frontier_raw_subset_bcircles [T2Space X] : frontier P.raw ⊆ P.bcircles := by
  have hsub : frontier P.raw ⊆ frontier P.posUnion ∪ frontier P.negUnion := by
    have h1 : P.raw = P.posUnion ∩ P.negUnionᶜ := by
      rw [raw, Set.sdiff_eq]
    rw [h1]
    refine (frontier_inter_subset _ _).trans ?_
    rw [frontier_compl]
    intro x hx
    rcases hx with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  intro x hx
  rcases hsub hx with h | h
  · have := frontier_biUnion_subset' P.pos (fun d ↦ d.odisk) h
    simp only [Set.mem_iUnion] at this
    obtain ⟨d, hd, hxd⟩ := this
    exact Or.inl (Set.mem_biUnion hd (d.frontier_odisk_subset_circ hxd))
  · have := frontier_biUnion_subset' P.neg (fun d ↦ d.disk) h
    simp only [Set.mem_iUnion] at this
    obtain ⟨d, hd, hxd⟩ := this
    exact Or.inr (Set.mem_biUnion hd (d.frontier_disk_subset_circ hxd))

end PieceData

end Uniformization
