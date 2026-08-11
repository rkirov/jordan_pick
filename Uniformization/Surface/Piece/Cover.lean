/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Piece.Data

/-!
# Covering a compact set by connected chart disks (W7 step L1)

`exists_pos_cover`: given a compact `K` on a Riemann surface and `x₀ ∈ K`,
there is a finite family `pos` of chart disks and a **compact connected
connector** `T` with `x₀ ∈ T`, `K ⊆ T`, and `T ⊆ ⋃ d ∈ pos, odisk d`.

The connector `T` (rather than connectedness of the disk union itself) is
what the downstream rounding step consumes: the corner-rounding negative
disks are chosen to miss `T`, so `T` survives inside `raw P` and forces `K`
into a single connected component of `raw P` — sidestepping any need to
prove that subtracting the rounding disks preserves connectedness of the
whole union (see `Uniformization/Surface/Piece/Round.lean`).

Construction: cover `K` by half-radius open chart disks (compactness); join
`x₀` to the center of each covering disk by a path (the surface is path
connected: charted over `ℂ` ⇒ locally path connected, plus connectedness);
`T` is the union of the compact half-radius disks and the compact path
images; cover the path images by further half-radius disks to keep
`T ⊆ ⋃ odisk`.
-/

open Set Metric Topology

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Around every point there is a chart disk whose *half-radius* closed disk
is still a neighbourhood of the point. -/
theorem exists_chartDisk_around (y : X) :
    ∃ d : ChartDisk X, d.e = chartAt ℂ y ∧ d.c = chartAt ℂ y y ∧
      y ∈ d.e.symm '' ball d.c (d.ρ / 2) := by
  set e := chartAt ℂ y with he_def
  have hy : y ∈ e.source := mem_chart_source ℂ y
  have hyt : e y ∈ e.target := e.map_source hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target _ hyt
  refine ⟨⟨e, chartAt_mem_riemannAtlas y, e y, ε / 2, by positivity, ?_⟩, rfl, rfl, ?_⟩
  · exact (closedBall_subset_ball (by linarith)).trans hball
  · exact ⟨e y, mem_ball_self (by positivity), e.left_inv hy⟩

/-- The half-radius closed disk of a chart disk. -/
def ChartDisk.core (d : ChartDisk X) : Set X := d.e.symm '' closedBall d.c (d.ρ / 2)

/-- The half-radius open disk of a chart disk. -/
def ChartDisk.ocore (d : ChartDisk X) : Set X := d.e.symm '' ball d.c (d.ρ / 2)

theorem ChartDisk.ocore_subset_core (d : ChartDisk X) : d.ocore ⊆ d.core :=
  image_mono ball_subset_closedBall

theorem ChartDisk.core_subset_odisk (d : ChartDisk X) : d.core ⊆ d.odisk :=
  image_mono (closedBall_subset_ball (by linarith [d.ρ_pos]))

theorem ChartDisk.isOpen_ocore (d : ChartDisk X) : IsOpen d.ocore :=
  d.e.symm.isOpen_image_of_subset_source isOpen_ball
    (by simpa using (ball_subset_closedBall.trans
      ((closedBall_subset_ball (by linarith [d.ρ_pos])).trans d.ball_seated)))

theorem ChartDisk.isCompact_core (d : ChartDisk X) : IsCompact d.core :=
  (isCompact_closedBall _ _).image_of_continuousOn (d.e.symm.continuousOn.mono
    (by simpa using ((closedBall_subset_ball (by linarith [d.ρ_pos])).trans d.ball_seated)))

theorem ChartDisk.isConnected_core (d : ChartDisk X) : IsConnected d.core := by
  have hpos := d.ρ_pos
  refine ⟨(nonempty_closedBall.mpr (by positivity)).image _, ?_⟩
  refine (convex_closedBall d.c (d.ρ / 2)).isPreconnected.image _
    (d.e.symm.continuousOn.mono ?_)
  simpa using ((closedBall_subset_ball (by linarith)).trans d.ball_seated)

/-- **W7 step L1**: a compact set `K ∋ x₀` on a connected Riemann surface is
covered by finitely many chart disks admitting a compact connected connector
`T` through `x₀` inside the open disk union. -/
theorem exists_pos_cover [T2Space X] [ConnectedSpace X]
    {K : Set X} (hK : IsCompact K) {x₀ : X} (hx₀ : x₀ ∈ K) :
    ∃ (pos : Finset (ChartDisk X)) (T : Set X), IsCompact T ∧ IsConnected T ∧
      x₀ ∈ T ∧ K ⊆ T ∧ T ⊆ ⋃ d ∈ pos, d.odisk := by
  classical
  have : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.mpr ‹_›
  -- one chart disk per point, with a distinguished half-radius core
  choose D hDe hDc hDmem using fun y : X => exists_chartDisk_around y
  -- finitely many cores cover `K`
  obtain ⟨tK, htK⟩ := hK.elim_nhds_subcover' (fun y _ => (D y).ocore)
    (fun y _ => (D y).isOpen_ocore.mem_nhds (hDmem y))
  -- paths from `x₀` to the covering disks' distinguished points
  set Γ : Set X :=
    {x₀} ∪ ⋃ y ∈ tK, range ((PathConnectedSpace.joined x₀ ((y : K) : X)).somePath) with hΓdef
  have hΓcpt : IsCompact Γ := by
    refine isCompact_singleton.union (tK.finite_toSet.isCompact_biUnion fun y _ => ?_)
    exact isCompact_range (Path.continuous _)
  have hx₀Γ : x₀ ∈ Γ := Or.inl rfl
  have hΓconn : IsConnected Γ := by
    refine ⟨⟨x₀, hx₀Γ⟩, isPreconnected_of_forall x₀ ?_⟩
    rintro z (rfl | hz)
    · exact ⟨{z}, subset_union_left, rfl, rfl, isPreconnected_singleton⟩
    · simp only [mem_iUnion] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      refine ⟨range ((PathConnectedSpace.joined x₀ ((y : K) : X)).somePath),
        ?_, ⟨0, Path.source _⟩, hzy, (isConnected_range (Path.continuous _)).isPreconnected⟩
      exact fun w hw => Or.inr (mem_biUnion hy hw)
  -- finitely many cores cover `Γ`
  obtain ⟨tΓ, htΓ⟩ := hΓcpt.elim_nhds_subcover' (fun z _ => (D z).ocore)
    (fun z _ => (D z).isOpen_ocore.mem_nhds (hDmem z))
  -- the disk family and the connector
  set pos : Finset (ChartDisk X) :=
    tK.image (fun y => D ((y : K) : X)) ∪ tΓ.image (fun z => D ((z : Γ) : X)) with hpos_def
  set T : Set X := Γ ∪ ⋃ y ∈ tK, (D ((y : K) : X)).core with hTdef
  refine ⟨pos, T, ?_, ?_, Or.inl hx₀Γ, ?_, ?_⟩
  · -- compact
    exact hΓcpt.union (tK.finite_toSet.isCompact_biUnion fun y _ => (D _).isCompact_core)
  · -- connected
    refine ⟨⟨x₀, Or.inl hx₀Γ⟩, isPreconnected_of_forall x₀ ?_⟩
    rintro z (hz | hz)
    · exact ⟨Γ, subset_union_left, hx₀Γ, hz, hΓconn.isPreconnected⟩
    · simp only [mem_iUnion] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      have hyΓ : ((y : K) : X) ∈ Γ := Or.inr (mem_biUnion hy ⟨1, Path.target _⟩)
      have hycore : ((y : K) : X) ∈ (D ((y : K) : X)).core := (D _).ocore_subset_core (hDmem _)
      refine ⟨Γ ∪ (D ((y : K) : X)).core, ?_, Or.inl hx₀Γ, Or.inr hzy, ?_⟩
      · exact union_subset_union_right Γ (fun w hw => mem_biUnion hy hw)
      · exact IsPreconnected.union _ hyΓ hycore hΓconn.isPreconnected
          (D _).isConnected_core.isPreconnected
  · -- `K ⊆ T`
    intro z hz
    have := htK hz
    simp only [mem_iUnion] at this
    obtain ⟨y, hy, hzy⟩ := this
    exact Or.inr (mem_biUnion hy ((D _).ocore_subset_core hzy))
  · -- `T ⊆ ⋃ odisk`
    intro z hz
    rcases hz with hz | hz
    · have := htΓ hz
      simp only [mem_iUnion] at this
      obtain ⟨w, hw, hzw⟩ := this
      refine mem_biUnion (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)) ?_
      exact (D _).core_subset_odisk ((D _).ocore_subset_core hzw)
    · simp only [mem_iUnion] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      refine mem_biUnion (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)) ?_
      exact (D _).core_subset_odisk hzy

end Uniformization
