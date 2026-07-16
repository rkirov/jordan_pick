/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Rado.Surface.Barriers

/-!
# Dirichlet problem on exterior-disk-regular domains

`ExteriorDiskAt W ξ` says a chart around the frontier point `ξ` contains a
closed disk touching `e ξ` whose interior misses `W` — the classical exterior
disk condition. It yields a strong log-barrier at `ξ` (use a smaller disk
internally tangent at `e ξ` to get quantitative separation away from `ξ`, then
extend by `max` with a negative constant outside the chart annulus, as in
`Rado/Surface/Barriers.lean`).

`exists_dirichlet_solution` solves the Dirichlet problem by Perron's method on
a relatively compact open set all of whose frontier points satisfy the
exterior disk condition: normalize the boundary data into `[0,1]`, run
`Rado.IsPerronFamily`/`Rado.perronSup`, and prove boundary attainment with the
barrier.
-/

open Set Metric Topology

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The exterior disk condition at a point `ξ` (relative to a set `W ⊆ X`):
some chart around `ξ` contains a closed disk whose interior misses `W` and
whose boundary circle passes through `e ξ`. This is the regularity condition
our exhaustion pieces satisfy at every frontier point. -/
def ExteriorDiskAt (W : Set X) (ξ : X) : Prop :=
  ∃ e ∈ riemannAtlas X, ξ ∈ e.source ∧ ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
    closedBall c r ⊆ e.target ∧ dist (e ξ) c = r ∧
    ∀ x ∈ W ∩ e.source, e x ∉ ball c r

/-- **Perron solution of the Dirichlet problem** on a relatively compact open
set with exterior-disk-regular frontier. -/
theorem exists_dirichlet_solution [T2Space X]
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact (closure W))
    (hfr : (frontier W).Nonempty)
    (hreg : ∀ ξ ∈ frontier W, ExteriorDiskAt W ξ)
    {f : X → ℝ} (hfc : ContinuousOn f (frontier W)) :
    ∃ u : X → ℝ, SurfaceHarmonicOn u W ∧ ContinuousOn u (closure W) ∧
      EqOn u f (frontier W) ∧
      ∀ x ∈ closure W, u x ∈ Icc (sInf (f '' frontier W)) (sSup (f '' frontier W)) := by
  sorry

end Uniformization
