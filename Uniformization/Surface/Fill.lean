/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Regularity

/-!
# Simply connected regular pieces exhausting a simply connected surface

The topological heart of the uniformization project (workstream W7 in
PLAN.md): every compact subset of a noncompact simply connected Riemann
surface is contained in a relatively compact, connected, **simply connected**
open piece all of whose frontier points satisfy the exterior disk condition.

Intended proof (A–S Theorem 12, Sard-free variant; see PLAN.md "Design
decisions v2" §2–3 and the templates listed under
`reference/classification-of-surfaces`):
1. Cover `K` by finitely many closed chart disks with generically chosen
   centers/radii (transversal boundary intersections; tangency radii are
   countable by analyticity), connected through a chain to `x₀ ∈ K`.
2. Hole-fill: add the relatively compact components of the complement.
   Frontier is preserved or shrunk, so exterior-disk regularity survives.
3. The frontier of each complement component decomposes into finitely many
   arc-cycles (combinatorial tracing at generic corners; no Jordan curve
   theorem). Each unbounded complement component has CONNECTED frontier —
   crossing-parity: an explicit collar of an arc-cycle yields `τ : X → S¹`
   with `τ = 1` off the collar; a loop crossing once has winding `±1`,
   contradicting `SimplyConnectedSpace X` via circle-covering lifting.
4. A–S retraction: collapse each unbounded complement component onto its
   frontier arc-cycle (cut along an escaping ray + Tietze, or the
   `FrontierGlue`-style vanishing-error collapse); a retraction `X → K̂`
   forces `π₁(K̂°) = 1`.
-/

open Set Metric Topology

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Simply connected regular pieces** (Anghel–Stan Theorem 12, single-piece
form). Every compact subset of a noncompact simply connected Riemann surface
lies in a relatively compact, connected, simply connected open set with
exterior-disk-regular frontier. -/
theorem exists_simply_connected_piece [T2Space X] [ConnectedSpace X]
    [SimplyConnectedSpace X] (hnc : ¬ CompactSpace X)
    {K : Set X} (hK : IsCompact K) {x₀ : X} (hx₀ : x₀ ∈ K) :
    ∃ V : Set X, IsOpen V ∧ IsConnected V ∧ IsCompact (closure V) ∧ K ⊆ V ∧
      IsSimplyConnected V ∧ (frontier V).Nonempty ∧
      ∀ ξ ∈ frontier V, ExteriorDiskAt V ξ := by
  sorry

end Uniformization
