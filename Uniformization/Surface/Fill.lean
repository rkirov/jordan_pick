/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.Collapse

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
  -- Take the harmonic level-set piece (F3.b/F3.c part 1); it already delivers
  -- every conjunct of the frozen theorem except simple connectivity, together
  -- with the harmonic collar data (`f`, `c`, `A`, the dichotomy, the
  -- straightening charts) driving the remaining W7 topology.
  obtain ⟨V, f, c, A, hVo, hVconn, hVcl, hKV, hVfr, hVnc, hAo, hfrA, hharm,
    hfc, hchart, hdich, hext⟩ := exists_level_piece_regular_frontier hnc hK hx₀
  refine ⟨V, hVo, hVconn, hVcl, hKV, ?_, hVfr, hext⟩
  -- Remaining W7 content: `IsSimplyConnected V`.
  --
  -- Collar layer (delivered, `Fill/Collar.lean`): `exists_collar_dichotomy hdich hfc`
  -- yields an open `A' ⊇ frontier V` with `x ∈ V ↔ c < f x` for all `x ∈ A'`, so
  -- the harmonic `f` is a global two-sided collar coordinate: `V`-side `{c < f}`,
  -- complement-side `{f ≤ c}`, `frontier V ⊆ {f = c}`.
  --
  -- Remaining (classical surface topology, NOT discharged — see report):
  --   L5.4  per-end frontier connectivity via `Fill/Parity.lean`
  --         (`lift_endpoint_eq_of_simplyConnected`) + a collar phase `τ : X → Circle`;
  --   L5.5  escaping ray in each noncompact complement end + cut/Tietze collapse,
  --         glued by `frontierGlue`, giving a retraction `r : C(X,X)` onto
  --         `closure V`, then `isSimplyConnected_of_retract` (`Fill/Retraction.lean`)
  --         ⇒ `IsSimplyConnected (closure V)`;
  --   L5.6  inner-collar push (the flow of `f`) as a homotopy equivalence
  --         `↥V ≃ₕ ↥(closure V)`, then `HomotopyEquiv.simplyConnectedSpace`
  --         ⇒ `IsSimplyConnected V`.
  obtain ⟨r, hrV, hrid⟩ :=
    exists_retraction_onto_closure hVo hVconn hVcl hVnc hAo hfrA hharm hfc hchart hdich
  have hcl_sc : IsSimplyConnected (closure V) := isSimplyConnected_of_retract r hrV hrid
  exact isSimplyConnected_of_closure hVo hVcl hdich hfc hchart hcl_sc

end Uniformization
