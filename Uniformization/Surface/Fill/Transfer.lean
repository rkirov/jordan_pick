/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Piece.Round

/-!
# Reduction of the frozen target to the pure simple-connectivity criterion (W7 L10)

This file assembles the delivered L1–L4 layer (`exists_regular_piece`) with the
*single missing ingredient* of workstream W7 — that an exterior-disk-regular
piece whose complement has no compact component is simply connected — into the
frozen `exists_simply_connected_piece`.

Concretely `exists_simply_connected_piece_of_regularSimplyConnected` shows: **if**
one proves the pure topological statement

  `regularSimplyConnected` :=
    every open, connected, relatively compact `V` in the simply connected
    surface `X`, with nonempty exterior-disk-regular frontier and no compact
    complement component, is simply connected,

**then** the frozen theorem follows immediately. This isolates the exact
remaining mathematical content of steps L5–L9 (collar structure, crossing
parity, escaping ray, retraction, and inner-collar transfer) as one crisp
hypothesis about a *given* piece, stripping away the L1–L4 construction. The
abstract engines feeding that hypothesis are delivered sorry-free in
`Uniformization/Surface/Fill/Retraction.lean` (retract ⇒ simply connected, the
L8 conclusion mechanism) and `Uniformization/Surface/Fill/Parity.lean` (the L6
`Circle.exp`-lifting crossing-parity contradiction).

Nothing here is `sorry`; the reduction is complete and the only gap left in the
project is the `regularSimplyConnected` hypothesis itself, which is precisely
`Fill.lean`'s remaining `sorry`.
-/

open Set Metric Topology

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The pure simple-connectivity criterion isolated by W7 steps L5–L9: on a
simply connected surface every open connected relatively compact set with
nonempty exterior-disk-regular frontier and no compact complement component is
simply connected. This is exactly the missing content; everything else in
`exists_simply_connected_piece` is delivered by `exists_regular_piece`. -/
def RegularSimplyConnected (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] : Prop :=
  ∀ V : Set X, IsOpen V → IsConnected V → IsCompact (closure V) →
    (frontier V).Nonempty → (∀ ξ ∈ frontier V, ExteriorDiskAt V ξ) →
    (∀ x ∉ V, ¬ IsCompact (connectedComponentIn Vᶜ x)) → IsSimplyConnected V

/-- **W7 L10 reduction.** Granting the pure criterion `RegularSimplyConnected X`,
the frozen `exists_simply_connected_piece` holds: apply `exists_regular_piece`
to obtain the piece `V` with every conjunct except simple connectivity, then
discharge that last conjunct from the criterion. -/
theorem exists_simply_connected_piece_of_regularSimplyConnected
    [T2Space X] [ConnectedSpace X] (hsc : RegularSimplyConnected X)
    (hnc : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) {x₀ : X} (hx₀ : x₀ ∈ K) :
    ∃ V : Set X, IsOpen V ∧ IsConnected V ∧ IsCompact (closure V) ∧ K ⊆ V ∧
      IsSimplyConnected V ∧ (frontier V).Nonempty ∧
      ∀ ξ ∈ frontier V, ExteriorDiskAt V ξ := by
  obtain ⟨V, hVo, hVconn, hVcl, hKV, -, hVfr, hVext, hVnc⟩ :=
    exists_regular_piece hnc hK hx₀
  exact ⟨V, hVo, hVconn, hVcl, hKV, hsc V hVo hVconn hVcl hVfr hVext hVnc, hVfr, hVext⟩

end Uniformization
