/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Injective
import Uniformization.Surface.Phi
import Uniformization.Surface.Regularity
import Uniformization.RMT.RiemannMapping

/-!
# Biholomorphism of a simply connected regular piece onto the unit ball

Anghel–Stan Theorem 10 + 11 packaged: a simply connected regular piece `V`
(from `exists_simply_connected_piece`) with `x₀ ∈ V` carries a holomorphic
bijection onto `ball 0 1` sending `x₀` to `0`.

Route: `exists_green_function` (M1) → `exists_phi_of_green` (M2a) gives
holomorphic `φ` with `‖φ‖ = e^{−G} < 1`, simple zero at `x₀`; `phi_injOn`
(M2b) gives injectivity; `φ` is an open embedding onto `φ '' V ⊆ ball 0 1`
(nonvanishing derivative from injectivity, as in `Packaging.lean`);
`IsSimplyConnected (φ '' V)` transfers along the homeomorphism-onto-image;
`φ '' V ≠ univ` (bounded); the ported RMT
`Complex.exists_bijOn_unitBall_map_eq_zero` upgrades to a bijection onto the
ball; compose.
-/

open Set Metric Topology

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Every simply connected regular piece is biholomorphic to the unit ball**
(Anghel–Stan Theorems 10 and 11). -/
theorem exists_biholo_ball [T2Space X]
    {V : Set X} (hVo : IsOpen V) (hVconn : IsConnected V)
    (hVcl : IsCompact (closure V)) (hVsc : IsSimplyConnected V)
    (hfr : (frontier V).Nonempty)
    (hreg : ∀ ξ ∈ frontier V, ExteriorDiskAt V ξ)
    {x₀ : X} (hx₀ : x₀ ∈ V) :
    ∃ φ : X → ℂ, HolomorphicOn φ V ∧ BijOn φ V (ball (0 : ℂ) 1) ∧ φ x₀ = 0 := by
  sorry

end Uniformization
