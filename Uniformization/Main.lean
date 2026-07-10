/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib

/-!
# Uniformization theorem for Riemann surfaces (Hubbard Theorem 1.1.2)

Target (lean-eval `uniformization`, submitter Junyan Xu, source Hubbard
*Teichmüller theory* Vol. 1, Ch. 1): a connected, noncompact, second countable
Riemann surface `X` with `H¹(X, ℝ) = 0` (written `Subsingleton (Hom(π₁ X, ℝ))`)
is biholomorphic to either `ℂ` or the upper half plane.

This is the exact statement of
<https://lean-lang.org/eval/problems/uniformization/>.

Second countability is a hypothesis here (the harness hands it to us) precisely
to avoid overlap with Radó's theorem (`rado_riemannSurface`, proved in `Rado/`),
which supplies it in general.
-/

namespace LeanEval.Geometry

noncomputable abbrev mℂ := modelWithCornersSelf ℂ ℂ

open scoped Manifold ContDiff

theorem uniformization {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold mℂ 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  sorry

end LeanEval.Geometry
