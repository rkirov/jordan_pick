/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib

/-!
# Uniformization theorem for Riemann surfaces (Hubbard Theorem 1.1.2)

Two lean-eval targets (submitter Junyan Xu), stated exactly as in
`LeanEval/Geometry/Uniformization.lean` after lean-eval PR #473:

* `uniformization_key` — a connected, noncompact, second countable, **simply
  connected** Riemann surface is biholomorphic to an open subset of `ℂ`.
  This is the "key step" problem added by PR #473: per its manifest note, it
  "just needs to be combined with the Riemann mapping theorem and Radó's
  theorem to yield a full proof" of `uniformization`. Source: Anghel–Stan,
  *Uniformization of Riemann surfaces revisited*, arXiv:2008.12189.

* `uniformization` — a connected, noncompact, second countable Riemann surface
  with `H¹(X, ℝ) = 0` (written `Subsingleton (Hom(π₁ X, ℝ))`) is biholomorphic
  to either `ℂ` or the upper half plane.
  <https://lean-lang.org/eval/problems/uniformization/>.

Second countability is a hypothesis in both (the harness hands it to us)
precisely to avoid overlap with Radó's theorem (`rado_riemannSurface`, proved
in `Rado/`), which supplies it in general.
-/

namespace LeanEval.Geometry

noncomputable abbrev mℂ := modelWithCornersSelf ℂ ℂ

open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
variable [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold mℂ 1 X]

theorem uniformization_key (hX : ¬ CompactSpace X) [SimplyConnectedSpace X] :
    ∃ D : TopologicalSpace.Opens ℂ, Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ D) := by
  sorry

theorem uniformization (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  sorry

end LeanEval.Geometry
