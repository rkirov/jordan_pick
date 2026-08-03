/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib
import Uniformization.Surface.Limit

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
  obtain ⟨ψ, hψ, hinj⟩ := Uniformization.exists_uniformizer hX
  exact Uniformization.exists_diffeomorph_opens_of_injective hψ hinj

/-- **H¹(X, ℝ) = 0 ⇒ simply connected, for a noncompact Riemann surface.**

This is the one classical input still missing from Mathlib at the pin, and the sole
remaining gap between `uniformization_key` and the harness statement `uniformization`.

**It is not the open question** that `Uniformization/Surface/PhiHomTrivial.lean` describes.
That file asks how `HomTrivialLoops` can kill an `ℝ/2πℤ`-valued modulus monodromy when
abstract group theory cannot (`Hom(ℤ/2, ℝ) = 0` yet `Hom(ℤ/2, ℝ/2πℤ) ≠ 0`), and flags it
for "Hubbard §1.5–1.7".  The answer is that the counterexample cannot arise:

> **π₁ of an open surface is free** — Ahlfors–Sario, *Riemann Surfaces* (1960), §44A, p. 102;
> also Massey (1967).  Via J. H. C. Whitehead's spine, an open metric surface deformation
> retracts onto a subgraph of the 1-skeleton of any triangulation, hence is homotopy
> equivalent to a countable graph.

A free group is torsion-free, and `Hom(F, A) ≅ A ^ rank F` for abelian `A`.  So
`Hom(π₁ X, ℝ) = 0` forces `rank = 0`, i.e. `π₁ X` trivial — which is *stronger* than
killing the monodromy, and makes the whole `HomTrivialLoops` / `HomTrivialRMT` layer
(≈700 lines, built to avoid needing simple connectivity) unnecessary for this route.

**Cost to discharge.**  The chain is: `X` open surface ⇒ triangulable (Radó) ⇒ spine
retraction (Whitehead) ⇒ `π₁` free ⇒ trivial.  The last step is easy in Mathlib; the first
two are absent from it, and `reference/classification-of-surfaces/` cannot supply them —
its Moise development is compact-only (`moise_finite_chart_cover` needs a *finite* chart
cover) and still carries live sorries of its own.  An alternative route avoiding π₁
entirely: `H²(X;ℤ) = 0` for a connected noncompact surface plus the Bockstein sequence of
`0 → ℤ → ℝ → ℝ/ℤ → 0` gives `H¹(X,ℝ) = 0 ⇒ H¹(X,ℝ/ℤ) = 0` directly.  Both are separate
projects of substantial size.

Full write-up, with both routes costed: `reference/uniformization/pi1-open-surface-free.md`. -/
theorem simplyConnectedSpace_of_homTrivial (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    SimplyConnectedSpace X := by
  sorry

theorem uniformization (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  -- Everything except `simplyConnectedSpace_of_homTrivial` is already available and
  -- sorry-free: with `SimplyConnectedSpace X` in hand this is exactly
  -- `Uniformization.uniformization_of_key hX` (`Uniformization/Surface/Dichotomy.lean`,
  -- itself `dichotomy_of_diffeo_opens (uniformization_key hX)`).  It cannot be written
  -- here because the import runs the other way: `Dichotomy.lean` consumes
  -- `uniformization_key` from *this* file.  Discharging the lemma above and moving this
  -- one line downstream is all that is left.
  sorry

end LeanEval.Geometry
