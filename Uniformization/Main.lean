/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib
import Uniformization.Surface.Dichotomy
import Uniformization.Pi1Free

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
  **Proved, sorry-free.**

* `uniformization` — a connected, noncompact, second countable Riemann surface
  with `H¹(X, ℝ) = 0` (written `Subsingleton (Hom(π₁ X, ℝ))`) is biholomorphic
  to either `ℂ` or the upper half plane.
  <https://lean-lang.org/eval/problems/uniformization/>.
  Proved modulo the single classical input `isFreeGroup_fundamentalGroup` below.

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

/-- **π₁ of an open surface is free.**

> Ahlfors–Sario, *Riemann Surfaces* (1960), §44A, p. 102; also Massey (1967).  Via
> J. H. C. Whitehead's spine, an open metric surface deformation retracts onto a subgraph of
> the 1-skeleton of any of its triangulations, hence is homotopy equivalent to a countable
> graph, whose fundamental group is free.

This is the **sole remaining gap** between `uniformization_key` and the harness statement
`uniformization`: everything downstream of it is proved sorry-free in
`Uniformization/Pi1Free.lean`.  The chain is
`X` open surface ⇒ triangulable (Radó) ⇒ spine retraction (Whitehead) ⇒ π₁ free.
Neither triangulability of *open* surfaces nor Whitehead's spine is in Mathlib at the pin,
and `reference/classification-of-surfaces/` cannot supply them — its Moise development is
compact-only (`moise_finite_chart_cover` needs a *finite* chart cover) and carries live
sorries of its own.

**On the shape of the statement.**  `Uniformization/Surface/PhiHomTrivial.lean` flags an
"open mathematical question (T3)": how can `H¹(X, ℝ) = 0` kill an `ℝ/2πℤ`-valued modulus
monodromy when abstract group theory cannot (`Hom(ℤ/2, ℝ) = 0` yet
`Hom(ℤ/2, ℝ/2πℤ) ≠ 0`)?  Freeness is the answer: the counterexample cannot arise, because a
free group is torsion-free.  Indeed freeness gives the *stronger* conclusion
`SimplyConnectedSpace X` outright, which is why this file can route through
`uniformization_key` and leave the `HomTrivialLoops` / `HomTrivialRMT` layer (built to avoid
needing simple connectivity) out of the critical path entirely.

**A strictly weaker sufficient input, if freeness proves too expensive.**  T3 needs only
`Hom(π₁ X, ℝ/2πℤ) = 0`, i.e. `H¹(X; ℝ/ℤ) = 0`, i.e. `H₁(X; ℤ)` torsion-free.  By the
Bockstein sequence of `0 → ℤ → ℝ → ℝ/ℤ → 0`,
`H¹(X;ℝ) → H¹(X;ℝ/ℤ) → H²(X;ℤ)`, so `H²(X;ℤ) = 0` — standard for any connected noncompact
`n`-manifold in top degree — suffices.  That route discharges T3 without triangulation, but
it lands in the `HomTrivial*` layer rather than here, and `H²` of manifolds is likewise
absent from Mathlib.

Full write-up, with both routes costed:
`reference/uniformization/pi1-open-surface-free.md`. -/
theorem isFreeGroup_fundamentalGroup (hX : ¬ CompactSpace X) (x : X) :
    IsFreeGroup (FundamentalGroup X x) := by
  sorry

/-- **H¹(X, ℝ) = 0 ⇒ simply connected, for a noncompact Riemann surface.**

Proved from `isFreeGroup_fundamentalGroup` (the one remaining classical gap) via the two
sorry-free reductions in `Uniformization/Pi1Free.lean`:
`Hom(π₁, ℝ) = 0` + `π₁` free ⇒ `π₁` trivial ⇒ (with path connectedness) simply connected. -/
theorem simplyConnectedSpace_of_homTrivial (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    SimplyConnectedSpace X := by
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  haveI : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  haveI := isFreeGroup_fundamentalGroup hX x
  exact Uniformization.simplyConnectedSpace_of_subsingleton_fundamentalGroup x
    (Uniformization.subsingleton_of_isFreeGroup _ inferInstance)

theorem uniformization (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  haveI := simplyConnectedSpace_of_homTrivial hX x
  exact Uniformization.uniformization_of_key hX

end LeanEval.Geometry
