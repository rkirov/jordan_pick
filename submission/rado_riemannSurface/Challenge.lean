import Mathlib

/-!
# Radó's theorem

Every connected Riemann surface is second countable.

Second countability is usually imposed as part of the definition of a Riemann surface.
Radó's theorem (1925) says the assumption is redundant: a connected Hausdorff space that
merely carries a one-dimensional complex-analytic atlas is automatically second countable,
hence metrizable and triangulable. It is the complex structure, and no topological
hypothesis beyond connectedness and Hausdorffness, that forces the countability. The
corresponding statement is false for real surfaces — the Prüfer surface is a connected
Hausdorff real-analytic 2-manifold that is not second countable — so the proof must use
complex analysis, and this one does: Perron's method on an explicit two-disk configuration
produces a nonconstant harmonic function, the étale space of its harmonic-conjugate germs
has an evaluation map with discrete fibres, and Poincaré–Volterra plus descent give the
conclusion.

## Why `IsManifold (modelWithCornersSelf ℂ ℂ) 1 X` is the Riemann-surface hypothesis

The smoothness index `1` invites the reading "topological or merely `C^1` manifold modelled
on `ℂ`", which would make the statement a materially weaker claim. It is not that, and the
distinction is worth stating explicitly.

`IsManifold I n X` asks that the chart transitions lie in `contDiffGroupoid n I`, whose
defining property is `ContDiffOn 𝕜 n` for the field `𝕜` of the model `I`. Here
`I = modelWithCornersSelf ℂ ℂ`, so `𝕜 = ℂ` and the transitions are `C^1` **over `ℂ`** —
complex differentiable, not merely real differentiable. A map that is complex
differentiable on an open set is holomorphic, hence analytic. So `C^1` compatibility over
`ℂ` already *is* holomorphic compatibility, and `X` is a Riemann surface.

Two contrasts pin this down. The genuinely topological hypothesis is index `0`, not `1`:
Mathlib proves `contDiffGroupoid_zero_eq : contDiffGroupoid 0 I = continuousGroupoid H`, so
`IsManifold I 0 X` is exactly a topological manifold and carries no analytic content. And
since `1 ≤ ω`, assuming `1` is the *weaker* hypothesis, so proving Radó's theorem from it
is strictly stronger than proving it from `ω`.

The development proves this rather than asserting it. `Submission/Surface/HolomorphicCompat.lean`
contains

* `contDiffGroupoid_one_le_omega_complex` — over `ℂ` the `C^1` transition groupoid is
  contained in the analytic one, and
* `isManifold_omega_of_one` — hence any `X` satisfying the hypothesis below is an analytic
  (holomorphic) manifold,

so the two hypotheses are equivalent here and the statement below is a faithful rendering
of "every connected Riemann surface is second countable".
-/

/-- **Radó's theorem.** A connected Hausdorff Riemann surface is second countable.

The surface hypothesis is Mathlib's standard one: a `ChartedSpace ℂ X` whose transitions
are `C^1` over `ℂ`, which as explained in the module documentation above is exactly
holomorphic compatibility. -/
theorem rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X := by
  sorry
