import Submission.Surface.Assembly

/-!
# lean-eval `rado_riemannSurface` — solver submission

**Radó's theorem**: a connected Hausdorff Riemann surface is second countable.

The full, self-contained proof lives in the re-rooted development under
`Submission/`, culminating in `Rado.secondCountableTopology_of_riemannSurface`
(`Submission/Surface/Assembly.lean`).
Route: Perron's method on an explicit two-disk configuration (Schwarz/Poisson
solution of the Dirichlet problem, chartwise subharmonic functions, explicit
log-barriers) produces a nonconstant harmonic function; the étale space of its
harmonic-conjugate germs has an evaluation map with discrete fibers; the
Poincaré–Volterra lemma and descent along the open covering projection give
second countability. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`),
depends only on Mathlib.
-/

namespace Submission

-- Statement copied verbatim from Challenge.lean; only the proof is replaced
-- with a delegation to our development.
theorem rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X :=
  Rado.secondCountableTopology_of_riemannSurface

end Submission
