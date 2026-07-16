/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Rado.Surface.Charts

/-!
# Packaging an injective holomorphic map as a diffeomorphism onto its image

An injective holomorphic function `φ : X → ℂ` on a Riemann surface has open
image `D` and induces `X ≃ₘ⟮mℂ, mℂ⟯ D` (a `Diffeomorph … ∞`). This is the
final packaging step of `uniformization_key`.

Ingredients: injectivity forces the chart derivative of `φ` to be nonvanishing
(otherwise the local normal form `z ↦ c·zᵏ`, `k ≥ 2`, kills injectivity), so
`φ` is a local biholomorphism; the image is open (open mapping theorem), the
inverse is holomorphic, and both directions are `ContMDiff … ∞`.

⚠ Regularity subtlety: `X` carries only `IsManifold mℂ 1 X`, and the pin has
no `1 ⇒ ω` upgrade instance over `ℂ`. `ContMDiff`-composition lemmas that
require `[IsManifold I ∞ M]` are therefore unavailable; prove `ContMDiffAt`
statements directly from analyticity in the canonical charts (`contMDiffAt_iff`
-style unfolding + `AnalyticAt.contDiffAt`), and use
`Rado.transition_analyticAt` for chart changes.
-/

open Set Metric Topology
open scoped Manifold ContDiff

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Packaging**: an injective globally holomorphic map from a Riemann
surface to `ℂ` is a diffeomorphism onto an open subset of `ℂ`. -/
theorem exists_diffeomorph_opens_of_injective [T2Space X] {φ : X → ℂ}
    (hφ : HolomorphicOn φ univ) (hinj : Function.Injective φ) :
    ∃ D : TopologicalSpace.Opens ℂ,
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ D) := by
  sorry

end Uniformization
