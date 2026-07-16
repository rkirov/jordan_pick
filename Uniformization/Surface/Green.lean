/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Regularity
import Uniformization.Complex.RemovableHarmonic

/-!
# Green's function with logarithmic pole (Anghel–Stan Proposition 9)

On a relatively compact, connected, exterior-disk-regular open `U ⊆ X` with
`x₀ ∈ U`, there is a Green's function: continuous on `closure U \ {x₀}`,
harmonic on `U \ {x₀}`, zero on `frontier U`, positive inside, with
`G ∘ e.symm + log‖·‖` extending harmonically across `0` in a chart `e`
centered at `x₀`.

Proof plan (A–S Prop 9): fix a chart disk `D` at `x₀`; solve the Dirichlet
problem (`exists_dirichlet_solution`) on `U \ e.symm '' closedBall 0 (1/2)`
with data `1` on the inner circle, `0` on `frontier U`, giving `h₁`; choose
`A B` with `B·a < A < B·(1 − …)` as in the paper and form the subharmonic
comparison function `h = max (−B·h₁) (log‖·‖ − A)`; run Perron on the family
of nonneg subharmonic `g` vanishing on the frontier with `g + h ≤ 0`
(renormalized into `[0,1]` to fit `Rado.IsPerronFamily`); the sup `G` is
harmonic on `U \ {x₀}`, sandwiched `−log‖ξ‖ ≤ G ≤ A − log‖ξ‖` near `x₀`, so
`G + log‖ξ‖` is bounded and `exists_harmonicOnNhd_extension_of_bounded`
finishes the pole normalization. Positivity via the strong minimum principle
(`Rado.SubMeanOn.eqOn_const_of_isMaxOn` applied to `−G`).
-/

open Set Metric Topology InnerProductSpace

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- `G` is a Green's function for the (relatively compact, open) set `U`
with pole at `x₀ ∈ U`. -/
structure IsGreenFunction (U : Set X) (x₀ : X) (G : X → ℝ) : Prop where
  continuousOn : ContinuousOn G (closure U \ {x₀})
  harmonicOn : SurfaceHarmonicOn G (U \ {x₀})
  pos : ∀ x ∈ U \ {x₀}, 0 < G x
  zero_frontier : EqOn G 0 (frontier U)
  /-- Logarithmic pole: in some chart centered at `x₀`, `G + log‖·‖` extends
  harmonically across the puncture. -/
  log_pole : ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : ℂ) r ⊆ e.target ∧
      e.symm '' closedBall (0 : ℂ) r ⊆ U ∧
      ∃ H : ℂ → ℝ, HarmonicOnNhd H (ball (0 : ℂ) r) ∧
        ∀ z ∈ ball (0 : ℂ) r \ {0}, G (e.symm z) = -Real.log ‖z‖ + H z

/-- **Existence of the Green's function** (Anghel–Stan Proposition 9) on a
relatively compact, connected, exterior-disk-regular open set. -/
theorem exists_green_function [T2Space X]
    {U : Set X} (hUo : IsOpen U) (hUc : IsCompact (closure U))
    (hUconn : IsPreconnected U)
    (hfr : (frontier U).Nonempty)
    (hreg : ∀ ξ ∈ frontier U, ExteriorDiskAt U ξ)
    {x₀ : X} (hx₀ : x₀ ∈ U) :
    ∃ G : X → ℝ, IsGreenFunction U x₀ G := by
  sorry

end Uniformization
