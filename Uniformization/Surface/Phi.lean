/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Green

/-!
# The map `φ = exp (−G − iF)` via a covering-space section

Given a Green's function `G` for a simply connected piece `U`, we produce a
global holomorphic `φ : U → ℂ` with `‖φ‖ = exp (−G)` on `U \ {x₀}` and a
simple zero at `x₀`. This replaces Anghel–Stan's period-quantization argument
(their Thm 10, first half, which uses Sard + Stokes).

Design (see PLAN.md "Design decisions v2"): build the étale space of germs of
local holomorphic `ψ` with `‖ψ‖ = exp (−G)` away from `x₀`, on domains that
may include `x₀` (where such `ψ` must vanish; locally `ψ = ξ·e^{−(H+iH̃)}`
in the pole chart). Two branches over a connected open agree up to a unimodular
constant (their ratio is holomorphic with constant modulus `1`, hence locally
constant), so:
* fibers are discrete;
* over a small disk in `U \ {x₀}` the sheets are `{c·ψ₀ : c ∈ S¹}` — trivial
  `S¹`-torsor;
* over the pole chart every branch on the punctured disk extends across `x₀`
  (its ratio to the distinguished branch `ξ·e^{−(H+iH̃)}` is constant), so the
  covering is trivialized there too — the integer residue of the log pole, in
  multiplicative form.
Hence the projection is an `IsCoveringMap` over ALL of `U`; `U` simply
connected (+ locally path-connected) gives a global section through the
distinguished germ at `x₀`, and `φ := eval ∘ section`. Mirror the étale-space
implementation of `Rado/Surface/Germs.lean` (sheets, basic sets, `proj`,
`eval`) in multiplicative form, then use path/homotopy lifting
(`Mathlib/Topology/Homotopy/Lifting.lean`, `IsCoveringMap`) or the
monodromy-style argument to produce the section.
-/

open Set Metric Topology InnerProductSpace

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Global holomorphic `φ` with `‖φ‖ = e^{−G}`** on a simply connected piece
(Anghel–Stan Theorem 10, existence half — Sard-free). -/
theorem exists_phi_of_green [T2Space X] {U : Set X} {x₀ : X} {G : X → ℝ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hx₀ : x₀ ∈ U)
    (hG : IsGreenFunction U x₀ G) :
    ∃ φ : X → ℂ, HolomorphicOn φ U ∧ φ x₀ = 0 ∧
      (∀ x ∈ U \ {x₀}, ‖φ x‖ = Real.exp (-G x)) ∧
      ∃ e ∈ riemannAtlas X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
        deriv (φ ∘ e.symm) 0 ≠ 0 := by
  sorry

end Uniformization
