/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Crossing parity via `Circle.exp` lifting (W7 step L6, abstract core)

The winding-number engine behind the Anghel–Stan crossing-parity argument
(W7_PLAN.md §L6, D5). It abstracts the `Moise/NoRetraction.lean` skeleton:
given a **simply connected** ambient space `X`, a continuous phase map
`τ : X → Circle`, a loop `δ : Path x x`, and *any* continuous real lift `Λ` of
the composite `τ ∘ δ` (i.e. `Circle.exp (Λ t) = τ (δ t)` for all `t`), the lift
returns to its start:

  `Λ 1 = Λ 0`.

Interpretation: the winding number of `τ ∘ δ` around the circle is forced to be
zero because `δ` is null-homotopic in the simply connected `X`. Contrapositive
(the form L6 uses): if one exhibits an explicit lift with `Λ 1 ≠ Λ 0` — e.g. a
collar phase that increases by `2π` across a single transversal crossing of a
frontier arc-cycle — then no such `δ` can exist, which is the contradiction
ruling out a *disconnected* complement-end frontier.

The proof compares two lifts of the loop `τ ∘ δ` starting at `Λ 0`: the given
`Λ`, and the constant lift of the constant loop `τ x`, which are lifts of
`{0,1}`-homotopic loops (`τ ∘ δ` vs. `τ ∘ (refl x)`, homotopic because
`δ ≃ refl x` in the simply connected `X`), hence share their endpoint via
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` for `Circle.isCoveringMap_exp`.
-/

open Set Topology
open scoped unitInterval

namespace Uniformization

variable {X : Type*} [TopologicalSpace X]

/-- **Winding of a lifted loop through a simply connected space vanishes.**
For a continuous `τ : X → Circle`, a loop `δ : Path x x` in a simply connected
`X`, and any continuous real lift `Λ` of `τ ∘ δ`, the lift is a loop:
`Λ 1 = Λ 0`. This is the abstract L6 crossing-parity contradiction engine. -/
theorem lift_endpoint_eq_of_simplyConnected [SimplyConnectedSpace X]
    {τ : X → Circle} (hτ : Continuous τ) {x : X} (δ : Path x x)
    (Λ : C(I, ℝ)) (hlift : ∀ t, Circle.exp (Λ t) = τ (δ t)) :
    Λ 1 = Λ 0 := by
  set cov := Circle.isCoveringMap_exp with hcov
  set τc : C(X, Circle) := ⟨τ, hτ⟩ with hτc
  -- the loop `τ ∘ δ` and the constant loop at `τ x`
  set γ₀ : C(I, Circle) := τc.comp δ.toContinuousMap with hγ₀
  set γ₁ : C(I, Circle) := τc.comp (Path.refl x).toContinuousMap with hγ₁
  set e : ℝ := Λ 0 with he
  -- `Λ` lifts `γ₀`
  have hcomp : (Circle.exp : ℝ → Circle) ∘ (Λ : I → ℝ) = (γ₀ : I → Circle) := by
    funext t; exact hlift t
  have hδ0 : δ 0 = x := δ.source
  -- endpoint hypotheses for the two lifts, both starting at `e`
  have h₀ : γ₀ 0 = Circle.exp e := by
    show τ (δ 0) = Circle.exp (Λ 0)
    rw [hlift 0]
  have h₁ : γ₁ 0 = Circle.exp e := by
    show τ ((Path.refl x) 0) = Circle.exp (Λ 0)
    rw [hlift 0, hδ0]; rfl
  -- the two loops are homotopic rel `{0,1}` (via `δ ≃ refl x` in simply conn. `X`)
  have hhr : γ₀.HomotopicRel γ₁ {0, 1} :=
    ContinuousMap.HomotopicRel.comp_continuousMap
      (SimplyConnectedSpace.paths_homotopic δ (Path.refl x)) τc
  -- `Λ` is the lift of `γ₀`
  have hLHS : Λ = cov.liftPath γ₀ e h₀ := (cov.eq_liftPath_iff' h₀).mpr ⟨hcomp, rfl⟩
  -- the constant lift is the lift of `γ₁`
  have hexp_e : Circle.exp e = τ x := by rw [← hδ0]; exact hlift 0
  have hRHS : (ContinuousMap.const I e) = cov.liftPath γ₁ e h₁ := by
    refine (cov.eq_liftPath_iff' h₁).mpr ⟨?_, rfl⟩
    funext t
    show Circle.exp e = τ ((Path.refl x) t)
    rw [hexp_e]; rfl
  -- the two lifts share their endpoint
  have hend : cov.liftPath γ₀ e h₀ 1 = cov.liftPath γ₁ e h₁ 1 :=
    cov.liftPath_apply_one_eq_of_homotopicRel hhr e h₀ h₁
  calc Λ 1 = cov.liftPath γ₀ e h₀ 1 := by rw [hLHS]
    _ = cov.liftPath γ₁ e h₁ 1 := hend
    _ = (ContinuousMap.const I e) 1 := by rw [hRHS]
    _ = Λ 0 := rfl

end Uniformization
