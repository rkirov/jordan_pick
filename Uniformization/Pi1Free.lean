/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib

/-!
# From "π₁ is free" to "simply connected"

This file discharges everything *downstream* of the one classical input that
`LeanEval.Geometry.uniformization` still needs, namely that the fundamental group of an
open (= connected, noncompact) surface is free.  See
`reference/uniformization/pi1-open-surface-free.md`.

Two steps, both sorry-free:

* `Uniformization.subsingleton_of_isFreeGroup` — a free group admitting no nontrivial
  `ℝ`-valued homomorphism is trivial.  (`Hom(F, ℝ) ≅ ℝ ^ rank F`, so `Subsingleton`
  forces the generating set to be empty.)
* `Uniformization.simplyConnectedSpace_of_subsingleton_fundamentalGroup` — a path
  connected space with trivial fundamental group *at a single basepoint* is simply
  connected.

Composing them reduces `uniformization`'s hypothesis `Subsingleton (Additive π₁ →+ ℝ)`,
i.e. `H¹(X, ℝ) = 0`, to `SimplyConnectedSpace X`, which is exactly what
`uniformization_key` consumes.
-/

namespace Uniformization

/-- **A free group with no nontrivial `ℝ`-valued homomorphism is trivial.**

For a free group `F` with basis `B` one has `Hom(F, ℝ) ≅ ℝ ^ B`, so `Subsingleton` of the
hom-set forces `B = ∅` and hence `F = 1`.  Concretely: a nonempty basis lets us build the
homomorphism sending one chosen generator to `1 : ℝ` and the rest to `0`, which is not the
zero map. -/
theorem subsingleton_of_isFreeGroup (G : Type*) [Group G] [IsFreeGroup G]
    (h : Subsingleton (Additive G →+ ℝ)) : Subsingleton G := by
  classical
  -- Step 1: the chosen generating set is empty.
  have hempty : IsEmpty (IsFreeGroup.Generators G) := by
    rw [isEmpty_iff]
    intro a
    -- The generator-indicator function, lifted to a homomorphism `G →* Multiplicative ℝ`.
    set f : IsFreeGroup.Generators G → Multiplicative ℝ :=
      fun b => if b = a then Multiplicative.ofAdd (1 : ℝ) else 1 with hf
    set φ : G →* Multiplicative ℝ := IsFreeGroup.lift f with hφ
    -- Repackage it as an element of the hom-set the hypothesis is about.
    set ψ : Additive G →+ ℝ :=
      { toFun := fun g => Multiplicative.toAdd (φ (Additive.toMul g))
        map_zero' := by simp
        map_add' := fun u v => by simp } with hψ
    -- It sends the chosen generator to `1`, so it is not the zero map …
    have h1 : ψ (Additive.ofMul (IsFreeGroup.of a)) = 1 := by
      simp [hψ, hφ, hf]
    -- … contradicting `Subsingleton`.
    rw [h.elim ψ 0] at h1
    simp at h1
  -- Step 2: no generators ⇒ the identity equals the trivial homomorphism.
  have hid : (MonoidHom.id G) = (1 : G →* G) :=
    IsFreeGroup.ext_hom fun a => (hempty.false a).elim
  have key : ∀ g : G, g = 1 := fun g => by
    have := congrArg (fun F : G →* G => F g) hid
    simpa using this
  exact ⟨fun a b => by rw [key a, key b]⟩

/-- **Trivial fundamental group at one basepoint ⇒ simply connected**, for a path connected
space.

Mathlib's `simply_connected_iff_loops_nullhomotopic` quantifies over *all* basepoints; path
connectedness transports the hypothesis from the given one via
`FundamentalGroup.fundamentalGroupMulEquivOfPathConnected`. -/
theorem simplyConnectedSpace_of_subsingleton_fundamentalGroup {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x₀ : X) (h : Subsingleton (FundamentalGroup X x₀)) :
    SimplyConnectedSpace X := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x γ => ?_⟩
  haveI : Subsingleton (FundamentalGroup X x₀) := h
  haveI hx : Subsingleton (FundamentalGroup X x) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x₀ x).symm.injective.subsingleton
  -- `FundamentalGroup X x` is the endomorphism monoid of `x` in the fundamental groupoid,
  -- i.e. `Path.Homotopic.Quotient x x`, but only up to unfolding.
  have hq : (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
    @Subsingleton.elim (FundamentalGroup X x) hx _ _
  exact Quotient.eq.mp hq

end Uniformization
