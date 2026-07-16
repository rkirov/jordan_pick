/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Path

/-!
# Retracts of simply connected spaces (W7 step L8, abstract core)

The algebraic-topology engine behind the Anghel–Stan retraction step L8: a
continuous **retraction** of a simply connected space onto a subset `A`
(a map `r : X → X` landing in `A` and fixing `A` pointwise) forces `A` to be
simply connected.

The proof is the clean π₁-retract argument specialised to the null-homotopy
characterisation `isSimplyConnected_iff_exists_homotopy_refl_forall_mem`:
a loop `p` in `A` is, viewed in `X`, null-homotopic (simple connectivity of
`X`); post-composing that null-homotopy with `r` keeps every stage inside `A`
and, because `r` fixes `A`, still starts at `p` and ends at the constant loop.

This is exactly the mechanism the plan (W7_PLAN.md §L8, D4) uses to pass from
a retraction `X → closure V` to `SimplyConnectedSpace (closure V)`; it is
stated abstractly here so it can be reused for both that step and the
inner-collar transfer L9 (any deformation retract is in particular a retract).
-/

open Set Topology

namespace Uniformization

variable {X : Type*} [TopologicalSpace X]

/-- **Retract null-homotopy transport.** If `r : X → X` is continuous, lands in
`A`, and fixes `A` pointwise, then every loop in `A` that is null-homotopic in
the ambient space is null-homotopic *within* `A`: post-compose the ambient
null-homotopy with `r`. -/
theorem exists_homotopy_refl_in_of_retract {A : Set X} (r : C(X, X))
    (hrA : ∀ x, r x ∈ A) (hrid : ∀ a ∈ A, r a = a) {x : X} (p : Path x x)
    (hp : ∀ t, p t ∈ A) (H : p.Homotopy (Path.refl x)) :
    ∃ F : p.Homotopy (Path.refl x), ∀ t, F t ∈ A := by
  have hxA : x ∈ A := by simpa using hp 0
  -- the post-composed homotopy `r ∘ H`
  refine ⟨{
    toFun := fun st => r (H st)
    continuous_toFun := r.continuous.comp H.continuous
    map_zero_left := fun t => by
      show r (H (0, t)) = p t
      rw [H.apply_zero t]
      exact hrid (p t) (hp t)
    map_one_left := fun t => by
      show r (H (1, t)) = (Path.refl x) t
      rw [H.apply_one t]
      show r x = x
      exact hrid x hxA
    prop' := fun t s hs => by
      -- `s ∈ {0,1}`, so `H (t,s) = p s = x` and `r x = x = p s`
      show r (H (t, s)) = p.toContinuousMap s
      have hHfix : H (t, s) = p s := H.eq_fst t hs
      rw [hHfix]
      have hps : p s ∈ A := hp s
      rw [hrid (p s) hps]
      rfl },
    ?_⟩
  intro t
  exact hrA _

/-- **A retract of a simply connected space is simply connected.** `r : X → X`
continuous, `r '' univ ⊆ A`, `r` fixes `A` pointwise, `X` simply connected ⇒
`IsSimplyConnected A`. This is the abstract heart of W7 step L8. -/
theorem isSimplyConnected_of_retract [SimplyConnectedSpace X] {A : Set X}
    (r : C(X, X)) (hrA : ∀ x, r x ∈ A) (hrid : ∀ a ∈ A, r a = a) :
    IsSimplyConnected A := by
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  refine ⟨?_, ?_⟩
  · -- `A = r '' univ` is path-connected (continuous image of a path-connected space)
    have hpc : IsPathConnected (r '' univ) :=
      (isPathConnected_univ (X := X)).image (f := r) r.continuous
    have hAeq : r '' univ = A := by
      apply Subset.antisymm
      · rintro _ ⟨y, -, rfl⟩; exact hrA y
      · intro a ha; exact ⟨a, mem_univ a, hrid a ha⟩
    rwa [hAeq] at hpc
  · intro x p hp
    -- view `p` as a loop in `X`; simple connectivity gives a null-homotopy
    have hhom : Path.Homotopic p (Path.refl x) :=
      SimplyConnectedSpace.paths_homotopic p (Path.refl x)
    exact exists_homotopy_refl_in_of_retract r hrA hrid p hp hhom.some

end Uniformization
