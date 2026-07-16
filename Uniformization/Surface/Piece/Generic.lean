/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib

/-!
# Countable-exclusion radius picking (W7 §1.3, exclusion engine)

The generic-radius engine of `W7_PLAN.md` §1.3: an interval of admissible
radii is uncountable, so any countable set of "bad" radii can be avoided.
These lemmas are pure real-set arithmetic and are **not** consumed by the
L1–L4 point-set layer delivered in `Piece/Round.lean` — that layer replaced
the plan's genericity predicate by a compactness-only rounding (see the
design note there). They are provided for the later collar/parity steps
(L5–L6), which will need transversal crossings and no triple points.

Scope cut (documented): the plan's `finite_tangency_radii` — finiteness or
countability of tangency radii of a circle pencil against an analytic arc,
via real-analytic critical values — is *not* proved here; it is only needed
for the L5 refinement and should be developed together with it.
-/

open Set

namespace Uniformization

/-- **Countable exclusion**: any countable set of bad radii misses some
radius in a nontrivial interval. -/
theorem exists_radius_notMem {bad : Set ℝ} (hbad : bad.Countable) {a b : ℝ} (hab : a < b) :
    ∃ ρ ∈ Ioo a b, ρ ∉ bad := by
  by_contra h
  push Not at h
  have : (Ioo a b).Countable := hbad.mono h
  rw [Cardinal.Real.Ioo_countable_iff] at this
  exact absurd hab (not_lt.mpr this)

/-- Iterated countable exclusion over finitely many bad families. -/
theorem exists_radius_notMem_iUnion {ι : Type*} [Countable ι] {bad : ι → Set ℝ}
    (hbad : ∀ i, (bad i).Countable) {a b : ℝ} (hab : a < b) :
    ∃ ρ ∈ Ioo a b, ∀ i, ρ ∉ bad i := by
  obtain ⟨ρ, hρ, hρbad⟩ := exists_radius_notMem (countable_iUnion hbad) hab
  exact ⟨ρ, hρ, fun i hi => hρbad (mem_iUnion.mpr ⟨i, hi⟩)⟩

/-- **Triple-point exclusion** (plan §1.3, `finite_triplePoint_radii`): the
set of radii at which a circle centered at `c` passes through one of finitely
many prescribed points is finite. -/
theorem finite_radii_through {S : Set ℂ} (hS : S.Finite) (c : ℂ) :
    {ρ : ℝ | ∃ s ∈ S, dist s c = ρ}.Finite := by
  have : {ρ : ℝ | ∃ s ∈ S, dist s c = ρ} = (fun s => dist s c) '' S := by
    ext ρ
    simp [eq_comm, Set.mem_image]
  rw [this]
  exact hS.image _

/-- A radius in a prescribed interval avoiding finitely many prescribed
points and a countable set of bad radii (the combined form used when nudging
disks into generic position). -/
theorem exists_radius_avoiding {S : Set ℂ} (hS : S.Finite) (c : ℂ)
    {bad : Set ℝ} (hbad : bad.Countable) {a b : ℝ} (hab : a < b) :
    ∃ ρ ∈ Ioo a b, ρ ∉ bad ∧ ∀ s ∈ S, dist s c ≠ ρ := by
  obtain ⟨ρ, hρ, hρbad⟩ :=
    exists_radius_notMem (hbad.union (finite_radii_through hS c).countable) hab
  refine ⟨ρ, hρ, fun h => hρbad (Or.inl h), fun s hs h => hρbad (Or.inr ⟨s, hs, h⟩)⟩

end Uniformization
