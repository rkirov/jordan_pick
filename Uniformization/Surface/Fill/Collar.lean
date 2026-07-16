/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.LevelChart

/-!
# Uniform collar of a harmonic level-set frontier (W7 step L5, collar layer)

The delivered `exists_level_piece_regular_frontier` (`LevelChart.lean`) equips the
piece `V` with a harmonic `f` and a level `c` such that, **at every frontier
point** `ξ`, the *local dichotomy* holds:

  `∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x)`.

Because the dichotomy is an *open* condition at each point, the collection of the
witnessing open neighbourhoods unions to a **single open set `A'`** containing all
of `frontier V` on which `x ∈ V ↔ c < f x` holds *pointwise*.  This is the
decisive simplification of the harmonic (F3) route over the compactness-only
rounding route: the collar coordinate is **`f` itself**, a genuine global
function on a neighbourhood of `frontier V`, with

* `V`-side  ` = {c < f}`  (the superlevel set),
* complement-side ` = {f ≤ c}`,
* `frontier V ⊆ {f = c}`,

so no partition-of-unity gluing of chart-local normal coordinates is needed to
obtain a two-sided collar (`W7_L5_PLAN.md` §2–3: the "route (iii)" collar, here
free from the harmonic structure).

`exists_collar_dichotomy` is the extraction; `collar_closure_ge` records that on
the collar `closure V` sits in `{c ≤ f}`.  Both are pure point-set topology
(no manifold or analytic input), so they are stated for a bare topological space.

This is the foundation of the remaining W7 steps L5.4–L5.6 (crossing parity,
end-collapse retraction, and the open↔closed inner-collar transfer); those steps
— the classical surface-topology core — are **not** discharged here (see the
report accompanying this file).
-/

open Set Topology Filter

namespace Uniformization

variable {X : Type*} [TopologicalSpace X]

/-- **Uniform collar dichotomy.**  If at every frontier point `ξ` of `V` the
local dichotomy `∀ᶠ x, x ∈ V ↔ c < f x` holds, then there is a *single* open set
`A'` containing `frontier V` on which the dichotomy holds pointwise:
`∀ x ∈ A', x ∈ V ↔ c < f x` (equivalently `x ∉ V ↔ f x ≤ c`).  If moreover
`f = c` on `frontier V`, then `frontier V ⊆ {f = c}`.

The proof is just: union the witnessing open neighbourhoods.  No compactness of
`frontier V` is required because an arbitrary union of open sets is open. -/
theorem exists_collar_dichotomy {V : Set X} {f : X → ℝ} {c : ℝ}
    (hdich : ∀ ξ ∈ frontier V, ∀ᶠ x in 𝓝 ξ, (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c) :
    ∃ A' : Set X, IsOpen A' ∧ frontier V ⊆ A' ∧
      (∀ x ∈ A', (x ∈ V ↔ c < f x)) ∧
      (∀ x ∈ A', (x ∉ V ↔ f x ≤ c)) ∧
      frontier V ⊆ {x | f x = c} := by
  choose! O hOsub hOo hOmem using
    fun ξ (hξ : ξ ∈ frontier V) => _root_.mem_nhds_iff.mp (hdich ξ hξ)
  refine ⟨⋃ ξ ∈ frontier V, O ξ, isOpen_biUnion (fun ξ hξ => hOo ξ hξ),
    fun ξ hξ => mem_biUnion hξ (hOmem ξ hξ), ?_, ?_, fun ξ hξ => hfc ξ hξ⟩
  · intro x hx
    obtain ⟨ξ, hξ, hxO⟩ := mem_iUnion₂.mp hx
    exact hOsub ξ hξ hxO
  · intro x hx
    obtain ⟨ξ, hξ, hxO⟩ := mem_iUnion₂.mp hx
    have hiff : x ∈ V ↔ c < f x := hOsub ξ hξ hxO
    rw [hiff, not_lt]

/-- On the collar, `closure V` lies in the closed superlevel set `{c ≤ f}`:
a point of `closure V = V ∪ frontier V` is either in `V` (so `c < f`) or in
`frontier V` (so `f = c`). -/
theorem collar_closure_ge {V : Set X} (hVo : IsOpen V) {A' : Set X}
    {f : X → ℝ} {c : ℝ} (hpos : ∀ x ∈ A', (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c) :
    ∀ x ∈ A', x ∈ closure V → c ≤ f x := by
  intro x hxA' hxcl
  have hUF : V ∪ frontier V = closure V := by
    rw [hVo.frontier_eq]; exact Set.union_sdiff_cancel subset_closure
  rw [← hUF] at hxcl
  rcases hxcl with h | h
  · exact le_of_lt ((hpos x hxA').mp h)
  · exact (hfc x h).ge

/-- The strict complement side `A' ∩ {f < c}` of the collar is genuinely
exterior: it is disjoint from `closure V`.  (Immediate from `collar_closure_ge`.) -/
theorem collar_neg_notMem_closure {V : Set X} (hVo : IsOpen V) {A' : Set X}
    {f : X → ℝ} {c : ℝ} (hpos : ∀ x ∈ A', (x ∈ V ↔ c < f x))
    (hfc : ∀ ξ ∈ frontier V, f ξ = c) {x : X} (hxA' : x ∈ A') (hlt : f x < c) :
    x ∉ closure V :=
  fun hxcl => absurd (collar_closure_ge hVo hpos hfc x hxA' hxcl) (not_le.mpr hlt)

/-- The `V`-side of the collar, `A' ∩ {c < f}`, is open when `f` is continuous on
`A'` (so it equals `V ∩ A'`, an open set). -/
theorem isOpen_collar_pos {A' : Set X} (hA'o : IsOpen A') {f : X → ℝ}
    (hf : ContinuousOn f A') (c : ℝ) :
    IsOpen (A' ∩ f ⁻¹' Ioi c) :=
  hf.isOpen_inter_preimage hA'o isOpen_Ioi

/-- The complement-side interior of the collar, `A' ∩ {f < c}`, is open when `f`
is continuous on `A'`. -/
theorem isOpen_collar_neg {A' : Set X} (hA'o : IsOpen A') {f : X → ℝ}
    (hf : ContinuousOn f A') (c : ℝ) :
    IsOpen (A' ∩ f ⁻¹' Iio c) :=
  hf.isOpen_inter_preimage hA'o isOpen_Iio
