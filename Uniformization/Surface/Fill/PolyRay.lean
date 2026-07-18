/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Uniformization.Surface.Fill.Ends

/-!
# An embedded, proper, chart-polyline ray in a complement end (W7 step A1)

This file delivers the *ray layer* consumed by the tube session (`TubeData`,
`RayBuild.lean`): an **embedded** (injective), **proper** ray inside a noncompact
complement end `Z`, presented as a **chart polyline** — a sequence of straight
segments read in local charts — together with the per-segment chart data and the
tube-thickness *separation* the tube construction needs.

## The reachability engine

The reusable core is `Rado.creach_eq`: in an open **preconnected** set `O ⊆ X`,
every point is reachable from a fixed base point by a finite chain of
**chart-straight segments** staying inside `O`.  Concretely, the one-step
relation `CStep O y z` asks for a maximal-atlas chart `e` with both `y, z` in its
source, whose straight segment `[e y, e z]` lies in `e.target` and whose image
`e.symm '' [e y, e z]` lies in `O`; the reachable set `CReach O x₀` is the
reflexive-transitive closure.  It is clopen in `O` (openness and relative
closedness both come from the chart-ball lemma `chart_ball_in`: a small ball
around any point of `O` is one-step reachable in both directions), hence equals
`O` by preconnectedness.

## The ray structure

`PolyRay Z z₀` packages the polyline: charts `e n`, straight endpoints
`a n, b n` (segment `[a n, b n] ⊆ (e n).target`, image `⊆ Z`), the chaining
`(e n).symm (b n) = (e (n+1)).symm (a (n+1))`, the start `z₀`, and the assembled
ray `δ : ℝ → X` (`δ (n + u) = (e n).symm (lineMap (a n) (b n) u)`), which is
continuous, **injective** on `[0,∞)`, and **proper** (`Z`-escaping).  The
separation field `hshell` records, per segment, an open set meeting only the
segment and its two neighbours — exactly the local finiteness the tube session
turns into a positive tube thickness.
-/

open Set Topology Filter

noncomputable section

namespace Rado

/-! ## The chart-polyline reachability engine (reusable topology) -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **One straight chart-segment step inside `O`.**  There is a maximal-atlas
chart `e` containing both `y` and `z` in its source, whose straight segment
`[e y, e z]` lies in the chart target and whose image lies in `O`. -/
def CStep (O : Set X) (y z : X) : Prop :=
  ∃ e ∈ riemannAtlas X, y ∈ e.source ∧ z ∈ e.source ∧
    segment ℝ (e y) (e z) ⊆ e.target ∧ e.symm '' (segment ℝ (e y) (e z)) ⊆ O

/-- **Chart-polyline reachability.**  Points reachable from `x₀` by a finite chain
of chart-straight segments staying inside `O`. -/
def CReach (O : Set X) (x₀ : X) : Set X := {z | Relation.ReflTransGen (CStep O) x₀ z}

/-- A point of an open set has a chart ball around it whose image lies in the set. -/
theorem chart_ball_in {O : Set X} (hO : IsOpen O) {x : X} (hx : x ∈ O) :
    ∃ e ∈ riemannAtlas X, x ∈ e.source ∧ ∃ r > 0,
      Metric.ball (e x) r ⊆ e.target ∧ e.symm '' Metric.ball (e x) r ⊆ O := by
  set e := chartAt ℂ x with he
  refine ⟨e, chartAt_mem_riemannAtlas x, mem_chart_source ℂ x, ?_⟩
  have hsrc : x ∈ e.source := mem_chart_source ℂ x
  have hUo : IsOpen (e.target ∩ e.symm ⁻¹' O) := e.isOpen_inter_preimage_symm hO
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' O := by
    refine ⟨e.map_source hsrc, ?_⟩
    rw [mem_preimage, e.left_inv hsrc]; exact hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo (e x) hmem
  exact ⟨r, hr, (subset_inter_iff.mp hball).1, by rintro _ ⟨z, hz, rfl⟩; exact (hball hz).2⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Reachable points stay inside `O`. -/
theorem creach_subset {O : Set X} {x₀ : X} (hx₀ : x₀ ∈ O) : CReach O x₀ ⊆ O := by
  intro z hz
  induction hz with
  | refl => exact hx₀
  | tail _ hstep _ =>
      obtain ⟨e, _, _, hzs, _, himg⟩ := hstep
      exact himg ⟨e _, right_mem_segment ℝ _ _, e.left_inv hzs⟩

/-- **The reachability engine.**  In an open preconnected `O`, chart-polyline
reachability from any base point is all of `O`: any two points of `O` are joined
by a finite chain of chart-straight segments inside `O`. -/
theorem creach_eq {O : Set X} (hO : IsOpen O) (hOc : IsPreconnected O)
    {x₀ : X} (hx₀ : x₀ ∈ O) : CReach O x₀ = O := by
  set R := CReach O x₀ with hR
  have hsub : R ⊆ O := creach_subset hx₀
  have hx₀R : x₀ ∈ R := Relation.ReflTransGen.refl
  -- `R` is open
  have hRopen : IsOpen R := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨e, he, hzs, r, hr, hbt, hbO⟩ := chart_ball_in hO (hsub hz)
    have hUopen : IsOpen (e.symm '' Metric.ball (e z) r) := by
      apply e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
      rw [e.symm_source]; exact hbt
    refine Filter.mem_of_superset
      (hUopen.mem_nhds ⟨e z, Metric.mem_ball_self hr, e.left_inv hzs⟩) ?_
    rintro w ⟨q, hq, rfl⟩
    have hbt' : segment ℝ (e z) q ⊆ Metric.ball (e z) r :=
      (convex_ball (e z) r).segment_subset (Metric.mem_ball_self hr) hq
    have hws : e.symm q ∈ e.source := e.map_target (hbt hq)
    have heew : e (e.symm q) = q := e.right_inv (hbt hq)
    have hstep : CStep O z (e.symm q) := by
      refine ⟨e, he, hzs, hws, ?_, ?_⟩
      · rw [heew]; exact hbt'.trans hbt
      · rw [heew]; exact (Set.image_mono hbt').trans hbO
    exact Relation.ReflTransGen.tail hz hstep
  -- `O \ R` is open
  have hCopen : IsOpen (O \ R) := by
    rw [isOpen_iff_mem_nhds]
    intro z ⟨hzO, hzR⟩
    obtain ⟨e, he, hzs, r, hr, hbt, hbO⟩ := chart_ball_in hO hzO
    have hUopen : IsOpen (e.symm '' Metric.ball (e z) r) := by
      apply e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
      rw [e.symm_source]; exact hbt
    refine Filter.mem_of_superset
      (hUopen.mem_nhds ⟨e z, Metric.mem_ball_self hr, e.left_inv hzs⟩) ?_
    rintro w ⟨q, hq, rfl⟩
    refine ⟨hbO ⟨q, hq, rfl⟩, ?_⟩
    intro hwR
    apply hzR
    have hbt' : segment ℝ q (e z) ⊆ Metric.ball (e z) r :=
      (convex_ball (e z) r).segment_subset hq (Metric.mem_ball_self hr)
    have hws : e.symm q ∈ e.source := e.map_target (hbt hq)
    have heew : e (e.symm q) = q := e.right_inv (hbt hq)
    have hstep : CStep O (e.symm q) z := by
      refine ⟨e, he, hws, hzs, ?_, ?_⟩
      · rw [heew]; exact hbt'.trans hbt
      · rw [heew]; exact (Set.image_mono hbt').trans hbO
    exact Relation.ReflTransGen.tail hwR hstep
  -- preconnectedness closes the split
  apply Set.Subset.antisymm hsub
  by_contra hne
  have hOv : (O ∩ (O \ R)).Nonempty := by
    rw [Set.inter_eq_self_of_subset_right Set.sdiff_subset, Set.not_subset] at *
    obtain ⟨z, hzO, hzR⟩ := hne
    exact ⟨z, hzO, hzR⟩
  have hOu : (O ∩ R).Nonempty := ⟨x₀, hx₀, hx₀R⟩
  have hcov : O ⊆ R ∪ (O \ R) := fun z hz => by
    by_cases h : z ∈ R
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  obtain ⟨z, _, hzR, _, hzRc⟩ := hOc R (O \ R) hRopen hCopen hcov hOu hOv
  exact hzRc hzR

/-- **Any two points of an open preconnected set are joined by a chart polyline.**
Usable form of `creach_eq`: from `x` to `y` there is a finite chain of
chart-straight segments inside `O`. -/
theorem exists_cStep_chain {O : Set X} (hO : IsOpen O) (hOc : IsPreconnected O)
    {x y : X} (hx : x ∈ O) (hy : y ∈ O) : Relation.ReflTransGen (CStep O) x y := by
  have : y ∈ CReach O x := by rw [creach_eq hO hOc hx]; exact hy
  exact this

end Rado

/-! ## The embedded proper chart-polyline ray -/

namespace Uniformization

open Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **An embedded, proper, chart-polyline ray inside `Z`.**

The ray is a sequence of straight chart segments.  For each `n`:

* `e n` is a maximal-atlas chart and `[a n, b n]` a straight segment in its target
  (`hseg_tgt`) whose image lies in `Z` (`hseg_Z`);
* consecutive segments chain up (`hchain`) and the first starts at `z₀`
  (`hstart`).

The assembled ray `δ : ℝ → X` reads, on `[n, n+1]`, as the affine sweep of the
`n`-th segment (`hδ`).  It is continuous (`hcont`) and starts at `z₀`
(`hδ0`), is **injective** on `[0,∞)` (`hinj`) — an embedding — and **proper**:
it eventually leaves every compact `K ⊆ Z` (`hproper`).

The `hshell` field is the *tube-thickness separation* the tube session consumes:
around each segment there is an open set meeting only that segment and its two
neighbours. -/
structure PolyRay (Z : Set X) (z₀ : X) where
  /-- The chart carrying the `n`-th segment. -/
  e : ℕ → OpenPartialHomeomorph X ℂ
  /-- Each chart is in the maximal atlas. -/
  he : ∀ n, e n ∈ riemannAtlas X
  /-- Start endpoint of the `n`-th straight segment (in the chart). -/
  a : ℕ → ℂ
  /-- End endpoint of the `n`-th straight segment (in the chart). -/
  b : ℕ → ℂ
  /-- The assembled ray in `X`. -/
  δ : ℝ → X
  /-- The `n`-th straight segment lies in the chart target. -/
  hseg_tgt : ∀ n, segment ℝ (a n) (b n) ⊆ (e n).target
  /-- The `n`-th segment's image lies in `Z`. -/
  hseg_Z : ∀ n, (e n).symm '' (segment ℝ (a n) (b n)) ⊆ Z
  /-- Consecutive endpoints chain. -/
  hchain : ∀ n, (e n).symm (b n) = (e (n + 1)).symm (a (n + 1))
  /-- The first segment starts at `z₀`. -/
  hstart : (e 0).symm (a 0) = z₀
  /-- The ray reads as the affine sweep of the `n`-th segment on `[n, n+1]`. -/
  hδ : ∀ (n : ℕ) (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      δ (n + u) = (e n).symm (AffineMap.lineMap (a n) (b n) u)
  /-- The ray is continuous on `[0,∞)`. -/
  hcont : ContinuousOn δ (Set.Ici 0)
  /-- The ray starts at `z₀`. -/
  hδ0 : δ 0 = z₀
  /-- The ray is injective on `[0,∞)` — an embedding. -/
  hinj : Set.InjOn δ (Set.Ici 0)
  /-- The ray is proper: it eventually leaves every compact subset of `Z`. -/
  hproper : ∀ K : Set X, IsCompact K → K ⊆ Z → ∃ T : ℝ, ∀ t, T ≤ t → δ t ∉ K
  /-- **Tube-thickness separation.**  Around each segment there is an open set
  meeting only that segment and its two neighbours. -/
  hshell : ∀ n : ℕ, ∃ U : Set X, IsOpen U ∧
      (e n).symm '' (segment ℝ (a n) (b n)) ⊆ U ∧
      ∀ m : ℕ, (U ∩ (e m).symm '' (segment ℝ (a m) (b m))).Nonempty →
        (m + 1 = n ∨ m = n ∨ n + 1 = m)

/-- **Existence of an embedded proper chart-polyline ray (W7 step A1).**  A
noncompact complement end `Z = connectedComponentIn (closure V)ᶜ x₀` admits, from
any base point `z₀ ∈ Z`, a `PolyRay`.

**Construction.**  Reuse the Ends machinery (`exists_noncompact_subcomponent`) to
refine a compact exhaustion `Qₙ` of `↥Z` into a decreasing chain of
noncompact-closure complement components `Cₙ` with escaping points `zₙ ∈ Cₙ`,
`zₙ ∉ Qₙ`.  Inside each open connected `Cₙ` connect `zₙ → zₙ₊₁` by a chart
polyline (`Rado.exists_cStep_chain`), then extract embeddedness in two levels:

* **within a stage**, prune the finite polyline to an injective one by the
  *last-exit* trick (the hit set of the next straight segment against the compact
  injective prefix is compact; truncate the prefix at its supremum hit and append
  the residual tail, which meets the truncated prefix only at that point);
* **across stages**, prune globally against the accumulated arc, keeping the
  invariants: the arc starts at `z₀`, ends after stage `n` at `zₙ₊₁`, is
  injective, and its stage-`n`-onward tail lies in `Z \ Qₙ` (properness).

Embeddedness + local finiteness (a compact meets finitely many stages) +
metrizability of `X` (`SecondCountableTopology` ⇒ `MetrizableSpace`) then makes
the `hshell` separation automatic: distinct non-adjacent segments are disjoint
(injectivity), hence at positive distance, so a metric thickening of each segment
meets only its neighbours.

*Status: statement frozen (proof pending — the injective pruning and separation
build arcwise connectedness, absent from mathlib at this pin).* -/
theorem exists_polyRay [T2Space X] [ConnectedSpace X] {V : Set X} {x₀ : X}
    (hZnc : ¬ IsCompact (connectedComponentIn (closure V)ᶜ x₀))
    {z₀ : X} (hz₀ : z₀ ∈ connectedComponentIn (closure V)ᶜ x₀) :
    Nonempty (PolyRay (connectedComponentIn (closure V)ᶜ x₀) z₀) := by
  sorry

end Uniformization

end
