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

/-! ## Polyline segments: the data model for pruning -/

/-- **A single chart-straight segment inside `O`.**  The building block of a
chart polyline: a maximal-atlas chart `e` and straight endpoints `a, b` whose
segment lies in `e.target` and whose image lies in `O`.  This is the data-bearing
form of `CStep`. -/
structure PLSeg (O : Set X) where
  /-- The carrying chart. -/
  e : OpenPartialHomeomorph X ℂ
  /-- The chart is in the maximal atlas. -/
  he : e ∈ riemannAtlas X
  /-- Start endpoint in the chart. -/
  a : ℂ
  /-- End endpoint in the chart. -/
  b : ℂ
  /-- The straight segment lies in the chart target. -/
  htgt : segment ℝ a b ⊆ e.target
  /-- The segment's image lies in `O`. -/
  hsub : e.symm '' (segment ℝ a b) ⊆ O

namespace PLSeg

variable {O : Set X} (s : PLSeg O)

/-- Image of the segment in `X`. -/
def img : Set X := s.e.symm '' (segment ℝ s.a s.b)
/-- Start point in `X`. -/
def p0 : X := s.e.symm s.a
/-- End point in `X`. -/
def p1 : X := s.e.symm s.b

theorem p0_mem : s.p0 ∈ s.img := ⟨s.a, left_mem_segment ℝ _ _, rfl⟩
theorem p1_mem : s.p1 ∈ s.img := ⟨s.b, right_mem_segment ℝ _ _, rfl⟩
theorem img_sub : s.img ⊆ O := s.hsub

theorem symm_contOn : ContinuousOn s.e.symm (segment ℝ s.a s.b) :=
  s.e.continuousOn_symm.mono s.htgt

theorem img_compact : IsCompact s.img := by
  have h : IsCompact (segment ℝ s.a s.b) := by
    rw [segment_eq_image_lineMap]; exact isCompact_Icc.image (by fun_prop)
  exact h.image_of_continuousOn s.symm_contOn

theorem img_conn : IsConnected s.img :=
  ((convex_segment s.a s.b).isConnected ⟨s.a, left_mem_segment ℝ _ _⟩).image _ s.symm_contOn

/-- Left sub-segment `[a, c]` for `c` in the segment; a chart-straight segment. -/
def splitL (c : ℂ) (hc : c ∈ segment ℝ s.a s.b) : PLSeg O where
  e := s.e; he := s.he; a := s.a; b := c
  htgt := ((convex_segment s.a s.b).segment_subset (left_mem_segment ℝ _ _) hc).trans s.htgt
  hsub := (Set.image_mono ((convex_segment s.a s.b).segment_subset
    (left_mem_segment ℝ _ _) hc)).trans s.hsub

/-- Right sub-segment `[c, b]`; a chart-straight segment. -/
def splitR (c : ℂ) (hc : c ∈ segment ℝ s.a s.b) : PLSeg O where
  e := s.e; he := s.he; a := c; b := s.b
  htgt := ((convex_segment s.a s.b).segment_subset hc (right_mem_segment ℝ _ _)).trans s.htgt
  hsub := (Set.image_mono ((convex_segment s.a s.b).segment_subset
    hc (right_mem_segment ℝ _ _))).trans s.hsub

theorem splitL_img_sub (c : ℂ) (hc : c ∈ segment ℝ s.a s.b) :
    (s.splitL c hc).img ⊆ s.img :=
  Set.image_mono ((convex_segment s.a s.b).segment_subset (left_mem_segment ℝ _ _) hc)

theorem splitR_img_sub (c : ℂ) (hc : c ∈ segment ℝ s.a s.b) :
    (s.splitR c hc).img ⊆ s.img :=
  Set.image_mono ((convex_segment s.a s.b).segment_subset hc (right_mem_segment ℝ _ _))

@[simp] theorem splitL_p0 (c : ℂ) (hc : c ∈ segment ℝ s.a s.b) : (s.splitL c hc).p0 = s.p0 := rfl
@[simp] theorem splitL_p1 (c : ℂ) (hc : c ∈ segment ℝ s.a s.b) :
    (s.splitL c hc).p1 = s.e.symm c := rfl
@[simp] theorem splitR_p0 (c : ℂ) (hc : c ∈ segment ℝ s.a s.b) :
    (s.splitR c hc).p0 = s.e.symm c := rfl
@[simp] theorem splitR_p1 (c : ℂ) (hc : c ∈ segment ℝ s.a s.b) : (s.splitR c hc).p1 = s.p1 := rfl

/-- A `CStep` yields a segment datum with the expected endpoints. -/
theorem _root_.Rado.CStep.toPLSeg {O : Set X} {y z : X} (h : CStep O y z) :
    ∃ s : PLSeg O, s.p0 = y ∧ s.p1 = z := by
  obtain ⟨e, he, hy, hz, htgt, hsub⟩ := h
  exact ⟨⟨e, he, e y, e z, htgt, hsub⟩, e.left_inv hy, e.left_inv hz⟩

end PLSeg

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

/-! ## The pruning target and the assembly -/

/-- **Simple ray data: the combinatorial output of the pruning.**  An
ℕ-indexed family of *nondegenerate* chart-straight segments (`hab`, `htgt`, `hZ`)
that chain up (`hchain`) from `z₀` (`hstart`) and are **simple**:

* consecutive segments meet only at their shared endpoint (`hadj`);
* segments at least two apart are disjoint (`hfar`);

is **escaping** (`hesc`: each compact `K ⊆ Z` is met by only a tail-bounded set of
segments) and carries the **shell separation** directly (`hshell`).

`polyRay_of_simple` assembles this into a `PolyRay`.  This is exactly the data the
last-exit pruning (P1 within a stage, P2 across stages) plus the metric separation
(P3) must produce; it plays the role `TubeData` plays for `RayCollar`. -/
structure SimpleRayData (Z : Set X) (z₀ : X) where
  /-- The chart carrying the `n`-th segment. -/
  e : ℕ → OpenPartialHomeomorph X ℂ
  /-- Each chart is in the maximal atlas. -/
  he : ∀ n, e n ∈ riemannAtlas X
  /-- Start endpoint of the `n`-th segment (in the chart). -/
  a : ℕ → ℂ
  /-- End endpoint of the `n`-th segment (in the chart). -/
  b : ℕ → ℂ
  /-- Each segment is nondegenerate. -/
  hab : ∀ n, a n ≠ b n
  /-- The `n`-th segment lies in the chart target. -/
  htgt : ∀ n, segment ℝ (a n) (b n) ⊆ (e n).target
  /-- The `n`-th segment's image lies in `Z`. -/
  hZ : ∀ n, (e n).symm '' (segment ℝ (a n) (b n)) ⊆ Z
  /-- Consecutive endpoints chain. -/
  hchain : ∀ n, (e n).symm (b n) = (e (n + 1)).symm (a (n + 1))
  /-- The first segment starts at `z₀`. -/
  hstart : (e 0).symm (a 0) = z₀
  /-- Consecutive segments meet only at their shared endpoint. -/
  hadj : ∀ n, (e n).symm '' segment ℝ (a n) (b n)
      ∩ (e (n + 1)).symm '' segment ℝ (a (n + 1)) (b (n + 1)) ⊆ {(e n).symm (b n)}
  /-- Segments at least two apart are disjoint. -/
  hfar : ∀ m n, m + 2 ≤ n → Disjoint ((e m).symm '' segment ℝ (a m) (b m))
      ((e n).symm '' segment ℝ (a n) (b n))
  /-- The family escapes every compact subset of `Z`. -/
  hesc : ∀ K : Set X, IsCompact K → K ⊆ Z →
      ∃ N : ℕ, ∀ n ≥ N, Disjoint ((e n).symm '' segment ℝ (a n) (b n)) K
  /-- The shell separation, delivered directly. -/
  hshell : ∀ n : ℕ, ∃ U : Set X, IsOpen U ∧
      (e n).symm '' (segment ℝ (a n) (b n)) ⊆ U ∧
      ∀ m : ℕ, (U ∩ (e m).symm '' (segment ℝ (a m) (b m))).Nonempty →
        (m + 1 = n ∨ m = n ∨ n + 1 = m)

/-- **Assembly: simple ray data yields an embedded proper chart-polyline ray.**
The ray `δ (n + u) = (e n).symm (lineMap (a n) (b n) u)` is continuous (floor
glue), starts at `z₀`, is **injective** — cross-segment collisions are excluded by
`hadj`/`hfar` and within-segment ones by nondegeneracy (`hab`) — and **proper**
via `hesc`.  The shell separation is carried over. -/
noncomputable def polyRay_of_simple {Z : Set X} {z₀ : X} (d : SimpleRayData Z z₀) :
    PolyRay Z z₀ where
  e := d.e
  he := d.he
  a := d.a
  b := d.b
  δ := fun t => (d.e ⌊t⌋₊).symm (AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - ⌊t⌋₊))
  hseg_tgt := d.htgt
  hseg_Z := d.hZ
  hchain := d.hchain
  hstart := d.hstart
  hshell := d.hshell
  hδ := by
    intro n u hu
    rcases eq_or_lt_of_le hu.2 with hu1 | hu1
    · subst hu1
      have hfloor : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
        rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
      simp only [hfloor]
      rw [show ((n : ℝ) + 1 - ((n + 1 : ℕ) : ℝ)) = 0 by push_cast; ring,
        AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, ← d.hchain n]
    · have hfloor : ⌊(n : ℝ) + u⌋₊ = n := by
        rw [Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg n) hu.1)]
        refine ⟨by simpa using hu.1, ?_⟩
        · linarith [hu.1]
      simp only [hfloor]
      rw [show ((n : ℝ) + u - (n : ℝ)) = u by ring]
  hδ0 := by
    show (d.e ⌊(0:ℝ)⌋₊).symm
      (AffineMap.lineMap (d.a ⌊(0:ℝ)⌋₊) (d.b ⌊(0:ℝ)⌋₊) ((0:ℝ) - ⌊(0:ℝ)⌋₊)) = z₀
    rw [Nat.floor_zero]
    simp only [Nat.cast_zero, sub_zero, AffineMap.lineMap_apply_zero]
    exact d.hstart
  hcont := by
    have hcover : Set.Ici (0 : ℝ) = ⋃ n : ℕ, Set.Icc (n : ℝ) (n + 1) := by
      ext t
      simp only [Set.mem_Ici, Set.mem_iUnion, Set.mem_Icc]
      constructor
      · intro ht; exact ⟨⌊t⌋₊, Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
      · rintro ⟨n, hn, _⟩; exact le_trans (Nat.cast_nonneg n) hn
    have hlf : LocallyFinite (fun n : ℕ => Set.Icc (n : ℝ) (n + 1)) := by
      intro x
      refine ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      apply Set.Finite.subset (Set.finite_Iic (⌊x + 1⌋₊ : ℕ))
      intro n hn
      obtain ⟨y, ⟨hy1, _⟩, _, hy4⟩ := hn
      rw [Set.mem_Iic]
      exact Nat.le_floor (le_of_lt (lt_of_le_of_lt hy1 hy4))
    have hcont_piece : ∀ N : ℕ, ContinuousOn
        (fun t : ℝ => (d.e ⌊t⌋₊).symm (AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - ⌊t⌋₊)))
        (Set.Icc (N : ℝ) (N + 1)) := by
      intro N
      have hmaps : Set.MapsTo (fun t : ℝ => AffineMap.lineMap (d.a N) (d.b N) (t - N))
          (Set.Icc (N : ℝ) (N + 1)) (d.e N).target := by
        intro t ht
        apply d.htgt N
        rw [segment_eq_image_lineMap]
        exact ⟨t - N, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
      have hcont_hn : ContinuousOn (fun t : ℝ => (d.e N).symm
          (AffineMap.lineMap (d.a N) (d.b N) (t - N))) (Set.Icc (N : ℝ) (N + 1)) :=
        (d.e N).continuousOn_symm.comp (by fun_prop) hmaps
      apply hcont_hn.congr
      intro t ht
      rcases lt_or_eq_of_le ht.2 with hlt | heq
      · have hfloor : ⌊t⌋₊ = N := by
          rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg N) ht.1)]; exact ⟨ht.1, hlt⟩
        show (d.e ⌊t⌋₊).symm (AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - (⌊t⌋₊ : ℝ)))
          = (d.e N).symm (AffineMap.lineMap (d.a N) (d.b N) (t - N))
        rw [hfloor]
      · show (d.e ⌊t⌋₊).symm (AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - (⌊t⌋₊ : ℝ)))
          = (d.e N).symm (AffineMap.lineMap (d.a N) (d.b N) (t - N))
        have hfloor : ⌊t⌋₊ = N + 1 := by
          rw [heq, show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
        rw [hfloor, heq, show ((N : ℝ) + 1 - ((N + 1 : ℕ) : ℝ)) = 0 by push_cast; ring,
          show ((N : ℝ) + 1 - (N : ℝ)) = 1 by ring, AffineMap.lineMap_apply_zero,
          AffineMap.lineMap_apply_one, ← d.hchain N]
    rw [hcover]
    exact hlf.continuousOn_iUnion (fun _ => isClosed_Icc) hcont_piece
  hinj := by
    have hu01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ t - (⌊t⌋₊:ℝ) ∧ t - (⌊t⌋₊:ℝ) < 1 := by
      intro t ht
      exact ⟨sub_nonneg.mpr (Nat.floor_le ht), by linarith [Nat.lt_floor_add_one t]⟩
    have hmemseg : ∀ t : ℝ, 0 ≤ t →
        AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - (⌊t⌋₊:ℝ))
          ∈ segment ℝ (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) := by
      intro t ht
      rw [segment_eq_image_lineMap]
      exact ⟨t - ⌊t⌋₊, ⟨(hu01 t ht).1, (hu01 t ht).2.le⟩, rfl⟩
    have hlm_tgt : ∀ t : ℝ, 0 ≤ t →
        AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - (⌊t⌋₊:ℝ)) ∈ (d.e ⌊t⌋₊).target :=
      fun t ht => d.htgt _ (hmemseg t ht)
    have hδmem : ∀ t : ℝ, 0 ≤ t →
        (d.e ⌊t⌋₊).symm (AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - ⌊t⌋₊))
          ∈ (d.e ⌊t⌋₊).symm '' segment ℝ (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) :=
      fun t ht => ⟨_, hmemseg t ht, rfl⟩
    have hinjsymm : ∀ (n : ℕ) {c c' : ℂ}, c ∈ (d.e n).target → c' ∈ (d.e n).target →
        (d.e n).symm c = (d.e n).symm c' → c = c' := by
      intro n c c' hc hc' h
      exact ((d.e n).symm_source ▸ (d.e n).symm.injOn) hc hc' h
    have key : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s ≤ t →
        (d.e ⌊s⌋₊).symm (AffineMap.lineMap (d.a ⌊s⌋₊) (d.b ⌊s⌋₊) (s - ⌊s⌋₊))
          = (d.e ⌊t⌋₊).symm (AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - ⌊t⌋₊)) → s = t := by
      intro s t hs ht hst hδst
      have hnm : ⌊s⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hst
      rcases eq_or_lt_of_le hnm with heq | hlt
      · rw [← heq] at hδst
        have hlm : AffineMap.lineMap (d.a ⌊s⌋₊) (d.b ⌊s⌋₊) (s - (⌊s⌋₊:ℝ))
            = AffineMap.lineMap (d.a ⌊s⌋₊) (d.b ⌊s⌋₊) (t - (⌊s⌋₊:ℝ)) := by
          apply hinjsymm ⌊s⌋₊ (hlm_tgt s hs) (heq ▸ hlm_tgt t ht) hδst
        rcases (AffineMap.lineMap_eq_lineMap_iff (k := ℝ) (V1 := ℂ)).mp hlm with hc | hc
        · exact absurd hc (d.hab _)
        · linarith [hc]
      · exfalso
        set n := ⌊s⌋₊ with hn
        set m := ⌊t⌋₊ with hm
        rcases Nat.lt_or_ge (n + 1) m with hgap | hle2
        · have h2 : n + 2 ≤ m := by omega
          exact Set.disjoint_left.mp (d.hfar n m h2) (hδmem s hs) (hm ▸ hδst ▸ hδmem t ht)
        · have hmeq : m = n + 1 := by omega
          have hmem_s : (d.e n).symm (AffineMap.lineMap (d.a n) (d.b n) (s - n))
              ∈ (d.e n).symm '' segment ℝ (d.a n) (d.b n) := hδmem s hs
          have hmem_t : (d.e n).symm (AffineMap.lineMap (d.a n) (d.b n) (s - n))
              ∈ (d.e (n+1)).symm '' segment ℝ (d.a (n+1)) (d.b (n+1)) := by
            have h1 := hδmem t ht
            rw [← hm, hmeq] at h1
            rw [hδst, hmeq]
            exact h1
          have hshared := d.hadj n ⟨hmem_s, hmem_t⟩
          rw [Set.mem_singleton_iff] at hshared
          have hlmb : AffineMap.lineMap (d.a n) (d.b n) (s - (n:ℝ)) = d.b n := by
            apply hinjsymm n (hlm_tgt s hs) (d.htgt n (right_mem_segment ℝ _ _)) hshared
          rcases (AffineMap.lineMap_eq_right_iff (k := ℝ) (V1 := ℂ)).mp hlmb with hc | hc
          · exact (d.hab n) hc
          · have := (hu01 s hs).2; rw [hn] at hc; linarith
    intro s hs t ht h
    rcases le_total s t with hle | hle
    · exact key s t hs ht hle h
    · exact (key t s ht hs hle h.symm).symm
  hproper := by
    intro K hK hKZ
    obtain ⟨N, hN⟩ := d.hesc K hK hKZ
    refine ⟨(N : ℝ), fun t htN => ?_⟩
    have hfloorN : N ≤ ⌊t⌋₊ := Nat.le_floor htN
    have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) htN
    have hmem : (d.e ⌊t⌋₊).symm (AffineMap.lineMap (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) (t - ⌊t⌋₊))
        ∈ (d.e ⌊t⌋₊).symm '' segment ℝ (d.a ⌊t⌋₊) (d.b ⌊t⌋₊) := by
      refine ⟨_, ?_, rfl⟩
      rw [segment_eq_image_lineMap]
      exact ⟨t - ⌊t⌋₊, ⟨by simp [Nat.floor_le ht0], by linarith [Nat.lt_floor_add_one t]⟩, rfl⟩
    exact Set.disjoint_left.mp (hN ⌊t⌋₊ hfloorN) hmem

/-- **The pruning obligation (P1–P3), frozen.**  A noncompact complement end
`Z = connectedComponentIn (closure V)ᶜ x₀` admits, from any base point `z₀ ∈ Z`,
`SimpleRayData` — the embedded, escaping, shell-separated chart-polyline family.

**Construction.**  Reuse the Ends machinery (`exists_noncompact_subcomponent`) to
refine a compact exhaustion `Qₙ` of `↥Z` into a decreasing chain of
noncompact-closure complement components `Cₙ` with escaping points `zₙ ∈ Cₙ`,
`zₙ ∉ Qₙ`.  Inside each open connected `Cₙ` connect `zₙ → zₙ₊₁` by a chart
polyline (`Rado.exists_cStep_chain`, as segment data `Rado.PLSeg`), then:

* **(P1)** within a stage, prune the finite polyline to a *simple* one by the
  last-exit trick — the hit set of the next straight segment against the compact
  prefix image is compact (use `Rado.PLSeg.img_compact`); truncate the prefix at
  its supremum hit (splitting the hit segment via `Rado.PLSeg.splitL`) and append
  the residual tail (`Rado.PLSeg.splitR`), which meets the truncated prefix only
  at that point;
* **(P2)** across stages, repeat the last-exit pruning against the accumulated
  arc, keeping the weaker invariants (start `z₀`, endpoint-at-stage-`n` = `zₙ₊₁`,
  simplicity, and stage-`m` material `⊆ Cₘ` — truncation only shrinks it — so the
  tail beyond the stage-`n` junction lies in `⋃_{m≥n} Cₘ ⊆ Z \ Qₙ`, giving
  `hesc`);
* **(P3)** derive `hshell` from simplicity + local finiteness (a compact meets
  finitely many stages) + metrizability of `X` (`SecondCountableTopology` ⇒
  `MetrizableSpace`, as in `RayCollar.lean`): non-adjacent segments are disjoint,
  hence at positive distance, so a metric thickening meets only neighbours.

*Status: frozen — the last-exit pruning builds arcwise connectedness, absent from
mathlib at this pin.  All downstream packaging (`polyRay_of_simple`) is
sorry-free.* -/
theorem nonempty_simpleRayData [T2Space X] [ConnectedSpace X] {V : Set X} {x₀ : X}
    (hZnc : ¬ IsCompact (connectedComponentIn (closure V)ᶜ x₀))
    {z₀ : X} (hz₀ : z₀ ∈ connectedComponentIn (closure V)ᶜ x₀) :
    Nonempty (SimpleRayData (connectedComponentIn (closure V)ᶜ x₀) z₀) := by
  sorry

/-- **An embedded, proper, chart-polyline ray exists in a noncompact end
(W7 step A1).**  Immediate from `polyRay_of_simple` and `nonempty_simpleRayData`. -/
theorem exists_polyRay [T2Space X] [ConnectedSpace X] {V : Set X} {x₀ : X}
    (hZnc : ¬ IsCompact (connectedComponentIn (closure V)ᶜ x₀))
    {z₀ : X} (hz₀ : z₀ ∈ connectedComponentIn (closure V)ᶜ x₀) :
    Nonempty (PolyRay (connectedComponentIn (closure V)ᶜ x₀) z₀) :=
  ⟨polyRay_of_simple (nonempty_simpleRayData hZnc hz₀).some⟩

end Uniformization

end
