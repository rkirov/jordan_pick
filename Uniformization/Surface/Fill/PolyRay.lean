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

/-- **Weakening the ambient set.**  `O` occurs in `PLSeg O` only through `hsub`, so a
segment inside `O` is literally a segment inside any larger `O'`.  This is what lets the
per-stage segments (each living in its own `Om m`) be collected into a single
`ℕ`-indexed family of `PLSeg Z`. -/
def mono {O₁ O₂ : Set X} (h : O₁ ⊆ O₂) (t : PLSeg O₁) : PLSeg O₂ :=
  { t with hsub := t.hsub.trans h }

@[simp] theorem mono_e {O₁ O₂ : Set X} (h : O₁ ⊆ O₂) (t : PLSeg O₁) : (mono h t).e = t.e := rfl
@[simp] theorem mono_a {O₁ O₂ : Set X} (h : O₁ ⊆ O₂) (t : PLSeg O₁) : (mono h t).a = t.a := rfl
@[simp] theorem mono_b {O₁ O₂ : Set X} (h : O₁ ⊆ O₂) (t : PLSeg O₁) : (mono h t).b = t.b := rfl
@[simp] theorem mono_img {O₁ O₂ : Set X} (h : O₁ ⊆ O₂) (t : PLSeg O₁) :
    (mono h t).img = t.img := rfl
@[simp] theorem mono_p0 {O₁ O₂ : Set X} (h : O₁ ⊆ O₂) (t : PLSeg O₁) : (mono h t).p0 = t.p0 := rfl
@[simp] theorem mono_p1 {O₁ O₂ : Set X} (h : O₁ ⊆ O₂) (t : PLSeg O₁) : (mono h t).p1 = t.p1 := rfl

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

/-! ## The noncompact-subcomponent step (copied from `Ends.lean`, which keeps it
`private`).  Abstract topology on a space `W` with the right instances. -/

/-- **Key existence step for the escaping ray.**  In a locally compact, locally
connected, preconnected Hausdorff space `W` with a compact exhaustion `Kex`, if
`C = connectedComponentIn (Kex n)ᶜ a` is a complement component whose closure is
*not* compact, then inside `C` there is a point `b` outside `Kex (n+1)` whose
component in `(Kex (n+1))ᶜ` again has noncompact closure. -/
private theorem exists_noncompact_subcomponent {W : Type*} [TopologicalSpace W]
    [T2Space W] [LocallyCompactSpace W] [LocallyConnectedSpace W] [PreconnectedSpace W]
    (Kex : CompactExhaustion W) {n : ℕ} {a : W} (_ha : a ∉ Kex n)
    (hnc : ¬ IsCompact (closure (connectedComponentIn (Kex n)ᶜ a))) :
    ∃ b : W, b ∉ Kex (n + 1) ∧ b ∈ connectedComponentIn (Kex n)ᶜ a ∧
      ¬ IsCompact (closure (connectedComponentIn (Kex (n + 1))ᶜ b)) := by
  classical
  set C := connectedComponentIn (Kex n)ᶜ a with hCdef
  haveI : Nonempty W := ⟨a⟩
  have hWnc : ¬ CompactSpace W := by
    intro hc; haveI := hc; exact hnc isClosed_closure.isCompact
  have hFopen : IsOpen ((Kex (n + 1))ᶜ) := (Kex.isCompact (n + 1)).isClosed.isOpen_compl
  by_contra hcon
  push Not at hcon
  have hesc : ∀ m, ∃ x, x ∈ C ∧ x ∉ Kex m := by
    intro m
    by_contra h
    push Not at h
    exact hnc ((Kex.isCompact m).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => h x hx) (Kex.isCompact m).isClosed))
  choose c hcC hcK using hesc
  set D : ℕ → Set W := fun m => connectedComponentIn (Kex (n + 1))ᶜ (c m) with hDdef
  have hcF : ∀ m, n + 1 ≤ m → c m ∈ (Kex (n + 1))ᶜ := by
    intro m hm hmem
    exact hcK m (Kex.subset hm hmem)
  have hcD : ∀ m, n + 1 ≤ m → c m ∈ D m := fun m hm => mem_connectedComponentIn (hcF m hm)
  have hDcompact : ∀ m, n + 1 ≤ m → IsCompact (closure (D m)) := by
    intro m hm
    exact hcon (c m) (hcF m hm) (hcC m)
  set R : Set (Set W) := {D' | ∃ m, n + 2 ≤ m ∧ D' = D m} with hRdef
  have hRinf : R.Infinite := by
    intro hRfin
    have hUcompact : IsCompact (⋃ D' ∈ R, closure D') := by
      refine hRfin.isCompact_biUnion ?_
      rintro D' ⟨m, hm, rfl⟩
      exact hDcompact m (by omega)
    obtain ⟨p, hp⟩ := Kex.exists_superset_of_isCompact hUcompact
    set m := max p (n + 2) with hmdef
    have hm2 : n + 2 ≤ m := le_max_right _ _
    have hmp : p ≤ m := le_max_left _ _
    have hcmDm : c m ∈ D m := hcD m (by omega)
    have hcmU : c m ∈ ⋃ D' ∈ R, closure D' :=
      mem_biUnion ⟨m, hm2, rfl⟩ (subset_closure hcmDm)
    exact hcK m (Kex.subset hmp (hp hcmU))
  have hcross : ∀ D' ∈ R, (D' ∩ frontier (Kex (n + 2))).Nonempty := by
    rintro D' ⟨m, hm, rfl⟩
    have hDopen : IsOpen (D m) := hFopen.connectedComponentIn
    have hcmDm : c m ∈ D m := hcD m (by omega)
    have hfrsub : frontier (D m) ⊆ Kex (n + 1) := by
      have h1 : frontier (D m) ⊆ frontier ((Kex (n + 1))ᶜ) :=
        frontier_connectedComponentIn_subset (U := (Kex (n + 1))ᶜ) (x := c m) hFopen
      rw [frontier_compl] at h1
      exact h1.trans (Kex.isCompact (n + 1)).isClosed.frontier_subset
    have hfrint : frontier (D m) ⊆ interior (Kex (n + 2)) :=
      hfrsub.trans (Kex.subset_interior_succ (n + 1))
    have hfrne : (frontier (D m)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hclopen : IsClopen (D m) := isClopen_iff_frontier_eq_empty.mpr hemp
      rcases isClopen_iff.mp hclopen with h | h
      · exact absurd (h ▸ hcmDm) (Set.notMem_empty _)
      · refine hWnc ?_
        rw [← isCompact_univ_iff]
        have := hDcompact m (by omega)
        rwa [h, closure_univ] at this
    obtain ⟨w, hwfr⟩ := hfrne
    have hwcl : w ∈ closure (D m) := hwfr.1
    obtain ⟨w', hw'int, hw'D⟩ :=
      _root_.mem_closure_iff.mp hwcl (interior (Kex (n + 2))) isOpen_interior (hfrint hwfr)
    have hcmnot : c m ∉ Kex (n + 2) := fun h => hcK m (Kex.subset hm h)
    have hpre : IsPreconnected (D m) := isPreconnected_connectedComponentIn
    have hdisj : Disjoint (interior (Kex (n + 2))) ((Kex (n + 2))ᶜ) :=
      disjoint_compl_right.mono_left interior_subset
    have hnotsub : ¬ (D m ⊆ interior (Kex (n + 2)) ∪ (Kex (n + 2))ᶜ) := by
      intro hsub
      rcases hpre.subset_or_subset isOpen_interior
          (Kex.isCompact (n + 2)).isClosed.isOpen_compl hdisj hsub with h | h
      · exact hcmnot (interior_subset (h hcmDm))
      · exact (h hw'D) (interior_subset hw'int)
    obtain ⟨z, hzD, hznotU⟩ := Set.not_subset.mp hnotsub
    rw [Set.mem_union, not_or] at hznotU
    obtain ⟨hzni, hznc⟩ := hznotU
    have hzK : z ∈ Kex (n + 2) := not_not.mp hznc
    have hzfr : z ∈ frontier (Kex (n + 2)) := by
      rw [(Kex.isCompact (n + 2)).isClosed.frontier_eq]
      exact ⟨hzK, hzni⟩
    exact ⟨z, hzD, hzfr⟩
  choose! Dpt hDpt using hcross
  set Y : Set W := Dpt '' R with hYdef
  have hYsub : Y ⊆ frontier (Kex (n + 2)) := by
    rintro _ ⟨D', hD'R, rfl⟩; exact (hDpt D' hD'R).2
  have hInjOn : Set.InjOn Dpt R := by
    rintro D₁ h₁ D₂ h₂ heq
    obtain ⟨m₁, hm₁, rfl⟩ := h₁
    obtain ⟨m₂, hm₂, rfl⟩ := h₂
    have hw1 : Dpt (D m₁) ∈ D m₁ := (hDpt (D m₁) ⟨m₁, hm₁, rfl⟩).1
    have hw2 : Dpt (D m₂) ∈ D m₂ := (hDpt (D m₂) ⟨m₂, hm₂, rfl⟩).1
    have e1 : D m₁ = connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₁)) :=
      connectedComponentIn_eq hw1
    have e2 : D m₂ = connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₂)) :=
      connectedComponentIn_eq hw2
    rw [e1, e2, heq]
  have hYinf : Y.Infinite := (Set.infinite_image_iff hInjOn).mpr hRinf
  have hSphcpt : IsCompact (frontier (Kex (n + 2))) :=
    (Kex.isCompact (n + 2)).of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (Kex.isCompact (n + 2)).isClosed.closure_eq.subset)
  obtain ⟨ys, hysmem, hAcc⟩ := hYinf.exists_accPt_of_subset_isCompact hSphcpt hYsub
  have hysint : ys ∉ interior (Kex (n + 2)) := by
    have := (Kex.isCompact (n + 2)).isClosed.frontier_eq ▸ hysmem
    exact this.2
  have hysF : ys ∈ (Kex (n + 1))ᶜ := fun hy =>
    hysint (Kex.subset_interior_succ (n + 1) hy)
  obtain ⟨N, ⟨hNo, hysN, hNconn⟩, hNF⟩ :=
    (LocallyConnectedSpace.open_connected_basis ys).mem_iff.mp (hFopen.mem_nhds hysF)
  have hND : N ⊆ connectedComponentIn (Kex (n + 1))ᶜ ys :=
    hNconn.isPreconnected.subset_connectedComponentIn hysN hNF
  have hAcc2 : AccPt ys (𝓟 (Y ∩ N)) := by
    rw [accPt_iff_nhds] at hAcc ⊢
    intro U hU
    obtain ⟨w, ⟨hwU, hwY⟩, hwne⟩ := hAcc (U ∩ N) (Filter.inter_mem hU (hNo.mem_nhds hysN))
    exact ⟨w, ⟨hwU.1, hwY, hwU.2⟩, hwne⟩
  have hYNinf : (Y ∩ N).Infinite := Set.Infinite.of_accPt hAcc2
  have hSub : (Y ∩ N).Subsingleton := by
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨hw₁Y, hw₁N⟩ := hw₁
    obtain ⟨hw₂Y, hw₂N⟩ := hw₂
    obtain ⟨D₁, hD₁R, rfl⟩ := hw₁Y
    obtain ⟨D₂, hD₂R, rfl⟩ := hw₂Y
    have hd1 : Dpt D₁ ∈ D₁ := (hDpt D₁ hD₁R).1
    have hd2 : Dpt D₂ ∈ D₂ := (hDpt D₂ hD₂R).1
    obtain ⟨m₁, _, rfl⟩ := hD₁R
    obtain ⟨m₂, _, rfl⟩ := hD₂R
    have e1 : D m₁ = connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₁)) :=
      connectedComponentIn_eq hd1
    have e2 : D m₂ = connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₂)) :=
      connectedComponentIn_eq hd2
    have f1 : connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₁))
        = connectedComponentIn (Kex (n + 1))ᶜ ys :=
      (connectedComponentIn_eq (hND hw₁N)).symm
    have f2 : connectedComponentIn (Kex (n + 1))ᶜ (Dpt (D m₂))
        = connectedComponentIn (Kex (n + 1))ᶜ ys :=
      (connectedComponentIn_eq (hND hw₂N)).symm
    have : D m₁ = D m₂ := by rw [e1, f1, ← f2, ← e2]
    rw [this]
  exact hYNinf hSub.finite

/-! ## Simplicity infrastructure for the pruning -/

/-- A nondegenerate chart segment has distinct image endpoints. -/
theorem _root_.Rado.PLSeg.p0_ne_p1 {O : Set X} (s : PLSeg O) (h : s.a ≠ s.b) :
    s.p0 ≠ s.p1 := by
  have ha : s.a ∈ s.e.target := s.htgt (left_mem_segment ℝ _ _)
  have hb : s.b ∈ s.e.target := s.htgt (right_mem_segment ℝ _ _)
  intro heq
  exact h ((s.e.symm_source ▸ s.e.symm.injOn) ha hb heq)

/-- **Extraction of `hadj`/`hfar` from the "meets-earlier-union-only-at-start"
invariant.**  If an ℕ-indexed family of nondegenerate chained segments has the
property that each segment meets the union of the earlier ones only at its start
point, then consecutive segments meet only at their shared endpoint and segments
at least two apart are disjoint. -/
theorem simple_family_adj_far {O : Set X} (f : ℕ → PLSeg O)
    (hne : ∀ i, (f i).p0 ≠ (f i).p1)
    (hch : ∀ i, (f i).p1 = (f (i + 1)).p0)
    (hsimp : ∀ i, (f i).img ∩ (⋃ j ∈ Finset.range i, (f j).img) ⊆ {(f i).p0}) :
    (∀ i, (f i).img ∩ (f (i + 1)).img ⊆ {(f i).p1}) ∧
    (∀ m n, m + 2 ≤ n → Disjoint ((f m).img) ((f n).img)) := by
  refine ⟨?_, ?_⟩
  · intro i
    have hmem : (f i).img ⊆ ⋃ j ∈ Finset.range (i + 1), (f j).img :=
      fun x hx => Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self i)) hx
    calc (f i).img ∩ (f (i + 1)).img
        ⊆ (f (i + 1)).img ∩ (⋃ j ∈ Finset.range (i + 1), (f j).img) := by
          rw [Set.inter_comm]; exact Set.inter_subset_inter_right _ hmem
      _ ⊆ {(f (i + 1)).p0} := hsimp (i + 1)
      _ = {(f i).p1} := by rw [hch i]
  · intro m n hmn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hmn' : m < n' := by omega
    rw [Set.disjoint_left]
    intro x hxm hxn
    -- `x = (f (n'+1)).p0 = (f n').p1`
    have hx1 : x ∈ ({(f (n' + 1)).p0} : Set X) := by
      refine hsimp (n' + 1) ⟨hxn, ?_⟩
      exact Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hxm
    rw [Set.mem_singleton_iff, ← hch n'] at hx1
    -- now `x = (f n').p1 ∈ (f n').img ∩ (f m).img ⊆ {(f n').p0}`
    have hxfn' : x ∈ (f n').img := hx1 ▸ (f n').p1_mem
    have hx2 : x ∈ ({(f n').p0} : Set X) := by
      refine hsimp n' ⟨hxfn', ?_⟩
      exact Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hxm
    rw [Set.mem_singleton_iff] at hx2
    exact hne n' (hx2 ▸ hx1)

/-- **Simplicity of a finite chart polyline (tail-first).**  Each segment meets
the union of the *earlier* segments only at its own start point.  This is the
invariant maintained by the last-exit pruning; `simple_family_adj_far` turns its
ℕ-indexed analogue into the `hadj`/`hfar` disjointness data. -/
def SimpleList {O : Set X} (L : List (PLSeg O)) : Prop :=
  ∀ i (h : i < L.length), L[i].img ∩ (⋃ t ∈ L.take i, t.img) ⊆ {L[i].p0}

theorem simpleList_nil {O : Set X} : SimpleList ([] : List (PLSeg O)) :=
  fun i h => absurd h (by simp)

/-- Appending a segment that meets the current union only at its start preserves
simplicity. -/
theorem SimpleList.snoc {O : Set X} {L : List (PLSeg O)} (hL : SimpleList L)
    {s : PLSeg O} (hs : s.img ∩ (⋃ t ∈ L, t.img) ⊆ {s.p0}) :
    SimpleList (L ++ [s]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i L.length with hlt | hge
  · -- element `i` is inside `L`
    rw [List.getElem_append_left hlt, List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact hL i hlt
  · -- element `i` is the appended `s`
    have hieq : i = L.length := by omega
    subst hieq
    rw [List.getElem_concat_length rfl, List.take_left]
    exact hs

/-- The image union of a polyline splits over its first segment. -/
theorem biUnion_img_cons {O : Set X} (s : PLSeg O) (L : List (PLSeg O)) :
    (⋃ t ∈ s :: L, t.img) = s.img ∪ (⋃ t ∈ L, t.img) := by
  ext y
  simp only [Set.mem_iUnion, List.mem_cons, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨t, rfl | ht, hy⟩
    · exact Or.inl hy
    · exact Or.inr ⟨t, ht, hy⟩
  · rintro (hy | ⟨t, ht, hy⟩)
    · exact ⟨s, Or.inl rfl, hy⟩
    · exact ⟨t, Or.inr ht, hy⟩

/-- The image union of a polyline splits over its last segment. -/
theorem biUnion_img_concat {O : Set X} (L : List (PLSeg O)) (s : PLSeg O) :
    (⋃ t ∈ L ++ [s], t.img) = (⋃ t ∈ L, t.img) ∪ s.img := by
  ext y
  simp only [Set.mem_iUnion, List.mem_append, List.mem_singleton, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨t, ht | rfl, hy⟩
    · exact Or.inl ⟨t, ht, hy⟩
    · exact Or.inr hy
  · rintro (⟨t, ht, hy⟩ | hy)
    · exact ⟨t, Or.inl ht, hy⟩
    · exact ⟨s, Or.inr rfl, hy⟩

/-- A segment's image is contained in the polyline's image union. -/
theorem img_subset_biUnion {O : Set X} {L : List (PLSeg O)} {t : PLSeg O} (ht : t ∈ L) :
    t.img ⊆ ⋃ t' ∈ L, t'.img :=
  fun y hy => Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hy⟩⟩

/-- The image union of a polyline is compact. -/
theorem biUnion_img_isCompact {O : Set X} (L : List (PLSeg O)) :
    IsCompact (⋃ t ∈ L, t.img) := by
  induction L with
  | nil => simp
  | cons s L ih =>
    have hsplit : (⋃ t ∈ s :: L, t.img) = s.img ∪ (⋃ t ∈ L, t.img) := by
      ext y
      simp only [List.mem_cons, Set.mem_iUnion, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨t, rfl | ht, hy⟩
        · exact Or.inl hy
        · exact Or.inr ⟨t, ht, hy⟩
      · rintro (hy | ⟨t, ht, hy⟩)
        · exact ⟨s, Or.inl rfl, hy⟩
        · exact ⟨t, Or.inr ht, hy⟩
    rw [hsplit]; exact s.img_compact.union ih

/-- Dropping the last segment preserves simplicity. -/
theorem SimpleList.of_concat {O : Set X} {L : List (PLSeg O)} {s : PLSeg O}
    (h : SimpleList (L ++ [s])) : SimpleList L := by
  intro i hi
  have hi' : i < (L ++ [s]).length := by rw [List.length_append]; omega
  have hh := h i hi'
  rwa [List.getElem_append_left hi, List.take_append_of_le_length (Nat.le_of_lt hi)] at hh

/-- In a simple polyline, the last segment meets the union of the earlier ones only
at its start point. -/
theorem SimpleList.last_meets {O : Set X} {L : List (PLSeg O)} {s : PLSeg O}
    (h : SimpleList (L ++ [s])) : s.img ∩ (⋃ t ∈ L, t.img) ⊆ {s.p0} := by
  have hlen : L.length < (L ++ [s]).length := by rw [List.length_append]; simp
  have hh := h L.length hlen
  rwa [List.getElem_concat_length rfl, List.take_left] at hh

/-- **Last-exit truncation of a simple polyline.**  Given a simple chained polyline
starting at `src` and a point `x` on it, there is a simple chained polyline starting
at `src` and *ending at* `x`, whose image is contained in the original one. -/
theorem exists_truncate {O : Set X} {src : X} :
    ∀ {L : List (PLSeg O)}, SimpleList L → List.IsChain (fun s t => s.p1 = t.p0) L →
      L.head?.elim True (fun s => s.p0 = src) → (∀ s ∈ L, s.a ≠ s.b) →
      ∀ {x : X}, x ∈ (⋃ t ∈ L, t.img) →
      ∃ L' : List (PLSeg O), SimpleList L' ∧
        List.IsChain (fun s t => s.p1 = t.p0) L' ∧
        L'.head?.elim True (fun s => s.p0 = src) ∧ (∀ s ∈ L', s.a ≠ s.b) ∧
        (⋃ t ∈ L', t.img) ⊆ (⋃ t ∈ L, t.img) ∧
        L'.getLast?.elim (x = src) (fun s => s.p1 = x) ∧
        -- **Prefix preservation.**  Truncation removes only a *suffix*: any prefix of `L`
        -- that the cut point `x` misses survives verbatim in `L'`.  This is the clause
        -- P2's stabilisation runs on — image containment alone does not compose across
        -- stages, but "the early segments are literally still there" does.
        (∀ {L₁ : List (PLSeg O)}, L₁ <+: L → (∀ t ∈ L₁, x ∉ t.img) → L₁ <+: L') := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ _ _ _ x hx; simp only [List.not_mem_nil, Set.iUnion_of_empty,
      Set.iUnion_empty, Set.mem_empty_iff_false] at hx
  | append_singleton L₀ s ih =>
    intro hsimple hchain hstart hnd x hx
    have hsimple₀ : SimpleList L₀ := hsimple.of_concat
    have hchain₀ : List.IsChain (fun s t => s.p1 = t.p0) L₀ :=
      (List.isChain_append.mp hchain).1
    have hconn : ∀ g ∈ L₀.getLast?, g.p1 = s.p0 := by
      intro g hg
      exact (List.isChain_append.mp hchain).2.2 g hg s (by simp)
    have hstart₀ : L₀.head?.elim True (fun t => t.p0 = src) := by
      cases L₀ with
      | nil => trivial
      | cons a t => simpa using hstart
    have hnd₀ : ∀ t ∈ L₀, t.a ≠ t.b := fun t ht => hnd t (List.mem_append_left _ ht)
    have hlast_meets : s.img ∩ (⋃ t ∈ L₀, t.img) ⊆ {s.p0} := hsimple.last_meets
    rw [biUnion_img_concat] at hx
    by_cases hxs : x ∈ s.img
    · -- the point is on the last segment: cut it here
      obtain ⟨d, hd, hdx⟩ := hxs
      by_cases hda : d = s.a
      · -- degenerate cut at the start of `s`: drop `s`
        refine ⟨L₀, hsimple₀, hchain₀, hstart₀, hnd₀, ?_, ?_, ?_⟩
        · rw [biUnion_img_concat]; exact Set.subset_union_left
        · have hxp0 : x = s.p0 := by rw [← hdx, hda]; rfl
          cases hlast : L₀.getLast? with
          | none => simp only [hlast, Option.elim]
                    have hL0nil : L₀ = [] := List.getLast?_eq_none_iff.mp hlast
                    subst hL0nil
                    simpa [hxp0] using hstart
          | some g => simp only [hlast, Option.elim]
                      rw [hxp0]; exact hconn g hlast
        · -- `x ∈ s.img`, so a prefix missing `x` cannot contain `s`; it lies in `L₀ = L'`.
          intro L₁ hpre hmiss
          rcases List.prefix_concat_iff.mp hpre with rfl | hpre'
          · -- `hxs` was destructured above, so rebuild `x ∈ s.img` from its pieces.
            exact absurd (show x ∈ s.img from ⟨d, hd, hdx⟩)
              (hmiss s (List.mem_append_right _ (List.mem_singleton_self _)))
          · exact hpre'
      · -- proper cut inside `s`: keep `s.splitL d`
        have hsL : s.img ∩ (⋃ t ∈ L₀, t.img) ⊆ {s.p0} := hlast_meets
        have hsplit_meets : (s.splitL d hd).img ∩ (⋃ t ∈ L₀, t.img) ⊆ {(s.splitL d hd).p0} := by
          intro y hy
          exact hsL ⟨s.splitL_img_sub d hd hy.1, hy.2⟩
        refine ⟨L₀ ++ [s.splitL d hd], hsimple₀.snoc hsplit_meets, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · refine List.IsChain.append hchain₀ (List.IsChain.singleton _) ?_
          intro g hg y hy
          rw [List.head?_singleton, Option.mem_some_iff] at hy
          rw [← hy]
          exact hconn g hg
        · cases L₀ with
          | nil => simp only [List.nil_append, List.head?_cons, Option.elim]
                   have : (s.splitL d hd).p0 = s.p0 := rfl
                   rw [this]; simpa using hstart
          | cons a t => simpa using hstart₀
        · intro t ht
          rcases List.mem_append.mp ht with ht' | ht'
          · exact hnd₀ t ht'
          · rw [List.mem_singleton] at ht'; subst ht'
            exact fun h => hda h.symm
        · rw [biUnion_img_concat, biUnion_img_concat]
          exact Set.union_subset_union_right _ (s.splitL_img_sub d hd)
        · simp only [List.getLast?_concat, Option.elim]
          show (s.splitL d hd).p1 = x
          rw [PLSeg.splitL_p1]; exact hdx
        · -- same as the drop case: `x ∈ s.img`, so a prefix missing `x` cannot contain
          -- `s`; it lies in `L₀`, which is a prefix of `L₀ ++ [s.splitL d hd]`.
          intro L₁ hpre hmiss
          rcases List.prefix_concat_iff.mp hpre with rfl | hpre'
          · -- `hxs` was destructured above, so rebuild `x ∈ s.img` from its pieces.
            exact absurd (show x ∈ s.img from ⟨d, hd, hdx⟩)
              (hmiss s (List.mem_append_right _ (List.mem_singleton_self _)))
          · exact hpre'.trans (List.prefix_append _ _)
    · -- the point is on an earlier segment: recurse
      have hx0 : x ∈ (⋃ t ∈ L₀, t.img) := hx.resolve_right hxs
      obtain ⟨L', h1, h2, h3, h4, h5, h6, h7⟩ := ih hsimple₀ hchain₀ hstart₀ hnd₀ hx0
      refine ⟨L', h1, h2, h3, h4, ?_, h6, ?_⟩
      · rw [biUnion_img_concat]
        exact h5.trans Set.subset_union_left
      · -- Here `x` lies in `⋃ L₀`, so a prefix missing `x` cannot be all of `L₀ ++ [s]`
        -- (that would contain the segment carrying `x`); hence it is a prefix of `L₀`,
        -- and the inductive hypothesis applies.
        intro L₁ hpre hmiss
        rcases List.prefix_concat_iff.mp hpre with rfl | hpre'
        · obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx0
          exact absurd hxt (hmiss t (List.mem_append_left _ ht))
        · exact h7 hpre' hmiss

/-- **Last-exit point of a chart segment from a compact set.**  If a straight
chart segment `σ` starts inside a compact set `K`, there is a *last* parameter
`T ∈ [0,1]` at which the segment lies in `K`: `σ` at `T` is in `K`, and for every
parameter beyond `T` the segment has left `K`.  (The supremum of the hit set.) -/
theorem exists_last_exit [T2Space X] {O : Set X} (σ : PLSeg O) {K : Set X}
    (hK : IsCompact K)
    (h0 : σ.e.symm (AffineMap.lineMap σ.a σ.b (0 : ℝ)) ∈ K) :
    ∃ T ∈ Set.Icc (0 : ℝ) 1,
      σ.e.symm (AffineMap.lineMap σ.a σ.b T) ∈ K ∧
      ∀ u ∈ Set.Ioc T 1, σ.e.symm (AffineMap.lineMap σ.a σ.b u) ∉ K := by
  set g : ℝ → X := fun u => σ.e.symm (AffineMap.lineMap σ.a σ.b u) with hg
  have hmaps : Set.MapsTo (AffineMap.lineMap σ.a σ.b) (Set.Icc (0 : ℝ) 1) σ.e.target :=
    fun u hu => σ.htgt (lineMap_mem_segment (𝕜 := ℝ) σ.a σ.b hu)
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    σ.e.continuousOn_symm.comp (by fun_prop) hmaps
  set H : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ g ⁻¹' K with hH
  have hHcl : IsClosed H := hgcont.preimage_isClosed_of_isClosed isClosed_Icc hK.isClosed
  have hHne : H.Nonempty := ⟨0, ⟨le_refl 0, zero_le_one⟩, h0⟩
  have hHbdd : BddAbove H := bddAbove_Icc.mono Set.inter_subset_left
  have hTmem : sSup H ∈ H := hHcl.csSup_mem hHne hHbdd
  refine ⟨sSup H, hTmem.1, hTmem.2, ?_⟩
  intro u hu hmem
  have huH : u ∈ H := ⟨⟨le_trans hTmem.1.1 (le_of_lt hu.1), hu.2⟩, hmem⟩
  exact absurd (le_csSup hHbdd huH) (not_le.mpr hu.1)

/-- The residual tail `σ.splitR cT` beyond the last-exit parameter `T` meets the
compact set `K` only at the exit point itself. -/
theorem splitR_meets_last_exit {O : Set X} (σ : PLSeg O) {T : ℝ} (hT1 : T ≤ 1)
    (hcT : AffineMap.lineMap σ.a σ.b T ∈ segment ℝ σ.a σ.b) {K : Set X}
    (hlast : ∀ u ∈ Set.Ioc T 1, σ.e.symm (AffineMap.lineMap σ.a σ.b u) ∉ K) :
    (σ.splitR (AffineMap.lineMap σ.a σ.b T) hcT).img ∩ K ⊆
      {σ.e.symm (AffineMap.lineMap σ.a σ.b T)} := by
  rintro y ⟨hyimg, hyK⟩
  obtain ⟨v, hv, rfl⟩ := hyimg
  rw [show (σ.splitR (AffineMap.lineMap σ.a σ.b T) hcT).b = σ.b from rfl,
    show (σ.splitR (AffineMap.lineMap σ.a σ.b T) hcT).a = AffineMap.lineMap σ.a σ.b T from rfl,
    segment_eq_image_lineMap] at hv
  obtain ⟨r, hr, rfl⟩ := hv
  set u : ℝ := AffineMap.lineMap T (1 : ℝ) r with hu
  have hval : AffineMap.lineMap (AffineMap.lineMap σ.a σ.b T) σ.b r
      = AffineMap.lineMap σ.a σ.b u := by
    rw [hu, AffineMap.apply_lineMap, AffineMap.lineMap_apply_one]
  have humem : u ∈ Set.Icc T 1 := by
    rw [← segment_eq_Icc hT1]; exact lineMap_mem_segment (𝕜 := ℝ) T 1 hr
  rw [hval] at hyK ⊢
  rcases eq_or_lt_of_le humem.1 with huT | huT
  · rw [← huT]; exact Set.mem_singleton_iff.mpr rfl
  · exact absurd hyK (hlast u ⟨huT, humem.2⟩)

/-- **P1: single last-exit prune step.**  Appending one straight raw segment `σ`
(starting where the accumulated simple arc ends) to a simple chained polyline, then
pruning by the last-exit trick, yields a simple chained polyline from the same start
to `σ.p1`.  The material only grows by (part of) `σ.img`, and every surviving
segment's image lies in the old union or in `σ.img`. -/
theorem prune_step [T2Space X] {O : Set X} {src p : X}
    {L : List (PLSeg O)} (hsimple : SimpleList L)
    (hchain : List.IsChain (fun s t => s.p1 = t.p0) L)
    (hstart : L.head?.elim True (fun s => s.p0 = src)) (hnd : ∀ s ∈ L, s.a ≠ s.b)
    (hend : L.getLast?.elim (src = p) (fun s => s.p1 = p))
    (σ : PLSeg O) (hσ0 : σ.p0 = p) :
    ∃ L' : List (PLSeg O), SimpleList L' ∧
      List.IsChain (fun s t => s.p1 = t.p0) L' ∧
      L'.head?.elim True (fun s => s.p0 = src) ∧ (∀ s ∈ L', s.a ≠ s.b) ∧
      L'.getLast?.elim (src = σ.p1) (fun s => s.p1 = σ.p1) ∧
      (⋃ t ∈ L', t.img) ⊆ (⋃ t ∈ L, t.img) ∪ σ.img ∧
      (∀ s ∈ L', s.img ⊆ (⋃ t ∈ L, t.img) ∨ s.img ⊆ σ.img) ∧
      -- **Prefix preservation** (inherited from `exists_truncate`).  The cut point lies
      -- on `σ`, so a prefix of the arc whose segments avoid `σ` entirely is untouched.
      -- Across stages this is what freezes the early segments: stage-`n` material lies
      -- in `Om n`, which escapes every compact set, hence misses any fixed prefix.
      (∀ {L₁ : List (PLSeg O)}, L₁ <+: L → (∀ t ∈ L₁, Disjoint t.img σ.img) →
        L₁ <+: L') := by
  set K : Set X := ⋃ t ∈ L, t.img with hKdef
  by_cases hdeg : σ.p0 = σ.p1
  · -- degenerate raw segment: keep the arc unchanged
    have hp : p = σ.p1 := hσ0.symm.trans hdeg
    refine ⟨L, hsimple, hchain, hstart, hnd, ?_, Set.subset_union_left,
      fun s hs => Or.inl (img_subset_biUnion hs), fun hpre _ => hpre⟩
    rw [hp] at hend; exact hend
  -- nondegenerate raw segment
  have hσab : σ.a ≠ σ.b := by
    intro h; exact hdeg (by show σ.e.symm σ.a = σ.e.symm σ.b; rw [h])
  by_cases hLnil : L = []
  · -- empty accumulator: start the arc with `σ`
    subst hLnil
    have hsp : src = p := by simpa using hend
    refine ⟨[σ], (simpleList_nil.snoc (by simp)), List.IsChain.singleton σ, ?_,
      ?_, ?_, ?_, ?_, fun hpre _ => by rw [List.prefix_nil.mp hpre]; exact List.nil_prefix⟩
    · show σ.p0 = src; rw [hσ0, hsp]
    · intro s hs; rw [List.mem_singleton] at hs; subst hs; exact hσab
    · show σ.p1 = σ.p1; rfl
    · simp
    · intro s hs; rw [List.mem_singleton] at hs; subst hs; exact Or.inr (le_refl _)
  -- nonempty accumulator: last-exit prune
  have hKcompact : IsCompact K := biUnion_img_isCompact L
  have hg : L.getLast hLnil ∈ L := List.getLast_mem hLnil
  have hgl : L.getLast? = some (L.getLast hLnil) := List.getLast?_eq_some_getLast hLnil
  rw [hgl] at hend
  have hpK : p ∈ K := hend ▸ (img_subset_biUnion hg (L.getLast hLnil).p1_mem)
  have h0 : σ.e.symm (AffineMap.lineMap σ.a σ.b (0 : ℝ)) ∈ K := by
    rw [AffineMap.lineMap_apply_zero]; show σ.p0 ∈ K; rw [hσ0]; exact hpK
  obtain ⟨T, hT, hcTK, hlast⟩ := exists_last_exit σ hKcompact h0
  have hcTseg : AffineMap.lineMap σ.a σ.b T ∈ segment ℝ σ.a σ.b :=
    lineMap_mem_segment (𝕜 := ℝ) σ.a σ.b hT
  set x : X := σ.e.symm (AffineMap.lineMap σ.a σ.b T) with hxdef
  have hxK : x ∈ ⋃ t ∈ L, t.img := hcTK
  obtain ⟨L', hS', hC', hH', hN', hU', hE', hP'⟩ :=
    exists_truncate (src := src) hsimple hchain hstart hnd hxK
  have hU'K : (⋃ t ∈ L', t.img) ⊆ K := hU'
  rcases eq_or_lt_of_le hT.2 with hTeq | hTlt
  · -- the whole raw segment is absorbed: `L'` already ends at `σ.p1`
    have hxp1 : x = σ.p1 := by
      rw [hxdef, hTeq, AffineMap.lineMap_apply_one]; rfl
    refine ⟨L', hS', hC', hH', hN', ?_, hU'.trans Set.subset_union_left,
      fun s hs => Or.inl ((img_subset_biUnion hs).trans hU'K),
      fun {L₁} hpre hdisj => hP' hpre (fun t ht =>
        Set.disjoint_right.mp (hdisj t ht) ⟨_, hcTseg, rfl⟩)⟩
    rw [hxp1] at hE'
    cases hgl' : L'.getLast? with
    | none => simp only [hgl', Option.elim] at hE' ⊢; exact hE'.symm
    | some g => simp only [hgl', Option.elim] at hE' ⊢; exact hE'
  · -- genuine residual tail: append `σ.splitR`
    set σ' : PLSeg O := σ.splitR (AffineMap.lineMap σ.a σ.b T) hcTseg with hσ'def
    have hσ'0 : σ'.p0 = x := rfl
    have hσ'1 : σ'.p1 = σ.p1 := rfl
    have hmeetK : σ'.img ∩ K ⊆ {x} :=
      splitR_meets_last_exit σ hT.2 hcTseg hlast
    have hmeetL' : σ'.img ∩ (⋃ t ∈ L', t.img) ⊆ {σ'.p0} := by
      rw [hσ'0]
      exact fun y hy => hmeetK ⟨hy.1, hU'K hy.2⟩
    have hconn : ∀ g ∈ L'.getLast?, g.p1 = σ'.p0 := by
      intro g hg'
      rw [hσ'0]
      have := hE'
      rw [(by exact hg' : L'.getLast? = some g)] at this
      exact this
    refine ⟨L' ++ [σ'], hS'.snoc hmeetL', ?_, ?_, ?_, ?_, ?_, ?_,
      fun {L₁} hpre hdisj => (hP' hpre (fun t ht =>
        Set.disjoint_right.mp (hdisj t ht) ⟨_, hcTseg, rfl⟩)).trans (List.prefix_append _ _)⟩
    · refine List.IsChain.append hC' (List.IsChain.singleton _) ?_
      intro g hg' y hy
      rw [List.head?_singleton, Option.mem_some_iff] at hy
      rw [← hy]; exact hconn g hg'
    · rcases eq_or_ne L' [] with hL'nil | hL'ne
      · subst hL'nil
        show σ'.p0 = src
        rw [hσ'0]; simpa using hE'
      · rw [List.head?_append_of_ne_nil L' hL'ne]; exact hH'
    · intro s hs
      rcases List.mem_append.mp hs with hs' | hs'
      · exact hN' s hs'
      · rw [List.mem_singleton] at hs'; subst hs'
        show AffineMap.lineMap σ.a σ.b T ≠ σ.b
        intro h
        rcases (AffineMap.lineMap_eq_right_iff (k := ℝ) (V1 := ℂ)).mp h with hc | hc
        · exact hσab hc
        · exact absurd hc (ne_of_lt hTlt)
    · simp only [List.getLast?_concat, Option.elim]; exact hσ'1
    · rw [biUnion_img_concat]
      refine Set.union_subset (hU'.trans Set.subset_union_left) ?_
      exact (σ.splitR_img_sub _ hcTseg).trans Set.subset_union_right
    · intro s hs
      rcases List.mem_append.mp hs with hs' | hs'
      · exact Or.inl ((img_subset_biUnion hs').trans hU'K)
      · rw [List.mem_singleton] at hs'; subst hs'
        exact Or.inr (σ.splitR_img_sub _ hcTseg)

/-! ### P2 step 0: the accumulated-arc package

The stage recursion carries six invariants at once.  Bundling them keeps the
`Nat.rec` in `nonempty_simpleRayData` readable and lets `prune_chain` be stated as
an endomorphism `ArcTo src p → ArcTo src q`. -/

/-- A simple, chained, nondegenerate polyline from `src` to `p` inside `O`. -/
structure ArcTo (O : Set X) (src p : X) where
  /-- The underlying segment list. -/
  L : List (PLSeg O)
  /-- Successive segments meet earlier ones only at the shared start. -/
  simple : SimpleList L
  /-- Consecutive segments chain. -/
  chain : List.IsChain (fun s t => s.p1 = t.p0) L
  /-- The arc starts at `src` (vacuous when empty). -/
  head : L.head?.elim True (fun s => s.p0 = src)
  /-- Every segment is nondegenerate in its chart. -/
  nd : ∀ s ∈ L, s.a ≠ s.b
  /-- The arc ends at `p` (degenerating to `src = p` when empty). -/
  fin : L.getLast?.elim (src = p) (fun s => s.p1 = p)

namespace ArcTo

variable {O : Set X} {src p : X}

/-- The material swept by the arc. -/
def img (A : ArcTo O src p) : Set X := ⋃ t ∈ A.L, t.img

theorem img_isCompact (A : ArcTo O src p) : IsCompact A.img := biUnion_img_isCompact A.L

/-- The empty arc, from `src` to itself. -/
def nil (O : Set X) (src : X) : ArcTo O src src where
  L := []
  simple := simpleList_nil
  chain := List.IsChain.nil
  head := by simp
  nd := by simp
  fin := by simp

@[simp] theorem nil_L (O : Set X) (src : X) : (nil O src).L = [] := rfl

end ArcTo

/-! ### P2 step 1: raw chains as segment lists, and the per-stage fold -/

/-- **A `CStep` chain, unfolded into a list of segments.**  No nondegeneracy is claimed:
`Relation.ReflTransGen` admits degenerate steps, and `prune_step` absorbs them. -/
theorem exists_plseg_list {O : Set X} {x y : X}
    (h : Relation.ReflTransGen (CStep O) x y) :
    ∃ R : List (PLSeg O), List.IsChain (fun s t => s.p1 = t.p0) R ∧
      R.head?.elim (x = y) (fun s => s.p0 = x) ∧
      R.getLast?.elim (x = y) (fun s => s.p1 = y) := by
  -- Build from the *head*: consing keeps `head?`/`IsChain` trivial, whereas appending
  -- forces `getLast?` case analysis at every step.
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], List.IsChain.nil, by simp, by simp⟩
  | @head u c h' _ ih =>
      obtain ⟨R, hRchain, hRhead, hRlast⟩ := ih
      obtain ⟨σ, hσ0, hσ1⟩ := Rado.CStep.toPLSeg h'
      rcases R with _ | ⟨hd, tl⟩
      · simp only [List.head?_nil, List.getLast?_nil, Option.elim] at hRhead hRlast
        exact ⟨[σ], List.IsChain.singleton _, by simpa using hσ0,
          by simpa [hσ1] using hRlast⟩
      · simp only [List.head?_cons, Option.elim] at hRhead
        refine ⟨σ :: hd :: tl, List.isChain_cons_cons.mpr ⟨by rw [hσ1, hRhead], hRchain⟩,
          by simpa using hσ0, ?_⟩
        -- `getLast?` of a cons-cons is the tail's, and it is never `none`, so the two
        -- `Option.elim` defaults (`u = y` here, `c = y` in `hRlast`) are both discarded.
        rw [List.getLast?_cons_cons]
        cases hw : (hd :: tl).getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hw) (by simp)
        | some w => rw [hw] at hRlast; simpa using hRlast

/-- A stage's raw chain, re-based into the ambient set `Z` while remembering that its
material stayed inside the (smaller) stage set `O`.  That memory is what the escape
argument consumes: stage `n` lives in `Om n`, which eventually misses any fixed
compact, hence any fixed prefix of the accumulated arc. -/
theorem exists_stage_list {O Z : Set X} (hOZ : O ⊆ Z) {x y : X}
    (h : Relation.ReflTransGen (CStep O) x y) :
    ∃ R : List (PLSeg Z), List.IsChain (fun s t => s.p1 = t.p0) R ∧
      R.head?.elim (x = y) (fun s => s.p0 = x) ∧
      R.getLast?.elim (x = y) (fun s => s.p1 = y) ∧
      (∀ t ∈ R, t.img ⊆ O) := by
  obtain ⟨R₀, hc, hh, hl⟩ := exists_plseg_list h
  refine ⟨R₀.map (PLSeg.mono hOZ), ?_,
    by simpa [Function.comp_def] using hh, by simpa [Function.comp_def] using hl, ?_⟩
  · exact List.isChain_map_of_isChain (PLSeg.mono hOZ) (fun _ _ hab => hab) hc
  · intro t ht
    obtain ⟨t₀, _, rfl⟩ := List.mem_map.mp ht
    exact t₀.hsub

/-- **P2, per stage: fold `prune_step` along a whole raw chain.**  Given a simple arc `L`
from `src` to `p` and a raw (possibly self-crossing, possibly degenerate) chain `R` from
`p` to `q`, last-exit pruning segment by segment yields a simple arc from `src` to `q`
whose material is drawn from `L` and `R` only.

The final clause is the one P2's stabilisation argument runs on: every surviving segment
came either from the old arc or from this stage's raw material, so a segment that is far
from stage `n`'s material cannot be disturbed at stage `n`. -/
theorem prune_chain [T2Space X] {O : Set X} {src : X} :
    ∀ (R : List (PLSeg O)) {p q : X} {L : List (PLSeg O)}, SimpleList L →
      List.IsChain (fun s t => s.p1 = t.p0) L →
      L.head?.elim True (fun s => s.p0 = src) → (∀ s ∈ L, s.a ≠ s.b) →
      L.getLast?.elim (src = p) (fun s => s.p1 = p) →
      List.IsChain (fun s t => s.p1 = t.p0) R →
      R.head?.elim (p = q) (fun s => s.p0 = p) →
      R.getLast?.elim (p = q) (fun s => s.p1 = q) →
      ∃ L' : List (PLSeg O), SimpleList L' ∧
        List.IsChain (fun s t => s.p1 = t.p0) L' ∧
        L'.head?.elim True (fun s => s.p0 = src) ∧ (∀ s ∈ L', s.a ≠ s.b) ∧
        L'.getLast?.elim (src = q) (fun s => s.p1 = q) ∧
        (⋃ t ∈ L', t.img) ⊆ (⋃ t ∈ L, t.img) ∪ (⋃ t ∈ R, t.img) ∧
        (∀ {L₁ : List (PLSeg O)}, L₁ <+: L →
          (∀ t ∈ L₁, ∀ u ∈ R, Disjoint t.img u.img) → L₁ <+: L') := by
  intro R
  induction R with
  | nil =>
      intro p q L hsimple hchain hstart hnd hend _ hRhead _
      simp only [List.head?_nil, Option.elim] at hRhead
      subst hRhead
      exact ⟨L, hsimple, hchain, hstart, hnd, hend, by simp, fun hpre _ => hpre⟩
  | cons σ R' ih =>
      intro p q L hsimple hchain hstart hnd hend hRchain hRhead hRlast
      simp only [List.head?_cons, Option.elim] at hRhead
      -- one last-exit prune against `σ` …
      obtain ⟨L₁, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        prune_step hsimple hchain hstart hnd hend σ hRhead
      -- … then recurse along the rest of the stage
      have hR'head : R'.head?.elim (σ.p1 = q) (fun s => s.p0 = σ.p1) := by
        cases hR : R' with
        | nil =>
            simp only [List.head?_nil, Option.elim]
            rw [hR] at hRlast; simpa using hRlast
        | cons hd tl =>
            simp only [List.head?_cons, Option.elim]
            rw [hR] at hRchain
            exact (List.isChain_cons_cons.mp hRchain).1.symm
      have hR'last : R'.getLast?.elim (σ.p1 = q) (fun s => s.p1 = q) := by
        cases hR : R' with
        | nil => simp only [List.getLast?_nil, Option.elim]; rw [hR] at hRlast; simpa using hRlast
        | cons hd tl =>
            rw [hR, List.getLast?_cons_cons] at hRlast
            cases hw : (hd :: tl).getLast? with
            | none => exact absurd (List.getLast?_eq_none_iff.mp hw) (by simp)
            | some w => rw [hw] at hRlast; simpa using hRlast
      obtain ⟨L₂, g1, g2, g3, g4, g5, g6, g7⟩ :=
        ih h1 h2 h3 h4 h5 (hRchain.tail) hR'head hR'last
      refine ⟨L₂, g1, g2, g3, g4, g5, ?_, ?_⟩
      · -- material: `⋃L₂ ⊆ ⋃L₁ ∪ ⋃R' ⊆ (⋃L ∪ σ.img) ∪ ⋃R' = ⋃L ∪ ⋃(σ :: R')`
        refine g6.trans ?_
        rw [biUnion_img_cons]
        refine Set.union_subset (h6.trans ?_) ?_
        · exact Set.union_subset_union_right _ Set.subset_union_left
        · exact Set.subset_union_of_subset_right Set.subset_union_right _
      · -- prefix: `σ` and every `u ∈ R'` miss the prefix, so neither prune touches it
        intro L₁' hpre hdisj
        exact g7 (h8 hpre (fun t ht => hdisj t ht σ (by simp)))
          (fun t ht u hu => hdisj t ht u (List.mem_cons_of_mem _ hu))

/-- `prune_chain` packaged as an extension of `ArcTo` along one stage.  This is the
step the `Nat.rec` in `nonempty_simpleRayData` iterates. -/
theorem ArcTo.extend [T2Space X] {O : Set X} {src p q : X} (A : ArcTo O src p)
    {R : List (PLSeg O)} (hRchain : List.IsChain (fun s t => s.p1 = t.p0) R)
    (hRhead : R.head?.elim (p = q) (fun s => s.p0 = p))
    (hRlast : R.getLast?.elim (p = q) (fun s => s.p1 = q)) :
    ∃ B : ArcTo O src q,
      B.img ⊆ A.img ∪ (⋃ t ∈ R, t.img) ∧
      (∀ L₁ : List (PLSeg O), L₁ <+: A.L →
        (∀ t ∈ L₁, ∀ u ∈ R, Disjoint t.img u.img) → L₁ <+: B.L) := by
  obtain ⟨L', h1, h2, h3, h4, h5, h6, h7⟩ :=
    prune_chain R A.simple A.chain A.head A.nd A.fin hRchain hRhead hRlast
  exact ⟨⟨L', h1, h2, h3, h4, h5⟩, h6, fun _ hpre hdisj => h7 hpre hdisj⟩

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
  classical
  haveI : LocallyCompactSpace X := Rado.locallyCompactSpace
  haveI : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  haveI : SecondCountableTopology X := Rado.secondCountableTopology_of_riemannSurface
  set Z := connectedComponentIn (closure V)ᶜ x₀ with hZdef
  have hZopen : IsOpen Z := isClosed_closure.isOpen_compl.connectedComponentIn
  have hZconn : IsConnected Z := ⟨⟨z₀, hz₀⟩, isPreconnected_connectedComponentIn⟩
  -- subspace instances on `↥Z`
  haveI hWlc : LocallyCompactSpace ↥Z := hZopen.locallyCompactSpace
  haveI hWsc : SecondCountableTopology ↥Z := inferInstance
  haveI hWsigma : SigmaCompactSpace ↥Z := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI hWconn : ConnectedSpace ↥Z := Subtype.connectedSpace hZconn
  haveI hWlconn : LocallyConnectedSpace ↥Z := hZopen.locallyConnectedSpace
  have hWncs : ¬ CompactSpace ↥Z := fun hc => hZnc (isCompact_iff_compactSpace.mpr hc)
  -- compact exhaustion of `↥Z` with `Kex 0 = ∅`
  set Kex : CompactExhaustion ↥Z := (default : CompactExhaustion ↥Z).shiftr with hKexdef
  have hK0 : (Kex 0 : Set ↥Z) = ∅ := rfl
  have hbase0 : (⟨z₀, hz₀⟩ : ↥Z) ∉ Kex 0 := by rw [hK0]; exact Set.notMem_empty _
  have hbase : ¬ IsCompact (closure (connectedComponentIn (Kex 0)ᶜ (⟨z₀, hz₀⟩ : ↥Z))) := by
    rw [hK0, compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ, closure_univ, isCompact_univ_iff]
    exact hWncs
  -- the decreasing chain of noncompact-closure complement components
  let A : (m : ℕ) →
      {x : ↥Z // x ∉ Kex m ∧ ¬ IsCompact (closure (connectedComponentIn (Kex m)ᶜ x))} :=
    fun m => Nat.rec
      (motive := fun m =>
        {x : ↥Z // x ∉ Kex m ∧ ¬ IsCompact (closure (connectedComponentIn (Kex m)ᶜ x))})
      ⟨⟨z₀, hz₀⟩, hbase0, hbase⟩
      (fun k ih => ⟨(exists_noncompact_subcomponent Kex ih.2.1 ih.2.2).choose,
        (exists_noncompact_subcomponent Kex ih.2.1 ih.2.2).choose_spec.1,
        (exists_noncompact_subcomponent Kex ih.2.1 ih.2.2).choose_spec.2.2⟩)
      m
  set a : ℕ → ↥Z := fun m => (A m).1 with hadef
  have ha_not : ∀ m, a m ∉ Kex m := fun m => (A m).2.1
  have hlink : ∀ m, a (m + 1) ∈ connectedComponentIn (Kex m)ᶜ (a m) := fun m =>
    (exists_noncompact_subcomponent Kex (A m).2.1 (A m).2.2).choose_spec.2.1
  -- the components in `↥Z`
  set C : ℕ → Set ↥Z := fun m => connectedComponentIn (Kex m)ᶜ (a m) with hCdef
  have hCopen : ∀ m, IsOpen (C m) := fun m =>
    ((Kex.isCompact m).isClosed.isOpen_compl).connectedComponentIn
  have hanC : ∀ m, a m ∈ C m := fun m => mem_connectedComponentIn (ha_not m)
  have hCconn : ∀ m, IsConnected (C m) := fun m => ⟨⟨a m, hanC m⟩, isPreconnected_connectedComponentIn⟩
  have hCsub : ∀ m, C m ⊆ (Kex m)ᶜ := fun m => connectedComponentIn_subset _ _
  have haC1 : ∀ m, a (m + 1) ∈ C m := hlink
  -- image sets in `X`: `Om m := Subtype.val '' C m`, open and preconnected in `X`
  have hemb : IsOpenEmbedding (Subtype.val : ↥Z → X) := hZopen.isOpenEmbedding_subtypeVal
  set Om : ℕ → Set X := fun m => Subtype.val '' (C m) with hOmdef
  have hOmopen : ∀ m, IsOpen (Om m) := fun m => hemb.isOpenMap _ (hCopen m)
  have hOmpre : ∀ m, IsPreconnected (Om m) := fun m =>
    (hCconn m).isPreconnected.image _ continuous_subtype_val.continuousOn
  have hOmsubZ : ∀ m, Om m ⊆ Z := by
    intro m
    rintro _ ⟨y, _, rfl⟩; exact y.2
  have haOm : ∀ m, (a m : X) ∈ Om m := fun m => ⟨a m, hanC m, rfl⟩
  have ha1Om : ∀ m, (a (m + 1) : X) ∈ Om m := fun m => ⟨a (m + 1), haC1 m, rfl⟩
  -- per-stage raw chart-polyline chains from `a m` to `a (m+1)` inside `Om m`
  have hrawchain : ∀ m, Relation.ReflTransGen (CStep (Om m)) (a m : X) (a (m + 1) : X) :=
    fun m => exists_cStep_chain (hOmopen m) (hOmpre m) (haOm m) (ha1Om m)
  -- ## P2: the accumulated arcs
  -- Each stage's raw chain, re-based into `Z` but remembering it lives in `Om m`.
  choose Rw hRwchain hRwhead hRwlast hRwsub using
    fun m => exists_stage_list (hOmsubZ m) (hrawchain m)
  -- One stage of last-exit pruning, as a step on `ArcTo` packages.
  have hstep : ∀ (n : ℕ) (A : ArcTo Z z₀ (a n : X)), ∃ B : ArcTo Z z₀ (a (n + 1) : X),
      B.img ⊆ A.img ∪ (⋃ t ∈ Rw n, t.img) ∧
      (∀ L₁ : List (PLSeg Z), L₁ <+: A.L →
        (∀ t ∈ L₁, ∀ u ∈ Rw n, Disjoint t.img u.img) → L₁ <+: B.L) :=
    fun n A => A.extend (hRwchain n) (hRwhead n) (hRwlast n)
  choose stepFn hstep_img hstep_pre using hstep
  -- The accumulated arc after `n` stages, from `z₀` to `a n`.
  have ha0 : (a 0 : X) = z₀ := rfl
  set Acc : ∀ n, ArcTo Z z₀ (a n : X) := fun n =>
    Nat.rec (motive := fun n => ArcTo Z z₀ (a n : X))
      (ha0 ▸ ArcTo.nil Z z₀) (fun k ih => stepFn k ih) n with hAccdef
  have hAcc_succ : ∀ n, Acc (n + 1) = stepFn n (Acc n) := fun _ => rfl
  -- Stage-`n` material lies in `Om n`, which is disjoint from `Kex n`'s image in `X`.
  have hRw_far : ∀ n, ∀ u ∈ Rw n, u.img ⊆ Om n := hRwsub
  -- **The escape property.**  Every compact subset of `Z` is missed by all late stages:
  -- `Kex` exhausts `↥Z`, so it eventually swallows the compactum, while stage `n`'s
  -- material lies in `Om n`, the image of `C n ⊆ (Kex n)ᶜ`.  This is what supplies
  -- `prune_chain`'s disjointness hypothesis and therefore freezes each fixed prefix.
  have hescape : ∀ S : Set X, IsCompact S → S ⊆ Z → ∃ N, ∀ n, N ≤ n → Disjoint S (Om n) := by
    intro S hS hSZ
    have hS' : IsCompact (Subtype.val ⁻¹' S : Set ↥Z) := by
      rw [hemb.isInducing.isCompact_iff, Subtype.image_preimage_coe,
        Set.inter_eq_self_of_subset_right hSZ]
      exact hS
    obtain ⟨N, hN⟩ := Kex.exists_superset_of_isCompact hS'
    refine ⟨N, fun n hn => ?_⟩
    rw [Set.disjoint_left]
    rintro x hxS ⟨y, hyC, rfl⟩
    exact absurd (Kex.subset hn (hN (by simpa using hxS))) (hCsub n hyC)
  -- REMAINING GAP (P1 + P2 + P3): the arcwise-simplification / last-exit pruning.
  --
  -- The SETUP above is complete and sorry-free.  The context now provides, from any
  -- base point `z₀ ∈ Z`, the decreasing escaping chain of open connected sets
  -- `Om m = Subtype.val '' C m ⊆ Z` (`hOmopen`, `hOmpre`, `hOmsubZ`) with
  -- `C m ⊆ (Kex m)ᶜ` (`hCsub`), endpoints `(a m : X) ∈ Om m`, `(a (m+1) : X) ∈ Om m`
  -- (`haOm`, `ha1Om`), and, crucially, a *raw* finite chart-polyline chain
  -- `hrawchain m : Relation.ReflTransGen (CStep (Om m)) (a m) (a (m+1))` inside each
  -- `Om m`.  Turning `hrawchain m` into a `List (PLSeg (Om m))` is
  -- `Rado.CStep.toPLSeg` + `List.exists_isChain_cons_of_relationReflTransGen`.
  --
  -- STATUS: **P1 is complete and sorry-free** (`prune_step`, built from
  -- `exists_last_exit` + `exists_truncate` + `SimpleList.snoc`): appending one raw
  -- segment to a simple accumulated arc and last-exit–pruning yields a simple arc to
  -- the new endpoint, with every surviving segment's image in the old union or in the
  -- raw segment's image.  The extraction `simple_family_adj_far` (with
  -- `Rado.PLSeg.p0_ne_p1`) turns the ℕ-indexed "meets-earlier-union-only-at-start"
  -- invariant into `hab`/`hadj`/`hfar`.
  --
  -- What remains (the single `sorry`) is the assembly:
  -- * (P2) the ℕ-limit across stages.  Fold `prune_step` over each stage's raw list
  --   (from `hrawchain m` via `Rado.CStep.toPLSeg` +
  --   `List.exists_isChain_cons_of_relationReflTransGen`), producing accumulated arcs
  --   `Acc n` from `z₀` to `a n`.  Each fixed segment index STABILIZES: stage-`n`
  --   material lies in `Om n`, and since `Om` is decreasing with `C n ⊆ (Kex n)ᶜ`
  --   (`hCsub`) and `Kex` exhausts `↥Z`, for `n` large `Om n` is disjoint from any
  --   fixed compact, so the last-exit truncation at stage `n` never reaches an early
  --   segment.  The stable limit is the ℕ-family; its `hsimp` (⇒ `hadj`/`hfar`),
  --   `hne`, `hchain`, `hstart`, and `hesc` follow, and `htgt`/`hZ`/`he` come from each
  --   `PLSeg` (with `hOmsubZ : Om m ⊆ Z`).
  -- * (P3) `hshell` from simplicity + local finiteness + `MetrizableSpace X`
  --   (from `[T2Space X]` + `SecondCountableTopology X` via Urysohn) and
  --   `Disjoint.exists_thickenings`.
  --
  -- P2's stabilized ℕ-limit is the arcwise-connectedness / loop-erasure bookkeeping
  -- absent from mathlib at this pin; it is isolated here as the single remaining
  -- `sorry`.  All of P1 and the SETUP above are sorry-free.
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
